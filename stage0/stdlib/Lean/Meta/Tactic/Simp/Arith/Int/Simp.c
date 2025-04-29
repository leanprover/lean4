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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__8;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__32;
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__12;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__16;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__42;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__37;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__15;
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__14;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__6;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2;
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__38;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__44;
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatEq(lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Expr_0__Lean_intLEPred;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__41;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Expr_0__Lean_intEqPred;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__43;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__6;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__8;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll_go(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__10;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__35;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1;
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__21;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntDvd(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__30;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__12;
uint8_t l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__27;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__34;
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__14;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__39;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__26;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__4;
extern lean_object* l_Lean_levelZero;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3;
lean_object* l_Array_get_x21Internal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__5;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__40;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isValidLe(lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___closed__1;
lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__7;
lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__33;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__46;
lean_object* l_Int_Linear_Poly_toExpr(lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__10;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__36;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_withAbstractAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__20;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll(lean_object*);
extern lean_object* l_Lean_levelOne;
extern lean_object* l___private_Lean_Expr_0__Lean_intAddFn;
extern lean_object* l_Lean_reflBoolTrue;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__31;
uint8_t l_Int_Linear_Poly_isValidEq(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__7;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__13;
lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__29;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__3;
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
lean_object* lean_int_ediv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__3;
lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__28;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__23;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__45;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__24;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27_go(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll_go(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Poly_gcdAll_go(x_1, x_2);
lean_dec(x_2);
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
x_7 = l_Int_Linear_Poly_gcdAll_go(x_6, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_gcdAll(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27_go(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Poly_gcdCoeffs_x27_go(x_1, x_2);
lean_dec(x_2);
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
x_6 = l_Int_Linear_Poly_gcdCoeffs_x27_go(x_5, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_gcdCoeffs_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_eq_false_of_divCoeff", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__7;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__8;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__10;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__11;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__12;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__14;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instNegInt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__16;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__17;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq_coeff", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__20;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__21;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__23;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__24;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__12;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__27;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq_var_const", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__29;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__30;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__30;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__26;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq_var", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__34;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__35;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__38;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__39;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_eq_true", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__41;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__42;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_eq_false", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__44;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__45;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_instInhabitedExpr;
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Array_get_x21Internal___boxed), 4, 3);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_4);
lean_inc(x_1);
lean_inc(x_11);
x_12 = l_Int_Linear_Expr_denoteExpr(x_11, x_1, x_5, x_6, x_7, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_2);
lean_inc(x_11);
x_16 = l_Int_Linear_Expr_denoteExpr(x_11, x_2, x_5, x_6, x_7, x_8, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_2010; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l___private_Lean_Expr_0__Lean_intEqPred;
x_21 = l_Lean_mkAppB(x_20, x_14, x_18);
lean_inc(x_2);
lean_inc(x_1);
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 0, x_1);
x_22 = l_Int_Linear_Expr_norm(x_12);
lean_dec(x_12);
x_2010 = l_Int_Linear_Poly_isUnsatEq(x_22);
if (x_2010 == 0)
{
uint8_t x_2011; 
x_2011 = l_Int_Linear_Poly_isValidEq(x_22);
if (x_2011 == 0)
{
lean_object* x_2012; uint8_t x_2013; 
lean_inc(x_22);
x_2012 = l_Int_Linear_Poly_toExpr(x_22);
x_2013 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_2012, x_1);
lean_dec(x_2012);
if (x_2013 == 0)
{
lean_object* x_2014; 
lean_free_object(x_16);
x_2014 = lean_box(0);
x_23 = x_2014;
goto block_2009;
}
else
{
lean_object* x_2015; uint8_t x_2016; 
x_2015 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__37;
x_2016 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_2, x_2015);
if (x_2016 == 0)
{
lean_object* x_2017; 
lean_free_object(x_16);
x_2017 = lean_box(0);
x_23 = x_2017;
goto block_2009;
}
else
{
lean_object* x_2018; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2018 = lean_box(0);
lean_ctor_set(x_16, 0, x_2018);
return x_16;
}
}
}
else
{
lean_object* x_2019; 
lean_dec(x_22);
lean_free_object(x_16);
lean_dec(x_11);
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2019 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_2019) == 0)
{
lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; 
x_2020 = lean_ctor_get(x_2019, 0);
lean_inc(x_2020);
x_2021 = lean_ctor_get(x_2019, 1);
lean_inc(x_2021);
lean_dec(x_2019);
x_2022 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2023 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2024 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__43;
x_2025 = l_Lean_reflBoolTrue;
x_2026 = l_Lean_mkApp4(x_2024, x_2020, x_2022, x_2023, x_2025);
x_2027 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__40;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2028 = l_Lean_Meta_mkEq(x_21, x_2027, x_5, x_6, x_7, x_8, x_2021);
if (lean_obj_tag(x_2028) == 0)
{
lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; 
x_2029 = lean_ctor_get(x_2028, 0);
lean_inc(x_2029);
x_2030 = lean_ctor_get(x_2028, 1);
lean_inc(x_2030);
lean_dec(x_2028);
x_2031 = l_Lean_Meta_mkExpectedTypeHint(x_2026, x_2029, x_5, x_6, x_7, x_8, x_2030);
if (lean_obj_tag(x_2031) == 0)
{
uint8_t x_2032; 
x_2032 = !lean_is_exclusive(x_2031);
if (x_2032 == 0)
{
lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; 
x_2033 = lean_ctor_get(x_2031, 0);
x_2034 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2034, 0, x_2027);
lean_ctor_set(x_2034, 1, x_2033);
x_2035 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2035, 0, x_2034);
lean_ctor_set(x_2031, 0, x_2035);
return x_2031;
}
else
{
lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; 
x_2036 = lean_ctor_get(x_2031, 0);
x_2037 = lean_ctor_get(x_2031, 1);
lean_inc(x_2037);
lean_inc(x_2036);
lean_dec(x_2031);
x_2038 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2038, 0, x_2027);
lean_ctor_set(x_2038, 1, x_2036);
x_2039 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2039, 0, x_2038);
x_2040 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2040, 0, x_2039);
lean_ctor_set(x_2040, 1, x_2037);
return x_2040;
}
}
else
{
uint8_t x_2041; 
x_2041 = !lean_is_exclusive(x_2031);
if (x_2041 == 0)
{
return x_2031;
}
else
{
lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; 
x_2042 = lean_ctor_get(x_2031, 0);
x_2043 = lean_ctor_get(x_2031, 1);
lean_inc(x_2043);
lean_inc(x_2042);
lean_dec(x_2031);
x_2044 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2044, 0, x_2042);
lean_ctor_set(x_2044, 1, x_2043);
return x_2044;
}
}
}
else
{
uint8_t x_2045; 
lean_dec(x_2026);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2045 = !lean_is_exclusive(x_2028);
if (x_2045 == 0)
{
return x_2028;
}
else
{
lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; 
x_2046 = lean_ctor_get(x_2028, 0);
x_2047 = lean_ctor_get(x_2028, 1);
lean_inc(x_2047);
lean_inc(x_2046);
lean_dec(x_2028);
x_2048 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2048, 0, x_2046);
lean_ctor_set(x_2048, 1, x_2047);
return x_2048;
}
}
}
else
{
uint8_t x_2049; 
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_2049 = !lean_is_exclusive(x_2019);
if (x_2049 == 0)
{
return x_2019;
}
else
{
lean_object* x_2050; lean_object* x_2051; lean_object* x_2052; 
x_2050 = lean_ctor_get(x_2019, 0);
x_2051 = lean_ctor_get(x_2019, 1);
lean_inc(x_2051);
lean_inc(x_2050);
lean_dec(x_2019);
x_2052 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2052, 0, x_2050);
lean_ctor_set(x_2052, 1, x_2051);
return x_2052;
}
}
}
}
else
{
lean_object* x_2053; 
lean_dec(x_22);
lean_free_object(x_16);
lean_dec(x_11);
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2053 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_2053) == 0)
{
lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; 
x_2054 = lean_ctor_get(x_2053, 0);
lean_inc(x_2054);
x_2055 = lean_ctor_get(x_2053, 1);
lean_inc(x_2055);
lean_dec(x_2053);
x_2056 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2057 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2058 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__46;
x_2059 = l_Lean_reflBoolTrue;
x_2060 = l_Lean_mkApp4(x_2058, x_2054, x_2056, x_2057, x_2059);
x_2061 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2062 = l_Lean_Meta_mkEq(x_21, x_2061, x_5, x_6, x_7, x_8, x_2055);
if (lean_obj_tag(x_2062) == 0)
{
lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; 
x_2063 = lean_ctor_get(x_2062, 0);
lean_inc(x_2063);
x_2064 = lean_ctor_get(x_2062, 1);
lean_inc(x_2064);
lean_dec(x_2062);
x_2065 = l_Lean_Meta_mkExpectedTypeHint(x_2060, x_2063, x_5, x_6, x_7, x_8, x_2064);
if (lean_obj_tag(x_2065) == 0)
{
uint8_t x_2066; 
x_2066 = !lean_is_exclusive(x_2065);
if (x_2066 == 0)
{
lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; 
x_2067 = lean_ctor_get(x_2065, 0);
x_2068 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2068, 0, x_2061);
lean_ctor_set(x_2068, 1, x_2067);
x_2069 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2069, 0, x_2068);
lean_ctor_set(x_2065, 0, x_2069);
return x_2065;
}
else
{
lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; 
x_2070 = lean_ctor_get(x_2065, 0);
x_2071 = lean_ctor_get(x_2065, 1);
lean_inc(x_2071);
lean_inc(x_2070);
lean_dec(x_2065);
x_2072 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2072, 0, x_2061);
lean_ctor_set(x_2072, 1, x_2070);
x_2073 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2073, 0, x_2072);
x_2074 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2074, 0, x_2073);
lean_ctor_set(x_2074, 1, x_2071);
return x_2074;
}
}
else
{
uint8_t x_2075; 
x_2075 = !lean_is_exclusive(x_2065);
if (x_2075 == 0)
{
return x_2065;
}
else
{
lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; 
x_2076 = lean_ctor_get(x_2065, 0);
x_2077 = lean_ctor_get(x_2065, 1);
lean_inc(x_2077);
lean_inc(x_2076);
lean_dec(x_2065);
x_2078 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2078, 0, x_2076);
lean_ctor_set(x_2078, 1, x_2077);
return x_2078;
}
}
}
else
{
uint8_t x_2079; 
lean_dec(x_2060);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2079 = !lean_is_exclusive(x_2062);
if (x_2079 == 0)
{
return x_2062;
}
else
{
lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; 
x_2080 = lean_ctor_get(x_2062, 0);
x_2081 = lean_ctor_get(x_2062, 1);
lean_inc(x_2081);
lean_inc(x_2080);
lean_dec(x_2062);
x_2082 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2082, 0, x_2080);
lean_ctor_set(x_2082, 1, x_2081);
return x_2082;
}
}
}
else
{
uint8_t x_2083; 
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_2083 = !lean_is_exclusive(x_2053);
if (x_2083 == 0)
{
return x_2053;
}
else
{
lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; 
x_2084 = lean_ctor_get(x_2053, 0);
x_2085 = lean_ctor_get(x_2053, 1);
lean_inc(x_2085);
lean_inc(x_2084);
lean_dec(x_2053);
x_2086 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2086, 0, x_2084);
lean_ctor_set(x_2086, 1, x_2085);
return x_2086;
}
}
}
block_2009:
{
lean_dec(x_23);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Int_Linear_Poly_gcdCoeffs_x27(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = l_Int_Linear_Poly_getConst(x_22);
x_28 = lean_nat_to_int(x_24);
x_29 = lean_int_emod(x_27, x_28);
lean_dec(x_27);
x_30 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_31 = lean_int_dec_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_11);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_35 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_39 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_40 = lean_int_dec_le(x_30, x_28);
x_41 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_42 = l_Lean_Meta_mkEq(x_21, x_41, x_5, x_6, x_7, x_8, x_37);
if (x_40 == 0)
{
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Expr_const___override(x_3, x_34);
x_46 = lean_int_neg(x_28);
lean_dec(x_28);
x_47 = l_Int_toNat(x_46);
lean_dec(x_46);
x_48 = l_Lean_instToExprInt_mkNat(x_47);
x_49 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_50 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_51 = l_Lean_mkApp3(x_49, x_45, x_50, x_48);
x_52 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_53 = l_Lean_reflBoolTrue;
x_54 = l_Lean_mkApp5(x_52, x_36, x_38, x_39, x_51, x_53);
x_55 = l_Lean_Meta_mkExpectedTypeHint(x_54, x_43, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_41);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_58);
lean_ctor_set(x_55, 0, x_22);
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_55, 0);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_61);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_22);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_free_object(x_22);
x_63 = !lean_is_exclusive(x_55);
if (x_63 == 0)
{
return x_55;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_55, 0);
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_55);
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
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_36);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_42);
if (x_67 == 0)
{
return x_42;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_42, 0);
x_69 = lean_ctor_get(x_42, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_42);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_42, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_42, 1);
lean_inc(x_72);
lean_dec(x_42);
x_73 = l_Int_toNat(x_28);
lean_dec(x_28);
x_74 = l_Lean_instToExprInt_mkNat(x_73);
x_75 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_76 = l_Lean_reflBoolTrue;
x_77 = l_Lean_mkApp5(x_75, x_36, x_38, x_39, x_74, x_76);
x_78 = l_Lean_Meta_mkExpectedTypeHint(x_77, x_71, x_5, x_6, x_7, x_8, x_72);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_41);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_81);
lean_ctor_set(x_78, 0, x_22);
return x_78;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_78, 0);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_78);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_41);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_84);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_22);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_free_object(x_22);
x_86 = !lean_is_exclusive(x_78);
if (x_86 == 0)
{
return x_78;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_78, 0);
x_88 = lean_ctor_get(x_78, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_78);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_36);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_90 = !lean_is_exclusive(x_42);
if (x_90 == 0)
{
return x_42;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_42, 0);
x_92 = lean_ctor_get(x_42, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_42);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_35);
if (x_94 == 0)
{
return x_35;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_35, 0);
x_96 = lean_ctor_get(x_35, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_35);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_22);
x_98 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_99 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_103 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_104 = lean_int_dec_le(x_30, x_28);
x_105 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_106 = l_Lean_Meta_mkEq(x_21, x_105, x_5, x_6, x_7, x_8, x_101);
if (x_104 == 0)
{
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Expr_const___override(x_3, x_98);
x_110 = lean_int_neg(x_28);
lean_dec(x_28);
x_111 = l_Int_toNat(x_110);
lean_dec(x_110);
x_112 = l_Lean_instToExprInt_mkNat(x_111);
x_113 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_114 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_115 = l_Lean_mkApp3(x_113, x_109, x_114, x_112);
x_116 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_117 = l_Lean_reflBoolTrue;
x_118 = l_Lean_mkApp5(x_116, x_100, x_102, x_103, x_115, x_117);
x_119 = l_Lean_Meta_mkExpectedTypeHint(x_118, x_107, x_5, x_6, x_7, x_8, x_108);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_105);
lean_ctor_set(x_123, 1, x_120);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
if (lean_is_scalar(x_122)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_122;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_121);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_119, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_119, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_128 = x_119;
} else {
 lean_dec_ref(x_119);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_130 = lean_ctor_get(x_106, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_106, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_132 = x_106;
} else {
 lean_dec_ref(x_106);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_134 = lean_ctor_get(x_106, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_106, 1);
lean_inc(x_135);
lean_dec(x_106);
x_136 = l_Int_toNat(x_28);
lean_dec(x_28);
x_137 = l_Lean_instToExprInt_mkNat(x_136);
x_138 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_139 = l_Lean_reflBoolTrue;
x_140 = l_Lean_mkApp5(x_138, x_100, x_102, x_103, x_137, x_139);
x_141 = l_Lean_Meta_mkExpectedTypeHint(x_140, x_134, x_5, x_6, x_7, x_8, x_135);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_105);
lean_ctor_set(x_145, 1, x_142);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
if (lean_is_scalar(x_144)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_144;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_143);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_141, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_141, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_150 = x_141;
} else {
 lean_dec_ref(x_141);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_152 = lean_ctor_get(x_106, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_106, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_154 = x_106;
} else {
 lean_dec_ref(x_106);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = lean_ctor_get(x_99, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_99, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_158 = x_99;
} else {
 lean_dec_ref(x_99);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
else
{
lean_object* x_160; uint8_t x_161; 
lean_inc(x_22);
x_160 = l_Int_Linear_Poly_div(x_28, x_22);
x_161 = !lean_is_exclusive(x_22);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = lean_ctor_get(x_22, 0);
lean_dec(x_162);
lean_inc(x_160);
x_163 = l_Int_Linear_Poly_denoteExpr(x_11, x_160, x_5, x_6, x_7, x_8, x_19);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = lean_ctor_get(x_163, 1);
x_167 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_168 = l_Lean_mkAppB(x_20, x_165, x_167);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_169 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_166);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_box(0);
x_173 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_174 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_175 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_160);
x_176 = lean_int_dec_le(x_30, x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_168);
x_177 = l_Lean_Meta_mkEq(x_21, x_168, x_5, x_6, x_7, x_8, x_171);
if (x_176 == 0)
{
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l_Lean_Expr_const___override(x_3, x_172);
x_181 = lean_int_neg(x_28);
lean_dec(x_28);
x_182 = l_Int_toNat(x_181);
lean_dec(x_181);
x_183 = l_Lean_instToExprInt_mkNat(x_182);
x_184 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_185 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_186 = l_Lean_mkApp3(x_184, x_180, x_185, x_183);
x_187 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_188 = l_Lean_reflBoolTrue;
x_189 = l_Lean_mkApp6(x_187, x_170, x_173, x_174, x_175, x_186, x_188);
x_190 = l_Lean_Meta_mkExpectedTypeHint(x_189, x_178, x_5, x_6, x_7, x_8, x_179);
if (lean_obj_tag(x_190) == 0)
{
uint8_t x_191; 
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_190, 0);
lean_ctor_set(x_163, 1, x_192);
lean_ctor_set(x_163, 0, x_168);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_163);
lean_ctor_set(x_190, 0, x_22);
return x_190;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_190, 0);
x_194 = lean_ctor_get(x_190, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_190);
lean_ctor_set(x_163, 1, x_193);
lean_ctor_set(x_163, 0, x_168);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_163);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_22);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
else
{
uint8_t x_196; 
lean_dec(x_168);
lean_free_object(x_163);
lean_free_object(x_22);
x_196 = !lean_is_exclusive(x_190);
if (x_196 == 0)
{
return x_190;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_190, 0);
x_198 = lean_ctor_get(x_190, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_190);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
uint8_t x_200; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_168);
lean_free_object(x_163);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_200 = !lean_is_exclusive(x_177);
if (x_200 == 0)
{
return x_177;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_177, 0);
x_202 = lean_ctor_get(x_177, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_177);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_204 = lean_ctor_get(x_177, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_177, 1);
lean_inc(x_205);
lean_dec(x_177);
x_206 = l_Int_toNat(x_28);
lean_dec(x_28);
x_207 = l_Lean_instToExprInt_mkNat(x_206);
x_208 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_209 = l_Lean_reflBoolTrue;
x_210 = l_Lean_mkApp6(x_208, x_170, x_173, x_174, x_175, x_207, x_209);
x_211 = l_Lean_Meta_mkExpectedTypeHint(x_210, x_204, x_5, x_6, x_7, x_8, x_205);
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_211, 0);
lean_ctor_set(x_163, 1, x_213);
lean_ctor_set(x_163, 0, x_168);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_163);
lean_ctor_set(x_211, 0, x_22);
return x_211;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_211, 0);
x_215 = lean_ctor_get(x_211, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_211);
lean_ctor_set(x_163, 1, x_214);
lean_ctor_set(x_163, 0, x_168);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_163);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_22);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
else
{
uint8_t x_217; 
lean_dec(x_168);
lean_free_object(x_163);
lean_free_object(x_22);
x_217 = !lean_is_exclusive(x_211);
if (x_217 == 0)
{
return x_211;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_211, 0);
x_219 = lean_ctor_get(x_211, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_211);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_168);
lean_free_object(x_163);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_221 = !lean_is_exclusive(x_177);
if (x_221 == 0)
{
return x_177;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_177, 0);
x_223 = lean_ctor_get(x_177, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_177);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
}
else
{
uint8_t x_225; 
lean_dec(x_168);
lean_free_object(x_163);
lean_free_object(x_22);
lean_dec(x_160);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_225 = !lean_is_exclusive(x_169);
if (x_225 == 0)
{
return x_169;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_169, 0);
x_227 = lean_ctor_get(x_169, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_169);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_163, 0);
x_230 = lean_ctor_get(x_163, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_163);
x_231 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_232 = l_Lean_mkAppB(x_20, x_229, x_231);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_233 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_230);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_box(0);
x_237 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_238 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_239 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_160);
x_240 = lean_int_dec_le(x_30, x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_232);
x_241 = l_Lean_Meta_mkEq(x_21, x_232, x_5, x_6, x_7, x_8, x_235);
if (x_240 == 0)
{
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_Expr_const___override(x_3, x_236);
x_245 = lean_int_neg(x_28);
lean_dec(x_28);
x_246 = l_Int_toNat(x_245);
lean_dec(x_245);
x_247 = l_Lean_instToExprInt_mkNat(x_246);
x_248 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_249 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_250 = l_Lean_mkApp3(x_248, x_244, x_249, x_247);
x_251 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_252 = l_Lean_reflBoolTrue;
x_253 = l_Lean_mkApp6(x_251, x_234, x_237, x_238, x_239, x_250, x_252);
x_254 = l_Lean_Meta_mkExpectedTypeHint(x_253, x_242, x_5, x_6, x_7, x_8, x_243);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_257 = x_254;
} else {
 lean_dec_ref(x_254);
 x_257 = lean_box(0);
}
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_232);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_258);
if (lean_is_scalar(x_257)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_257;
}
lean_ctor_set(x_259, 0, x_22);
lean_ctor_set(x_259, 1, x_256);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_232);
lean_free_object(x_22);
x_260 = lean_ctor_get(x_254, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_254, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_262 = x_254;
} else {
 lean_dec_ref(x_254);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_234);
lean_dec(x_232);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_264 = lean_ctor_get(x_241, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_241, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_266 = x_241;
} else {
 lean_dec_ref(x_241);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_268 = lean_ctor_get(x_241, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_241, 1);
lean_inc(x_269);
lean_dec(x_241);
x_270 = l_Int_toNat(x_28);
lean_dec(x_28);
x_271 = l_Lean_instToExprInt_mkNat(x_270);
x_272 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_273 = l_Lean_reflBoolTrue;
x_274 = l_Lean_mkApp6(x_272, x_234, x_237, x_238, x_239, x_271, x_273);
x_275 = l_Lean_Meta_mkExpectedTypeHint(x_274, x_268, x_5, x_6, x_7, x_8, x_269);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_278 = x_275;
} else {
 lean_dec_ref(x_275);
 x_278 = lean_box(0);
}
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_232);
lean_ctor_set(x_279, 1, x_276);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_279);
if (lean_is_scalar(x_278)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_278;
}
lean_ctor_set(x_280, 0, x_22);
lean_ctor_set(x_280, 1, x_277);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_232);
lean_free_object(x_22);
x_281 = lean_ctor_get(x_275, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_275, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_283 = x_275;
} else {
 lean_dec_ref(x_275);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_234);
lean_dec(x_232);
lean_free_object(x_22);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_285 = lean_ctor_get(x_241, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_241, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_287 = x_241;
} else {
 lean_dec_ref(x_241);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_232);
lean_free_object(x_22);
lean_dec(x_160);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_289 = lean_ctor_get(x_233, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_233, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_291 = x_233;
} else {
 lean_dec_ref(x_233);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_290);
return x_292;
}
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_22);
lean_inc(x_160);
x_293 = l_Int_Linear_Poly_denoteExpr(x_11, x_160, x_5, x_6, x_7, x_8, x_19);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_296 = x_293;
} else {
 lean_dec_ref(x_293);
 x_296 = lean_box(0);
}
x_297 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_298 = l_Lean_mkAppB(x_20, x_294, x_297);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_299 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_295);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_box(0);
x_303 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_304 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_305 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_160);
x_306 = lean_int_dec_le(x_30, x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_298);
x_307 = l_Lean_Meta_mkEq(x_21, x_298, x_5, x_6, x_7, x_8, x_301);
if (x_306 == 0)
{
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = l_Lean_Expr_const___override(x_3, x_302);
x_311 = lean_int_neg(x_28);
lean_dec(x_28);
x_312 = l_Int_toNat(x_311);
lean_dec(x_311);
x_313 = l_Lean_instToExprInt_mkNat(x_312);
x_314 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_315 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_316 = l_Lean_mkApp3(x_314, x_310, x_315, x_313);
x_317 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_318 = l_Lean_reflBoolTrue;
x_319 = l_Lean_mkApp6(x_317, x_300, x_303, x_304, x_305, x_316, x_318);
x_320 = l_Lean_Meta_mkExpectedTypeHint(x_319, x_308, x_5, x_6, x_7, x_8, x_309);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_323 = x_320;
} else {
 lean_dec_ref(x_320);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_296;
}
lean_ctor_set(x_324, 0, x_298);
lean_ctor_set(x_324, 1, x_321);
x_325 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_325, 0, x_324);
if (lean_is_scalar(x_323)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_323;
}
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_322);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_298);
lean_dec(x_296);
x_327 = lean_ctor_get(x_320, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_320, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_329 = x_320;
} else {
 lean_dec_ref(x_320);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_300);
lean_dec(x_298);
lean_dec(x_296);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_331 = lean_ctor_get(x_307, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_307, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_333 = x_307;
} else {
 lean_dec_ref(x_307);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_335 = lean_ctor_get(x_307, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_307, 1);
lean_inc(x_336);
lean_dec(x_307);
x_337 = l_Int_toNat(x_28);
lean_dec(x_28);
x_338 = l_Lean_instToExprInt_mkNat(x_337);
x_339 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_340 = l_Lean_reflBoolTrue;
x_341 = l_Lean_mkApp6(x_339, x_300, x_303, x_304, x_305, x_338, x_340);
x_342 = l_Lean_Meta_mkExpectedTypeHint(x_341, x_335, x_5, x_6, x_7, x_8, x_336);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_345 = x_342;
} else {
 lean_dec_ref(x_342);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_296;
}
lean_ctor_set(x_346, 0, x_298);
lean_ctor_set(x_346, 1, x_343);
x_347 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_347, 0, x_346);
if (lean_is_scalar(x_345)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_345;
}
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_344);
return x_348;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_298);
lean_dec(x_296);
x_349 = lean_ctor_get(x_342, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_342, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_351 = x_342;
} else {
 lean_dec_ref(x_342);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_351)) {
 x_352 = lean_alloc_ctor(1, 2, 0);
} else {
 x_352 = x_351;
}
lean_ctor_set(x_352, 0, x_349);
lean_ctor_set(x_352, 1, x_350);
return x_352;
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_300);
lean_dec(x_298);
lean_dec(x_296);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_353 = lean_ctor_get(x_307, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_307, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_355 = x_307;
} else {
 lean_dec_ref(x_307);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_354);
return x_356;
}
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_298);
lean_dec(x_296);
lean_dec(x_160);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_357 = lean_ctor_get(x_299, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_299, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_359 = x_299;
} else {
 lean_dec_ref(x_299);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
}
}
else
{
lean_object* x_361; uint8_t x_362; 
lean_dec(x_24);
lean_dec(x_3);
lean_inc(x_22);
x_361 = l_Int_Linear_Poly_denoteExpr(x_11, x_22, x_5, x_6, x_7, x_8, x_19);
x_362 = !lean_is_exclusive(x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_363 = lean_ctor_get(x_361, 0);
x_364 = lean_ctor_get(x_361, 1);
x_365 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_366 = l_Lean_mkAppB(x_20, x_363, x_365);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_367 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_364);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_371 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
lean_inc(x_22);
x_372 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_22);
x_373 = !lean_is_exclusive(x_22);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_374 = lean_ctor_get(x_22, 0);
lean_dec(x_374);
x_375 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_376 = l_Lean_reflBoolTrue;
x_377 = l_Lean_mkApp5(x_375, x_368, x_370, x_371, x_372, x_376);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_366);
x_378 = l_Lean_Meta_mkEq(x_21, x_366, x_5, x_6, x_7, x_8, x_369);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = l_Lean_Meta_mkExpectedTypeHint(x_377, x_379, x_5, x_6, x_7, x_8, x_380);
if (lean_obj_tag(x_381) == 0)
{
uint8_t x_382; 
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; 
x_383 = lean_ctor_get(x_381, 0);
lean_ctor_set(x_361, 1, x_383);
lean_ctor_set(x_361, 0, x_366);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_361);
lean_ctor_set(x_381, 0, x_22);
return x_381;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = lean_ctor_get(x_381, 0);
x_385 = lean_ctor_get(x_381, 1);
lean_inc(x_385);
lean_inc(x_384);
lean_dec(x_381);
lean_ctor_set(x_361, 1, x_384);
lean_ctor_set(x_361, 0, x_366);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_361);
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_22);
lean_ctor_set(x_386, 1, x_385);
return x_386;
}
}
else
{
uint8_t x_387; 
lean_free_object(x_22);
lean_dec(x_366);
lean_free_object(x_361);
x_387 = !lean_is_exclusive(x_381);
if (x_387 == 0)
{
return x_381;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_381, 0);
x_389 = lean_ctor_get(x_381, 1);
lean_inc(x_389);
lean_inc(x_388);
lean_dec(x_381);
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
return x_390;
}
}
}
else
{
uint8_t x_391; 
lean_dec(x_377);
lean_free_object(x_22);
lean_dec(x_366);
lean_free_object(x_361);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_391 = !lean_is_exclusive(x_378);
if (x_391 == 0)
{
return x_378;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_378, 0);
x_393 = lean_ctor_get(x_378, 1);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_378);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
return x_394;
}
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_22);
x_395 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_396 = l_Lean_reflBoolTrue;
x_397 = l_Lean_mkApp5(x_395, x_368, x_370, x_371, x_372, x_396);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_366);
x_398 = l_Lean_Meta_mkEq(x_21, x_366, x_5, x_6, x_7, x_8, x_369);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = l_Lean_Meta_mkExpectedTypeHint(x_397, x_399, x_5, x_6, x_7, x_8, x_400);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_404 = x_401;
} else {
 lean_dec_ref(x_401);
 x_404 = lean_box(0);
}
lean_ctor_set(x_361, 1, x_402);
lean_ctor_set(x_361, 0, x_366);
x_405 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_405, 0, x_361);
if (lean_is_scalar(x_404)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_404;
}
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_403);
return x_406;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_366);
lean_free_object(x_361);
x_407 = lean_ctor_get(x_401, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_401, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_409 = x_401;
} else {
 lean_dec_ref(x_401);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_397);
lean_dec(x_366);
lean_free_object(x_361);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_411 = lean_ctor_get(x_398, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_398, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_413 = x_398;
} else {
 lean_dec_ref(x_398);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 2, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_412);
return x_414;
}
}
}
else
{
uint8_t x_415; 
lean_dec(x_366);
lean_free_object(x_361);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_415 = !lean_is_exclusive(x_367);
if (x_415 == 0)
{
return x_367;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_367, 0);
x_417 = lean_ctor_get(x_367, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_367);
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
return x_418;
}
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_419 = lean_ctor_get(x_361, 0);
x_420 = lean_ctor_get(x_361, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_361);
x_421 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_422 = l_Lean_mkAppB(x_20, x_419, x_421);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_423 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_420);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
x_426 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_427 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
lean_inc(x_22);
x_428 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_22);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_429 = x_22;
} else {
 lean_dec_ref(x_22);
 x_429 = lean_box(0);
}
x_430 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_431 = l_Lean_reflBoolTrue;
x_432 = l_Lean_mkApp5(x_430, x_424, x_426, x_427, x_428, x_431);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_422);
x_433 = l_Lean_Meta_mkEq(x_21, x_422, x_5, x_6, x_7, x_8, x_425);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
x_436 = l_Lean_Meta_mkExpectedTypeHint(x_432, x_434, x_5, x_6, x_7, x_8, x_435);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_439 = x_436;
} else {
 lean_dec_ref(x_436);
 x_439 = lean_box(0);
}
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_422);
lean_ctor_set(x_440, 1, x_437);
if (lean_is_scalar(x_429)) {
 x_441 = lean_alloc_ctor(1, 1, 0);
} else {
 x_441 = x_429;
 lean_ctor_set_tag(x_441, 1);
}
lean_ctor_set(x_441, 0, x_440);
if (lean_is_scalar(x_439)) {
 x_442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_442 = x_439;
}
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_438);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_429);
lean_dec(x_422);
x_443 = lean_ctor_get(x_436, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_436, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_445 = x_436;
} else {
 lean_dec_ref(x_436);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(1, 2, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_443);
lean_ctor_set(x_446, 1, x_444);
return x_446;
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_432);
lean_dec(x_429);
lean_dec(x_422);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_447 = lean_ctor_get(x_433, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_433, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_449 = x_433;
} else {
 lean_dec_ref(x_433);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_450 = lean_alloc_ctor(1, 2, 0);
} else {
 x_450 = x_449;
}
lean_ctor_set(x_450, 0, x_447);
lean_ctor_set(x_450, 1, x_448);
return x_450;
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_422);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_451 = lean_ctor_get(x_423, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_423, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_453 = x_423;
} else {
 lean_dec_ref(x_423);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 2, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_451);
lean_ctor_set(x_454, 1, x_452);
return x_454;
}
}
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; 
x_455 = lean_ctor_get(x_22, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_22, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_22, 2);
lean_inc(x_457);
x_458 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__26;
x_459 = lean_int_dec_eq(x_455, x_458);
lean_dec(x_455);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; uint8_t x_462; 
lean_dec(x_457);
lean_dec(x_456);
x_460 = l_Int_Linear_Poly_gcdCoeffs_x27(x_22);
x_461 = lean_unsigned_to_nat(1u);
x_462 = lean_nat_dec_eq(x_460, x_461);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; 
x_463 = l_Int_Linear_Poly_getConst(x_22);
x_464 = lean_nat_to_int(x_460);
x_465 = lean_int_emod(x_463, x_464);
lean_dec(x_463);
x_466 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_467 = lean_int_dec_eq(x_465, x_466);
lean_dec(x_465);
if (x_467 == 0)
{
lean_object* x_468; lean_object* x_469; 
lean_dec(x_22);
lean_dec(x_11);
x_468 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_469 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; lean_object* x_475; lean_object* x_476; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
lean_dec(x_469);
x_472 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_473 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_474 = lean_int_dec_le(x_466, x_464);
x_475 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_476 = l_Lean_Meta_mkEq(x_21, x_475, x_5, x_6, x_7, x_8, x_471);
if (x_474 == 0)
{
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
x_479 = l_Lean_Expr_const___override(x_3, x_468);
x_480 = lean_int_neg(x_464);
lean_dec(x_464);
x_481 = l_Int_toNat(x_480);
lean_dec(x_480);
x_482 = l_Lean_instToExprInt_mkNat(x_481);
x_483 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_484 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_485 = l_Lean_mkApp3(x_483, x_479, x_484, x_482);
x_486 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_487 = l_Lean_reflBoolTrue;
x_488 = l_Lean_mkApp5(x_486, x_470, x_472, x_473, x_485, x_487);
x_489 = l_Lean_Meta_mkExpectedTypeHint(x_488, x_477, x_5, x_6, x_7, x_8, x_478);
if (lean_obj_tag(x_489) == 0)
{
uint8_t x_490; 
x_490 = !lean_is_exclusive(x_489);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_489, 0);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_475);
lean_ctor_set(x_492, 1, x_491);
x_493 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_489, 0, x_493);
return x_489;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_494 = lean_ctor_get(x_489, 0);
x_495 = lean_ctor_get(x_489, 1);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_489);
x_496 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_496, 0, x_475);
lean_ctor_set(x_496, 1, x_494);
x_497 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_497, 0, x_496);
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_495);
return x_498;
}
}
else
{
uint8_t x_499; 
x_499 = !lean_is_exclusive(x_489);
if (x_499 == 0)
{
return x_489;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_ctor_get(x_489, 0);
x_501 = lean_ctor_get(x_489, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_489);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
return x_502;
}
}
}
else
{
uint8_t x_503; 
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_470);
lean_dec(x_464);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_503 = !lean_is_exclusive(x_476);
if (x_503 == 0)
{
return x_476;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_476, 0);
x_505 = lean_ctor_get(x_476, 1);
lean_inc(x_505);
lean_inc(x_504);
lean_dec(x_476);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
return x_506;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_507 = lean_ctor_get(x_476, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_476, 1);
lean_inc(x_508);
lean_dec(x_476);
x_509 = l_Int_toNat(x_464);
lean_dec(x_464);
x_510 = l_Lean_instToExprInt_mkNat(x_509);
x_511 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_512 = l_Lean_reflBoolTrue;
x_513 = l_Lean_mkApp5(x_511, x_470, x_472, x_473, x_510, x_512);
x_514 = l_Lean_Meta_mkExpectedTypeHint(x_513, x_507, x_5, x_6, x_7, x_8, x_508);
if (lean_obj_tag(x_514) == 0)
{
uint8_t x_515; 
x_515 = !lean_is_exclusive(x_514);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_514, 0);
x_517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_517, 0, x_475);
lean_ctor_set(x_517, 1, x_516);
x_518 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_514, 0, x_518);
return x_514;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_519 = lean_ctor_get(x_514, 0);
x_520 = lean_ctor_get(x_514, 1);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_514);
x_521 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_521, 0, x_475);
lean_ctor_set(x_521, 1, x_519);
x_522 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_522, 0, x_521);
x_523 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_523, 0, x_522);
lean_ctor_set(x_523, 1, x_520);
return x_523;
}
}
else
{
uint8_t x_524; 
x_524 = !lean_is_exclusive(x_514);
if (x_524 == 0)
{
return x_514;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_525 = lean_ctor_get(x_514, 0);
x_526 = lean_ctor_get(x_514, 1);
lean_inc(x_526);
lean_inc(x_525);
lean_dec(x_514);
x_527 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_527, 0, x_525);
lean_ctor_set(x_527, 1, x_526);
return x_527;
}
}
}
else
{
uint8_t x_528; 
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_470);
lean_dec(x_464);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_528 = !lean_is_exclusive(x_476);
if (x_528 == 0)
{
return x_476;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_476, 0);
x_530 = lean_ctor_get(x_476, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_476);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
return x_531;
}
}
}
}
else
{
uint8_t x_532; 
lean_dec(x_464);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_532 = !lean_is_exclusive(x_469);
if (x_532 == 0)
{
return x_469;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_533 = lean_ctor_get(x_469, 0);
x_534 = lean_ctor_get(x_469, 1);
lean_inc(x_534);
lean_inc(x_533);
lean_dec(x_469);
x_535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_535, 0, x_533);
lean_ctor_set(x_535, 1, x_534);
return x_535;
}
}
}
else
{
lean_object* x_536; lean_object* x_537; uint8_t x_538; 
x_536 = l_Int_Linear_Poly_div(x_464, x_22);
lean_inc(x_536);
x_537 = l_Int_Linear_Poly_denoteExpr(x_11, x_536, x_5, x_6, x_7, x_8, x_19);
x_538 = !lean_is_exclusive(x_537);
if (x_538 == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_539 = lean_ctor_get(x_537, 0);
x_540 = lean_ctor_get(x_537, 1);
x_541 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_542 = l_Lean_mkAppB(x_20, x_539, x_541);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_543 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_540);
if (lean_obj_tag(x_543) == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; uint8_t x_550; lean_object* x_551; 
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec(x_543);
x_546 = lean_box(0);
x_547 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_548 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_549 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_536);
x_550 = lean_int_dec_le(x_466, x_464);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_542);
x_551 = l_Lean_Meta_mkEq(x_21, x_542, x_5, x_6, x_7, x_8, x_545);
if (x_550 == 0)
{
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
x_554 = l_Lean_Expr_const___override(x_3, x_546);
x_555 = lean_int_neg(x_464);
lean_dec(x_464);
x_556 = l_Int_toNat(x_555);
lean_dec(x_555);
x_557 = l_Lean_instToExprInt_mkNat(x_556);
x_558 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_559 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_560 = l_Lean_mkApp3(x_558, x_554, x_559, x_557);
x_561 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_562 = l_Lean_reflBoolTrue;
x_563 = l_Lean_mkApp6(x_561, x_544, x_547, x_548, x_549, x_560, x_562);
x_564 = l_Lean_Meta_mkExpectedTypeHint(x_563, x_552, x_5, x_6, x_7, x_8, x_553);
if (lean_obj_tag(x_564) == 0)
{
uint8_t x_565; 
x_565 = !lean_is_exclusive(x_564);
if (x_565 == 0)
{
lean_object* x_566; lean_object* x_567; 
x_566 = lean_ctor_get(x_564, 0);
lean_ctor_set(x_537, 1, x_566);
lean_ctor_set(x_537, 0, x_542);
x_567 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_567, 0, x_537);
lean_ctor_set(x_564, 0, x_567);
return x_564;
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_568 = lean_ctor_get(x_564, 0);
x_569 = lean_ctor_get(x_564, 1);
lean_inc(x_569);
lean_inc(x_568);
lean_dec(x_564);
lean_ctor_set(x_537, 1, x_568);
lean_ctor_set(x_537, 0, x_542);
x_570 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_570, 0, x_537);
x_571 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_569);
return x_571;
}
}
else
{
uint8_t x_572; 
lean_dec(x_542);
lean_free_object(x_537);
x_572 = !lean_is_exclusive(x_564);
if (x_572 == 0)
{
return x_564;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_573 = lean_ctor_get(x_564, 0);
x_574 = lean_ctor_get(x_564, 1);
lean_inc(x_574);
lean_inc(x_573);
lean_dec(x_564);
x_575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_575, 0, x_573);
lean_ctor_set(x_575, 1, x_574);
return x_575;
}
}
}
else
{
uint8_t x_576; 
lean_dec(x_549);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_544);
lean_dec(x_542);
lean_free_object(x_537);
lean_dec(x_464);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_576 = !lean_is_exclusive(x_551);
if (x_576 == 0)
{
return x_551;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_577 = lean_ctor_get(x_551, 0);
x_578 = lean_ctor_get(x_551, 1);
lean_inc(x_578);
lean_inc(x_577);
lean_dec(x_551);
x_579 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_579, 0, x_577);
lean_ctor_set(x_579, 1, x_578);
return x_579;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_580 = lean_ctor_get(x_551, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_551, 1);
lean_inc(x_581);
lean_dec(x_551);
x_582 = l_Int_toNat(x_464);
lean_dec(x_464);
x_583 = l_Lean_instToExprInt_mkNat(x_582);
x_584 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_585 = l_Lean_reflBoolTrue;
x_586 = l_Lean_mkApp6(x_584, x_544, x_547, x_548, x_549, x_583, x_585);
x_587 = l_Lean_Meta_mkExpectedTypeHint(x_586, x_580, x_5, x_6, x_7, x_8, x_581);
if (lean_obj_tag(x_587) == 0)
{
uint8_t x_588; 
x_588 = !lean_is_exclusive(x_587);
if (x_588 == 0)
{
lean_object* x_589; lean_object* x_590; 
x_589 = lean_ctor_get(x_587, 0);
lean_ctor_set(x_537, 1, x_589);
lean_ctor_set(x_537, 0, x_542);
x_590 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_590, 0, x_537);
lean_ctor_set(x_587, 0, x_590);
return x_587;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_591 = lean_ctor_get(x_587, 0);
x_592 = lean_ctor_get(x_587, 1);
lean_inc(x_592);
lean_inc(x_591);
lean_dec(x_587);
lean_ctor_set(x_537, 1, x_591);
lean_ctor_set(x_537, 0, x_542);
x_593 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_593, 0, x_537);
x_594 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_594, 0, x_593);
lean_ctor_set(x_594, 1, x_592);
return x_594;
}
}
else
{
uint8_t x_595; 
lean_dec(x_542);
lean_free_object(x_537);
x_595 = !lean_is_exclusive(x_587);
if (x_595 == 0)
{
return x_587;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_596 = lean_ctor_get(x_587, 0);
x_597 = lean_ctor_get(x_587, 1);
lean_inc(x_597);
lean_inc(x_596);
lean_dec(x_587);
x_598 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_598, 0, x_596);
lean_ctor_set(x_598, 1, x_597);
return x_598;
}
}
}
else
{
uint8_t x_599; 
lean_dec(x_549);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_544);
lean_dec(x_542);
lean_free_object(x_537);
lean_dec(x_464);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_599 = !lean_is_exclusive(x_551);
if (x_599 == 0)
{
return x_551;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_551, 0);
x_601 = lean_ctor_get(x_551, 1);
lean_inc(x_601);
lean_inc(x_600);
lean_dec(x_551);
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
return x_602;
}
}
}
}
else
{
uint8_t x_603; 
lean_dec(x_542);
lean_free_object(x_537);
lean_dec(x_536);
lean_dec(x_464);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_603 = !lean_is_exclusive(x_543);
if (x_603 == 0)
{
return x_543;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_604 = lean_ctor_get(x_543, 0);
x_605 = lean_ctor_get(x_543, 1);
lean_inc(x_605);
lean_inc(x_604);
lean_dec(x_543);
x_606 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_606, 0, x_604);
lean_ctor_set(x_606, 1, x_605);
return x_606;
}
}
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_607 = lean_ctor_get(x_537, 0);
x_608 = lean_ctor_get(x_537, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_537);
x_609 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_610 = l_Lean_mkAppB(x_20, x_607, x_609);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_611 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_608);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; uint8_t x_618; lean_object* x_619; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
lean_dec(x_611);
x_614 = lean_box(0);
x_615 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_616 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_617 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_536);
x_618 = lean_int_dec_le(x_466, x_464);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_610);
x_619 = l_Lean_Meta_mkEq(x_21, x_610, x_5, x_6, x_7, x_8, x_613);
if (x_618 == 0)
{
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
lean_dec(x_619);
x_622 = l_Lean_Expr_const___override(x_3, x_614);
x_623 = lean_int_neg(x_464);
lean_dec(x_464);
x_624 = l_Int_toNat(x_623);
lean_dec(x_623);
x_625 = l_Lean_instToExprInt_mkNat(x_624);
x_626 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_627 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_628 = l_Lean_mkApp3(x_626, x_622, x_627, x_625);
x_629 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_630 = l_Lean_reflBoolTrue;
x_631 = l_Lean_mkApp6(x_629, x_612, x_615, x_616, x_617, x_628, x_630);
x_632 = l_Lean_Meta_mkExpectedTypeHint(x_631, x_620, x_5, x_6, x_7, x_8, x_621);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_635 = x_632;
} else {
 lean_dec_ref(x_632);
 x_635 = lean_box(0);
}
x_636 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_636, 0, x_610);
lean_ctor_set(x_636, 1, x_633);
x_637 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_637, 0, x_636);
if (lean_is_scalar(x_635)) {
 x_638 = lean_alloc_ctor(0, 2, 0);
} else {
 x_638 = x_635;
}
lean_ctor_set(x_638, 0, x_637);
lean_ctor_set(x_638, 1, x_634);
return x_638;
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
lean_dec(x_610);
x_639 = lean_ctor_get(x_632, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_632, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_641 = x_632;
} else {
 lean_dec_ref(x_632);
 x_641 = lean_box(0);
}
if (lean_is_scalar(x_641)) {
 x_642 = lean_alloc_ctor(1, 2, 0);
} else {
 x_642 = x_641;
}
lean_ctor_set(x_642, 0, x_639);
lean_ctor_set(x_642, 1, x_640);
return x_642;
}
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_612);
lean_dec(x_610);
lean_dec(x_464);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_643 = lean_ctor_get(x_619, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_619, 1);
lean_inc(x_644);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_645 = x_619;
} else {
 lean_dec_ref(x_619);
 x_645 = lean_box(0);
}
if (lean_is_scalar(x_645)) {
 x_646 = lean_alloc_ctor(1, 2, 0);
} else {
 x_646 = x_645;
}
lean_ctor_set(x_646, 0, x_643);
lean_ctor_set(x_646, 1, x_644);
return x_646;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_647 = lean_ctor_get(x_619, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_619, 1);
lean_inc(x_648);
lean_dec(x_619);
x_649 = l_Int_toNat(x_464);
lean_dec(x_464);
x_650 = l_Lean_instToExprInt_mkNat(x_649);
x_651 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_652 = l_Lean_reflBoolTrue;
x_653 = l_Lean_mkApp6(x_651, x_612, x_615, x_616, x_617, x_650, x_652);
x_654 = l_Lean_Meta_mkExpectedTypeHint(x_653, x_647, x_5, x_6, x_7, x_8, x_648);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_654, 1);
lean_inc(x_656);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 x_657 = x_654;
} else {
 lean_dec_ref(x_654);
 x_657 = lean_box(0);
}
x_658 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_658, 0, x_610);
lean_ctor_set(x_658, 1, x_655);
x_659 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_659, 0, x_658);
if (lean_is_scalar(x_657)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_657;
}
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_656);
return x_660;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_610);
x_661 = lean_ctor_get(x_654, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_654, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 x_663 = x_654;
} else {
 lean_dec_ref(x_654);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_662);
return x_664;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_612);
lean_dec(x_610);
lean_dec(x_464);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_665 = lean_ctor_get(x_619, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_619, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_667 = x_619;
} else {
 lean_dec_ref(x_619);
 x_667 = lean_box(0);
}
if (lean_is_scalar(x_667)) {
 x_668 = lean_alloc_ctor(1, 2, 0);
} else {
 x_668 = x_667;
}
lean_ctor_set(x_668, 0, x_665);
lean_ctor_set(x_668, 1, x_666);
return x_668;
}
}
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_610);
lean_dec(x_536);
lean_dec(x_464);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_669 = lean_ctor_get(x_611, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_611, 1);
lean_inc(x_670);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 x_671 = x_611;
} else {
 lean_dec_ref(x_611);
 x_671 = lean_box(0);
}
if (lean_is_scalar(x_671)) {
 x_672 = lean_alloc_ctor(1, 2, 0);
} else {
 x_672 = x_671;
}
lean_ctor_set(x_672, 0, x_669);
lean_ctor_set(x_672, 1, x_670);
return x_672;
}
}
}
}
else
{
lean_object* x_673; uint8_t x_674; 
lean_dec(x_460);
lean_dec(x_3);
lean_inc(x_22);
x_673 = l_Int_Linear_Poly_denoteExpr(x_11, x_22, x_5, x_6, x_7, x_8, x_19);
x_674 = !lean_is_exclusive(x_673);
if (x_674 == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_675 = lean_ctor_get(x_673, 0);
x_676 = lean_ctor_get(x_673, 1);
x_677 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_678 = l_Lean_mkAppB(x_20, x_675, x_677);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_679 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_676);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 1);
lean_inc(x_681);
lean_dec(x_679);
x_682 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_683 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_684 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_22);
x_685 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_686 = l_Lean_reflBoolTrue;
x_687 = l_Lean_mkApp5(x_685, x_680, x_682, x_683, x_684, x_686);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_678);
x_688 = l_Lean_Meta_mkEq(x_21, x_678, x_5, x_6, x_7, x_8, x_681);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
lean_dec(x_688);
x_691 = l_Lean_Meta_mkExpectedTypeHint(x_687, x_689, x_5, x_6, x_7, x_8, x_690);
if (lean_obj_tag(x_691) == 0)
{
uint8_t x_692; 
x_692 = !lean_is_exclusive(x_691);
if (x_692 == 0)
{
lean_object* x_693; lean_object* x_694; 
x_693 = lean_ctor_get(x_691, 0);
lean_ctor_set(x_673, 1, x_693);
lean_ctor_set(x_673, 0, x_678);
x_694 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_694, 0, x_673);
lean_ctor_set(x_691, 0, x_694);
return x_691;
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_695 = lean_ctor_get(x_691, 0);
x_696 = lean_ctor_get(x_691, 1);
lean_inc(x_696);
lean_inc(x_695);
lean_dec(x_691);
lean_ctor_set(x_673, 1, x_695);
lean_ctor_set(x_673, 0, x_678);
x_697 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_697, 0, x_673);
x_698 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_698, 0, x_697);
lean_ctor_set(x_698, 1, x_696);
return x_698;
}
}
else
{
uint8_t x_699; 
lean_dec(x_678);
lean_free_object(x_673);
x_699 = !lean_is_exclusive(x_691);
if (x_699 == 0)
{
return x_691;
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_700 = lean_ctor_get(x_691, 0);
x_701 = lean_ctor_get(x_691, 1);
lean_inc(x_701);
lean_inc(x_700);
lean_dec(x_691);
x_702 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_702, 0, x_700);
lean_ctor_set(x_702, 1, x_701);
return x_702;
}
}
}
else
{
uint8_t x_703; 
lean_dec(x_687);
lean_dec(x_678);
lean_free_object(x_673);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_703 = !lean_is_exclusive(x_688);
if (x_703 == 0)
{
return x_688;
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_704 = lean_ctor_get(x_688, 0);
x_705 = lean_ctor_get(x_688, 1);
lean_inc(x_705);
lean_inc(x_704);
lean_dec(x_688);
x_706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set(x_706, 1, x_705);
return x_706;
}
}
}
else
{
uint8_t x_707; 
lean_dec(x_678);
lean_free_object(x_673);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_707 = !lean_is_exclusive(x_679);
if (x_707 == 0)
{
return x_679;
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; 
x_708 = lean_ctor_get(x_679, 0);
x_709 = lean_ctor_get(x_679, 1);
lean_inc(x_709);
lean_inc(x_708);
lean_dec(x_679);
x_710 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_710, 0, x_708);
lean_ctor_set(x_710, 1, x_709);
return x_710;
}
}
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_711 = lean_ctor_get(x_673, 0);
x_712 = lean_ctor_get(x_673, 1);
lean_inc(x_712);
lean_inc(x_711);
lean_dec(x_673);
x_713 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_714 = l_Lean_mkAppB(x_20, x_711, x_713);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_715 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_712);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
lean_dec(x_715);
x_718 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_719 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_720 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_22);
x_721 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_722 = l_Lean_reflBoolTrue;
x_723 = l_Lean_mkApp5(x_721, x_716, x_718, x_719, x_720, x_722);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_714);
x_724 = l_Lean_Meta_mkEq(x_21, x_714, x_5, x_6, x_7, x_8, x_717);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
x_727 = l_Lean_Meta_mkExpectedTypeHint(x_723, x_725, x_5, x_6, x_7, x_8, x_726);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_730 = x_727;
} else {
 lean_dec_ref(x_727);
 x_730 = lean_box(0);
}
x_731 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_731, 0, x_714);
lean_ctor_set(x_731, 1, x_728);
x_732 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_732, 0, x_731);
if (lean_is_scalar(x_730)) {
 x_733 = lean_alloc_ctor(0, 2, 0);
} else {
 x_733 = x_730;
}
lean_ctor_set(x_733, 0, x_732);
lean_ctor_set(x_733, 1, x_729);
return x_733;
}
else
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
lean_dec(x_714);
x_734 = lean_ctor_get(x_727, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_727, 1);
lean_inc(x_735);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_736 = x_727;
} else {
 lean_dec_ref(x_727);
 x_736 = lean_box(0);
}
if (lean_is_scalar(x_736)) {
 x_737 = lean_alloc_ctor(1, 2, 0);
} else {
 x_737 = x_736;
}
lean_ctor_set(x_737, 0, x_734);
lean_ctor_set(x_737, 1, x_735);
return x_737;
}
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
lean_dec(x_723);
lean_dec(x_714);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_738 = lean_ctor_get(x_724, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_724, 1);
lean_inc(x_739);
if (lean_is_exclusive(x_724)) {
 lean_ctor_release(x_724, 0);
 lean_ctor_release(x_724, 1);
 x_740 = x_724;
} else {
 lean_dec_ref(x_724);
 x_740 = lean_box(0);
}
if (lean_is_scalar(x_740)) {
 x_741 = lean_alloc_ctor(1, 2, 0);
} else {
 x_741 = x_740;
}
lean_ctor_set(x_741, 0, x_738);
lean_ctor_set(x_741, 1, x_739);
return x_741;
}
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_714);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_742 = lean_ctor_get(x_715, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_715, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_744 = x_715;
} else {
 lean_dec_ref(x_715);
 x_744 = lean_box(0);
}
if (lean_is_scalar(x_744)) {
 x_745 = lean_alloc_ctor(1, 2, 0);
} else {
 x_745 = x_744;
}
lean_ctor_set(x_745, 0, x_742);
lean_ctor_set(x_745, 1, x_743);
return x_745;
}
}
}
}
else
{
if (lean_obj_tag(x_457) == 0)
{
uint8_t x_746; 
lean_dec(x_22);
lean_dec(x_11);
x_746 = !lean_is_exclusive(x_457);
if (x_746 == 0)
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; 
x_747 = lean_ctor_get(x_457, 0);
x_748 = lean_array_get(x_10, x_4, x_456);
x_749 = lean_int_neg(x_747);
lean_dec(x_747);
x_750 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_751 = lean_int_dec_le(x_750, x_749);
if (x_751 == 0)
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_752 = lean_box(0);
x_753 = l_Lean_Expr_const___override(x_3, x_752);
x_754 = lean_int_neg(x_749);
lean_dec(x_749);
x_755 = l_Int_toNat(x_754);
lean_dec(x_754);
x_756 = l_Lean_instToExprInt_mkNat(x_755);
x_757 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__28;
x_758 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_759 = l_Lean_mkApp3(x_757, x_753, x_758, x_756);
lean_inc(x_759);
x_760 = l_Lean_mkAppB(x_20, x_748, x_759);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_761 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_762 = lean_ctor_get(x_761, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_761, 1);
lean_inc(x_763);
lean_dec(x_761);
x_764 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_765 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_766 = l_Lean_mkNatLit(x_456);
x_767 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__31;
x_768 = l_Lean_reflBoolTrue;
x_769 = l_Lean_mkApp6(x_767, x_762, x_764, x_765, x_766, x_759, x_768);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_760);
x_770 = l_Lean_Meta_mkEq(x_21, x_760, x_5, x_6, x_7, x_8, x_763);
if (lean_obj_tag(x_770) == 0)
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_771 = lean_ctor_get(x_770, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_770, 1);
lean_inc(x_772);
lean_dec(x_770);
x_773 = l_Lean_Meta_mkExpectedTypeHint(x_769, x_771, x_5, x_6, x_7, x_8, x_772);
if (lean_obj_tag(x_773) == 0)
{
uint8_t x_774; 
x_774 = !lean_is_exclusive(x_773);
if (x_774 == 0)
{
lean_object* x_775; lean_object* x_776; 
x_775 = lean_ctor_get(x_773, 0);
x_776 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_776, 0, x_760);
lean_ctor_set(x_776, 1, x_775);
lean_ctor_set_tag(x_457, 1);
lean_ctor_set(x_457, 0, x_776);
lean_ctor_set(x_773, 0, x_457);
return x_773;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_777 = lean_ctor_get(x_773, 0);
x_778 = lean_ctor_get(x_773, 1);
lean_inc(x_778);
lean_inc(x_777);
lean_dec(x_773);
x_779 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_779, 0, x_760);
lean_ctor_set(x_779, 1, x_777);
lean_ctor_set_tag(x_457, 1);
lean_ctor_set(x_457, 0, x_779);
x_780 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_780, 0, x_457);
lean_ctor_set(x_780, 1, x_778);
return x_780;
}
}
else
{
uint8_t x_781; 
lean_dec(x_760);
lean_free_object(x_457);
x_781 = !lean_is_exclusive(x_773);
if (x_781 == 0)
{
return x_773;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_782 = lean_ctor_get(x_773, 0);
x_783 = lean_ctor_get(x_773, 1);
lean_inc(x_783);
lean_inc(x_782);
lean_dec(x_773);
x_784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_784, 0, x_782);
lean_ctor_set(x_784, 1, x_783);
return x_784;
}
}
}
else
{
uint8_t x_785; 
lean_dec(x_769);
lean_dec(x_760);
lean_free_object(x_457);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_785 = !lean_is_exclusive(x_770);
if (x_785 == 0)
{
return x_770;
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_786 = lean_ctor_get(x_770, 0);
x_787 = lean_ctor_get(x_770, 1);
lean_inc(x_787);
lean_inc(x_786);
lean_dec(x_770);
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_786);
lean_ctor_set(x_788, 1, x_787);
return x_788;
}
}
}
else
{
uint8_t x_789; 
lean_dec(x_760);
lean_dec(x_759);
lean_free_object(x_457);
lean_dec(x_456);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_789 = !lean_is_exclusive(x_761);
if (x_789 == 0)
{
return x_761;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_761, 0);
x_791 = lean_ctor_get(x_761, 1);
lean_inc(x_791);
lean_inc(x_790);
lean_dec(x_761);
x_792 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_792, 0, x_790);
lean_ctor_set(x_792, 1, x_791);
return x_792;
}
}
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
lean_dec(x_3);
x_793 = l_Int_toNat(x_749);
lean_dec(x_749);
x_794 = l_Lean_instToExprInt_mkNat(x_793);
lean_inc(x_794);
x_795 = l_Lean_mkAppB(x_20, x_748, x_794);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_796 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_796) == 0)
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_796, 1);
lean_inc(x_798);
lean_dec(x_796);
x_799 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_800 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_801 = l_Lean_mkNatLit(x_456);
x_802 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__32;
x_803 = l_Lean_reflBoolTrue;
x_804 = l_Lean_mkApp6(x_802, x_797, x_799, x_800, x_801, x_794, x_803);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_795);
x_805 = l_Lean_Meta_mkEq(x_21, x_795, x_5, x_6, x_7, x_8, x_798);
if (lean_obj_tag(x_805) == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_806 = lean_ctor_get(x_805, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_805, 1);
lean_inc(x_807);
lean_dec(x_805);
x_808 = l_Lean_Meta_mkExpectedTypeHint(x_804, x_806, x_5, x_6, x_7, x_8, x_807);
if (lean_obj_tag(x_808) == 0)
{
uint8_t x_809; 
x_809 = !lean_is_exclusive(x_808);
if (x_809 == 0)
{
lean_object* x_810; lean_object* x_811; 
x_810 = lean_ctor_get(x_808, 0);
x_811 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_811, 0, x_795);
lean_ctor_set(x_811, 1, x_810);
lean_ctor_set_tag(x_457, 1);
lean_ctor_set(x_457, 0, x_811);
lean_ctor_set(x_808, 0, x_457);
return x_808;
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_812 = lean_ctor_get(x_808, 0);
x_813 = lean_ctor_get(x_808, 1);
lean_inc(x_813);
lean_inc(x_812);
lean_dec(x_808);
x_814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_814, 0, x_795);
lean_ctor_set(x_814, 1, x_812);
lean_ctor_set_tag(x_457, 1);
lean_ctor_set(x_457, 0, x_814);
x_815 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_815, 0, x_457);
lean_ctor_set(x_815, 1, x_813);
return x_815;
}
}
else
{
uint8_t x_816; 
lean_dec(x_795);
lean_free_object(x_457);
x_816 = !lean_is_exclusive(x_808);
if (x_816 == 0)
{
return x_808;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_817 = lean_ctor_get(x_808, 0);
x_818 = lean_ctor_get(x_808, 1);
lean_inc(x_818);
lean_inc(x_817);
lean_dec(x_808);
x_819 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_819, 0, x_817);
lean_ctor_set(x_819, 1, x_818);
return x_819;
}
}
}
else
{
uint8_t x_820; 
lean_dec(x_804);
lean_dec(x_795);
lean_free_object(x_457);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_820 = !lean_is_exclusive(x_805);
if (x_820 == 0)
{
return x_805;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_ctor_get(x_805, 0);
x_822 = lean_ctor_get(x_805, 1);
lean_inc(x_822);
lean_inc(x_821);
lean_dec(x_805);
x_823 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_823, 0, x_821);
lean_ctor_set(x_823, 1, x_822);
return x_823;
}
}
}
else
{
uint8_t x_824; 
lean_dec(x_795);
lean_dec(x_794);
lean_free_object(x_457);
lean_dec(x_456);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_824 = !lean_is_exclusive(x_796);
if (x_824 == 0)
{
return x_796;
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_825 = lean_ctor_get(x_796, 0);
x_826 = lean_ctor_get(x_796, 1);
lean_inc(x_826);
lean_inc(x_825);
lean_dec(x_796);
x_827 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_827, 0, x_825);
lean_ctor_set(x_827, 1, x_826);
return x_827;
}
}
}
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; uint8_t x_832; 
x_828 = lean_ctor_get(x_457, 0);
lean_inc(x_828);
lean_dec(x_457);
x_829 = lean_array_get(x_10, x_4, x_456);
x_830 = lean_int_neg(x_828);
lean_dec(x_828);
x_831 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_832 = lean_int_dec_le(x_831, x_830);
if (x_832 == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
x_833 = lean_box(0);
x_834 = l_Lean_Expr_const___override(x_3, x_833);
x_835 = lean_int_neg(x_830);
lean_dec(x_830);
x_836 = l_Int_toNat(x_835);
lean_dec(x_835);
x_837 = l_Lean_instToExprInt_mkNat(x_836);
x_838 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__28;
x_839 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_840 = l_Lean_mkApp3(x_838, x_834, x_839, x_837);
lean_inc(x_840);
x_841 = l_Lean_mkAppB(x_20, x_829, x_840);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_842 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_842) == 0)
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_843 = lean_ctor_get(x_842, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_842, 1);
lean_inc(x_844);
lean_dec(x_842);
x_845 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_846 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_847 = l_Lean_mkNatLit(x_456);
x_848 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__31;
x_849 = l_Lean_reflBoolTrue;
x_850 = l_Lean_mkApp6(x_848, x_843, x_845, x_846, x_847, x_840, x_849);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_841);
x_851 = l_Lean_Meta_mkEq(x_21, x_841, x_5, x_6, x_7, x_8, x_844);
if (lean_obj_tag(x_851) == 0)
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; 
x_852 = lean_ctor_get(x_851, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_851, 1);
lean_inc(x_853);
lean_dec(x_851);
x_854 = l_Lean_Meta_mkExpectedTypeHint(x_850, x_852, x_5, x_6, x_7, x_8, x_853);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_854, 1);
lean_inc(x_856);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_857 = x_854;
} else {
 lean_dec_ref(x_854);
 x_857 = lean_box(0);
}
x_858 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_858, 0, x_841);
lean_ctor_set(x_858, 1, x_855);
x_859 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_859, 0, x_858);
if (lean_is_scalar(x_857)) {
 x_860 = lean_alloc_ctor(0, 2, 0);
} else {
 x_860 = x_857;
}
lean_ctor_set(x_860, 0, x_859);
lean_ctor_set(x_860, 1, x_856);
return x_860;
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
lean_dec(x_841);
x_861 = lean_ctor_get(x_854, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_854, 1);
lean_inc(x_862);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_863 = x_854;
} else {
 lean_dec_ref(x_854);
 x_863 = lean_box(0);
}
if (lean_is_scalar(x_863)) {
 x_864 = lean_alloc_ctor(1, 2, 0);
} else {
 x_864 = x_863;
}
lean_ctor_set(x_864, 0, x_861);
lean_ctor_set(x_864, 1, x_862);
return x_864;
}
}
else
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_850);
lean_dec(x_841);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_865 = lean_ctor_get(x_851, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_851, 1);
lean_inc(x_866);
if (lean_is_exclusive(x_851)) {
 lean_ctor_release(x_851, 0);
 lean_ctor_release(x_851, 1);
 x_867 = x_851;
} else {
 lean_dec_ref(x_851);
 x_867 = lean_box(0);
}
if (lean_is_scalar(x_867)) {
 x_868 = lean_alloc_ctor(1, 2, 0);
} else {
 x_868 = x_867;
}
lean_ctor_set(x_868, 0, x_865);
lean_ctor_set(x_868, 1, x_866);
return x_868;
}
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
lean_dec(x_841);
lean_dec(x_840);
lean_dec(x_456);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_869 = lean_ctor_get(x_842, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_842, 1);
lean_inc(x_870);
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 lean_ctor_release(x_842, 1);
 x_871 = x_842;
} else {
 lean_dec_ref(x_842);
 x_871 = lean_box(0);
}
if (lean_is_scalar(x_871)) {
 x_872 = lean_alloc_ctor(1, 2, 0);
} else {
 x_872 = x_871;
}
lean_ctor_set(x_872, 0, x_869);
lean_ctor_set(x_872, 1, x_870);
return x_872;
}
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
lean_dec(x_3);
x_873 = l_Int_toNat(x_830);
lean_dec(x_830);
x_874 = l_Lean_instToExprInt_mkNat(x_873);
lean_inc(x_874);
x_875 = l_Lean_mkAppB(x_20, x_829, x_874);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_876 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; 
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_876, 1);
lean_inc(x_878);
lean_dec(x_876);
x_879 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_880 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_881 = l_Lean_mkNatLit(x_456);
x_882 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__32;
x_883 = l_Lean_reflBoolTrue;
x_884 = l_Lean_mkApp6(x_882, x_877, x_879, x_880, x_881, x_874, x_883);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_875);
x_885 = l_Lean_Meta_mkEq(x_21, x_875, x_5, x_6, x_7, x_8, x_878);
if (lean_obj_tag(x_885) == 0)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_885, 1);
lean_inc(x_887);
lean_dec(x_885);
x_888 = l_Lean_Meta_mkExpectedTypeHint(x_884, x_886, x_5, x_6, x_7, x_8, x_887);
if (lean_obj_tag(x_888) == 0)
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_888, 1);
lean_inc(x_890);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 x_891 = x_888;
} else {
 lean_dec_ref(x_888);
 x_891 = lean_box(0);
}
x_892 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_892, 0, x_875);
lean_ctor_set(x_892, 1, x_889);
x_893 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_893, 0, x_892);
if (lean_is_scalar(x_891)) {
 x_894 = lean_alloc_ctor(0, 2, 0);
} else {
 x_894 = x_891;
}
lean_ctor_set(x_894, 0, x_893);
lean_ctor_set(x_894, 1, x_890);
return x_894;
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
lean_dec(x_875);
x_895 = lean_ctor_get(x_888, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_888, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 x_897 = x_888;
} else {
 lean_dec_ref(x_888);
 x_897 = lean_box(0);
}
if (lean_is_scalar(x_897)) {
 x_898 = lean_alloc_ctor(1, 2, 0);
} else {
 x_898 = x_897;
}
lean_ctor_set(x_898, 0, x_895);
lean_ctor_set(x_898, 1, x_896);
return x_898;
}
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_dec(x_884);
lean_dec(x_875);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_899 = lean_ctor_get(x_885, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_885, 1);
lean_inc(x_900);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 x_901 = x_885;
} else {
 lean_dec_ref(x_885);
 x_901 = lean_box(0);
}
if (lean_is_scalar(x_901)) {
 x_902 = lean_alloc_ctor(1, 2, 0);
} else {
 x_902 = x_901;
}
lean_ctor_set(x_902, 0, x_899);
lean_ctor_set(x_902, 1, x_900);
return x_902;
}
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
lean_dec(x_875);
lean_dec(x_874);
lean_dec(x_456);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_903 = lean_ctor_get(x_876, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_876, 1);
lean_inc(x_904);
if (lean_is_exclusive(x_876)) {
 lean_ctor_release(x_876, 0);
 lean_ctor_release(x_876, 1);
 x_905 = x_876;
} else {
 lean_dec_ref(x_876);
 x_905 = lean_box(0);
}
if (lean_is_scalar(x_905)) {
 x_906 = lean_alloc_ctor(1, 2, 0);
} else {
 x_906 = x_905;
}
lean_ctor_set(x_906, 0, x_903);
lean_ctor_set(x_906, 1, x_904);
return x_906;
}
}
}
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; uint8_t x_911; 
x_907 = lean_ctor_get(x_457, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_457, 1);
lean_inc(x_908);
x_909 = lean_ctor_get(x_457, 2);
lean_inc(x_909);
lean_dec(x_457);
x_910 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__33;
x_911 = lean_int_dec_eq(x_907, x_910);
lean_dec(x_907);
if (x_911 == 0)
{
lean_object* x_912; lean_object* x_913; uint8_t x_914; 
lean_dec(x_909);
lean_dec(x_908);
lean_dec(x_456);
x_912 = l_Int_Linear_Poly_gcdCoeffs_x27(x_22);
x_913 = lean_unsigned_to_nat(1u);
x_914 = lean_nat_dec_eq(x_912, x_913);
if (x_914 == 0)
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; uint8_t x_919; 
x_915 = l_Int_Linear_Poly_getConst(x_22);
x_916 = lean_nat_to_int(x_912);
x_917 = lean_int_emod(x_915, x_916);
lean_dec(x_915);
x_918 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_919 = lean_int_dec_eq(x_917, x_918);
lean_dec(x_917);
if (x_919 == 0)
{
lean_object* x_920; lean_object* x_921; 
lean_dec(x_22);
lean_dec(x_11);
x_920 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_921 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_921) == 0)
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; uint8_t x_926; lean_object* x_927; lean_object* x_928; 
x_922 = lean_ctor_get(x_921, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_921, 1);
lean_inc(x_923);
lean_dec(x_921);
x_924 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_925 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_926 = lean_int_dec_le(x_918, x_916);
x_927 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_928 = l_Lean_Meta_mkEq(x_21, x_927, x_5, x_6, x_7, x_8, x_923);
if (x_926 == 0)
{
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
x_929 = lean_ctor_get(x_928, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_928, 1);
lean_inc(x_930);
lean_dec(x_928);
x_931 = l_Lean_Expr_const___override(x_3, x_920);
x_932 = lean_int_neg(x_916);
lean_dec(x_916);
x_933 = l_Int_toNat(x_932);
lean_dec(x_932);
x_934 = l_Lean_instToExprInt_mkNat(x_933);
x_935 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_936 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_937 = l_Lean_mkApp3(x_935, x_931, x_936, x_934);
x_938 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_939 = l_Lean_reflBoolTrue;
x_940 = l_Lean_mkApp5(x_938, x_922, x_924, x_925, x_937, x_939);
x_941 = l_Lean_Meta_mkExpectedTypeHint(x_940, x_929, x_5, x_6, x_7, x_8, x_930);
if (lean_obj_tag(x_941) == 0)
{
uint8_t x_942; 
x_942 = !lean_is_exclusive(x_941);
if (x_942 == 0)
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; 
x_943 = lean_ctor_get(x_941, 0);
x_944 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_944, 0, x_927);
lean_ctor_set(x_944, 1, x_943);
x_945 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_945, 0, x_944);
lean_ctor_set(x_941, 0, x_945);
return x_941;
}
else
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
x_946 = lean_ctor_get(x_941, 0);
x_947 = lean_ctor_get(x_941, 1);
lean_inc(x_947);
lean_inc(x_946);
lean_dec(x_941);
x_948 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_948, 0, x_927);
lean_ctor_set(x_948, 1, x_946);
x_949 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_949, 0, x_948);
x_950 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_950, 0, x_949);
lean_ctor_set(x_950, 1, x_947);
return x_950;
}
}
else
{
uint8_t x_951; 
x_951 = !lean_is_exclusive(x_941);
if (x_951 == 0)
{
return x_941;
}
else
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; 
x_952 = lean_ctor_get(x_941, 0);
x_953 = lean_ctor_get(x_941, 1);
lean_inc(x_953);
lean_inc(x_952);
lean_dec(x_941);
x_954 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_954, 0, x_952);
lean_ctor_set(x_954, 1, x_953);
return x_954;
}
}
}
else
{
uint8_t x_955; 
lean_dec(x_925);
lean_dec(x_924);
lean_dec(x_922);
lean_dec(x_916);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_955 = !lean_is_exclusive(x_928);
if (x_955 == 0)
{
return x_928;
}
else
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; 
x_956 = lean_ctor_get(x_928, 0);
x_957 = lean_ctor_get(x_928, 1);
lean_inc(x_957);
lean_inc(x_956);
lean_dec(x_928);
x_958 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_958, 0, x_956);
lean_ctor_set(x_958, 1, x_957);
return x_958;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; 
x_959 = lean_ctor_get(x_928, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_928, 1);
lean_inc(x_960);
lean_dec(x_928);
x_961 = l_Int_toNat(x_916);
lean_dec(x_916);
x_962 = l_Lean_instToExprInt_mkNat(x_961);
x_963 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_964 = l_Lean_reflBoolTrue;
x_965 = l_Lean_mkApp5(x_963, x_922, x_924, x_925, x_962, x_964);
x_966 = l_Lean_Meta_mkExpectedTypeHint(x_965, x_959, x_5, x_6, x_7, x_8, x_960);
if (lean_obj_tag(x_966) == 0)
{
uint8_t x_967; 
x_967 = !lean_is_exclusive(x_966);
if (x_967 == 0)
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; 
x_968 = lean_ctor_get(x_966, 0);
x_969 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_969, 0, x_927);
lean_ctor_set(x_969, 1, x_968);
x_970 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_970, 0, x_969);
lean_ctor_set(x_966, 0, x_970);
return x_966;
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; 
x_971 = lean_ctor_get(x_966, 0);
x_972 = lean_ctor_get(x_966, 1);
lean_inc(x_972);
lean_inc(x_971);
lean_dec(x_966);
x_973 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_973, 0, x_927);
lean_ctor_set(x_973, 1, x_971);
x_974 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_974, 0, x_973);
x_975 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_975, 0, x_974);
lean_ctor_set(x_975, 1, x_972);
return x_975;
}
}
else
{
uint8_t x_976; 
x_976 = !lean_is_exclusive(x_966);
if (x_976 == 0)
{
return x_966;
}
else
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; 
x_977 = lean_ctor_get(x_966, 0);
x_978 = lean_ctor_get(x_966, 1);
lean_inc(x_978);
lean_inc(x_977);
lean_dec(x_966);
x_979 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_979, 0, x_977);
lean_ctor_set(x_979, 1, x_978);
return x_979;
}
}
}
else
{
uint8_t x_980; 
lean_dec(x_925);
lean_dec(x_924);
lean_dec(x_922);
lean_dec(x_916);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_980 = !lean_is_exclusive(x_928);
if (x_980 == 0)
{
return x_928;
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_981 = lean_ctor_get(x_928, 0);
x_982 = lean_ctor_get(x_928, 1);
lean_inc(x_982);
lean_inc(x_981);
lean_dec(x_928);
x_983 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_983, 0, x_981);
lean_ctor_set(x_983, 1, x_982);
return x_983;
}
}
}
}
else
{
uint8_t x_984; 
lean_dec(x_916);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_984 = !lean_is_exclusive(x_921);
if (x_984 == 0)
{
return x_921;
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_985 = lean_ctor_get(x_921, 0);
x_986 = lean_ctor_get(x_921, 1);
lean_inc(x_986);
lean_inc(x_985);
lean_dec(x_921);
x_987 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_987, 0, x_985);
lean_ctor_set(x_987, 1, x_986);
return x_987;
}
}
}
else
{
lean_object* x_988; lean_object* x_989; uint8_t x_990; 
x_988 = l_Int_Linear_Poly_div(x_916, x_22);
lean_inc(x_988);
x_989 = l_Int_Linear_Poly_denoteExpr(x_11, x_988, x_5, x_6, x_7, x_8, x_19);
x_990 = !lean_is_exclusive(x_989);
if (x_990 == 0)
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_991 = lean_ctor_get(x_989, 0);
x_992 = lean_ctor_get(x_989, 1);
x_993 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_994 = l_Lean_mkAppB(x_20, x_991, x_993);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_995 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_992);
if (lean_obj_tag(x_995) == 0)
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; uint8_t x_1002; lean_object* x_1003; 
x_996 = lean_ctor_get(x_995, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_995, 1);
lean_inc(x_997);
lean_dec(x_995);
x_998 = lean_box(0);
x_999 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1000 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1001 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_988);
x_1002 = lean_int_dec_le(x_918, x_916);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_994);
x_1003 = l_Lean_Meta_mkEq(x_21, x_994, x_5, x_6, x_7, x_8, x_997);
if (x_1002 == 0)
{
if (lean_obj_tag(x_1003) == 0)
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1004 = lean_ctor_get(x_1003, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_1003, 1);
lean_inc(x_1005);
lean_dec(x_1003);
x_1006 = l_Lean_Expr_const___override(x_3, x_998);
x_1007 = lean_int_neg(x_916);
lean_dec(x_916);
x_1008 = l_Int_toNat(x_1007);
lean_dec(x_1007);
x_1009 = l_Lean_instToExprInt_mkNat(x_1008);
x_1010 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_1011 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_1012 = l_Lean_mkApp3(x_1010, x_1006, x_1011, x_1009);
x_1013 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1014 = l_Lean_reflBoolTrue;
x_1015 = l_Lean_mkApp6(x_1013, x_996, x_999, x_1000, x_1001, x_1012, x_1014);
x_1016 = l_Lean_Meta_mkExpectedTypeHint(x_1015, x_1004, x_5, x_6, x_7, x_8, x_1005);
if (lean_obj_tag(x_1016) == 0)
{
uint8_t x_1017; 
x_1017 = !lean_is_exclusive(x_1016);
if (x_1017 == 0)
{
lean_object* x_1018; lean_object* x_1019; 
x_1018 = lean_ctor_get(x_1016, 0);
lean_ctor_set(x_989, 1, x_1018);
lean_ctor_set(x_989, 0, x_994);
x_1019 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1019, 0, x_989);
lean_ctor_set(x_1016, 0, x_1019);
return x_1016;
}
else
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1020 = lean_ctor_get(x_1016, 0);
x_1021 = lean_ctor_get(x_1016, 1);
lean_inc(x_1021);
lean_inc(x_1020);
lean_dec(x_1016);
lean_ctor_set(x_989, 1, x_1020);
lean_ctor_set(x_989, 0, x_994);
x_1022 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1022, 0, x_989);
x_1023 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1023, 0, x_1022);
lean_ctor_set(x_1023, 1, x_1021);
return x_1023;
}
}
else
{
uint8_t x_1024; 
lean_dec(x_994);
lean_free_object(x_989);
x_1024 = !lean_is_exclusive(x_1016);
if (x_1024 == 0)
{
return x_1016;
}
else
{
lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
x_1025 = lean_ctor_get(x_1016, 0);
x_1026 = lean_ctor_get(x_1016, 1);
lean_inc(x_1026);
lean_inc(x_1025);
lean_dec(x_1016);
x_1027 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1027, 0, x_1025);
lean_ctor_set(x_1027, 1, x_1026);
return x_1027;
}
}
}
else
{
uint8_t x_1028; 
lean_dec(x_1001);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_996);
lean_dec(x_994);
lean_free_object(x_989);
lean_dec(x_916);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1028 = !lean_is_exclusive(x_1003);
if (x_1028 == 0)
{
return x_1003;
}
else
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
x_1029 = lean_ctor_get(x_1003, 0);
x_1030 = lean_ctor_get(x_1003, 1);
lean_inc(x_1030);
lean_inc(x_1029);
lean_dec(x_1003);
x_1031 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1031, 0, x_1029);
lean_ctor_set(x_1031, 1, x_1030);
return x_1031;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1003) == 0)
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
x_1032 = lean_ctor_get(x_1003, 0);
lean_inc(x_1032);
x_1033 = lean_ctor_get(x_1003, 1);
lean_inc(x_1033);
lean_dec(x_1003);
x_1034 = l_Int_toNat(x_916);
lean_dec(x_916);
x_1035 = l_Lean_instToExprInt_mkNat(x_1034);
x_1036 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1037 = l_Lean_reflBoolTrue;
x_1038 = l_Lean_mkApp6(x_1036, x_996, x_999, x_1000, x_1001, x_1035, x_1037);
x_1039 = l_Lean_Meta_mkExpectedTypeHint(x_1038, x_1032, x_5, x_6, x_7, x_8, x_1033);
if (lean_obj_tag(x_1039) == 0)
{
uint8_t x_1040; 
x_1040 = !lean_is_exclusive(x_1039);
if (x_1040 == 0)
{
lean_object* x_1041; lean_object* x_1042; 
x_1041 = lean_ctor_get(x_1039, 0);
lean_ctor_set(x_989, 1, x_1041);
lean_ctor_set(x_989, 0, x_994);
x_1042 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1042, 0, x_989);
lean_ctor_set(x_1039, 0, x_1042);
return x_1039;
}
else
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
x_1043 = lean_ctor_get(x_1039, 0);
x_1044 = lean_ctor_get(x_1039, 1);
lean_inc(x_1044);
lean_inc(x_1043);
lean_dec(x_1039);
lean_ctor_set(x_989, 1, x_1043);
lean_ctor_set(x_989, 0, x_994);
x_1045 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1045, 0, x_989);
x_1046 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1046, 0, x_1045);
lean_ctor_set(x_1046, 1, x_1044);
return x_1046;
}
}
else
{
uint8_t x_1047; 
lean_dec(x_994);
lean_free_object(x_989);
x_1047 = !lean_is_exclusive(x_1039);
if (x_1047 == 0)
{
return x_1039;
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
x_1048 = lean_ctor_get(x_1039, 0);
x_1049 = lean_ctor_get(x_1039, 1);
lean_inc(x_1049);
lean_inc(x_1048);
lean_dec(x_1039);
x_1050 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1050, 0, x_1048);
lean_ctor_set(x_1050, 1, x_1049);
return x_1050;
}
}
}
else
{
uint8_t x_1051; 
lean_dec(x_1001);
lean_dec(x_1000);
lean_dec(x_999);
lean_dec(x_996);
lean_dec(x_994);
lean_free_object(x_989);
lean_dec(x_916);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1051 = !lean_is_exclusive(x_1003);
if (x_1051 == 0)
{
return x_1003;
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
x_1052 = lean_ctor_get(x_1003, 0);
x_1053 = lean_ctor_get(x_1003, 1);
lean_inc(x_1053);
lean_inc(x_1052);
lean_dec(x_1003);
x_1054 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1054, 0, x_1052);
lean_ctor_set(x_1054, 1, x_1053);
return x_1054;
}
}
}
}
else
{
uint8_t x_1055; 
lean_dec(x_994);
lean_free_object(x_989);
lean_dec(x_988);
lean_dec(x_916);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1055 = !lean_is_exclusive(x_995);
if (x_1055 == 0)
{
return x_995;
}
else
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; 
x_1056 = lean_ctor_get(x_995, 0);
x_1057 = lean_ctor_get(x_995, 1);
lean_inc(x_1057);
lean_inc(x_1056);
lean_dec(x_995);
x_1058 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1058, 0, x_1056);
lean_ctor_set(x_1058, 1, x_1057);
return x_1058;
}
}
}
else
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
x_1059 = lean_ctor_get(x_989, 0);
x_1060 = lean_ctor_get(x_989, 1);
lean_inc(x_1060);
lean_inc(x_1059);
lean_dec(x_989);
x_1061 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_1062 = l_Lean_mkAppB(x_20, x_1059, x_1061);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1063 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_1060);
if (lean_obj_tag(x_1063) == 0)
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; uint8_t x_1070; lean_object* x_1071; 
x_1064 = lean_ctor_get(x_1063, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1063, 1);
lean_inc(x_1065);
lean_dec(x_1063);
x_1066 = lean_box(0);
x_1067 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1068 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1069 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_988);
x_1070 = lean_int_dec_le(x_918, x_916);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1062);
x_1071 = l_Lean_Meta_mkEq(x_21, x_1062, x_5, x_6, x_7, x_8, x_1065);
if (x_1070 == 0)
{
if (lean_obj_tag(x_1071) == 0)
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
x_1072 = lean_ctor_get(x_1071, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1071, 1);
lean_inc(x_1073);
lean_dec(x_1071);
x_1074 = l_Lean_Expr_const___override(x_3, x_1066);
x_1075 = lean_int_neg(x_916);
lean_dec(x_916);
x_1076 = l_Int_toNat(x_1075);
lean_dec(x_1075);
x_1077 = l_Lean_instToExprInt_mkNat(x_1076);
x_1078 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_1079 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_1080 = l_Lean_mkApp3(x_1078, x_1074, x_1079, x_1077);
x_1081 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1082 = l_Lean_reflBoolTrue;
x_1083 = l_Lean_mkApp6(x_1081, x_1064, x_1067, x_1068, x_1069, x_1080, x_1082);
x_1084 = l_Lean_Meta_mkExpectedTypeHint(x_1083, x_1072, x_5, x_6, x_7, x_8, x_1073);
if (lean_obj_tag(x_1084) == 0)
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; 
x_1085 = lean_ctor_get(x_1084, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1084, 1);
lean_inc(x_1086);
if (lean_is_exclusive(x_1084)) {
 lean_ctor_release(x_1084, 0);
 lean_ctor_release(x_1084, 1);
 x_1087 = x_1084;
} else {
 lean_dec_ref(x_1084);
 x_1087 = lean_box(0);
}
x_1088 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1088, 0, x_1062);
lean_ctor_set(x_1088, 1, x_1085);
x_1089 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1089, 0, x_1088);
if (lean_is_scalar(x_1087)) {
 x_1090 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1090 = x_1087;
}
lean_ctor_set(x_1090, 0, x_1089);
lean_ctor_set(x_1090, 1, x_1086);
return x_1090;
}
else
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; 
lean_dec(x_1062);
x_1091 = lean_ctor_get(x_1084, 0);
lean_inc(x_1091);
x_1092 = lean_ctor_get(x_1084, 1);
lean_inc(x_1092);
if (lean_is_exclusive(x_1084)) {
 lean_ctor_release(x_1084, 0);
 lean_ctor_release(x_1084, 1);
 x_1093 = x_1084;
} else {
 lean_dec_ref(x_1084);
 x_1093 = lean_box(0);
}
if (lean_is_scalar(x_1093)) {
 x_1094 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1094 = x_1093;
}
lean_ctor_set(x_1094, 0, x_1091);
lean_ctor_set(x_1094, 1, x_1092);
return x_1094;
}
}
else
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1067);
lean_dec(x_1064);
lean_dec(x_1062);
lean_dec(x_916);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1095 = lean_ctor_get(x_1071, 0);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1071, 1);
lean_inc(x_1096);
if (lean_is_exclusive(x_1071)) {
 lean_ctor_release(x_1071, 0);
 lean_ctor_release(x_1071, 1);
 x_1097 = x_1071;
} else {
 lean_dec_ref(x_1071);
 x_1097 = lean_box(0);
}
if (lean_is_scalar(x_1097)) {
 x_1098 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1098 = x_1097;
}
lean_ctor_set(x_1098, 0, x_1095);
lean_ctor_set(x_1098, 1, x_1096);
return x_1098;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1071) == 0)
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
x_1099 = lean_ctor_get(x_1071, 0);
lean_inc(x_1099);
x_1100 = lean_ctor_get(x_1071, 1);
lean_inc(x_1100);
lean_dec(x_1071);
x_1101 = l_Int_toNat(x_916);
lean_dec(x_916);
x_1102 = l_Lean_instToExprInt_mkNat(x_1101);
x_1103 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1104 = l_Lean_reflBoolTrue;
x_1105 = l_Lean_mkApp6(x_1103, x_1064, x_1067, x_1068, x_1069, x_1102, x_1104);
x_1106 = l_Lean_Meta_mkExpectedTypeHint(x_1105, x_1099, x_5, x_6, x_7, x_8, x_1100);
if (lean_obj_tag(x_1106) == 0)
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; 
x_1107 = lean_ctor_get(x_1106, 0);
lean_inc(x_1107);
x_1108 = lean_ctor_get(x_1106, 1);
lean_inc(x_1108);
if (lean_is_exclusive(x_1106)) {
 lean_ctor_release(x_1106, 0);
 lean_ctor_release(x_1106, 1);
 x_1109 = x_1106;
} else {
 lean_dec_ref(x_1106);
 x_1109 = lean_box(0);
}
x_1110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1110, 0, x_1062);
lean_ctor_set(x_1110, 1, x_1107);
x_1111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1111, 0, x_1110);
if (lean_is_scalar(x_1109)) {
 x_1112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1112 = x_1109;
}
lean_ctor_set(x_1112, 0, x_1111);
lean_ctor_set(x_1112, 1, x_1108);
return x_1112;
}
else
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; 
lean_dec(x_1062);
x_1113 = lean_ctor_get(x_1106, 0);
lean_inc(x_1113);
x_1114 = lean_ctor_get(x_1106, 1);
lean_inc(x_1114);
if (lean_is_exclusive(x_1106)) {
 lean_ctor_release(x_1106, 0);
 lean_ctor_release(x_1106, 1);
 x_1115 = x_1106;
} else {
 lean_dec_ref(x_1106);
 x_1115 = lean_box(0);
}
if (lean_is_scalar(x_1115)) {
 x_1116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1116 = x_1115;
}
lean_ctor_set(x_1116, 0, x_1113);
lean_ctor_set(x_1116, 1, x_1114);
return x_1116;
}
}
else
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; 
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1067);
lean_dec(x_1064);
lean_dec(x_1062);
lean_dec(x_916);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1117 = lean_ctor_get(x_1071, 0);
lean_inc(x_1117);
x_1118 = lean_ctor_get(x_1071, 1);
lean_inc(x_1118);
if (lean_is_exclusive(x_1071)) {
 lean_ctor_release(x_1071, 0);
 lean_ctor_release(x_1071, 1);
 x_1119 = x_1071;
} else {
 lean_dec_ref(x_1071);
 x_1119 = lean_box(0);
}
if (lean_is_scalar(x_1119)) {
 x_1120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1120 = x_1119;
}
lean_ctor_set(x_1120, 0, x_1117);
lean_ctor_set(x_1120, 1, x_1118);
return x_1120;
}
}
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
lean_dec(x_1062);
lean_dec(x_988);
lean_dec(x_916);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1121 = lean_ctor_get(x_1063, 0);
lean_inc(x_1121);
x_1122 = lean_ctor_get(x_1063, 1);
lean_inc(x_1122);
if (lean_is_exclusive(x_1063)) {
 lean_ctor_release(x_1063, 0);
 lean_ctor_release(x_1063, 1);
 x_1123 = x_1063;
} else {
 lean_dec_ref(x_1063);
 x_1123 = lean_box(0);
}
if (lean_is_scalar(x_1123)) {
 x_1124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1124 = x_1123;
}
lean_ctor_set(x_1124, 0, x_1121);
lean_ctor_set(x_1124, 1, x_1122);
return x_1124;
}
}
}
}
else
{
lean_object* x_1125; uint8_t x_1126; 
lean_dec(x_912);
lean_dec(x_3);
lean_inc(x_22);
x_1125 = l_Int_Linear_Poly_denoteExpr(x_11, x_22, x_5, x_6, x_7, x_8, x_19);
x_1126 = !lean_is_exclusive(x_1125);
if (x_1126 == 0)
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1127 = lean_ctor_get(x_1125, 0);
x_1128 = lean_ctor_get(x_1125, 1);
x_1129 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_1130 = l_Lean_mkAppB(x_20, x_1127, x_1129);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1131 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_1128);
if (lean_obj_tag(x_1131) == 0)
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
x_1132 = lean_ctor_get(x_1131, 0);
lean_inc(x_1132);
x_1133 = lean_ctor_get(x_1131, 1);
lean_inc(x_1133);
lean_dec(x_1131);
x_1134 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1135 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1136 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_22);
x_1137 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_1138 = l_Lean_reflBoolTrue;
x_1139 = l_Lean_mkApp5(x_1137, x_1132, x_1134, x_1135, x_1136, x_1138);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1130);
x_1140 = l_Lean_Meta_mkEq(x_21, x_1130, x_5, x_6, x_7, x_8, x_1133);
if (lean_obj_tag(x_1140) == 0)
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
x_1141 = lean_ctor_get(x_1140, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1140, 1);
lean_inc(x_1142);
lean_dec(x_1140);
x_1143 = l_Lean_Meta_mkExpectedTypeHint(x_1139, x_1141, x_5, x_6, x_7, x_8, x_1142);
if (lean_obj_tag(x_1143) == 0)
{
uint8_t x_1144; 
x_1144 = !lean_is_exclusive(x_1143);
if (x_1144 == 0)
{
lean_object* x_1145; lean_object* x_1146; 
x_1145 = lean_ctor_get(x_1143, 0);
lean_ctor_set(x_1125, 1, x_1145);
lean_ctor_set(x_1125, 0, x_1130);
x_1146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1146, 0, x_1125);
lean_ctor_set(x_1143, 0, x_1146);
return x_1143;
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1147 = lean_ctor_get(x_1143, 0);
x_1148 = lean_ctor_get(x_1143, 1);
lean_inc(x_1148);
lean_inc(x_1147);
lean_dec(x_1143);
lean_ctor_set(x_1125, 1, x_1147);
lean_ctor_set(x_1125, 0, x_1130);
x_1149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1149, 0, x_1125);
x_1150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1150, 0, x_1149);
lean_ctor_set(x_1150, 1, x_1148);
return x_1150;
}
}
else
{
uint8_t x_1151; 
lean_dec(x_1130);
lean_free_object(x_1125);
x_1151 = !lean_is_exclusive(x_1143);
if (x_1151 == 0)
{
return x_1143;
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; 
x_1152 = lean_ctor_get(x_1143, 0);
x_1153 = lean_ctor_get(x_1143, 1);
lean_inc(x_1153);
lean_inc(x_1152);
lean_dec(x_1143);
x_1154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1154, 0, x_1152);
lean_ctor_set(x_1154, 1, x_1153);
return x_1154;
}
}
}
else
{
uint8_t x_1155; 
lean_dec(x_1139);
lean_dec(x_1130);
lean_free_object(x_1125);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1155 = !lean_is_exclusive(x_1140);
if (x_1155 == 0)
{
return x_1140;
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
x_1156 = lean_ctor_get(x_1140, 0);
x_1157 = lean_ctor_get(x_1140, 1);
lean_inc(x_1157);
lean_inc(x_1156);
lean_dec(x_1140);
x_1158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1158, 0, x_1156);
lean_ctor_set(x_1158, 1, x_1157);
return x_1158;
}
}
}
else
{
uint8_t x_1159; 
lean_dec(x_1130);
lean_free_object(x_1125);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1159 = !lean_is_exclusive(x_1131);
if (x_1159 == 0)
{
return x_1131;
}
else
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
x_1160 = lean_ctor_get(x_1131, 0);
x_1161 = lean_ctor_get(x_1131, 1);
lean_inc(x_1161);
lean_inc(x_1160);
lean_dec(x_1131);
x_1162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1162, 0, x_1160);
lean_ctor_set(x_1162, 1, x_1161);
return x_1162;
}
}
}
else
{
lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
x_1163 = lean_ctor_get(x_1125, 0);
x_1164 = lean_ctor_get(x_1125, 1);
lean_inc(x_1164);
lean_inc(x_1163);
lean_dec(x_1125);
x_1165 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_1166 = l_Lean_mkAppB(x_20, x_1163, x_1165);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1167 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_1164);
if (lean_obj_tag(x_1167) == 0)
{
lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
x_1168 = lean_ctor_get(x_1167, 0);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1167, 1);
lean_inc(x_1169);
lean_dec(x_1167);
x_1170 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1171 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1172 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_22);
x_1173 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_1174 = l_Lean_reflBoolTrue;
x_1175 = l_Lean_mkApp5(x_1173, x_1168, x_1170, x_1171, x_1172, x_1174);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1166);
x_1176 = l_Lean_Meta_mkEq(x_21, x_1166, x_5, x_6, x_7, x_8, x_1169);
if (lean_obj_tag(x_1176) == 0)
{
lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
x_1177 = lean_ctor_get(x_1176, 0);
lean_inc(x_1177);
x_1178 = lean_ctor_get(x_1176, 1);
lean_inc(x_1178);
lean_dec(x_1176);
x_1179 = l_Lean_Meta_mkExpectedTypeHint(x_1175, x_1177, x_5, x_6, x_7, x_8, x_1178);
if (lean_obj_tag(x_1179) == 0)
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; 
x_1180 = lean_ctor_get(x_1179, 0);
lean_inc(x_1180);
x_1181 = lean_ctor_get(x_1179, 1);
lean_inc(x_1181);
if (lean_is_exclusive(x_1179)) {
 lean_ctor_release(x_1179, 0);
 lean_ctor_release(x_1179, 1);
 x_1182 = x_1179;
} else {
 lean_dec_ref(x_1179);
 x_1182 = lean_box(0);
}
x_1183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1183, 0, x_1166);
lean_ctor_set(x_1183, 1, x_1180);
x_1184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1184, 0, x_1183);
if (lean_is_scalar(x_1182)) {
 x_1185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1185 = x_1182;
}
lean_ctor_set(x_1185, 0, x_1184);
lean_ctor_set(x_1185, 1, x_1181);
return x_1185;
}
else
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; 
lean_dec(x_1166);
x_1186 = lean_ctor_get(x_1179, 0);
lean_inc(x_1186);
x_1187 = lean_ctor_get(x_1179, 1);
lean_inc(x_1187);
if (lean_is_exclusive(x_1179)) {
 lean_ctor_release(x_1179, 0);
 lean_ctor_release(x_1179, 1);
 x_1188 = x_1179;
} else {
 lean_dec_ref(x_1179);
 x_1188 = lean_box(0);
}
if (lean_is_scalar(x_1188)) {
 x_1189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1189 = x_1188;
}
lean_ctor_set(x_1189, 0, x_1186);
lean_ctor_set(x_1189, 1, x_1187);
return x_1189;
}
}
else
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; 
lean_dec(x_1175);
lean_dec(x_1166);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1190 = lean_ctor_get(x_1176, 0);
lean_inc(x_1190);
x_1191 = lean_ctor_get(x_1176, 1);
lean_inc(x_1191);
if (lean_is_exclusive(x_1176)) {
 lean_ctor_release(x_1176, 0);
 lean_ctor_release(x_1176, 1);
 x_1192 = x_1176;
} else {
 lean_dec_ref(x_1176);
 x_1192 = lean_box(0);
}
if (lean_is_scalar(x_1192)) {
 x_1193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1193 = x_1192;
}
lean_ctor_set(x_1193, 0, x_1190);
lean_ctor_set(x_1193, 1, x_1191);
return x_1193;
}
}
else
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; 
lean_dec(x_1166);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1194 = lean_ctor_get(x_1167, 0);
lean_inc(x_1194);
x_1195 = lean_ctor_get(x_1167, 1);
lean_inc(x_1195);
if (lean_is_exclusive(x_1167)) {
 lean_ctor_release(x_1167, 0);
 lean_ctor_release(x_1167, 1);
 x_1196 = x_1167;
} else {
 lean_dec_ref(x_1167);
 x_1196 = lean_box(0);
}
if (lean_is_scalar(x_1196)) {
 x_1197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1197 = x_1196;
}
lean_ctor_set(x_1197, 0, x_1194);
lean_ctor_set(x_1197, 1, x_1195);
return x_1197;
}
}
}
}
else
{
if (lean_obj_tag(x_909) == 0)
{
uint8_t x_1198; 
x_1198 = !lean_is_exclusive(x_909);
if (x_1198 == 0)
{
lean_object* x_1199; lean_object* x_1200; uint8_t x_1201; 
x_1199 = lean_ctor_get(x_909, 0);
x_1200 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_1201 = lean_int_dec_eq(x_1199, x_1200);
lean_dec(x_1199);
if (x_1201 == 0)
{
lean_object* x_1202; lean_object* x_1203; uint8_t x_1204; 
lean_dec(x_908);
lean_dec(x_456);
x_1202 = l_Int_Linear_Poly_gcdCoeffs_x27(x_22);
x_1203 = lean_unsigned_to_nat(1u);
x_1204 = lean_nat_dec_eq(x_1202, x_1203);
if (x_1204 == 0)
{
lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; uint8_t x_1208; 
x_1205 = l_Int_Linear_Poly_getConst(x_22);
x_1206 = lean_nat_to_int(x_1202);
x_1207 = lean_int_emod(x_1205, x_1206);
lean_dec(x_1205);
x_1208 = lean_int_dec_eq(x_1207, x_1200);
lean_dec(x_1207);
if (x_1208 == 0)
{
lean_object* x_1209; lean_object* x_1210; 
lean_dec(x_22);
lean_dec(x_11);
x_1209 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1210 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_1210) == 0)
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; uint8_t x_1215; lean_object* x_1216; lean_object* x_1217; 
x_1211 = lean_ctor_get(x_1210, 0);
lean_inc(x_1211);
x_1212 = lean_ctor_get(x_1210, 1);
lean_inc(x_1212);
lean_dec(x_1210);
x_1213 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1214 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1215 = lean_int_dec_le(x_1200, x_1206);
x_1216 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1217 = l_Lean_Meta_mkEq(x_21, x_1216, x_5, x_6, x_7, x_8, x_1212);
if (x_1215 == 0)
{
if (lean_obj_tag(x_1217) == 0)
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; 
x_1218 = lean_ctor_get(x_1217, 0);
lean_inc(x_1218);
x_1219 = lean_ctor_get(x_1217, 1);
lean_inc(x_1219);
lean_dec(x_1217);
x_1220 = l_Lean_Expr_const___override(x_3, x_1209);
x_1221 = lean_int_neg(x_1206);
lean_dec(x_1206);
x_1222 = l_Int_toNat(x_1221);
lean_dec(x_1221);
x_1223 = l_Lean_instToExprInt_mkNat(x_1222);
x_1224 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_1225 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_1226 = l_Lean_mkApp3(x_1224, x_1220, x_1225, x_1223);
x_1227 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_1228 = l_Lean_reflBoolTrue;
x_1229 = l_Lean_mkApp5(x_1227, x_1211, x_1213, x_1214, x_1226, x_1228);
x_1230 = l_Lean_Meta_mkExpectedTypeHint(x_1229, x_1218, x_5, x_6, x_7, x_8, x_1219);
if (lean_obj_tag(x_1230) == 0)
{
uint8_t x_1231; 
x_1231 = !lean_is_exclusive(x_1230);
if (x_1231 == 0)
{
lean_object* x_1232; lean_object* x_1233; 
x_1232 = lean_ctor_get(x_1230, 0);
x_1233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1233, 0, x_1216);
lean_ctor_set(x_1233, 1, x_1232);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1233);
lean_ctor_set(x_1230, 0, x_909);
return x_1230;
}
else
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; 
x_1234 = lean_ctor_get(x_1230, 0);
x_1235 = lean_ctor_get(x_1230, 1);
lean_inc(x_1235);
lean_inc(x_1234);
lean_dec(x_1230);
x_1236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1236, 0, x_1216);
lean_ctor_set(x_1236, 1, x_1234);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1236);
x_1237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1237, 0, x_909);
lean_ctor_set(x_1237, 1, x_1235);
return x_1237;
}
}
else
{
uint8_t x_1238; 
lean_free_object(x_909);
x_1238 = !lean_is_exclusive(x_1230);
if (x_1238 == 0)
{
return x_1230;
}
else
{
lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; 
x_1239 = lean_ctor_get(x_1230, 0);
x_1240 = lean_ctor_get(x_1230, 1);
lean_inc(x_1240);
lean_inc(x_1239);
lean_dec(x_1230);
x_1241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1241, 0, x_1239);
lean_ctor_set(x_1241, 1, x_1240);
return x_1241;
}
}
}
else
{
uint8_t x_1242; 
lean_dec(x_1214);
lean_dec(x_1213);
lean_dec(x_1211);
lean_dec(x_1206);
lean_free_object(x_909);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1242 = !lean_is_exclusive(x_1217);
if (x_1242 == 0)
{
return x_1217;
}
else
{
lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; 
x_1243 = lean_ctor_get(x_1217, 0);
x_1244 = lean_ctor_get(x_1217, 1);
lean_inc(x_1244);
lean_inc(x_1243);
lean_dec(x_1217);
x_1245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1245, 0, x_1243);
lean_ctor_set(x_1245, 1, x_1244);
return x_1245;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1217) == 0)
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; 
x_1246 = lean_ctor_get(x_1217, 0);
lean_inc(x_1246);
x_1247 = lean_ctor_get(x_1217, 1);
lean_inc(x_1247);
lean_dec(x_1217);
x_1248 = l_Int_toNat(x_1206);
lean_dec(x_1206);
x_1249 = l_Lean_instToExprInt_mkNat(x_1248);
x_1250 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_1251 = l_Lean_reflBoolTrue;
x_1252 = l_Lean_mkApp5(x_1250, x_1211, x_1213, x_1214, x_1249, x_1251);
x_1253 = l_Lean_Meta_mkExpectedTypeHint(x_1252, x_1246, x_5, x_6, x_7, x_8, x_1247);
if (lean_obj_tag(x_1253) == 0)
{
uint8_t x_1254; 
x_1254 = !lean_is_exclusive(x_1253);
if (x_1254 == 0)
{
lean_object* x_1255; lean_object* x_1256; 
x_1255 = lean_ctor_get(x_1253, 0);
x_1256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1256, 0, x_1216);
lean_ctor_set(x_1256, 1, x_1255);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1256);
lean_ctor_set(x_1253, 0, x_909);
return x_1253;
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
x_1257 = lean_ctor_get(x_1253, 0);
x_1258 = lean_ctor_get(x_1253, 1);
lean_inc(x_1258);
lean_inc(x_1257);
lean_dec(x_1253);
x_1259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1259, 0, x_1216);
lean_ctor_set(x_1259, 1, x_1257);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1259);
x_1260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1260, 0, x_909);
lean_ctor_set(x_1260, 1, x_1258);
return x_1260;
}
}
else
{
uint8_t x_1261; 
lean_free_object(x_909);
x_1261 = !lean_is_exclusive(x_1253);
if (x_1261 == 0)
{
return x_1253;
}
else
{
lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
x_1262 = lean_ctor_get(x_1253, 0);
x_1263 = lean_ctor_get(x_1253, 1);
lean_inc(x_1263);
lean_inc(x_1262);
lean_dec(x_1253);
x_1264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1264, 0, x_1262);
lean_ctor_set(x_1264, 1, x_1263);
return x_1264;
}
}
}
else
{
uint8_t x_1265; 
lean_dec(x_1214);
lean_dec(x_1213);
lean_dec(x_1211);
lean_dec(x_1206);
lean_free_object(x_909);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1265 = !lean_is_exclusive(x_1217);
if (x_1265 == 0)
{
return x_1217;
}
else
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
x_1266 = lean_ctor_get(x_1217, 0);
x_1267 = lean_ctor_get(x_1217, 1);
lean_inc(x_1267);
lean_inc(x_1266);
lean_dec(x_1217);
x_1268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1268, 0, x_1266);
lean_ctor_set(x_1268, 1, x_1267);
return x_1268;
}
}
}
}
else
{
uint8_t x_1269; 
lean_dec(x_1206);
lean_free_object(x_909);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1269 = !lean_is_exclusive(x_1210);
if (x_1269 == 0)
{
return x_1210;
}
else
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
x_1270 = lean_ctor_get(x_1210, 0);
x_1271 = lean_ctor_get(x_1210, 1);
lean_inc(x_1271);
lean_inc(x_1270);
lean_dec(x_1210);
x_1272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1272, 0, x_1270);
lean_ctor_set(x_1272, 1, x_1271);
return x_1272;
}
}
}
else
{
lean_object* x_1273; lean_object* x_1274; uint8_t x_1275; 
x_1273 = l_Int_Linear_Poly_div(x_1206, x_22);
lean_inc(x_1273);
x_1274 = l_Int_Linear_Poly_denoteExpr(x_11, x_1273, x_5, x_6, x_7, x_8, x_19);
x_1275 = !lean_is_exclusive(x_1274);
if (x_1275 == 0)
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; 
x_1276 = lean_ctor_get(x_1274, 0);
x_1277 = lean_ctor_get(x_1274, 1);
x_1278 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_1279 = l_Lean_mkAppB(x_20, x_1276, x_1278);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1280 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_1277);
if (lean_obj_tag(x_1280) == 0)
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; uint8_t x_1287; lean_object* x_1288; 
x_1281 = lean_ctor_get(x_1280, 0);
lean_inc(x_1281);
x_1282 = lean_ctor_get(x_1280, 1);
lean_inc(x_1282);
lean_dec(x_1280);
x_1283 = lean_box(0);
x_1284 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1285 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1286 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_1273);
x_1287 = lean_int_dec_le(x_1200, x_1206);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1279);
x_1288 = l_Lean_Meta_mkEq(x_21, x_1279, x_5, x_6, x_7, x_8, x_1282);
if (x_1287 == 0)
{
if (lean_obj_tag(x_1288) == 0)
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; 
x_1289 = lean_ctor_get(x_1288, 0);
lean_inc(x_1289);
x_1290 = lean_ctor_get(x_1288, 1);
lean_inc(x_1290);
lean_dec(x_1288);
x_1291 = l_Lean_Expr_const___override(x_3, x_1283);
x_1292 = lean_int_neg(x_1206);
lean_dec(x_1206);
x_1293 = l_Int_toNat(x_1292);
lean_dec(x_1292);
x_1294 = l_Lean_instToExprInt_mkNat(x_1293);
x_1295 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_1296 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_1297 = l_Lean_mkApp3(x_1295, x_1291, x_1296, x_1294);
x_1298 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1299 = l_Lean_reflBoolTrue;
x_1300 = l_Lean_mkApp6(x_1298, x_1281, x_1284, x_1285, x_1286, x_1297, x_1299);
x_1301 = l_Lean_Meta_mkExpectedTypeHint(x_1300, x_1289, x_5, x_6, x_7, x_8, x_1290);
if (lean_obj_tag(x_1301) == 0)
{
uint8_t x_1302; 
x_1302 = !lean_is_exclusive(x_1301);
if (x_1302 == 0)
{
lean_object* x_1303; 
x_1303 = lean_ctor_get(x_1301, 0);
lean_ctor_set(x_1274, 1, x_1303);
lean_ctor_set(x_1274, 0, x_1279);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1274);
lean_ctor_set(x_1301, 0, x_909);
return x_1301;
}
else
{
lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
x_1304 = lean_ctor_get(x_1301, 0);
x_1305 = lean_ctor_get(x_1301, 1);
lean_inc(x_1305);
lean_inc(x_1304);
lean_dec(x_1301);
lean_ctor_set(x_1274, 1, x_1304);
lean_ctor_set(x_1274, 0, x_1279);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1274);
x_1306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1306, 0, x_909);
lean_ctor_set(x_1306, 1, x_1305);
return x_1306;
}
}
else
{
uint8_t x_1307; 
lean_dec(x_1279);
lean_free_object(x_1274);
lean_free_object(x_909);
x_1307 = !lean_is_exclusive(x_1301);
if (x_1307 == 0)
{
return x_1301;
}
else
{
lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; 
x_1308 = lean_ctor_get(x_1301, 0);
x_1309 = lean_ctor_get(x_1301, 1);
lean_inc(x_1309);
lean_inc(x_1308);
lean_dec(x_1301);
x_1310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1310, 0, x_1308);
lean_ctor_set(x_1310, 1, x_1309);
return x_1310;
}
}
}
else
{
uint8_t x_1311; 
lean_dec(x_1286);
lean_dec(x_1285);
lean_dec(x_1284);
lean_dec(x_1281);
lean_dec(x_1279);
lean_free_object(x_1274);
lean_dec(x_1206);
lean_free_object(x_909);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1311 = !lean_is_exclusive(x_1288);
if (x_1311 == 0)
{
return x_1288;
}
else
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
x_1312 = lean_ctor_get(x_1288, 0);
x_1313 = lean_ctor_get(x_1288, 1);
lean_inc(x_1313);
lean_inc(x_1312);
lean_dec(x_1288);
x_1314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1314, 0, x_1312);
lean_ctor_set(x_1314, 1, x_1313);
return x_1314;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1288) == 0)
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; 
x_1315 = lean_ctor_get(x_1288, 0);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1288, 1);
lean_inc(x_1316);
lean_dec(x_1288);
x_1317 = l_Int_toNat(x_1206);
lean_dec(x_1206);
x_1318 = l_Lean_instToExprInt_mkNat(x_1317);
x_1319 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1320 = l_Lean_reflBoolTrue;
x_1321 = l_Lean_mkApp6(x_1319, x_1281, x_1284, x_1285, x_1286, x_1318, x_1320);
x_1322 = l_Lean_Meta_mkExpectedTypeHint(x_1321, x_1315, x_5, x_6, x_7, x_8, x_1316);
if (lean_obj_tag(x_1322) == 0)
{
uint8_t x_1323; 
x_1323 = !lean_is_exclusive(x_1322);
if (x_1323 == 0)
{
lean_object* x_1324; 
x_1324 = lean_ctor_get(x_1322, 0);
lean_ctor_set(x_1274, 1, x_1324);
lean_ctor_set(x_1274, 0, x_1279);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1274);
lean_ctor_set(x_1322, 0, x_909);
return x_1322;
}
else
{
lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; 
x_1325 = lean_ctor_get(x_1322, 0);
x_1326 = lean_ctor_get(x_1322, 1);
lean_inc(x_1326);
lean_inc(x_1325);
lean_dec(x_1322);
lean_ctor_set(x_1274, 1, x_1325);
lean_ctor_set(x_1274, 0, x_1279);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1274);
x_1327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1327, 0, x_909);
lean_ctor_set(x_1327, 1, x_1326);
return x_1327;
}
}
else
{
uint8_t x_1328; 
lean_dec(x_1279);
lean_free_object(x_1274);
lean_free_object(x_909);
x_1328 = !lean_is_exclusive(x_1322);
if (x_1328 == 0)
{
return x_1322;
}
else
{
lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; 
x_1329 = lean_ctor_get(x_1322, 0);
x_1330 = lean_ctor_get(x_1322, 1);
lean_inc(x_1330);
lean_inc(x_1329);
lean_dec(x_1322);
x_1331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1331, 0, x_1329);
lean_ctor_set(x_1331, 1, x_1330);
return x_1331;
}
}
}
else
{
uint8_t x_1332; 
lean_dec(x_1286);
lean_dec(x_1285);
lean_dec(x_1284);
lean_dec(x_1281);
lean_dec(x_1279);
lean_free_object(x_1274);
lean_dec(x_1206);
lean_free_object(x_909);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1332 = !lean_is_exclusive(x_1288);
if (x_1332 == 0)
{
return x_1288;
}
else
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
x_1333 = lean_ctor_get(x_1288, 0);
x_1334 = lean_ctor_get(x_1288, 1);
lean_inc(x_1334);
lean_inc(x_1333);
lean_dec(x_1288);
x_1335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1335, 0, x_1333);
lean_ctor_set(x_1335, 1, x_1334);
return x_1335;
}
}
}
}
else
{
uint8_t x_1336; 
lean_dec(x_1279);
lean_free_object(x_1274);
lean_dec(x_1273);
lean_dec(x_1206);
lean_free_object(x_909);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1336 = !lean_is_exclusive(x_1280);
if (x_1336 == 0)
{
return x_1280;
}
else
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; 
x_1337 = lean_ctor_get(x_1280, 0);
x_1338 = lean_ctor_get(x_1280, 1);
lean_inc(x_1338);
lean_inc(x_1337);
lean_dec(x_1280);
x_1339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1339, 0, x_1337);
lean_ctor_set(x_1339, 1, x_1338);
return x_1339;
}
}
}
else
{
lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
x_1340 = lean_ctor_get(x_1274, 0);
x_1341 = lean_ctor_get(x_1274, 1);
lean_inc(x_1341);
lean_inc(x_1340);
lean_dec(x_1274);
x_1342 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_1343 = l_Lean_mkAppB(x_20, x_1340, x_1342);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1344 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_1341);
if (lean_obj_tag(x_1344) == 0)
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; uint8_t x_1351; lean_object* x_1352; 
x_1345 = lean_ctor_get(x_1344, 0);
lean_inc(x_1345);
x_1346 = lean_ctor_get(x_1344, 1);
lean_inc(x_1346);
lean_dec(x_1344);
x_1347 = lean_box(0);
x_1348 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1349 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1350 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_1273);
x_1351 = lean_int_dec_le(x_1200, x_1206);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1343);
x_1352 = l_Lean_Meta_mkEq(x_21, x_1343, x_5, x_6, x_7, x_8, x_1346);
if (x_1351 == 0)
{
if (lean_obj_tag(x_1352) == 0)
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; 
x_1353 = lean_ctor_get(x_1352, 0);
lean_inc(x_1353);
x_1354 = lean_ctor_get(x_1352, 1);
lean_inc(x_1354);
lean_dec(x_1352);
x_1355 = l_Lean_Expr_const___override(x_3, x_1347);
x_1356 = lean_int_neg(x_1206);
lean_dec(x_1206);
x_1357 = l_Int_toNat(x_1356);
lean_dec(x_1356);
x_1358 = l_Lean_instToExprInt_mkNat(x_1357);
x_1359 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_1360 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_1361 = l_Lean_mkApp3(x_1359, x_1355, x_1360, x_1358);
x_1362 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1363 = l_Lean_reflBoolTrue;
x_1364 = l_Lean_mkApp6(x_1362, x_1345, x_1348, x_1349, x_1350, x_1361, x_1363);
x_1365 = l_Lean_Meta_mkExpectedTypeHint(x_1364, x_1353, x_5, x_6, x_7, x_8, x_1354);
if (lean_obj_tag(x_1365) == 0)
{
lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; 
x_1366 = lean_ctor_get(x_1365, 0);
lean_inc(x_1366);
x_1367 = lean_ctor_get(x_1365, 1);
lean_inc(x_1367);
if (lean_is_exclusive(x_1365)) {
 lean_ctor_release(x_1365, 0);
 lean_ctor_release(x_1365, 1);
 x_1368 = x_1365;
} else {
 lean_dec_ref(x_1365);
 x_1368 = lean_box(0);
}
x_1369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1369, 0, x_1343);
lean_ctor_set(x_1369, 1, x_1366);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1369);
if (lean_is_scalar(x_1368)) {
 x_1370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1370 = x_1368;
}
lean_ctor_set(x_1370, 0, x_909);
lean_ctor_set(x_1370, 1, x_1367);
return x_1370;
}
else
{
lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
lean_dec(x_1343);
lean_free_object(x_909);
x_1371 = lean_ctor_get(x_1365, 0);
lean_inc(x_1371);
x_1372 = lean_ctor_get(x_1365, 1);
lean_inc(x_1372);
if (lean_is_exclusive(x_1365)) {
 lean_ctor_release(x_1365, 0);
 lean_ctor_release(x_1365, 1);
 x_1373 = x_1365;
} else {
 lean_dec_ref(x_1365);
 x_1373 = lean_box(0);
}
if (lean_is_scalar(x_1373)) {
 x_1374 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1374 = x_1373;
}
lean_ctor_set(x_1374, 0, x_1371);
lean_ctor_set(x_1374, 1, x_1372);
return x_1374;
}
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; 
lean_dec(x_1350);
lean_dec(x_1349);
lean_dec(x_1348);
lean_dec(x_1345);
lean_dec(x_1343);
lean_dec(x_1206);
lean_free_object(x_909);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1375 = lean_ctor_get(x_1352, 0);
lean_inc(x_1375);
x_1376 = lean_ctor_get(x_1352, 1);
lean_inc(x_1376);
if (lean_is_exclusive(x_1352)) {
 lean_ctor_release(x_1352, 0);
 lean_ctor_release(x_1352, 1);
 x_1377 = x_1352;
} else {
 lean_dec_ref(x_1352);
 x_1377 = lean_box(0);
}
if (lean_is_scalar(x_1377)) {
 x_1378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1378 = x_1377;
}
lean_ctor_set(x_1378, 0, x_1375);
lean_ctor_set(x_1378, 1, x_1376);
return x_1378;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1352) == 0)
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
x_1379 = lean_ctor_get(x_1352, 0);
lean_inc(x_1379);
x_1380 = lean_ctor_get(x_1352, 1);
lean_inc(x_1380);
lean_dec(x_1352);
x_1381 = l_Int_toNat(x_1206);
lean_dec(x_1206);
x_1382 = l_Lean_instToExprInt_mkNat(x_1381);
x_1383 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1384 = l_Lean_reflBoolTrue;
x_1385 = l_Lean_mkApp6(x_1383, x_1345, x_1348, x_1349, x_1350, x_1382, x_1384);
x_1386 = l_Lean_Meta_mkExpectedTypeHint(x_1385, x_1379, x_5, x_6, x_7, x_8, x_1380);
if (lean_obj_tag(x_1386) == 0)
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; 
x_1387 = lean_ctor_get(x_1386, 0);
lean_inc(x_1387);
x_1388 = lean_ctor_get(x_1386, 1);
lean_inc(x_1388);
if (lean_is_exclusive(x_1386)) {
 lean_ctor_release(x_1386, 0);
 lean_ctor_release(x_1386, 1);
 x_1389 = x_1386;
} else {
 lean_dec_ref(x_1386);
 x_1389 = lean_box(0);
}
x_1390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1390, 0, x_1343);
lean_ctor_set(x_1390, 1, x_1387);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1390);
if (lean_is_scalar(x_1389)) {
 x_1391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1391 = x_1389;
}
lean_ctor_set(x_1391, 0, x_909);
lean_ctor_set(x_1391, 1, x_1388);
return x_1391;
}
else
{
lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; 
lean_dec(x_1343);
lean_free_object(x_909);
x_1392 = lean_ctor_get(x_1386, 0);
lean_inc(x_1392);
x_1393 = lean_ctor_get(x_1386, 1);
lean_inc(x_1393);
if (lean_is_exclusive(x_1386)) {
 lean_ctor_release(x_1386, 0);
 lean_ctor_release(x_1386, 1);
 x_1394 = x_1386;
} else {
 lean_dec_ref(x_1386);
 x_1394 = lean_box(0);
}
if (lean_is_scalar(x_1394)) {
 x_1395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1395 = x_1394;
}
lean_ctor_set(x_1395, 0, x_1392);
lean_ctor_set(x_1395, 1, x_1393);
return x_1395;
}
}
else
{
lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; 
lean_dec(x_1350);
lean_dec(x_1349);
lean_dec(x_1348);
lean_dec(x_1345);
lean_dec(x_1343);
lean_dec(x_1206);
lean_free_object(x_909);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1396 = lean_ctor_get(x_1352, 0);
lean_inc(x_1396);
x_1397 = lean_ctor_get(x_1352, 1);
lean_inc(x_1397);
if (lean_is_exclusive(x_1352)) {
 lean_ctor_release(x_1352, 0);
 lean_ctor_release(x_1352, 1);
 x_1398 = x_1352;
} else {
 lean_dec_ref(x_1352);
 x_1398 = lean_box(0);
}
if (lean_is_scalar(x_1398)) {
 x_1399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1399 = x_1398;
}
lean_ctor_set(x_1399, 0, x_1396);
lean_ctor_set(x_1399, 1, x_1397);
return x_1399;
}
}
}
else
{
lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
lean_dec(x_1343);
lean_dec(x_1273);
lean_dec(x_1206);
lean_free_object(x_909);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1400 = lean_ctor_get(x_1344, 0);
lean_inc(x_1400);
x_1401 = lean_ctor_get(x_1344, 1);
lean_inc(x_1401);
if (lean_is_exclusive(x_1344)) {
 lean_ctor_release(x_1344, 0);
 lean_ctor_release(x_1344, 1);
 x_1402 = x_1344;
} else {
 lean_dec_ref(x_1344);
 x_1402 = lean_box(0);
}
if (lean_is_scalar(x_1402)) {
 x_1403 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1403 = x_1402;
}
lean_ctor_set(x_1403, 0, x_1400);
lean_ctor_set(x_1403, 1, x_1401);
return x_1403;
}
}
}
}
else
{
lean_object* x_1404; uint8_t x_1405; 
lean_dec(x_1202);
lean_dec(x_3);
lean_inc(x_22);
x_1404 = l_Int_Linear_Poly_denoteExpr(x_11, x_22, x_5, x_6, x_7, x_8, x_19);
x_1405 = !lean_is_exclusive(x_1404);
if (x_1405 == 0)
{
lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; 
x_1406 = lean_ctor_get(x_1404, 0);
x_1407 = lean_ctor_get(x_1404, 1);
x_1408 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_1409 = l_Lean_mkAppB(x_20, x_1406, x_1408);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1410 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_1407);
if (lean_obj_tag(x_1410) == 0)
{
lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
x_1411 = lean_ctor_get(x_1410, 0);
lean_inc(x_1411);
x_1412 = lean_ctor_get(x_1410, 1);
lean_inc(x_1412);
lean_dec(x_1410);
x_1413 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1414 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1415 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_22);
x_1416 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_1417 = l_Lean_reflBoolTrue;
x_1418 = l_Lean_mkApp5(x_1416, x_1411, x_1413, x_1414, x_1415, x_1417);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1409);
x_1419 = l_Lean_Meta_mkEq(x_21, x_1409, x_5, x_6, x_7, x_8, x_1412);
if (lean_obj_tag(x_1419) == 0)
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; 
x_1420 = lean_ctor_get(x_1419, 0);
lean_inc(x_1420);
x_1421 = lean_ctor_get(x_1419, 1);
lean_inc(x_1421);
lean_dec(x_1419);
x_1422 = l_Lean_Meta_mkExpectedTypeHint(x_1418, x_1420, x_5, x_6, x_7, x_8, x_1421);
if (lean_obj_tag(x_1422) == 0)
{
uint8_t x_1423; 
x_1423 = !lean_is_exclusive(x_1422);
if (x_1423 == 0)
{
lean_object* x_1424; 
x_1424 = lean_ctor_get(x_1422, 0);
lean_ctor_set(x_1404, 1, x_1424);
lean_ctor_set(x_1404, 0, x_1409);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1404);
lean_ctor_set(x_1422, 0, x_909);
return x_1422;
}
else
{
lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; 
x_1425 = lean_ctor_get(x_1422, 0);
x_1426 = lean_ctor_get(x_1422, 1);
lean_inc(x_1426);
lean_inc(x_1425);
lean_dec(x_1422);
lean_ctor_set(x_1404, 1, x_1425);
lean_ctor_set(x_1404, 0, x_1409);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1404);
x_1427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1427, 0, x_909);
lean_ctor_set(x_1427, 1, x_1426);
return x_1427;
}
}
else
{
uint8_t x_1428; 
lean_dec(x_1409);
lean_free_object(x_1404);
lean_free_object(x_909);
x_1428 = !lean_is_exclusive(x_1422);
if (x_1428 == 0)
{
return x_1422;
}
else
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; 
x_1429 = lean_ctor_get(x_1422, 0);
x_1430 = lean_ctor_get(x_1422, 1);
lean_inc(x_1430);
lean_inc(x_1429);
lean_dec(x_1422);
x_1431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1431, 0, x_1429);
lean_ctor_set(x_1431, 1, x_1430);
return x_1431;
}
}
}
else
{
uint8_t x_1432; 
lean_dec(x_1418);
lean_dec(x_1409);
lean_free_object(x_1404);
lean_free_object(x_909);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1432 = !lean_is_exclusive(x_1419);
if (x_1432 == 0)
{
return x_1419;
}
else
{
lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; 
x_1433 = lean_ctor_get(x_1419, 0);
x_1434 = lean_ctor_get(x_1419, 1);
lean_inc(x_1434);
lean_inc(x_1433);
lean_dec(x_1419);
x_1435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1435, 0, x_1433);
lean_ctor_set(x_1435, 1, x_1434);
return x_1435;
}
}
}
else
{
uint8_t x_1436; 
lean_dec(x_1409);
lean_free_object(x_1404);
lean_free_object(x_909);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1436 = !lean_is_exclusive(x_1410);
if (x_1436 == 0)
{
return x_1410;
}
else
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; 
x_1437 = lean_ctor_get(x_1410, 0);
x_1438 = lean_ctor_get(x_1410, 1);
lean_inc(x_1438);
lean_inc(x_1437);
lean_dec(x_1410);
x_1439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1439, 0, x_1437);
lean_ctor_set(x_1439, 1, x_1438);
return x_1439;
}
}
}
else
{
lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; 
x_1440 = lean_ctor_get(x_1404, 0);
x_1441 = lean_ctor_get(x_1404, 1);
lean_inc(x_1441);
lean_inc(x_1440);
lean_dec(x_1404);
x_1442 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_1443 = l_Lean_mkAppB(x_20, x_1440, x_1442);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1444 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_1441);
if (lean_obj_tag(x_1444) == 0)
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; 
x_1445 = lean_ctor_get(x_1444, 0);
lean_inc(x_1445);
x_1446 = lean_ctor_get(x_1444, 1);
lean_inc(x_1446);
lean_dec(x_1444);
x_1447 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1448 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1449 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_22);
x_1450 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_1451 = l_Lean_reflBoolTrue;
x_1452 = l_Lean_mkApp5(x_1450, x_1445, x_1447, x_1448, x_1449, x_1451);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1443);
x_1453 = l_Lean_Meta_mkEq(x_21, x_1443, x_5, x_6, x_7, x_8, x_1446);
if (lean_obj_tag(x_1453) == 0)
{
lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; 
x_1454 = lean_ctor_get(x_1453, 0);
lean_inc(x_1454);
x_1455 = lean_ctor_get(x_1453, 1);
lean_inc(x_1455);
lean_dec(x_1453);
x_1456 = l_Lean_Meta_mkExpectedTypeHint(x_1452, x_1454, x_5, x_6, x_7, x_8, x_1455);
if (lean_obj_tag(x_1456) == 0)
{
lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; 
x_1457 = lean_ctor_get(x_1456, 0);
lean_inc(x_1457);
x_1458 = lean_ctor_get(x_1456, 1);
lean_inc(x_1458);
if (lean_is_exclusive(x_1456)) {
 lean_ctor_release(x_1456, 0);
 lean_ctor_release(x_1456, 1);
 x_1459 = x_1456;
} else {
 lean_dec_ref(x_1456);
 x_1459 = lean_box(0);
}
x_1460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1460, 0, x_1443);
lean_ctor_set(x_1460, 1, x_1457);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1460);
if (lean_is_scalar(x_1459)) {
 x_1461 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1461 = x_1459;
}
lean_ctor_set(x_1461, 0, x_909);
lean_ctor_set(x_1461, 1, x_1458);
return x_1461;
}
else
{
lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; 
lean_dec(x_1443);
lean_free_object(x_909);
x_1462 = lean_ctor_get(x_1456, 0);
lean_inc(x_1462);
x_1463 = lean_ctor_get(x_1456, 1);
lean_inc(x_1463);
if (lean_is_exclusive(x_1456)) {
 lean_ctor_release(x_1456, 0);
 lean_ctor_release(x_1456, 1);
 x_1464 = x_1456;
} else {
 lean_dec_ref(x_1456);
 x_1464 = lean_box(0);
}
if (lean_is_scalar(x_1464)) {
 x_1465 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1465 = x_1464;
}
lean_ctor_set(x_1465, 0, x_1462);
lean_ctor_set(x_1465, 1, x_1463);
return x_1465;
}
}
else
{
lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; 
lean_dec(x_1452);
lean_dec(x_1443);
lean_free_object(x_909);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1466 = lean_ctor_get(x_1453, 0);
lean_inc(x_1466);
x_1467 = lean_ctor_get(x_1453, 1);
lean_inc(x_1467);
if (lean_is_exclusive(x_1453)) {
 lean_ctor_release(x_1453, 0);
 lean_ctor_release(x_1453, 1);
 x_1468 = x_1453;
} else {
 lean_dec_ref(x_1453);
 x_1468 = lean_box(0);
}
if (lean_is_scalar(x_1468)) {
 x_1469 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1469 = x_1468;
}
lean_ctor_set(x_1469, 0, x_1466);
lean_ctor_set(x_1469, 1, x_1467);
return x_1469;
}
}
else
{
lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; 
lean_dec(x_1443);
lean_free_object(x_909);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1470 = lean_ctor_get(x_1444, 0);
lean_inc(x_1470);
x_1471 = lean_ctor_get(x_1444, 1);
lean_inc(x_1471);
if (lean_is_exclusive(x_1444)) {
 lean_ctor_release(x_1444, 0);
 lean_ctor_release(x_1444, 1);
 x_1472 = x_1444;
} else {
 lean_dec_ref(x_1444);
 x_1472 = lean_box(0);
}
if (lean_is_scalar(x_1472)) {
 x_1473 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1473 = x_1472;
}
lean_ctor_set(x_1473, 0, x_1470);
lean_ctor_set(x_1473, 1, x_1471);
return x_1473;
}
}
}
}
else
{
lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_3);
x_1474 = lean_array_get(x_10, x_4, x_456);
x_1475 = lean_array_get(x_10, x_4, x_908);
x_1476 = l_Lean_mkAppB(x_20, x_1474, x_1475);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1477 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_1477) == 0)
{
lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; 
x_1478 = lean_ctor_get(x_1477, 0);
lean_inc(x_1478);
x_1479 = lean_ctor_get(x_1477, 1);
lean_inc(x_1479);
lean_dec(x_1477);
x_1480 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1481 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1482 = l_Lean_mkNatLit(x_456);
x_1483 = l_Lean_mkNatLit(x_908);
x_1484 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__36;
x_1485 = l_Lean_reflBoolTrue;
x_1486 = l_Lean_mkApp6(x_1484, x_1478, x_1480, x_1481, x_1482, x_1483, x_1485);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1476);
x_1487 = l_Lean_Meta_mkEq(x_21, x_1476, x_5, x_6, x_7, x_8, x_1479);
if (lean_obj_tag(x_1487) == 0)
{
lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; 
x_1488 = lean_ctor_get(x_1487, 0);
lean_inc(x_1488);
x_1489 = lean_ctor_get(x_1487, 1);
lean_inc(x_1489);
lean_dec(x_1487);
x_1490 = l_Lean_Meta_mkExpectedTypeHint(x_1486, x_1488, x_5, x_6, x_7, x_8, x_1489);
if (lean_obj_tag(x_1490) == 0)
{
uint8_t x_1491; 
x_1491 = !lean_is_exclusive(x_1490);
if (x_1491 == 0)
{
lean_object* x_1492; lean_object* x_1493; 
x_1492 = lean_ctor_get(x_1490, 0);
x_1493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1493, 0, x_1476);
lean_ctor_set(x_1493, 1, x_1492);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1493);
lean_ctor_set(x_1490, 0, x_909);
return x_1490;
}
else
{
lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; 
x_1494 = lean_ctor_get(x_1490, 0);
x_1495 = lean_ctor_get(x_1490, 1);
lean_inc(x_1495);
lean_inc(x_1494);
lean_dec(x_1490);
x_1496 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1496, 0, x_1476);
lean_ctor_set(x_1496, 1, x_1494);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 0, x_1496);
x_1497 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1497, 0, x_909);
lean_ctor_set(x_1497, 1, x_1495);
return x_1497;
}
}
else
{
uint8_t x_1498; 
lean_dec(x_1476);
lean_free_object(x_909);
x_1498 = !lean_is_exclusive(x_1490);
if (x_1498 == 0)
{
return x_1490;
}
else
{
lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; 
x_1499 = lean_ctor_get(x_1490, 0);
x_1500 = lean_ctor_get(x_1490, 1);
lean_inc(x_1500);
lean_inc(x_1499);
lean_dec(x_1490);
x_1501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1501, 0, x_1499);
lean_ctor_set(x_1501, 1, x_1500);
return x_1501;
}
}
}
else
{
uint8_t x_1502; 
lean_dec(x_1486);
lean_dec(x_1476);
lean_free_object(x_909);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1502 = !lean_is_exclusive(x_1487);
if (x_1502 == 0)
{
return x_1487;
}
else
{
lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; 
x_1503 = lean_ctor_get(x_1487, 0);
x_1504 = lean_ctor_get(x_1487, 1);
lean_inc(x_1504);
lean_inc(x_1503);
lean_dec(x_1487);
x_1505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1505, 0, x_1503);
lean_ctor_set(x_1505, 1, x_1504);
return x_1505;
}
}
}
else
{
uint8_t x_1506; 
lean_dec(x_1476);
lean_free_object(x_909);
lean_dec(x_908);
lean_dec(x_456);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1506 = !lean_is_exclusive(x_1477);
if (x_1506 == 0)
{
return x_1477;
}
else
{
lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; 
x_1507 = lean_ctor_get(x_1477, 0);
x_1508 = lean_ctor_get(x_1477, 1);
lean_inc(x_1508);
lean_inc(x_1507);
lean_dec(x_1477);
x_1509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1509, 0, x_1507);
lean_ctor_set(x_1509, 1, x_1508);
return x_1509;
}
}
}
}
else
{
lean_object* x_1510; lean_object* x_1511; uint8_t x_1512; 
x_1510 = lean_ctor_get(x_909, 0);
lean_inc(x_1510);
lean_dec(x_909);
x_1511 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_1512 = lean_int_dec_eq(x_1510, x_1511);
lean_dec(x_1510);
if (x_1512 == 0)
{
lean_object* x_1513; lean_object* x_1514; uint8_t x_1515; 
lean_dec(x_908);
lean_dec(x_456);
x_1513 = l_Int_Linear_Poly_gcdCoeffs_x27(x_22);
x_1514 = lean_unsigned_to_nat(1u);
x_1515 = lean_nat_dec_eq(x_1513, x_1514);
if (x_1515 == 0)
{
lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; uint8_t x_1519; 
x_1516 = l_Int_Linear_Poly_getConst(x_22);
x_1517 = lean_nat_to_int(x_1513);
x_1518 = lean_int_emod(x_1516, x_1517);
lean_dec(x_1516);
x_1519 = lean_int_dec_eq(x_1518, x_1511);
lean_dec(x_1518);
if (x_1519 == 0)
{
lean_object* x_1520; lean_object* x_1521; 
lean_dec(x_22);
lean_dec(x_11);
x_1520 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1521 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_1521) == 0)
{
lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; uint8_t x_1526; lean_object* x_1527; lean_object* x_1528; 
x_1522 = lean_ctor_get(x_1521, 0);
lean_inc(x_1522);
x_1523 = lean_ctor_get(x_1521, 1);
lean_inc(x_1523);
lean_dec(x_1521);
x_1524 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1525 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1526 = lean_int_dec_le(x_1511, x_1517);
x_1527 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1528 = l_Lean_Meta_mkEq(x_21, x_1527, x_5, x_6, x_7, x_8, x_1523);
if (x_1526 == 0)
{
if (lean_obj_tag(x_1528) == 0)
{
lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; 
x_1529 = lean_ctor_get(x_1528, 0);
lean_inc(x_1529);
x_1530 = lean_ctor_get(x_1528, 1);
lean_inc(x_1530);
lean_dec(x_1528);
x_1531 = l_Lean_Expr_const___override(x_3, x_1520);
x_1532 = lean_int_neg(x_1517);
lean_dec(x_1517);
x_1533 = l_Int_toNat(x_1532);
lean_dec(x_1532);
x_1534 = l_Lean_instToExprInt_mkNat(x_1533);
x_1535 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_1536 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_1537 = l_Lean_mkApp3(x_1535, x_1531, x_1536, x_1534);
x_1538 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_1539 = l_Lean_reflBoolTrue;
x_1540 = l_Lean_mkApp5(x_1538, x_1522, x_1524, x_1525, x_1537, x_1539);
x_1541 = l_Lean_Meta_mkExpectedTypeHint(x_1540, x_1529, x_5, x_6, x_7, x_8, x_1530);
if (lean_obj_tag(x_1541) == 0)
{
lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; 
x_1542 = lean_ctor_get(x_1541, 0);
lean_inc(x_1542);
x_1543 = lean_ctor_get(x_1541, 1);
lean_inc(x_1543);
if (lean_is_exclusive(x_1541)) {
 lean_ctor_release(x_1541, 0);
 lean_ctor_release(x_1541, 1);
 x_1544 = x_1541;
} else {
 lean_dec_ref(x_1541);
 x_1544 = lean_box(0);
}
x_1545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1545, 0, x_1527);
lean_ctor_set(x_1545, 1, x_1542);
x_1546 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1546, 0, x_1545);
if (lean_is_scalar(x_1544)) {
 x_1547 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1547 = x_1544;
}
lean_ctor_set(x_1547, 0, x_1546);
lean_ctor_set(x_1547, 1, x_1543);
return x_1547;
}
else
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; 
x_1548 = lean_ctor_get(x_1541, 0);
lean_inc(x_1548);
x_1549 = lean_ctor_get(x_1541, 1);
lean_inc(x_1549);
if (lean_is_exclusive(x_1541)) {
 lean_ctor_release(x_1541, 0);
 lean_ctor_release(x_1541, 1);
 x_1550 = x_1541;
} else {
 lean_dec_ref(x_1541);
 x_1550 = lean_box(0);
}
if (lean_is_scalar(x_1550)) {
 x_1551 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1551 = x_1550;
}
lean_ctor_set(x_1551, 0, x_1548);
lean_ctor_set(x_1551, 1, x_1549);
return x_1551;
}
}
else
{
lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; 
lean_dec(x_1525);
lean_dec(x_1524);
lean_dec(x_1522);
lean_dec(x_1517);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1552 = lean_ctor_get(x_1528, 0);
lean_inc(x_1552);
x_1553 = lean_ctor_get(x_1528, 1);
lean_inc(x_1553);
if (lean_is_exclusive(x_1528)) {
 lean_ctor_release(x_1528, 0);
 lean_ctor_release(x_1528, 1);
 x_1554 = x_1528;
} else {
 lean_dec_ref(x_1528);
 x_1554 = lean_box(0);
}
if (lean_is_scalar(x_1554)) {
 x_1555 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1555 = x_1554;
}
lean_ctor_set(x_1555, 0, x_1552);
lean_ctor_set(x_1555, 1, x_1553);
return x_1555;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1528) == 0)
{
lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; 
x_1556 = lean_ctor_get(x_1528, 0);
lean_inc(x_1556);
x_1557 = lean_ctor_get(x_1528, 1);
lean_inc(x_1557);
lean_dec(x_1528);
x_1558 = l_Int_toNat(x_1517);
lean_dec(x_1517);
x_1559 = l_Lean_instToExprInt_mkNat(x_1558);
x_1560 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_1561 = l_Lean_reflBoolTrue;
x_1562 = l_Lean_mkApp5(x_1560, x_1522, x_1524, x_1525, x_1559, x_1561);
x_1563 = l_Lean_Meta_mkExpectedTypeHint(x_1562, x_1556, x_5, x_6, x_7, x_8, x_1557);
if (lean_obj_tag(x_1563) == 0)
{
lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; 
x_1564 = lean_ctor_get(x_1563, 0);
lean_inc(x_1564);
x_1565 = lean_ctor_get(x_1563, 1);
lean_inc(x_1565);
if (lean_is_exclusive(x_1563)) {
 lean_ctor_release(x_1563, 0);
 lean_ctor_release(x_1563, 1);
 x_1566 = x_1563;
} else {
 lean_dec_ref(x_1563);
 x_1566 = lean_box(0);
}
x_1567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1567, 0, x_1527);
lean_ctor_set(x_1567, 1, x_1564);
x_1568 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1568, 0, x_1567);
if (lean_is_scalar(x_1566)) {
 x_1569 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1569 = x_1566;
}
lean_ctor_set(x_1569, 0, x_1568);
lean_ctor_set(x_1569, 1, x_1565);
return x_1569;
}
else
{
lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; 
x_1570 = lean_ctor_get(x_1563, 0);
lean_inc(x_1570);
x_1571 = lean_ctor_get(x_1563, 1);
lean_inc(x_1571);
if (lean_is_exclusive(x_1563)) {
 lean_ctor_release(x_1563, 0);
 lean_ctor_release(x_1563, 1);
 x_1572 = x_1563;
} else {
 lean_dec_ref(x_1563);
 x_1572 = lean_box(0);
}
if (lean_is_scalar(x_1572)) {
 x_1573 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1573 = x_1572;
}
lean_ctor_set(x_1573, 0, x_1570);
lean_ctor_set(x_1573, 1, x_1571);
return x_1573;
}
}
else
{
lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; 
lean_dec(x_1525);
lean_dec(x_1524);
lean_dec(x_1522);
lean_dec(x_1517);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1574 = lean_ctor_get(x_1528, 0);
lean_inc(x_1574);
x_1575 = lean_ctor_get(x_1528, 1);
lean_inc(x_1575);
if (lean_is_exclusive(x_1528)) {
 lean_ctor_release(x_1528, 0);
 lean_ctor_release(x_1528, 1);
 x_1576 = x_1528;
} else {
 lean_dec_ref(x_1528);
 x_1576 = lean_box(0);
}
if (lean_is_scalar(x_1576)) {
 x_1577 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1577 = x_1576;
}
lean_ctor_set(x_1577, 0, x_1574);
lean_ctor_set(x_1577, 1, x_1575);
return x_1577;
}
}
}
else
{
lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; 
lean_dec(x_1517);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1578 = lean_ctor_get(x_1521, 0);
lean_inc(x_1578);
x_1579 = lean_ctor_get(x_1521, 1);
lean_inc(x_1579);
if (lean_is_exclusive(x_1521)) {
 lean_ctor_release(x_1521, 0);
 lean_ctor_release(x_1521, 1);
 x_1580 = x_1521;
} else {
 lean_dec_ref(x_1521);
 x_1580 = lean_box(0);
}
if (lean_is_scalar(x_1580)) {
 x_1581 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1581 = x_1580;
}
lean_ctor_set(x_1581, 0, x_1578);
lean_ctor_set(x_1581, 1, x_1579);
return x_1581;
}
}
else
{
lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; 
x_1582 = l_Int_Linear_Poly_div(x_1517, x_22);
lean_inc(x_1582);
x_1583 = l_Int_Linear_Poly_denoteExpr(x_11, x_1582, x_5, x_6, x_7, x_8, x_19);
x_1584 = lean_ctor_get(x_1583, 0);
lean_inc(x_1584);
x_1585 = lean_ctor_get(x_1583, 1);
lean_inc(x_1585);
if (lean_is_exclusive(x_1583)) {
 lean_ctor_release(x_1583, 0);
 lean_ctor_release(x_1583, 1);
 x_1586 = x_1583;
} else {
 lean_dec_ref(x_1583);
 x_1586 = lean_box(0);
}
x_1587 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_1588 = l_Lean_mkAppB(x_20, x_1584, x_1587);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1589 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_1585);
if (lean_obj_tag(x_1589) == 0)
{
lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; uint8_t x_1596; lean_object* x_1597; 
x_1590 = lean_ctor_get(x_1589, 0);
lean_inc(x_1590);
x_1591 = lean_ctor_get(x_1589, 1);
lean_inc(x_1591);
lean_dec(x_1589);
x_1592 = lean_box(0);
x_1593 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1594 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1595 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_1582);
x_1596 = lean_int_dec_le(x_1511, x_1517);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1588);
x_1597 = l_Lean_Meta_mkEq(x_21, x_1588, x_5, x_6, x_7, x_8, x_1591);
if (x_1596 == 0)
{
if (lean_obj_tag(x_1597) == 0)
{
lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; 
x_1598 = lean_ctor_get(x_1597, 0);
lean_inc(x_1598);
x_1599 = lean_ctor_get(x_1597, 1);
lean_inc(x_1599);
lean_dec(x_1597);
x_1600 = l_Lean_Expr_const___override(x_3, x_1592);
x_1601 = lean_int_neg(x_1517);
lean_dec(x_1517);
x_1602 = l_Int_toNat(x_1601);
lean_dec(x_1601);
x_1603 = l_Lean_instToExprInt_mkNat(x_1602);
x_1604 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_1605 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_1606 = l_Lean_mkApp3(x_1604, x_1600, x_1605, x_1603);
x_1607 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1608 = l_Lean_reflBoolTrue;
x_1609 = l_Lean_mkApp6(x_1607, x_1590, x_1593, x_1594, x_1595, x_1606, x_1608);
x_1610 = l_Lean_Meta_mkExpectedTypeHint(x_1609, x_1598, x_5, x_6, x_7, x_8, x_1599);
if (lean_obj_tag(x_1610) == 0)
{
lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; 
x_1611 = lean_ctor_get(x_1610, 0);
lean_inc(x_1611);
x_1612 = lean_ctor_get(x_1610, 1);
lean_inc(x_1612);
if (lean_is_exclusive(x_1610)) {
 lean_ctor_release(x_1610, 0);
 lean_ctor_release(x_1610, 1);
 x_1613 = x_1610;
} else {
 lean_dec_ref(x_1610);
 x_1613 = lean_box(0);
}
if (lean_is_scalar(x_1586)) {
 x_1614 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1614 = x_1586;
}
lean_ctor_set(x_1614, 0, x_1588);
lean_ctor_set(x_1614, 1, x_1611);
x_1615 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1615, 0, x_1614);
if (lean_is_scalar(x_1613)) {
 x_1616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1616 = x_1613;
}
lean_ctor_set(x_1616, 0, x_1615);
lean_ctor_set(x_1616, 1, x_1612);
return x_1616;
}
else
{
lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; 
lean_dec(x_1588);
lean_dec(x_1586);
x_1617 = lean_ctor_get(x_1610, 0);
lean_inc(x_1617);
x_1618 = lean_ctor_get(x_1610, 1);
lean_inc(x_1618);
if (lean_is_exclusive(x_1610)) {
 lean_ctor_release(x_1610, 0);
 lean_ctor_release(x_1610, 1);
 x_1619 = x_1610;
} else {
 lean_dec_ref(x_1610);
 x_1619 = lean_box(0);
}
if (lean_is_scalar(x_1619)) {
 x_1620 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1620 = x_1619;
}
lean_ctor_set(x_1620, 0, x_1617);
lean_ctor_set(x_1620, 1, x_1618);
return x_1620;
}
}
else
{
lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; 
lean_dec(x_1595);
lean_dec(x_1594);
lean_dec(x_1593);
lean_dec(x_1590);
lean_dec(x_1588);
lean_dec(x_1586);
lean_dec(x_1517);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1621 = lean_ctor_get(x_1597, 0);
lean_inc(x_1621);
x_1622 = lean_ctor_get(x_1597, 1);
lean_inc(x_1622);
if (lean_is_exclusive(x_1597)) {
 lean_ctor_release(x_1597, 0);
 lean_ctor_release(x_1597, 1);
 x_1623 = x_1597;
} else {
 lean_dec_ref(x_1597);
 x_1623 = lean_box(0);
}
if (lean_is_scalar(x_1623)) {
 x_1624 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1624 = x_1623;
}
lean_ctor_set(x_1624, 0, x_1621);
lean_ctor_set(x_1624, 1, x_1622);
return x_1624;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1597) == 0)
{
lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; 
x_1625 = lean_ctor_get(x_1597, 0);
lean_inc(x_1625);
x_1626 = lean_ctor_get(x_1597, 1);
lean_inc(x_1626);
lean_dec(x_1597);
x_1627 = l_Int_toNat(x_1517);
lean_dec(x_1517);
x_1628 = l_Lean_instToExprInt_mkNat(x_1627);
x_1629 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1630 = l_Lean_reflBoolTrue;
x_1631 = l_Lean_mkApp6(x_1629, x_1590, x_1593, x_1594, x_1595, x_1628, x_1630);
x_1632 = l_Lean_Meta_mkExpectedTypeHint(x_1631, x_1625, x_5, x_6, x_7, x_8, x_1626);
if (lean_obj_tag(x_1632) == 0)
{
lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; 
x_1633 = lean_ctor_get(x_1632, 0);
lean_inc(x_1633);
x_1634 = lean_ctor_get(x_1632, 1);
lean_inc(x_1634);
if (lean_is_exclusive(x_1632)) {
 lean_ctor_release(x_1632, 0);
 lean_ctor_release(x_1632, 1);
 x_1635 = x_1632;
} else {
 lean_dec_ref(x_1632);
 x_1635 = lean_box(0);
}
if (lean_is_scalar(x_1586)) {
 x_1636 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1636 = x_1586;
}
lean_ctor_set(x_1636, 0, x_1588);
lean_ctor_set(x_1636, 1, x_1633);
x_1637 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1637, 0, x_1636);
if (lean_is_scalar(x_1635)) {
 x_1638 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1638 = x_1635;
}
lean_ctor_set(x_1638, 0, x_1637);
lean_ctor_set(x_1638, 1, x_1634);
return x_1638;
}
else
{
lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; 
lean_dec(x_1588);
lean_dec(x_1586);
x_1639 = lean_ctor_get(x_1632, 0);
lean_inc(x_1639);
x_1640 = lean_ctor_get(x_1632, 1);
lean_inc(x_1640);
if (lean_is_exclusive(x_1632)) {
 lean_ctor_release(x_1632, 0);
 lean_ctor_release(x_1632, 1);
 x_1641 = x_1632;
} else {
 lean_dec_ref(x_1632);
 x_1641 = lean_box(0);
}
if (lean_is_scalar(x_1641)) {
 x_1642 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1642 = x_1641;
}
lean_ctor_set(x_1642, 0, x_1639);
lean_ctor_set(x_1642, 1, x_1640);
return x_1642;
}
}
else
{
lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; 
lean_dec(x_1595);
lean_dec(x_1594);
lean_dec(x_1593);
lean_dec(x_1590);
lean_dec(x_1588);
lean_dec(x_1586);
lean_dec(x_1517);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1643 = lean_ctor_get(x_1597, 0);
lean_inc(x_1643);
x_1644 = lean_ctor_get(x_1597, 1);
lean_inc(x_1644);
if (lean_is_exclusive(x_1597)) {
 lean_ctor_release(x_1597, 0);
 lean_ctor_release(x_1597, 1);
 x_1645 = x_1597;
} else {
 lean_dec_ref(x_1597);
 x_1645 = lean_box(0);
}
if (lean_is_scalar(x_1645)) {
 x_1646 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1646 = x_1645;
}
lean_ctor_set(x_1646, 0, x_1643);
lean_ctor_set(x_1646, 1, x_1644);
return x_1646;
}
}
}
else
{
lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; 
lean_dec(x_1588);
lean_dec(x_1586);
lean_dec(x_1582);
lean_dec(x_1517);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1647 = lean_ctor_get(x_1589, 0);
lean_inc(x_1647);
x_1648 = lean_ctor_get(x_1589, 1);
lean_inc(x_1648);
if (lean_is_exclusive(x_1589)) {
 lean_ctor_release(x_1589, 0);
 lean_ctor_release(x_1589, 1);
 x_1649 = x_1589;
} else {
 lean_dec_ref(x_1589);
 x_1649 = lean_box(0);
}
if (lean_is_scalar(x_1649)) {
 x_1650 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1650 = x_1649;
}
lean_ctor_set(x_1650, 0, x_1647);
lean_ctor_set(x_1650, 1, x_1648);
return x_1650;
}
}
}
else
{
lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; 
lean_dec(x_1513);
lean_dec(x_3);
lean_inc(x_22);
x_1651 = l_Int_Linear_Poly_denoteExpr(x_11, x_22, x_5, x_6, x_7, x_8, x_19);
x_1652 = lean_ctor_get(x_1651, 0);
lean_inc(x_1652);
x_1653 = lean_ctor_get(x_1651, 1);
lean_inc(x_1653);
if (lean_is_exclusive(x_1651)) {
 lean_ctor_release(x_1651, 0);
 lean_ctor_release(x_1651, 1);
 x_1654 = x_1651;
} else {
 lean_dec_ref(x_1651);
 x_1654 = lean_box(0);
}
x_1655 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_1656 = l_Lean_mkAppB(x_20, x_1652, x_1655);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1657 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_1653);
if (lean_obj_tag(x_1657) == 0)
{
lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; 
x_1658 = lean_ctor_get(x_1657, 0);
lean_inc(x_1658);
x_1659 = lean_ctor_get(x_1657, 1);
lean_inc(x_1659);
lean_dec(x_1657);
x_1660 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1661 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1662 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_22);
x_1663 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_1664 = l_Lean_reflBoolTrue;
x_1665 = l_Lean_mkApp5(x_1663, x_1658, x_1660, x_1661, x_1662, x_1664);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1656);
x_1666 = l_Lean_Meta_mkEq(x_21, x_1656, x_5, x_6, x_7, x_8, x_1659);
if (lean_obj_tag(x_1666) == 0)
{
lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; 
x_1667 = lean_ctor_get(x_1666, 0);
lean_inc(x_1667);
x_1668 = lean_ctor_get(x_1666, 1);
lean_inc(x_1668);
lean_dec(x_1666);
x_1669 = l_Lean_Meta_mkExpectedTypeHint(x_1665, x_1667, x_5, x_6, x_7, x_8, x_1668);
if (lean_obj_tag(x_1669) == 0)
{
lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; 
x_1670 = lean_ctor_get(x_1669, 0);
lean_inc(x_1670);
x_1671 = lean_ctor_get(x_1669, 1);
lean_inc(x_1671);
if (lean_is_exclusive(x_1669)) {
 lean_ctor_release(x_1669, 0);
 lean_ctor_release(x_1669, 1);
 x_1672 = x_1669;
} else {
 lean_dec_ref(x_1669);
 x_1672 = lean_box(0);
}
if (lean_is_scalar(x_1654)) {
 x_1673 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1673 = x_1654;
}
lean_ctor_set(x_1673, 0, x_1656);
lean_ctor_set(x_1673, 1, x_1670);
x_1674 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1674, 0, x_1673);
if (lean_is_scalar(x_1672)) {
 x_1675 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1675 = x_1672;
}
lean_ctor_set(x_1675, 0, x_1674);
lean_ctor_set(x_1675, 1, x_1671);
return x_1675;
}
else
{
lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; 
lean_dec(x_1656);
lean_dec(x_1654);
x_1676 = lean_ctor_get(x_1669, 0);
lean_inc(x_1676);
x_1677 = lean_ctor_get(x_1669, 1);
lean_inc(x_1677);
if (lean_is_exclusive(x_1669)) {
 lean_ctor_release(x_1669, 0);
 lean_ctor_release(x_1669, 1);
 x_1678 = x_1669;
} else {
 lean_dec_ref(x_1669);
 x_1678 = lean_box(0);
}
if (lean_is_scalar(x_1678)) {
 x_1679 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1679 = x_1678;
}
lean_ctor_set(x_1679, 0, x_1676);
lean_ctor_set(x_1679, 1, x_1677);
return x_1679;
}
}
else
{
lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; 
lean_dec(x_1665);
lean_dec(x_1656);
lean_dec(x_1654);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1680 = lean_ctor_get(x_1666, 0);
lean_inc(x_1680);
x_1681 = lean_ctor_get(x_1666, 1);
lean_inc(x_1681);
if (lean_is_exclusive(x_1666)) {
 lean_ctor_release(x_1666, 0);
 lean_ctor_release(x_1666, 1);
 x_1682 = x_1666;
} else {
 lean_dec_ref(x_1666);
 x_1682 = lean_box(0);
}
if (lean_is_scalar(x_1682)) {
 x_1683 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1683 = x_1682;
}
lean_ctor_set(x_1683, 0, x_1680);
lean_ctor_set(x_1683, 1, x_1681);
return x_1683;
}
}
else
{
lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; 
lean_dec(x_1656);
lean_dec(x_1654);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1684 = lean_ctor_get(x_1657, 0);
lean_inc(x_1684);
x_1685 = lean_ctor_get(x_1657, 1);
lean_inc(x_1685);
if (lean_is_exclusive(x_1657)) {
 lean_ctor_release(x_1657, 0);
 lean_ctor_release(x_1657, 1);
 x_1686 = x_1657;
} else {
 lean_dec_ref(x_1657);
 x_1686 = lean_box(0);
}
if (lean_is_scalar(x_1686)) {
 x_1687 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1687 = x_1686;
}
lean_ctor_set(x_1687, 0, x_1684);
lean_ctor_set(x_1687, 1, x_1685);
return x_1687;
}
}
}
else
{
lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_3);
x_1688 = lean_array_get(x_10, x_4, x_456);
x_1689 = lean_array_get(x_10, x_4, x_908);
x_1690 = l_Lean_mkAppB(x_20, x_1688, x_1689);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1691 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_1691) == 0)
{
lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; 
x_1692 = lean_ctor_get(x_1691, 0);
lean_inc(x_1692);
x_1693 = lean_ctor_get(x_1691, 1);
lean_inc(x_1693);
lean_dec(x_1691);
x_1694 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1695 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1696 = l_Lean_mkNatLit(x_456);
x_1697 = l_Lean_mkNatLit(x_908);
x_1698 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__36;
x_1699 = l_Lean_reflBoolTrue;
x_1700 = l_Lean_mkApp6(x_1698, x_1692, x_1694, x_1695, x_1696, x_1697, x_1699);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1690);
x_1701 = l_Lean_Meta_mkEq(x_21, x_1690, x_5, x_6, x_7, x_8, x_1693);
if (lean_obj_tag(x_1701) == 0)
{
lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; 
x_1702 = lean_ctor_get(x_1701, 0);
lean_inc(x_1702);
x_1703 = lean_ctor_get(x_1701, 1);
lean_inc(x_1703);
lean_dec(x_1701);
x_1704 = l_Lean_Meta_mkExpectedTypeHint(x_1700, x_1702, x_5, x_6, x_7, x_8, x_1703);
if (lean_obj_tag(x_1704) == 0)
{
lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; 
x_1705 = lean_ctor_get(x_1704, 0);
lean_inc(x_1705);
x_1706 = lean_ctor_get(x_1704, 1);
lean_inc(x_1706);
if (lean_is_exclusive(x_1704)) {
 lean_ctor_release(x_1704, 0);
 lean_ctor_release(x_1704, 1);
 x_1707 = x_1704;
} else {
 lean_dec_ref(x_1704);
 x_1707 = lean_box(0);
}
x_1708 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1708, 0, x_1690);
lean_ctor_set(x_1708, 1, x_1705);
x_1709 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1709, 0, x_1708);
if (lean_is_scalar(x_1707)) {
 x_1710 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1710 = x_1707;
}
lean_ctor_set(x_1710, 0, x_1709);
lean_ctor_set(x_1710, 1, x_1706);
return x_1710;
}
else
{
lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; 
lean_dec(x_1690);
x_1711 = lean_ctor_get(x_1704, 0);
lean_inc(x_1711);
x_1712 = lean_ctor_get(x_1704, 1);
lean_inc(x_1712);
if (lean_is_exclusive(x_1704)) {
 lean_ctor_release(x_1704, 0);
 lean_ctor_release(x_1704, 1);
 x_1713 = x_1704;
} else {
 lean_dec_ref(x_1704);
 x_1713 = lean_box(0);
}
if (lean_is_scalar(x_1713)) {
 x_1714 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1714 = x_1713;
}
lean_ctor_set(x_1714, 0, x_1711);
lean_ctor_set(x_1714, 1, x_1712);
return x_1714;
}
}
else
{
lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; 
lean_dec(x_1700);
lean_dec(x_1690);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1715 = lean_ctor_get(x_1701, 0);
lean_inc(x_1715);
x_1716 = lean_ctor_get(x_1701, 1);
lean_inc(x_1716);
if (lean_is_exclusive(x_1701)) {
 lean_ctor_release(x_1701, 0);
 lean_ctor_release(x_1701, 1);
 x_1717 = x_1701;
} else {
 lean_dec_ref(x_1701);
 x_1717 = lean_box(0);
}
if (lean_is_scalar(x_1717)) {
 x_1718 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1718 = x_1717;
}
lean_ctor_set(x_1718, 0, x_1715);
lean_ctor_set(x_1718, 1, x_1716);
return x_1718;
}
}
else
{
lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; 
lean_dec(x_1690);
lean_dec(x_908);
lean_dec(x_456);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1719 = lean_ctor_get(x_1691, 0);
lean_inc(x_1719);
x_1720 = lean_ctor_get(x_1691, 1);
lean_inc(x_1720);
if (lean_is_exclusive(x_1691)) {
 lean_ctor_release(x_1691, 0);
 lean_ctor_release(x_1691, 1);
 x_1721 = x_1691;
} else {
 lean_dec_ref(x_1691);
 x_1721 = lean_box(0);
}
if (lean_is_scalar(x_1721)) {
 x_1722 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1722 = x_1721;
}
lean_ctor_set(x_1722, 0, x_1719);
lean_ctor_set(x_1722, 1, x_1720);
return x_1722;
}
}
}
}
else
{
lean_object* x_1723; lean_object* x_1724; uint8_t x_1725; 
lean_dec(x_909);
lean_dec(x_908);
lean_dec(x_456);
x_1723 = l_Int_Linear_Poly_gcdCoeffs_x27(x_22);
x_1724 = lean_unsigned_to_nat(1u);
x_1725 = lean_nat_dec_eq(x_1723, x_1724);
if (x_1725 == 0)
{
lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; uint8_t x_1730; 
x_1726 = l_Int_Linear_Poly_getConst(x_22);
x_1727 = lean_nat_to_int(x_1723);
x_1728 = lean_int_emod(x_1726, x_1727);
lean_dec(x_1726);
x_1729 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_1730 = lean_int_dec_eq(x_1728, x_1729);
lean_dec(x_1728);
if (x_1730 == 0)
{
lean_object* x_1731; lean_object* x_1732; 
lean_dec(x_22);
lean_dec(x_11);
x_1731 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1732 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_1732) == 0)
{
lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; uint8_t x_1737; lean_object* x_1738; lean_object* x_1739; 
x_1733 = lean_ctor_get(x_1732, 0);
lean_inc(x_1733);
x_1734 = lean_ctor_get(x_1732, 1);
lean_inc(x_1734);
lean_dec(x_1732);
x_1735 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1736 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1737 = lean_int_dec_le(x_1729, x_1727);
x_1738 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1739 = l_Lean_Meta_mkEq(x_21, x_1738, x_5, x_6, x_7, x_8, x_1734);
if (x_1737 == 0)
{
if (lean_obj_tag(x_1739) == 0)
{
lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; 
x_1740 = lean_ctor_get(x_1739, 0);
lean_inc(x_1740);
x_1741 = lean_ctor_get(x_1739, 1);
lean_inc(x_1741);
lean_dec(x_1739);
x_1742 = l_Lean_Expr_const___override(x_3, x_1731);
x_1743 = lean_int_neg(x_1727);
lean_dec(x_1727);
x_1744 = l_Int_toNat(x_1743);
lean_dec(x_1743);
x_1745 = l_Lean_instToExprInt_mkNat(x_1744);
x_1746 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_1747 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_1748 = l_Lean_mkApp3(x_1746, x_1742, x_1747, x_1745);
x_1749 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_1750 = l_Lean_reflBoolTrue;
x_1751 = l_Lean_mkApp5(x_1749, x_1733, x_1735, x_1736, x_1748, x_1750);
x_1752 = l_Lean_Meta_mkExpectedTypeHint(x_1751, x_1740, x_5, x_6, x_7, x_8, x_1741);
if (lean_obj_tag(x_1752) == 0)
{
uint8_t x_1753; 
x_1753 = !lean_is_exclusive(x_1752);
if (x_1753 == 0)
{
lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; 
x_1754 = lean_ctor_get(x_1752, 0);
x_1755 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1755, 0, x_1738);
lean_ctor_set(x_1755, 1, x_1754);
x_1756 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1756, 0, x_1755);
lean_ctor_set(x_1752, 0, x_1756);
return x_1752;
}
else
{
lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; 
x_1757 = lean_ctor_get(x_1752, 0);
x_1758 = lean_ctor_get(x_1752, 1);
lean_inc(x_1758);
lean_inc(x_1757);
lean_dec(x_1752);
x_1759 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1759, 0, x_1738);
lean_ctor_set(x_1759, 1, x_1757);
x_1760 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1760, 0, x_1759);
x_1761 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1761, 0, x_1760);
lean_ctor_set(x_1761, 1, x_1758);
return x_1761;
}
}
else
{
uint8_t x_1762; 
x_1762 = !lean_is_exclusive(x_1752);
if (x_1762 == 0)
{
return x_1752;
}
else
{
lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; 
x_1763 = lean_ctor_get(x_1752, 0);
x_1764 = lean_ctor_get(x_1752, 1);
lean_inc(x_1764);
lean_inc(x_1763);
lean_dec(x_1752);
x_1765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1765, 0, x_1763);
lean_ctor_set(x_1765, 1, x_1764);
return x_1765;
}
}
}
else
{
uint8_t x_1766; 
lean_dec(x_1736);
lean_dec(x_1735);
lean_dec(x_1733);
lean_dec(x_1727);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1766 = !lean_is_exclusive(x_1739);
if (x_1766 == 0)
{
return x_1739;
}
else
{
lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; 
x_1767 = lean_ctor_get(x_1739, 0);
x_1768 = lean_ctor_get(x_1739, 1);
lean_inc(x_1768);
lean_inc(x_1767);
lean_dec(x_1739);
x_1769 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1769, 0, x_1767);
lean_ctor_set(x_1769, 1, x_1768);
return x_1769;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1739) == 0)
{
lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; 
x_1770 = lean_ctor_get(x_1739, 0);
lean_inc(x_1770);
x_1771 = lean_ctor_get(x_1739, 1);
lean_inc(x_1771);
lean_dec(x_1739);
x_1772 = l_Int_toNat(x_1727);
lean_dec(x_1727);
x_1773 = l_Lean_instToExprInt_mkNat(x_1772);
x_1774 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_1775 = l_Lean_reflBoolTrue;
x_1776 = l_Lean_mkApp5(x_1774, x_1733, x_1735, x_1736, x_1773, x_1775);
x_1777 = l_Lean_Meta_mkExpectedTypeHint(x_1776, x_1770, x_5, x_6, x_7, x_8, x_1771);
if (lean_obj_tag(x_1777) == 0)
{
uint8_t x_1778; 
x_1778 = !lean_is_exclusive(x_1777);
if (x_1778 == 0)
{
lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; 
x_1779 = lean_ctor_get(x_1777, 0);
x_1780 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1780, 0, x_1738);
lean_ctor_set(x_1780, 1, x_1779);
x_1781 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1781, 0, x_1780);
lean_ctor_set(x_1777, 0, x_1781);
return x_1777;
}
else
{
lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; 
x_1782 = lean_ctor_get(x_1777, 0);
x_1783 = lean_ctor_get(x_1777, 1);
lean_inc(x_1783);
lean_inc(x_1782);
lean_dec(x_1777);
x_1784 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1784, 0, x_1738);
lean_ctor_set(x_1784, 1, x_1782);
x_1785 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1785, 0, x_1784);
x_1786 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1786, 0, x_1785);
lean_ctor_set(x_1786, 1, x_1783);
return x_1786;
}
}
else
{
uint8_t x_1787; 
x_1787 = !lean_is_exclusive(x_1777);
if (x_1787 == 0)
{
return x_1777;
}
else
{
lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; 
x_1788 = lean_ctor_get(x_1777, 0);
x_1789 = lean_ctor_get(x_1777, 1);
lean_inc(x_1789);
lean_inc(x_1788);
lean_dec(x_1777);
x_1790 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1790, 0, x_1788);
lean_ctor_set(x_1790, 1, x_1789);
return x_1790;
}
}
}
else
{
uint8_t x_1791; 
lean_dec(x_1736);
lean_dec(x_1735);
lean_dec(x_1733);
lean_dec(x_1727);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1791 = !lean_is_exclusive(x_1739);
if (x_1791 == 0)
{
return x_1739;
}
else
{
lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; 
x_1792 = lean_ctor_get(x_1739, 0);
x_1793 = lean_ctor_get(x_1739, 1);
lean_inc(x_1793);
lean_inc(x_1792);
lean_dec(x_1739);
x_1794 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1794, 0, x_1792);
lean_ctor_set(x_1794, 1, x_1793);
return x_1794;
}
}
}
}
else
{
uint8_t x_1795; 
lean_dec(x_1727);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1795 = !lean_is_exclusive(x_1732);
if (x_1795 == 0)
{
return x_1732;
}
else
{
lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; 
x_1796 = lean_ctor_get(x_1732, 0);
x_1797 = lean_ctor_get(x_1732, 1);
lean_inc(x_1797);
lean_inc(x_1796);
lean_dec(x_1732);
x_1798 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1798, 0, x_1796);
lean_ctor_set(x_1798, 1, x_1797);
return x_1798;
}
}
}
else
{
lean_object* x_1799; lean_object* x_1800; uint8_t x_1801; 
x_1799 = l_Int_Linear_Poly_div(x_1727, x_22);
lean_inc(x_1799);
x_1800 = l_Int_Linear_Poly_denoteExpr(x_11, x_1799, x_5, x_6, x_7, x_8, x_19);
x_1801 = !lean_is_exclusive(x_1800);
if (x_1801 == 0)
{
lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; 
x_1802 = lean_ctor_get(x_1800, 0);
x_1803 = lean_ctor_get(x_1800, 1);
x_1804 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_1805 = l_Lean_mkAppB(x_20, x_1802, x_1804);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1806 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_1803);
if (lean_obj_tag(x_1806) == 0)
{
lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; uint8_t x_1813; lean_object* x_1814; 
x_1807 = lean_ctor_get(x_1806, 0);
lean_inc(x_1807);
x_1808 = lean_ctor_get(x_1806, 1);
lean_inc(x_1808);
lean_dec(x_1806);
x_1809 = lean_box(0);
x_1810 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1811 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1812 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_1799);
x_1813 = lean_int_dec_le(x_1729, x_1727);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1805);
x_1814 = l_Lean_Meta_mkEq(x_21, x_1805, x_5, x_6, x_7, x_8, x_1808);
if (x_1813 == 0)
{
if (lean_obj_tag(x_1814) == 0)
{
lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; 
x_1815 = lean_ctor_get(x_1814, 0);
lean_inc(x_1815);
x_1816 = lean_ctor_get(x_1814, 1);
lean_inc(x_1816);
lean_dec(x_1814);
x_1817 = l_Lean_Expr_const___override(x_3, x_1809);
x_1818 = lean_int_neg(x_1727);
lean_dec(x_1727);
x_1819 = l_Int_toNat(x_1818);
lean_dec(x_1818);
x_1820 = l_Lean_instToExprInt_mkNat(x_1819);
x_1821 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_1822 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_1823 = l_Lean_mkApp3(x_1821, x_1817, x_1822, x_1820);
x_1824 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1825 = l_Lean_reflBoolTrue;
x_1826 = l_Lean_mkApp6(x_1824, x_1807, x_1810, x_1811, x_1812, x_1823, x_1825);
x_1827 = l_Lean_Meta_mkExpectedTypeHint(x_1826, x_1815, x_5, x_6, x_7, x_8, x_1816);
if (lean_obj_tag(x_1827) == 0)
{
uint8_t x_1828; 
x_1828 = !lean_is_exclusive(x_1827);
if (x_1828 == 0)
{
lean_object* x_1829; lean_object* x_1830; 
x_1829 = lean_ctor_get(x_1827, 0);
lean_ctor_set(x_1800, 1, x_1829);
lean_ctor_set(x_1800, 0, x_1805);
x_1830 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1830, 0, x_1800);
lean_ctor_set(x_1827, 0, x_1830);
return x_1827;
}
else
{
lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; 
x_1831 = lean_ctor_get(x_1827, 0);
x_1832 = lean_ctor_get(x_1827, 1);
lean_inc(x_1832);
lean_inc(x_1831);
lean_dec(x_1827);
lean_ctor_set(x_1800, 1, x_1831);
lean_ctor_set(x_1800, 0, x_1805);
x_1833 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1833, 0, x_1800);
x_1834 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1834, 0, x_1833);
lean_ctor_set(x_1834, 1, x_1832);
return x_1834;
}
}
else
{
uint8_t x_1835; 
lean_dec(x_1805);
lean_free_object(x_1800);
x_1835 = !lean_is_exclusive(x_1827);
if (x_1835 == 0)
{
return x_1827;
}
else
{
lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; 
x_1836 = lean_ctor_get(x_1827, 0);
x_1837 = lean_ctor_get(x_1827, 1);
lean_inc(x_1837);
lean_inc(x_1836);
lean_dec(x_1827);
x_1838 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1838, 0, x_1836);
lean_ctor_set(x_1838, 1, x_1837);
return x_1838;
}
}
}
else
{
uint8_t x_1839; 
lean_dec(x_1812);
lean_dec(x_1811);
lean_dec(x_1810);
lean_dec(x_1807);
lean_dec(x_1805);
lean_free_object(x_1800);
lean_dec(x_1727);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1839 = !lean_is_exclusive(x_1814);
if (x_1839 == 0)
{
return x_1814;
}
else
{
lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; 
x_1840 = lean_ctor_get(x_1814, 0);
x_1841 = lean_ctor_get(x_1814, 1);
lean_inc(x_1841);
lean_inc(x_1840);
lean_dec(x_1814);
x_1842 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1842, 0, x_1840);
lean_ctor_set(x_1842, 1, x_1841);
return x_1842;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1814) == 0)
{
lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; 
x_1843 = lean_ctor_get(x_1814, 0);
lean_inc(x_1843);
x_1844 = lean_ctor_get(x_1814, 1);
lean_inc(x_1844);
lean_dec(x_1814);
x_1845 = l_Int_toNat(x_1727);
lean_dec(x_1727);
x_1846 = l_Lean_instToExprInt_mkNat(x_1845);
x_1847 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1848 = l_Lean_reflBoolTrue;
x_1849 = l_Lean_mkApp6(x_1847, x_1807, x_1810, x_1811, x_1812, x_1846, x_1848);
x_1850 = l_Lean_Meta_mkExpectedTypeHint(x_1849, x_1843, x_5, x_6, x_7, x_8, x_1844);
if (lean_obj_tag(x_1850) == 0)
{
uint8_t x_1851; 
x_1851 = !lean_is_exclusive(x_1850);
if (x_1851 == 0)
{
lean_object* x_1852; lean_object* x_1853; 
x_1852 = lean_ctor_get(x_1850, 0);
lean_ctor_set(x_1800, 1, x_1852);
lean_ctor_set(x_1800, 0, x_1805);
x_1853 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1853, 0, x_1800);
lean_ctor_set(x_1850, 0, x_1853);
return x_1850;
}
else
{
lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; 
x_1854 = lean_ctor_get(x_1850, 0);
x_1855 = lean_ctor_get(x_1850, 1);
lean_inc(x_1855);
lean_inc(x_1854);
lean_dec(x_1850);
lean_ctor_set(x_1800, 1, x_1854);
lean_ctor_set(x_1800, 0, x_1805);
x_1856 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1856, 0, x_1800);
x_1857 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1857, 0, x_1856);
lean_ctor_set(x_1857, 1, x_1855);
return x_1857;
}
}
else
{
uint8_t x_1858; 
lean_dec(x_1805);
lean_free_object(x_1800);
x_1858 = !lean_is_exclusive(x_1850);
if (x_1858 == 0)
{
return x_1850;
}
else
{
lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; 
x_1859 = lean_ctor_get(x_1850, 0);
x_1860 = lean_ctor_get(x_1850, 1);
lean_inc(x_1860);
lean_inc(x_1859);
lean_dec(x_1850);
x_1861 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1861, 0, x_1859);
lean_ctor_set(x_1861, 1, x_1860);
return x_1861;
}
}
}
else
{
uint8_t x_1862; 
lean_dec(x_1812);
lean_dec(x_1811);
lean_dec(x_1810);
lean_dec(x_1807);
lean_dec(x_1805);
lean_free_object(x_1800);
lean_dec(x_1727);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1862 = !lean_is_exclusive(x_1814);
if (x_1862 == 0)
{
return x_1814;
}
else
{
lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; 
x_1863 = lean_ctor_get(x_1814, 0);
x_1864 = lean_ctor_get(x_1814, 1);
lean_inc(x_1864);
lean_inc(x_1863);
lean_dec(x_1814);
x_1865 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1865, 0, x_1863);
lean_ctor_set(x_1865, 1, x_1864);
return x_1865;
}
}
}
}
else
{
uint8_t x_1866; 
lean_dec(x_1805);
lean_free_object(x_1800);
lean_dec(x_1799);
lean_dec(x_1727);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1866 = !lean_is_exclusive(x_1806);
if (x_1866 == 0)
{
return x_1806;
}
else
{
lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; 
x_1867 = lean_ctor_get(x_1806, 0);
x_1868 = lean_ctor_get(x_1806, 1);
lean_inc(x_1868);
lean_inc(x_1867);
lean_dec(x_1806);
x_1869 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1869, 0, x_1867);
lean_ctor_set(x_1869, 1, x_1868);
return x_1869;
}
}
}
else
{
lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; 
x_1870 = lean_ctor_get(x_1800, 0);
x_1871 = lean_ctor_get(x_1800, 1);
lean_inc(x_1871);
lean_inc(x_1870);
lean_dec(x_1800);
x_1872 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_1873 = l_Lean_mkAppB(x_20, x_1870, x_1872);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1874 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_1871);
if (lean_obj_tag(x_1874) == 0)
{
lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; uint8_t x_1881; lean_object* x_1882; 
x_1875 = lean_ctor_get(x_1874, 0);
lean_inc(x_1875);
x_1876 = lean_ctor_get(x_1874, 1);
lean_inc(x_1876);
lean_dec(x_1874);
x_1877 = lean_box(0);
x_1878 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1879 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1880 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_1799);
x_1881 = lean_int_dec_le(x_1729, x_1727);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1873);
x_1882 = l_Lean_Meta_mkEq(x_21, x_1873, x_5, x_6, x_7, x_8, x_1876);
if (x_1881 == 0)
{
if (lean_obj_tag(x_1882) == 0)
{
lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; 
x_1883 = lean_ctor_get(x_1882, 0);
lean_inc(x_1883);
x_1884 = lean_ctor_get(x_1882, 1);
lean_inc(x_1884);
lean_dec(x_1882);
x_1885 = l_Lean_Expr_const___override(x_3, x_1877);
x_1886 = lean_int_neg(x_1727);
lean_dec(x_1727);
x_1887 = l_Int_toNat(x_1886);
lean_dec(x_1886);
x_1888 = l_Lean_instToExprInt_mkNat(x_1887);
x_1889 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_1890 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_1891 = l_Lean_mkApp3(x_1889, x_1885, x_1890, x_1888);
x_1892 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1893 = l_Lean_reflBoolTrue;
x_1894 = l_Lean_mkApp6(x_1892, x_1875, x_1878, x_1879, x_1880, x_1891, x_1893);
x_1895 = l_Lean_Meta_mkExpectedTypeHint(x_1894, x_1883, x_5, x_6, x_7, x_8, x_1884);
if (lean_obj_tag(x_1895) == 0)
{
lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; 
x_1896 = lean_ctor_get(x_1895, 0);
lean_inc(x_1896);
x_1897 = lean_ctor_get(x_1895, 1);
lean_inc(x_1897);
if (lean_is_exclusive(x_1895)) {
 lean_ctor_release(x_1895, 0);
 lean_ctor_release(x_1895, 1);
 x_1898 = x_1895;
} else {
 lean_dec_ref(x_1895);
 x_1898 = lean_box(0);
}
x_1899 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1899, 0, x_1873);
lean_ctor_set(x_1899, 1, x_1896);
x_1900 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1900, 0, x_1899);
if (lean_is_scalar(x_1898)) {
 x_1901 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1901 = x_1898;
}
lean_ctor_set(x_1901, 0, x_1900);
lean_ctor_set(x_1901, 1, x_1897);
return x_1901;
}
else
{
lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; 
lean_dec(x_1873);
x_1902 = lean_ctor_get(x_1895, 0);
lean_inc(x_1902);
x_1903 = lean_ctor_get(x_1895, 1);
lean_inc(x_1903);
if (lean_is_exclusive(x_1895)) {
 lean_ctor_release(x_1895, 0);
 lean_ctor_release(x_1895, 1);
 x_1904 = x_1895;
} else {
 lean_dec_ref(x_1895);
 x_1904 = lean_box(0);
}
if (lean_is_scalar(x_1904)) {
 x_1905 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1905 = x_1904;
}
lean_ctor_set(x_1905, 0, x_1902);
lean_ctor_set(x_1905, 1, x_1903);
return x_1905;
}
}
else
{
lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; 
lean_dec(x_1880);
lean_dec(x_1879);
lean_dec(x_1878);
lean_dec(x_1875);
lean_dec(x_1873);
lean_dec(x_1727);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1906 = lean_ctor_get(x_1882, 0);
lean_inc(x_1906);
x_1907 = lean_ctor_get(x_1882, 1);
lean_inc(x_1907);
if (lean_is_exclusive(x_1882)) {
 lean_ctor_release(x_1882, 0);
 lean_ctor_release(x_1882, 1);
 x_1908 = x_1882;
} else {
 lean_dec_ref(x_1882);
 x_1908 = lean_box(0);
}
if (lean_is_scalar(x_1908)) {
 x_1909 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1909 = x_1908;
}
lean_ctor_set(x_1909, 0, x_1906);
lean_ctor_set(x_1909, 1, x_1907);
return x_1909;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1882) == 0)
{
lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; 
x_1910 = lean_ctor_get(x_1882, 0);
lean_inc(x_1910);
x_1911 = lean_ctor_get(x_1882, 1);
lean_inc(x_1911);
lean_dec(x_1882);
x_1912 = l_Int_toNat(x_1727);
lean_dec(x_1727);
x_1913 = l_Lean_instToExprInt_mkNat(x_1912);
x_1914 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_1915 = l_Lean_reflBoolTrue;
x_1916 = l_Lean_mkApp6(x_1914, x_1875, x_1878, x_1879, x_1880, x_1913, x_1915);
x_1917 = l_Lean_Meta_mkExpectedTypeHint(x_1916, x_1910, x_5, x_6, x_7, x_8, x_1911);
if (lean_obj_tag(x_1917) == 0)
{
lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; 
x_1918 = lean_ctor_get(x_1917, 0);
lean_inc(x_1918);
x_1919 = lean_ctor_get(x_1917, 1);
lean_inc(x_1919);
if (lean_is_exclusive(x_1917)) {
 lean_ctor_release(x_1917, 0);
 lean_ctor_release(x_1917, 1);
 x_1920 = x_1917;
} else {
 lean_dec_ref(x_1917);
 x_1920 = lean_box(0);
}
x_1921 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1921, 0, x_1873);
lean_ctor_set(x_1921, 1, x_1918);
x_1922 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1922, 0, x_1921);
if (lean_is_scalar(x_1920)) {
 x_1923 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1923 = x_1920;
}
lean_ctor_set(x_1923, 0, x_1922);
lean_ctor_set(x_1923, 1, x_1919);
return x_1923;
}
else
{
lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; 
lean_dec(x_1873);
x_1924 = lean_ctor_get(x_1917, 0);
lean_inc(x_1924);
x_1925 = lean_ctor_get(x_1917, 1);
lean_inc(x_1925);
if (lean_is_exclusive(x_1917)) {
 lean_ctor_release(x_1917, 0);
 lean_ctor_release(x_1917, 1);
 x_1926 = x_1917;
} else {
 lean_dec_ref(x_1917);
 x_1926 = lean_box(0);
}
if (lean_is_scalar(x_1926)) {
 x_1927 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1927 = x_1926;
}
lean_ctor_set(x_1927, 0, x_1924);
lean_ctor_set(x_1927, 1, x_1925);
return x_1927;
}
}
else
{
lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; 
lean_dec(x_1880);
lean_dec(x_1879);
lean_dec(x_1878);
lean_dec(x_1875);
lean_dec(x_1873);
lean_dec(x_1727);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1928 = lean_ctor_get(x_1882, 0);
lean_inc(x_1928);
x_1929 = lean_ctor_get(x_1882, 1);
lean_inc(x_1929);
if (lean_is_exclusive(x_1882)) {
 lean_ctor_release(x_1882, 0);
 lean_ctor_release(x_1882, 1);
 x_1930 = x_1882;
} else {
 lean_dec_ref(x_1882);
 x_1930 = lean_box(0);
}
if (lean_is_scalar(x_1930)) {
 x_1931 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1931 = x_1930;
}
lean_ctor_set(x_1931, 0, x_1928);
lean_ctor_set(x_1931, 1, x_1929);
return x_1931;
}
}
}
else
{
lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; 
lean_dec(x_1873);
lean_dec(x_1799);
lean_dec(x_1727);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1932 = lean_ctor_get(x_1874, 0);
lean_inc(x_1932);
x_1933 = lean_ctor_get(x_1874, 1);
lean_inc(x_1933);
if (lean_is_exclusive(x_1874)) {
 lean_ctor_release(x_1874, 0);
 lean_ctor_release(x_1874, 1);
 x_1934 = x_1874;
} else {
 lean_dec_ref(x_1874);
 x_1934 = lean_box(0);
}
if (lean_is_scalar(x_1934)) {
 x_1935 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1935 = x_1934;
}
lean_ctor_set(x_1935, 0, x_1932);
lean_ctor_set(x_1935, 1, x_1933);
return x_1935;
}
}
}
}
else
{
lean_object* x_1936; uint8_t x_1937; 
lean_dec(x_1723);
lean_dec(x_3);
lean_inc(x_22);
x_1936 = l_Int_Linear_Poly_denoteExpr(x_11, x_22, x_5, x_6, x_7, x_8, x_19);
x_1937 = !lean_is_exclusive(x_1936);
if (x_1937 == 0)
{
lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; 
x_1938 = lean_ctor_get(x_1936, 0);
x_1939 = lean_ctor_get(x_1936, 1);
x_1940 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_1941 = l_Lean_mkAppB(x_20, x_1938, x_1940);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1942 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_1939);
if (lean_obj_tag(x_1942) == 0)
{
lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; 
x_1943 = lean_ctor_get(x_1942, 0);
lean_inc(x_1943);
x_1944 = lean_ctor_get(x_1942, 1);
lean_inc(x_1944);
lean_dec(x_1942);
x_1945 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1946 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1947 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_22);
x_1948 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_1949 = l_Lean_reflBoolTrue;
x_1950 = l_Lean_mkApp5(x_1948, x_1943, x_1945, x_1946, x_1947, x_1949);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1941);
x_1951 = l_Lean_Meta_mkEq(x_21, x_1941, x_5, x_6, x_7, x_8, x_1944);
if (lean_obj_tag(x_1951) == 0)
{
lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; 
x_1952 = lean_ctor_get(x_1951, 0);
lean_inc(x_1952);
x_1953 = lean_ctor_get(x_1951, 1);
lean_inc(x_1953);
lean_dec(x_1951);
x_1954 = l_Lean_Meta_mkExpectedTypeHint(x_1950, x_1952, x_5, x_6, x_7, x_8, x_1953);
if (lean_obj_tag(x_1954) == 0)
{
uint8_t x_1955; 
x_1955 = !lean_is_exclusive(x_1954);
if (x_1955 == 0)
{
lean_object* x_1956; lean_object* x_1957; 
x_1956 = lean_ctor_get(x_1954, 0);
lean_ctor_set(x_1936, 1, x_1956);
lean_ctor_set(x_1936, 0, x_1941);
x_1957 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1957, 0, x_1936);
lean_ctor_set(x_1954, 0, x_1957);
return x_1954;
}
else
{
lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; 
x_1958 = lean_ctor_get(x_1954, 0);
x_1959 = lean_ctor_get(x_1954, 1);
lean_inc(x_1959);
lean_inc(x_1958);
lean_dec(x_1954);
lean_ctor_set(x_1936, 1, x_1958);
lean_ctor_set(x_1936, 0, x_1941);
x_1960 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1960, 0, x_1936);
x_1961 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1961, 0, x_1960);
lean_ctor_set(x_1961, 1, x_1959);
return x_1961;
}
}
else
{
uint8_t x_1962; 
lean_dec(x_1941);
lean_free_object(x_1936);
x_1962 = !lean_is_exclusive(x_1954);
if (x_1962 == 0)
{
return x_1954;
}
else
{
lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; 
x_1963 = lean_ctor_get(x_1954, 0);
x_1964 = lean_ctor_get(x_1954, 1);
lean_inc(x_1964);
lean_inc(x_1963);
lean_dec(x_1954);
x_1965 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1965, 0, x_1963);
lean_ctor_set(x_1965, 1, x_1964);
return x_1965;
}
}
}
else
{
uint8_t x_1966; 
lean_dec(x_1950);
lean_dec(x_1941);
lean_free_object(x_1936);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1966 = !lean_is_exclusive(x_1951);
if (x_1966 == 0)
{
return x_1951;
}
else
{
lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; 
x_1967 = lean_ctor_get(x_1951, 0);
x_1968 = lean_ctor_get(x_1951, 1);
lean_inc(x_1968);
lean_inc(x_1967);
lean_dec(x_1951);
x_1969 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1969, 0, x_1967);
lean_ctor_set(x_1969, 1, x_1968);
return x_1969;
}
}
}
else
{
uint8_t x_1970; 
lean_dec(x_1941);
lean_free_object(x_1936);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1970 = !lean_is_exclusive(x_1942);
if (x_1970 == 0)
{
return x_1942;
}
else
{
lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; 
x_1971 = lean_ctor_get(x_1942, 0);
x_1972 = lean_ctor_get(x_1942, 1);
lean_inc(x_1972);
lean_inc(x_1971);
lean_dec(x_1942);
x_1973 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1973, 0, x_1971);
lean_ctor_set(x_1973, 1, x_1972);
return x_1973;
}
}
}
else
{
lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; lean_object* x_1978; 
x_1974 = lean_ctor_get(x_1936, 0);
x_1975 = lean_ctor_get(x_1936, 1);
lean_inc(x_1975);
lean_inc(x_1974);
lean_dec(x_1936);
x_1976 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_1977 = l_Lean_mkAppB(x_20, x_1974, x_1976);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_1978 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_1975);
if (lean_obj_tag(x_1978) == 0)
{
lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; 
x_1979 = lean_ctor_get(x_1978, 0);
lean_inc(x_1979);
x_1980 = lean_ctor_get(x_1978, 1);
lean_inc(x_1980);
lean_dec(x_1978);
x_1981 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_1982 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_1983 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_22);
x_1984 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_1985 = l_Lean_reflBoolTrue;
x_1986 = l_Lean_mkApp5(x_1984, x_1979, x_1981, x_1982, x_1983, x_1985);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1977);
x_1987 = l_Lean_Meta_mkEq(x_21, x_1977, x_5, x_6, x_7, x_8, x_1980);
if (lean_obj_tag(x_1987) == 0)
{
lean_object* x_1988; lean_object* x_1989; lean_object* x_1990; 
x_1988 = lean_ctor_get(x_1987, 0);
lean_inc(x_1988);
x_1989 = lean_ctor_get(x_1987, 1);
lean_inc(x_1989);
lean_dec(x_1987);
x_1990 = l_Lean_Meta_mkExpectedTypeHint(x_1986, x_1988, x_5, x_6, x_7, x_8, x_1989);
if (lean_obj_tag(x_1990) == 0)
{
lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; 
x_1991 = lean_ctor_get(x_1990, 0);
lean_inc(x_1991);
x_1992 = lean_ctor_get(x_1990, 1);
lean_inc(x_1992);
if (lean_is_exclusive(x_1990)) {
 lean_ctor_release(x_1990, 0);
 lean_ctor_release(x_1990, 1);
 x_1993 = x_1990;
} else {
 lean_dec_ref(x_1990);
 x_1993 = lean_box(0);
}
x_1994 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1994, 0, x_1977);
lean_ctor_set(x_1994, 1, x_1991);
x_1995 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1995, 0, x_1994);
if (lean_is_scalar(x_1993)) {
 x_1996 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1996 = x_1993;
}
lean_ctor_set(x_1996, 0, x_1995);
lean_ctor_set(x_1996, 1, x_1992);
return x_1996;
}
else
{
lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; 
lean_dec(x_1977);
x_1997 = lean_ctor_get(x_1990, 0);
lean_inc(x_1997);
x_1998 = lean_ctor_get(x_1990, 1);
lean_inc(x_1998);
if (lean_is_exclusive(x_1990)) {
 lean_ctor_release(x_1990, 0);
 lean_ctor_release(x_1990, 1);
 x_1999 = x_1990;
} else {
 lean_dec_ref(x_1990);
 x_1999 = lean_box(0);
}
if (lean_is_scalar(x_1999)) {
 x_2000 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2000 = x_1999;
}
lean_ctor_set(x_2000, 0, x_1997);
lean_ctor_set(x_2000, 1, x_1998);
return x_2000;
}
}
else
{
lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; 
lean_dec(x_1986);
lean_dec(x_1977);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2001 = lean_ctor_get(x_1987, 0);
lean_inc(x_2001);
x_2002 = lean_ctor_get(x_1987, 1);
lean_inc(x_2002);
if (lean_is_exclusive(x_1987)) {
 lean_ctor_release(x_1987, 0);
 lean_ctor_release(x_1987, 1);
 x_2003 = x_1987;
} else {
 lean_dec_ref(x_1987);
 x_2003 = lean_box(0);
}
if (lean_is_scalar(x_2003)) {
 x_2004 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2004 = x_2003;
}
lean_ctor_set(x_2004, 0, x_2001);
lean_ctor_set(x_2004, 1, x_2002);
return x_2004;
}
}
else
{
lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; 
lean_dec(x_1977);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_2005 = lean_ctor_get(x_1978, 0);
lean_inc(x_2005);
x_2006 = lean_ctor_get(x_1978, 1);
lean_inc(x_2006);
if (lean_is_exclusive(x_1978)) {
 lean_ctor_release(x_1978, 0);
 lean_ctor_release(x_1978, 1);
 x_2007 = x_1978;
} else {
 lean_dec_ref(x_1978);
 x_2007 = lean_box(0);
}
if (lean_is_scalar(x_2007)) {
 x_2008 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2008 = x_2007;
}
lean_ctor_set(x_2008, 0, x_2005);
lean_ctor_set(x_2008, 1, x_2006);
return x_2008;
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
else
{
lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; uint8_t x_3105; 
x_2087 = lean_ctor_get(x_16, 0);
x_2088 = lean_ctor_get(x_16, 1);
lean_inc(x_2088);
lean_inc(x_2087);
lean_dec(x_16);
x_2089 = l___private_Lean_Expr_0__Lean_intEqPred;
x_2090 = l_Lean_mkAppB(x_2089, x_14, x_2087);
lean_inc(x_2);
lean_inc(x_1);
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 0, x_1);
x_2091 = l_Int_Linear_Expr_norm(x_12);
lean_dec(x_12);
x_3105 = l_Int_Linear_Poly_isUnsatEq(x_2091);
if (x_3105 == 0)
{
uint8_t x_3106; 
x_3106 = l_Int_Linear_Poly_isValidEq(x_2091);
if (x_3106 == 0)
{
lean_object* x_3107; uint8_t x_3108; 
lean_inc(x_2091);
x_3107 = l_Int_Linear_Poly_toExpr(x_2091);
x_3108 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_3107, x_1);
lean_dec(x_3107);
if (x_3108 == 0)
{
lean_object* x_3109; 
x_3109 = lean_box(0);
x_2092 = x_3109;
goto block_3104;
}
else
{
lean_object* x_3110; uint8_t x_3111; 
x_3110 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__37;
x_3111 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_2, x_3110);
if (x_3111 == 0)
{
lean_object* x_3112; 
x_3112 = lean_box(0);
x_2092 = x_3112;
goto block_3104;
}
else
{
lean_object* x_3113; lean_object* x_3114; 
lean_dec(x_2091);
lean_dec(x_2090);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3113 = lean_box(0);
x_3114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3114, 0, x_3113);
lean_ctor_set(x_3114, 1, x_2088);
return x_3114;
}
}
}
else
{
lean_object* x_3115; 
lean_dec(x_2091);
lean_dec(x_11);
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3115 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2088);
if (lean_obj_tag(x_3115) == 0)
{
lean_object* x_3116; lean_object* x_3117; lean_object* x_3118; lean_object* x_3119; lean_object* x_3120; lean_object* x_3121; lean_object* x_3122; lean_object* x_3123; lean_object* x_3124; 
x_3116 = lean_ctor_get(x_3115, 0);
lean_inc(x_3116);
x_3117 = lean_ctor_get(x_3115, 1);
lean_inc(x_3117);
lean_dec(x_3115);
x_3118 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3119 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3120 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__43;
x_3121 = l_Lean_reflBoolTrue;
x_3122 = l_Lean_mkApp4(x_3120, x_3116, x_3118, x_3119, x_3121);
x_3123 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__40;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3124 = l_Lean_Meta_mkEq(x_2090, x_3123, x_5, x_6, x_7, x_8, x_3117);
if (lean_obj_tag(x_3124) == 0)
{
lean_object* x_3125; lean_object* x_3126; lean_object* x_3127; 
x_3125 = lean_ctor_get(x_3124, 0);
lean_inc(x_3125);
x_3126 = lean_ctor_get(x_3124, 1);
lean_inc(x_3126);
lean_dec(x_3124);
x_3127 = l_Lean_Meta_mkExpectedTypeHint(x_3122, x_3125, x_5, x_6, x_7, x_8, x_3126);
if (lean_obj_tag(x_3127) == 0)
{
lean_object* x_3128; lean_object* x_3129; lean_object* x_3130; lean_object* x_3131; lean_object* x_3132; lean_object* x_3133; 
x_3128 = lean_ctor_get(x_3127, 0);
lean_inc(x_3128);
x_3129 = lean_ctor_get(x_3127, 1);
lean_inc(x_3129);
if (lean_is_exclusive(x_3127)) {
 lean_ctor_release(x_3127, 0);
 lean_ctor_release(x_3127, 1);
 x_3130 = x_3127;
} else {
 lean_dec_ref(x_3127);
 x_3130 = lean_box(0);
}
x_3131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3131, 0, x_3123);
lean_ctor_set(x_3131, 1, x_3128);
x_3132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3132, 0, x_3131);
if (lean_is_scalar(x_3130)) {
 x_3133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3133 = x_3130;
}
lean_ctor_set(x_3133, 0, x_3132);
lean_ctor_set(x_3133, 1, x_3129);
return x_3133;
}
else
{
lean_object* x_3134; lean_object* x_3135; lean_object* x_3136; lean_object* x_3137; 
x_3134 = lean_ctor_get(x_3127, 0);
lean_inc(x_3134);
x_3135 = lean_ctor_get(x_3127, 1);
lean_inc(x_3135);
if (lean_is_exclusive(x_3127)) {
 lean_ctor_release(x_3127, 0);
 lean_ctor_release(x_3127, 1);
 x_3136 = x_3127;
} else {
 lean_dec_ref(x_3127);
 x_3136 = lean_box(0);
}
if (lean_is_scalar(x_3136)) {
 x_3137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3137 = x_3136;
}
lean_ctor_set(x_3137, 0, x_3134);
lean_ctor_set(x_3137, 1, x_3135);
return x_3137;
}
}
else
{
lean_object* x_3138; lean_object* x_3139; lean_object* x_3140; lean_object* x_3141; 
lean_dec(x_3122);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3138 = lean_ctor_get(x_3124, 0);
lean_inc(x_3138);
x_3139 = lean_ctor_get(x_3124, 1);
lean_inc(x_3139);
if (lean_is_exclusive(x_3124)) {
 lean_ctor_release(x_3124, 0);
 lean_ctor_release(x_3124, 1);
 x_3140 = x_3124;
} else {
 lean_dec_ref(x_3124);
 x_3140 = lean_box(0);
}
if (lean_is_scalar(x_3140)) {
 x_3141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3141 = x_3140;
}
lean_ctor_set(x_3141, 0, x_3138);
lean_ctor_set(x_3141, 1, x_3139);
return x_3141;
}
}
else
{
lean_object* x_3142; lean_object* x_3143; lean_object* x_3144; lean_object* x_3145; 
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_3142 = lean_ctor_get(x_3115, 0);
lean_inc(x_3142);
x_3143 = lean_ctor_get(x_3115, 1);
lean_inc(x_3143);
if (lean_is_exclusive(x_3115)) {
 lean_ctor_release(x_3115, 0);
 lean_ctor_release(x_3115, 1);
 x_3144 = x_3115;
} else {
 lean_dec_ref(x_3115);
 x_3144 = lean_box(0);
}
if (lean_is_scalar(x_3144)) {
 x_3145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3145 = x_3144;
}
lean_ctor_set(x_3145, 0, x_3142);
lean_ctor_set(x_3145, 1, x_3143);
return x_3145;
}
}
}
else
{
lean_object* x_3146; 
lean_dec(x_2091);
lean_dec(x_11);
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3146 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2088);
if (lean_obj_tag(x_3146) == 0)
{
lean_object* x_3147; lean_object* x_3148; lean_object* x_3149; lean_object* x_3150; lean_object* x_3151; lean_object* x_3152; lean_object* x_3153; lean_object* x_3154; lean_object* x_3155; 
x_3147 = lean_ctor_get(x_3146, 0);
lean_inc(x_3147);
x_3148 = lean_ctor_get(x_3146, 1);
lean_inc(x_3148);
lean_dec(x_3146);
x_3149 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3150 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3151 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__46;
x_3152 = l_Lean_reflBoolTrue;
x_3153 = l_Lean_mkApp4(x_3151, x_3147, x_3149, x_3150, x_3152);
x_3154 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3155 = l_Lean_Meta_mkEq(x_2090, x_3154, x_5, x_6, x_7, x_8, x_3148);
if (lean_obj_tag(x_3155) == 0)
{
lean_object* x_3156; lean_object* x_3157; lean_object* x_3158; 
x_3156 = lean_ctor_get(x_3155, 0);
lean_inc(x_3156);
x_3157 = lean_ctor_get(x_3155, 1);
lean_inc(x_3157);
lean_dec(x_3155);
x_3158 = l_Lean_Meta_mkExpectedTypeHint(x_3153, x_3156, x_5, x_6, x_7, x_8, x_3157);
if (lean_obj_tag(x_3158) == 0)
{
lean_object* x_3159; lean_object* x_3160; lean_object* x_3161; lean_object* x_3162; lean_object* x_3163; lean_object* x_3164; 
x_3159 = lean_ctor_get(x_3158, 0);
lean_inc(x_3159);
x_3160 = lean_ctor_get(x_3158, 1);
lean_inc(x_3160);
if (lean_is_exclusive(x_3158)) {
 lean_ctor_release(x_3158, 0);
 lean_ctor_release(x_3158, 1);
 x_3161 = x_3158;
} else {
 lean_dec_ref(x_3158);
 x_3161 = lean_box(0);
}
x_3162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3162, 0, x_3154);
lean_ctor_set(x_3162, 1, x_3159);
x_3163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3163, 0, x_3162);
if (lean_is_scalar(x_3161)) {
 x_3164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3164 = x_3161;
}
lean_ctor_set(x_3164, 0, x_3163);
lean_ctor_set(x_3164, 1, x_3160);
return x_3164;
}
else
{
lean_object* x_3165; lean_object* x_3166; lean_object* x_3167; lean_object* x_3168; 
x_3165 = lean_ctor_get(x_3158, 0);
lean_inc(x_3165);
x_3166 = lean_ctor_get(x_3158, 1);
lean_inc(x_3166);
if (lean_is_exclusive(x_3158)) {
 lean_ctor_release(x_3158, 0);
 lean_ctor_release(x_3158, 1);
 x_3167 = x_3158;
} else {
 lean_dec_ref(x_3158);
 x_3167 = lean_box(0);
}
if (lean_is_scalar(x_3167)) {
 x_3168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3168 = x_3167;
}
lean_ctor_set(x_3168, 0, x_3165);
lean_ctor_set(x_3168, 1, x_3166);
return x_3168;
}
}
else
{
lean_object* x_3169; lean_object* x_3170; lean_object* x_3171; lean_object* x_3172; 
lean_dec(x_3153);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3169 = lean_ctor_get(x_3155, 0);
lean_inc(x_3169);
x_3170 = lean_ctor_get(x_3155, 1);
lean_inc(x_3170);
if (lean_is_exclusive(x_3155)) {
 lean_ctor_release(x_3155, 0);
 lean_ctor_release(x_3155, 1);
 x_3171 = x_3155;
} else {
 lean_dec_ref(x_3155);
 x_3171 = lean_box(0);
}
if (lean_is_scalar(x_3171)) {
 x_3172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3172 = x_3171;
}
lean_ctor_set(x_3172, 0, x_3169);
lean_ctor_set(x_3172, 1, x_3170);
return x_3172;
}
}
else
{
lean_object* x_3173; lean_object* x_3174; lean_object* x_3175; lean_object* x_3176; 
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_3173 = lean_ctor_get(x_3146, 0);
lean_inc(x_3173);
x_3174 = lean_ctor_get(x_3146, 1);
lean_inc(x_3174);
if (lean_is_exclusive(x_3146)) {
 lean_ctor_release(x_3146, 0);
 lean_ctor_release(x_3146, 1);
 x_3175 = x_3146;
} else {
 lean_dec_ref(x_3146);
 x_3175 = lean_box(0);
}
if (lean_is_scalar(x_3175)) {
 x_3176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3176 = x_3175;
}
lean_ctor_set(x_3176, 0, x_3173);
lean_ctor_set(x_3176, 1, x_3174);
return x_3176;
}
}
block_3104:
{
lean_dec(x_2092);
if (lean_obj_tag(x_2091) == 0)
{
lean_object* x_2093; lean_object* x_2094; uint8_t x_2095; 
x_2093 = l_Int_Linear_Poly_gcdCoeffs_x27(x_2091);
x_2094 = lean_unsigned_to_nat(1u);
x_2095 = lean_nat_dec_eq(x_2093, x_2094);
if (x_2095 == 0)
{
lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; uint8_t x_2100; 
x_2096 = l_Int_Linear_Poly_getConst(x_2091);
x_2097 = lean_nat_to_int(x_2093);
x_2098 = lean_int_emod(x_2096, x_2097);
lean_dec(x_2096);
x_2099 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_2100 = lean_int_dec_eq(x_2098, x_2099);
lean_dec(x_2098);
if (x_2100 == 0)
{
lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; 
lean_dec(x_11);
if (lean_is_exclusive(x_2091)) {
 lean_ctor_release(x_2091, 0);
 x_2101 = x_2091;
} else {
 lean_dec_ref(x_2091);
 x_2101 = lean_box(0);
}
x_2102 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2103 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2088);
if (lean_obj_tag(x_2103) == 0)
{
lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; uint8_t x_2108; lean_object* x_2109; lean_object* x_2110; 
x_2104 = lean_ctor_get(x_2103, 0);
lean_inc(x_2104);
x_2105 = lean_ctor_get(x_2103, 1);
lean_inc(x_2105);
lean_dec(x_2103);
x_2106 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2107 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2108 = lean_int_dec_le(x_2099, x_2097);
x_2109 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2110 = l_Lean_Meta_mkEq(x_2090, x_2109, x_5, x_6, x_7, x_8, x_2105);
if (x_2108 == 0)
{
if (lean_obj_tag(x_2110) == 0)
{
lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; 
x_2111 = lean_ctor_get(x_2110, 0);
lean_inc(x_2111);
x_2112 = lean_ctor_get(x_2110, 1);
lean_inc(x_2112);
lean_dec(x_2110);
x_2113 = l_Lean_Expr_const___override(x_3, x_2102);
x_2114 = lean_int_neg(x_2097);
lean_dec(x_2097);
x_2115 = l_Int_toNat(x_2114);
lean_dec(x_2114);
x_2116 = l_Lean_instToExprInt_mkNat(x_2115);
x_2117 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_2118 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_2119 = l_Lean_mkApp3(x_2117, x_2113, x_2118, x_2116);
x_2120 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_2121 = l_Lean_reflBoolTrue;
x_2122 = l_Lean_mkApp5(x_2120, x_2104, x_2106, x_2107, x_2119, x_2121);
x_2123 = l_Lean_Meta_mkExpectedTypeHint(x_2122, x_2111, x_5, x_6, x_7, x_8, x_2112);
if (lean_obj_tag(x_2123) == 0)
{
lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; 
x_2124 = lean_ctor_get(x_2123, 0);
lean_inc(x_2124);
x_2125 = lean_ctor_get(x_2123, 1);
lean_inc(x_2125);
if (lean_is_exclusive(x_2123)) {
 lean_ctor_release(x_2123, 0);
 lean_ctor_release(x_2123, 1);
 x_2126 = x_2123;
} else {
 lean_dec_ref(x_2123);
 x_2126 = lean_box(0);
}
x_2127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2127, 0, x_2109);
lean_ctor_set(x_2127, 1, x_2124);
if (lean_is_scalar(x_2101)) {
 x_2128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2128 = x_2101;
 lean_ctor_set_tag(x_2128, 1);
}
lean_ctor_set(x_2128, 0, x_2127);
if (lean_is_scalar(x_2126)) {
 x_2129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2129 = x_2126;
}
lean_ctor_set(x_2129, 0, x_2128);
lean_ctor_set(x_2129, 1, x_2125);
return x_2129;
}
else
{
lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; 
lean_dec(x_2101);
x_2130 = lean_ctor_get(x_2123, 0);
lean_inc(x_2130);
x_2131 = lean_ctor_get(x_2123, 1);
lean_inc(x_2131);
if (lean_is_exclusive(x_2123)) {
 lean_ctor_release(x_2123, 0);
 lean_ctor_release(x_2123, 1);
 x_2132 = x_2123;
} else {
 lean_dec_ref(x_2123);
 x_2132 = lean_box(0);
}
if (lean_is_scalar(x_2132)) {
 x_2133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2133 = x_2132;
}
lean_ctor_set(x_2133, 0, x_2130);
lean_ctor_set(x_2133, 1, x_2131);
return x_2133;
}
}
else
{
lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; lean_object* x_2137; 
lean_dec(x_2107);
lean_dec(x_2106);
lean_dec(x_2104);
lean_dec(x_2101);
lean_dec(x_2097);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_2134 = lean_ctor_get(x_2110, 0);
lean_inc(x_2134);
x_2135 = lean_ctor_get(x_2110, 1);
lean_inc(x_2135);
if (lean_is_exclusive(x_2110)) {
 lean_ctor_release(x_2110, 0);
 lean_ctor_release(x_2110, 1);
 x_2136 = x_2110;
} else {
 lean_dec_ref(x_2110);
 x_2136 = lean_box(0);
}
if (lean_is_scalar(x_2136)) {
 x_2137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2137 = x_2136;
}
lean_ctor_set(x_2137, 0, x_2134);
lean_ctor_set(x_2137, 1, x_2135);
return x_2137;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2110) == 0)
{
lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; lean_object* x_2145; 
x_2138 = lean_ctor_get(x_2110, 0);
lean_inc(x_2138);
x_2139 = lean_ctor_get(x_2110, 1);
lean_inc(x_2139);
lean_dec(x_2110);
x_2140 = l_Int_toNat(x_2097);
lean_dec(x_2097);
x_2141 = l_Lean_instToExprInt_mkNat(x_2140);
x_2142 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_2143 = l_Lean_reflBoolTrue;
x_2144 = l_Lean_mkApp5(x_2142, x_2104, x_2106, x_2107, x_2141, x_2143);
x_2145 = l_Lean_Meta_mkExpectedTypeHint(x_2144, x_2138, x_5, x_6, x_7, x_8, x_2139);
if (lean_obj_tag(x_2145) == 0)
{
lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; lean_object* x_2149; lean_object* x_2150; lean_object* x_2151; 
x_2146 = lean_ctor_get(x_2145, 0);
lean_inc(x_2146);
x_2147 = lean_ctor_get(x_2145, 1);
lean_inc(x_2147);
if (lean_is_exclusive(x_2145)) {
 lean_ctor_release(x_2145, 0);
 lean_ctor_release(x_2145, 1);
 x_2148 = x_2145;
} else {
 lean_dec_ref(x_2145);
 x_2148 = lean_box(0);
}
x_2149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2149, 0, x_2109);
lean_ctor_set(x_2149, 1, x_2146);
if (lean_is_scalar(x_2101)) {
 x_2150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2150 = x_2101;
 lean_ctor_set_tag(x_2150, 1);
}
lean_ctor_set(x_2150, 0, x_2149);
if (lean_is_scalar(x_2148)) {
 x_2151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2151 = x_2148;
}
lean_ctor_set(x_2151, 0, x_2150);
lean_ctor_set(x_2151, 1, x_2147);
return x_2151;
}
else
{
lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; 
lean_dec(x_2101);
x_2152 = lean_ctor_get(x_2145, 0);
lean_inc(x_2152);
x_2153 = lean_ctor_get(x_2145, 1);
lean_inc(x_2153);
if (lean_is_exclusive(x_2145)) {
 lean_ctor_release(x_2145, 0);
 lean_ctor_release(x_2145, 1);
 x_2154 = x_2145;
} else {
 lean_dec_ref(x_2145);
 x_2154 = lean_box(0);
}
if (lean_is_scalar(x_2154)) {
 x_2155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2155 = x_2154;
}
lean_ctor_set(x_2155, 0, x_2152);
lean_ctor_set(x_2155, 1, x_2153);
return x_2155;
}
}
else
{
lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; 
lean_dec(x_2107);
lean_dec(x_2106);
lean_dec(x_2104);
lean_dec(x_2101);
lean_dec(x_2097);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2156 = lean_ctor_get(x_2110, 0);
lean_inc(x_2156);
x_2157 = lean_ctor_get(x_2110, 1);
lean_inc(x_2157);
if (lean_is_exclusive(x_2110)) {
 lean_ctor_release(x_2110, 0);
 lean_ctor_release(x_2110, 1);
 x_2158 = x_2110;
} else {
 lean_dec_ref(x_2110);
 x_2158 = lean_box(0);
}
if (lean_is_scalar(x_2158)) {
 x_2159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2159 = x_2158;
}
lean_ctor_set(x_2159, 0, x_2156);
lean_ctor_set(x_2159, 1, x_2157);
return x_2159;
}
}
}
else
{
lean_object* x_2160; lean_object* x_2161; lean_object* x_2162; lean_object* x_2163; 
lean_dec(x_2101);
lean_dec(x_2097);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2160 = lean_ctor_get(x_2103, 0);
lean_inc(x_2160);
x_2161 = lean_ctor_get(x_2103, 1);
lean_inc(x_2161);
if (lean_is_exclusive(x_2103)) {
 lean_ctor_release(x_2103, 0);
 lean_ctor_release(x_2103, 1);
 x_2162 = x_2103;
} else {
 lean_dec_ref(x_2103);
 x_2162 = lean_box(0);
}
if (lean_is_scalar(x_2162)) {
 x_2163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2163 = x_2162;
}
lean_ctor_set(x_2163, 0, x_2160);
lean_ctor_set(x_2163, 1, x_2161);
return x_2163;
}
}
else
{
lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; 
lean_inc(x_2091);
x_2164 = l_Int_Linear_Poly_div(x_2097, x_2091);
if (lean_is_exclusive(x_2091)) {
 lean_ctor_release(x_2091, 0);
 x_2165 = x_2091;
} else {
 lean_dec_ref(x_2091);
 x_2165 = lean_box(0);
}
lean_inc(x_2164);
x_2166 = l_Int_Linear_Poly_denoteExpr(x_11, x_2164, x_5, x_6, x_7, x_8, x_2088);
x_2167 = lean_ctor_get(x_2166, 0);
lean_inc(x_2167);
x_2168 = lean_ctor_get(x_2166, 1);
lean_inc(x_2168);
if (lean_is_exclusive(x_2166)) {
 lean_ctor_release(x_2166, 0);
 lean_ctor_release(x_2166, 1);
 x_2169 = x_2166;
} else {
 lean_dec_ref(x_2166);
 x_2169 = lean_box(0);
}
x_2170 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_2171 = l_Lean_mkAppB(x_2089, x_2167, x_2170);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2172 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2168);
if (lean_obj_tag(x_2172) == 0)
{
lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; uint8_t x_2179; lean_object* x_2180; 
x_2173 = lean_ctor_get(x_2172, 0);
lean_inc(x_2173);
x_2174 = lean_ctor_get(x_2172, 1);
lean_inc(x_2174);
lean_dec(x_2172);
x_2175 = lean_box(0);
x_2176 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2177 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2178 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_2164);
x_2179 = lean_int_dec_le(x_2099, x_2097);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2171);
x_2180 = l_Lean_Meta_mkEq(x_2090, x_2171, x_5, x_6, x_7, x_8, x_2174);
if (x_2179 == 0)
{
if (lean_obj_tag(x_2180) == 0)
{
lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; lean_object* x_2188; lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; 
x_2181 = lean_ctor_get(x_2180, 0);
lean_inc(x_2181);
x_2182 = lean_ctor_get(x_2180, 1);
lean_inc(x_2182);
lean_dec(x_2180);
x_2183 = l_Lean_Expr_const___override(x_3, x_2175);
x_2184 = lean_int_neg(x_2097);
lean_dec(x_2097);
x_2185 = l_Int_toNat(x_2184);
lean_dec(x_2184);
x_2186 = l_Lean_instToExprInt_mkNat(x_2185);
x_2187 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_2188 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_2189 = l_Lean_mkApp3(x_2187, x_2183, x_2188, x_2186);
x_2190 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_2191 = l_Lean_reflBoolTrue;
x_2192 = l_Lean_mkApp6(x_2190, x_2173, x_2176, x_2177, x_2178, x_2189, x_2191);
x_2193 = l_Lean_Meta_mkExpectedTypeHint(x_2192, x_2181, x_5, x_6, x_7, x_8, x_2182);
if (lean_obj_tag(x_2193) == 0)
{
lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; 
x_2194 = lean_ctor_get(x_2193, 0);
lean_inc(x_2194);
x_2195 = lean_ctor_get(x_2193, 1);
lean_inc(x_2195);
if (lean_is_exclusive(x_2193)) {
 lean_ctor_release(x_2193, 0);
 lean_ctor_release(x_2193, 1);
 x_2196 = x_2193;
} else {
 lean_dec_ref(x_2193);
 x_2196 = lean_box(0);
}
if (lean_is_scalar(x_2169)) {
 x_2197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2197 = x_2169;
}
lean_ctor_set(x_2197, 0, x_2171);
lean_ctor_set(x_2197, 1, x_2194);
if (lean_is_scalar(x_2165)) {
 x_2198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2198 = x_2165;
 lean_ctor_set_tag(x_2198, 1);
}
lean_ctor_set(x_2198, 0, x_2197);
if (lean_is_scalar(x_2196)) {
 x_2199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2199 = x_2196;
}
lean_ctor_set(x_2199, 0, x_2198);
lean_ctor_set(x_2199, 1, x_2195);
return x_2199;
}
else
{
lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; lean_object* x_2203; 
lean_dec(x_2171);
lean_dec(x_2169);
lean_dec(x_2165);
x_2200 = lean_ctor_get(x_2193, 0);
lean_inc(x_2200);
x_2201 = lean_ctor_get(x_2193, 1);
lean_inc(x_2201);
if (lean_is_exclusive(x_2193)) {
 lean_ctor_release(x_2193, 0);
 lean_ctor_release(x_2193, 1);
 x_2202 = x_2193;
} else {
 lean_dec_ref(x_2193);
 x_2202 = lean_box(0);
}
if (lean_is_scalar(x_2202)) {
 x_2203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2203 = x_2202;
}
lean_ctor_set(x_2203, 0, x_2200);
lean_ctor_set(x_2203, 1, x_2201);
return x_2203;
}
}
else
{
lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; lean_object* x_2207; 
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2176);
lean_dec(x_2173);
lean_dec(x_2171);
lean_dec(x_2169);
lean_dec(x_2165);
lean_dec(x_2097);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_2204 = lean_ctor_get(x_2180, 0);
lean_inc(x_2204);
x_2205 = lean_ctor_get(x_2180, 1);
lean_inc(x_2205);
if (lean_is_exclusive(x_2180)) {
 lean_ctor_release(x_2180, 0);
 lean_ctor_release(x_2180, 1);
 x_2206 = x_2180;
} else {
 lean_dec_ref(x_2180);
 x_2206 = lean_box(0);
}
if (lean_is_scalar(x_2206)) {
 x_2207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2207 = x_2206;
}
lean_ctor_set(x_2207, 0, x_2204);
lean_ctor_set(x_2207, 1, x_2205);
return x_2207;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2180) == 0)
{
lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; lean_object* x_2212; lean_object* x_2213; lean_object* x_2214; lean_object* x_2215; 
x_2208 = lean_ctor_get(x_2180, 0);
lean_inc(x_2208);
x_2209 = lean_ctor_get(x_2180, 1);
lean_inc(x_2209);
lean_dec(x_2180);
x_2210 = l_Int_toNat(x_2097);
lean_dec(x_2097);
x_2211 = l_Lean_instToExprInt_mkNat(x_2210);
x_2212 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_2213 = l_Lean_reflBoolTrue;
x_2214 = l_Lean_mkApp6(x_2212, x_2173, x_2176, x_2177, x_2178, x_2211, x_2213);
x_2215 = l_Lean_Meta_mkExpectedTypeHint(x_2214, x_2208, x_5, x_6, x_7, x_8, x_2209);
if (lean_obj_tag(x_2215) == 0)
{
lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; lean_object* x_2220; lean_object* x_2221; 
x_2216 = lean_ctor_get(x_2215, 0);
lean_inc(x_2216);
x_2217 = lean_ctor_get(x_2215, 1);
lean_inc(x_2217);
if (lean_is_exclusive(x_2215)) {
 lean_ctor_release(x_2215, 0);
 lean_ctor_release(x_2215, 1);
 x_2218 = x_2215;
} else {
 lean_dec_ref(x_2215);
 x_2218 = lean_box(0);
}
if (lean_is_scalar(x_2169)) {
 x_2219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2219 = x_2169;
}
lean_ctor_set(x_2219, 0, x_2171);
lean_ctor_set(x_2219, 1, x_2216);
if (lean_is_scalar(x_2165)) {
 x_2220 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2220 = x_2165;
 lean_ctor_set_tag(x_2220, 1);
}
lean_ctor_set(x_2220, 0, x_2219);
if (lean_is_scalar(x_2218)) {
 x_2221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2221 = x_2218;
}
lean_ctor_set(x_2221, 0, x_2220);
lean_ctor_set(x_2221, 1, x_2217);
return x_2221;
}
else
{
lean_object* x_2222; lean_object* x_2223; lean_object* x_2224; lean_object* x_2225; 
lean_dec(x_2171);
lean_dec(x_2169);
lean_dec(x_2165);
x_2222 = lean_ctor_get(x_2215, 0);
lean_inc(x_2222);
x_2223 = lean_ctor_get(x_2215, 1);
lean_inc(x_2223);
if (lean_is_exclusive(x_2215)) {
 lean_ctor_release(x_2215, 0);
 lean_ctor_release(x_2215, 1);
 x_2224 = x_2215;
} else {
 lean_dec_ref(x_2215);
 x_2224 = lean_box(0);
}
if (lean_is_scalar(x_2224)) {
 x_2225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2225 = x_2224;
}
lean_ctor_set(x_2225, 0, x_2222);
lean_ctor_set(x_2225, 1, x_2223);
return x_2225;
}
}
else
{
lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; 
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2176);
lean_dec(x_2173);
lean_dec(x_2171);
lean_dec(x_2169);
lean_dec(x_2165);
lean_dec(x_2097);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2226 = lean_ctor_get(x_2180, 0);
lean_inc(x_2226);
x_2227 = lean_ctor_get(x_2180, 1);
lean_inc(x_2227);
if (lean_is_exclusive(x_2180)) {
 lean_ctor_release(x_2180, 0);
 lean_ctor_release(x_2180, 1);
 x_2228 = x_2180;
} else {
 lean_dec_ref(x_2180);
 x_2228 = lean_box(0);
}
if (lean_is_scalar(x_2228)) {
 x_2229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2229 = x_2228;
}
lean_ctor_set(x_2229, 0, x_2226);
lean_ctor_set(x_2229, 1, x_2227);
return x_2229;
}
}
}
else
{
lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; lean_object* x_2233; 
lean_dec(x_2171);
lean_dec(x_2169);
lean_dec(x_2165);
lean_dec(x_2164);
lean_dec(x_2097);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2230 = lean_ctor_get(x_2172, 0);
lean_inc(x_2230);
x_2231 = lean_ctor_get(x_2172, 1);
lean_inc(x_2231);
if (lean_is_exclusive(x_2172)) {
 lean_ctor_release(x_2172, 0);
 lean_ctor_release(x_2172, 1);
 x_2232 = x_2172;
} else {
 lean_dec_ref(x_2172);
 x_2232 = lean_box(0);
}
if (lean_is_scalar(x_2232)) {
 x_2233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2233 = x_2232;
}
lean_ctor_set(x_2233, 0, x_2230);
lean_ctor_set(x_2233, 1, x_2231);
return x_2233;
}
}
}
else
{
lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; lean_object* x_2238; lean_object* x_2239; lean_object* x_2240; 
lean_dec(x_2093);
lean_dec(x_3);
lean_inc(x_2091);
x_2234 = l_Int_Linear_Poly_denoteExpr(x_11, x_2091, x_5, x_6, x_7, x_8, x_2088);
x_2235 = lean_ctor_get(x_2234, 0);
lean_inc(x_2235);
x_2236 = lean_ctor_get(x_2234, 1);
lean_inc(x_2236);
if (lean_is_exclusive(x_2234)) {
 lean_ctor_release(x_2234, 0);
 lean_ctor_release(x_2234, 1);
 x_2237 = x_2234;
} else {
 lean_dec_ref(x_2234);
 x_2237 = lean_box(0);
}
x_2238 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_2239 = l_Lean_mkAppB(x_2089, x_2235, x_2238);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2240 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2236);
if (lean_obj_tag(x_2240) == 0)
{
lean_object* x_2241; lean_object* x_2242; lean_object* x_2243; lean_object* x_2244; lean_object* x_2245; lean_object* x_2246; lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; lean_object* x_2250; 
x_2241 = lean_ctor_get(x_2240, 0);
lean_inc(x_2241);
x_2242 = lean_ctor_get(x_2240, 1);
lean_inc(x_2242);
lean_dec(x_2240);
x_2243 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2244 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
lean_inc(x_2091);
x_2245 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_2091);
if (lean_is_exclusive(x_2091)) {
 lean_ctor_release(x_2091, 0);
 x_2246 = x_2091;
} else {
 lean_dec_ref(x_2091);
 x_2246 = lean_box(0);
}
x_2247 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_2248 = l_Lean_reflBoolTrue;
x_2249 = l_Lean_mkApp5(x_2247, x_2241, x_2243, x_2244, x_2245, x_2248);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2239);
x_2250 = l_Lean_Meta_mkEq(x_2090, x_2239, x_5, x_6, x_7, x_8, x_2242);
if (lean_obj_tag(x_2250) == 0)
{
lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; 
x_2251 = lean_ctor_get(x_2250, 0);
lean_inc(x_2251);
x_2252 = lean_ctor_get(x_2250, 1);
lean_inc(x_2252);
lean_dec(x_2250);
x_2253 = l_Lean_Meta_mkExpectedTypeHint(x_2249, x_2251, x_5, x_6, x_7, x_8, x_2252);
if (lean_obj_tag(x_2253) == 0)
{
lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; lean_object* x_2258; lean_object* x_2259; 
x_2254 = lean_ctor_get(x_2253, 0);
lean_inc(x_2254);
x_2255 = lean_ctor_get(x_2253, 1);
lean_inc(x_2255);
if (lean_is_exclusive(x_2253)) {
 lean_ctor_release(x_2253, 0);
 lean_ctor_release(x_2253, 1);
 x_2256 = x_2253;
} else {
 lean_dec_ref(x_2253);
 x_2256 = lean_box(0);
}
if (lean_is_scalar(x_2237)) {
 x_2257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2257 = x_2237;
}
lean_ctor_set(x_2257, 0, x_2239);
lean_ctor_set(x_2257, 1, x_2254);
if (lean_is_scalar(x_2246)) {
 x_2258 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2258 = x_2246;
 lean_ctor_set_tag(x_2258, 1);
}
lean_ctor_set(x_2258, 0, x_2257);
if (lean_is_scalar(x_2256)) {
 x_2259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2259 = x_2256;
}
lean_ctor_set(x_2259, 0, x_2258);
lean_ctor_set(x_2259, 1, x_2255);
return x_2259;
}
else
{
lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; lean_object* x_2263; 
lean_dec(x_2246);
lean_dec(x_2239);
lean_dec(x_2237);
x_2260 = lean_ctor_get(x_2253, 0);
lean_inc(x_2260);
x_2261 = lean_ctor_get(x_2253, 1);
lean_inc(x_2261);
if (lean_is_exclusive(x_2253)) {
 lean_ctor_release(x_2253, 0);
 lean_ctor_release(x_2253, 1);
 x_2262 = x_2253;
} else {
 lean_dec_ref(x_2253);
 x_2262 = lean_box(0);
}
if (lean_is_scalar(x_2262)) {
 x_2263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2263 = x_2262;
}
lean_ctor_set(x_2263, 0, x_2260);
lean_ctor_set(x_2263, 1, x_2261);
return x_2263;
}
}
else
{
lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; lean_object* x_2267; 
lean_dec(x_2249);
lean_dec(x_2246);
lean_dec(x_2239);
lean_dec(x_2237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2264 = lean_ctor_get(x_2250, 0);
lean_inc(x_2264);
x_2265 = lean_ctor_get(x_2250, 1);
lean_inc(x_2265);
if (lean_is_exclusive(x_2250)) {
 lean_ctor_release(x_2250, 0);
 lean_ctor_release(x_2250, 1);
 x_2266 = x_2250;
} else {
 lean_dec_ref(x_2250);
 x_2266 = lean_box(0);
}
if (lean_is_scalar(x_2266)) {
 x_2267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2267 = x_2266;
}
lean_ctor_set(x_2267, 0, x_2264);
lean_ctor_set(x_2267, 1, x_2265);
return x_2267;
}
}
else
{
lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; lean_object* x_2271; 
lean_dec(x_2239);
lean_dec(x_2237);
lean_dec(x_2091);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_2268 = lean_ctor_get(x_2240, 0);
lean_inc(x_2268);
x_2269 = lean_ctor_get(x_2240, 1);
lean_inc(x_2269);
if (lean_is_exclusive(x_2240)) {
 lean_ctor_release(x_2240, 0);
 lean_ctor_release(x_2240, 1);
 x_2270 = x_2240;
} else {
 lean_dec_ref(x_2240);
 x_2270 = lean_box(0);
}
if (lean_is_scalar(x_2270)) {
 x_2271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2271 = x_2270;
}
lean_ctor_set(x_2271, 0, x_2268);
lean_ctor_set(x_2271, 1, x_2269);
return x_2271;
}
}
}
else
{
lean_object* x_2272; lean_object* x_2273; lean_object* x_2274; lean_object* x_2275; uint8_t x_2276; 
x_2272 = lean_ctor_get(x_2091, 0);
lean_inc(x_2272);
x_2273 = lean_ctor_get(x_2091, 1);
lean_inc(x_2273);
x_2274 = lean_ctor_get(x_2091, 2);
lean_inc(x_2274);
x_2275 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__26;
x_2276 = lean_int_dec_eq(x_2272, x_2275);
lean_dec(x_2272);
if (x_2276 == 0)
{
lean_object* x_2277; lean_object* x_2278; uint8_t x_2279; 
lean_dec(x_2274);
lean_dec(x_2273);
x_2277 = l_Int_Linear_Poly_gcdCoeffs_x27(x_2091);
x_2278 = lean_unsigned_to_nat(1u);
x_2279 = lean_nat_dec_eq(x_2277, x_2278);
if (x_2279 == 0)
{
lean_object* x_2280; lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; uint8_t x_2284; 
x_2280 = l_Int_Linear_Poly_getConst(x_2091);
x_2281 = lean_nat_to_int(x_2277);
x_2282 = lean_int_emod(x_2280, x_2281);
lean_dec(x_2280);
x_2283 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_2284 = lean_int_dec_eq(x_2282, x_2283);
lean_dec(x_2282);
if (x_2284 == 0)
{
lean_object* x_2285; lean_object* x_2286; 
lean_dec(x_2091);
lean_dec(x_11);
x_2285 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2286 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2088);
if (lean_obj_tag(x_2286) == 0)
{
lean_object* x_2287; lean_object* x_2288; lean_object* x_2289; lean_object* x_2290; uint8_t x_2291; lean_object* x_2292; lean_object* x_2293; 
x_2287 = lean_ctor_get(x_2286, 0);
lean_inc(x_2287);
x_2288 = lean_ctor_get(x_2286, 1);
lean_inc(x_2288);
lean_dec(x_2286);
x_2289 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2290 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2291 = lean_int_dec_le(x_2283, x_2281);
x_2292 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2293 = l_Lean_Meta_mkEq(x_2090, x_2292, x_5, x_6, x_7, x_8, x_2288);
if (x_2291 == 0)
{
if (lean_obj_tag(x_2293) == 0)
{
lean_object* x_2294; lean_object* x_2295; lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; lean_object* x_2299; lean_object* x_2300; lean_object* x_2301; lean_object* x_2302; lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; 
x_2294 = lean_ctor_get(x_2293, 0);
lean_inc(x_2294);
x_2295 = lean_ctor_get(x_2293, 1);
lean_inc(x_2295);
lean_dec(x_2293);
x_2296 = l_Lean_Expr_const___override(x_3, x_2285);
x_2297 = lean_int_neg(x_2281);
lean_dec(x_2281);
x_2298 = l_Int_toNat(x_2297);
lean_dec(x_2297);
x_2299 = l_Lean_instToExprInt_mkNat(x_2298);
x_2300 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_2301 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_2302 = l_Lean_mkApp3(x_2300, x_2296, x_2301, x_2299);
x_2303 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_2304 = l_Lean_reflBoolTrue;
x_2305 = l_Lean_mkApp5(x_2303, x_2287, x_2289, x_2290, x_2302, x_2304);
x_2306 = l_Lean_Meta_mkExpectedTypeHint(x_2305, x_2294, x_5, x_6, x_7, x_8, x_2295);
if (lean_obj_tag(x_2306) == 0)
{
lean_object* x_2307; lean_object* x_2308; lean_object* x_2309; lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; 
x_2307 = lean_ctor_get(x_2306, 0);
lean_inc(x_2307);
x_2308 = lean_ctor_get(x_2306, 1);
lean_inc(x_2308);
if (lean_is_exclusive(x_2306)) {
 lean_ctor_release(x_2306, 0);
 lean_ctor_release(x_2306, 1);
 x_2309 = x_2306;
} else {
 lean_dec_ref(x_2306);
 x_2309 = lean_box(0);
}
x_2310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2310, 0, x_2292);
lean_ctor_set(x_2310, 1, x_2307);
x_2311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2311, 0, x_2310);
if (lean_is_scalar(x_2309)) {
 x_2312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2312 = x_2309;
}
lean_ctor_set(x_2312, 0, x_2311);
lean_ctor_set(x_2312, 1, x_2308);
return x_2312;
}
else
{
lean_object* x_2313; lean_object* x_2314; lean_object* x_2315; lean_object* x_2316; 
x_2313 = lean_ctor_get(x_2306, 0);
lean_inc(x_2313);
x_2314 = lean_ctor_get(x_2306, 1);
lean_inc(x_2314);
if (lean_is_exclusive(x_2306)) {
 lean_ctor_release(x_2306, 0);
 lean_ctor_release(x_2306, 1);
 x_2315 = x_2306;
} else {
 lean_dec_ref(x_2306);
 x_2315 = lean_box(0);
}
if (lean_is_scalar(x_2315)) {
 x_2316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2316 = x_2315;
}
lean_ctor_set(x_2316, 0, x_2313);
lean_ctor_set(x_2316, 1, x_2314);
return x_2316;
}
}
else
{
lean_object* x_2317; lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; 
lean_dec(x_2290);
lean_dec(x_2289);
lean_dec(x_2287);
lean_dec(x_2281);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_2317 = lean_ctor_get(x_2293, 0);
lean_inc(x_2317);
x_2318 = lean_ctor_get(x_2293, 1);
lean_inc(x_2318);
if (lean_is_exclusive(x_2293)) {
 lean_ctor_release(x_2293, 0);
 lean_ctor_release(x_2293, 1);
 x_2319 = x_2293;
} else {
 lean_dec_ref(x_2293);
 x_2319 = lean_box(0);
}
if (lean_is_scalar(x_2319)) {
 x_2320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2320 = x_2319;
}
lean_ctor_set(x_2320, 0, x_2317);
lean_ctor_set(x_2320, 1, x_2318);
return x_2320;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2293) == 0)
{
lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; 
x_2321 = lean_ctor_get(x_2293, 0);
lean_inc(x_2321);
x_2322 = lean_ctor_get(x_2293, 1);
lean_inc(x_2322);
lean_dec(x_2293);
x_2323 = l_Int_toNat(x_2281);
lean_dec(x_2281);
x_2324 = l_Lean_instToExprInt_mkNat(x_2323);
x_2325 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_2326 = l_Lean_reflBoolTrue;
x_2327 = l_Lean_mkApp5(x_2325, x_2287, x_2289, x_2290, x_2324, x_2326);
x_2328 = l_Lean_Meta_mkExpectedTypeHint(x_2327, x_2321, x_5, x_6, x_7, x_8, x_2322);
if (lean_obj_tag(x_2328) == 0)
{
lean_object* x_2329; lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; lean_object* x_2333; lean_object* x_2334; 
x_2329 = lean_ctor_get(x_2328, 0);
lean_inc(x_2329);
x_2330 = lean_ctor_get(x_2328, 1);
lean_inc(x_2330);
if (lean_is_exclusive(x_2328)) {
 lean_ctor_release(x_2328, 0);
 lean_ctor_release(x_2328, 1);
 x_2331 = x_2328;
} else {
 lean_dec_ref(x_2328);
 x_2331 = lean_box(0);
}
x_2332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2332, 0, x_2292);
lean_ctor_set(x_2332, 1, x_2329);
x_2333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2333, 0, x_2332);
if (lean_is_scalar(x_2331)) {
 x_2334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2334 = x_2331;
}
lean_ctor_set(x_2334, 0, x_2333);
lean_ctor_set(x_2334, 1, x_2330);
return x_2334;
}
else
{
lean_object* x_2335; lean_object* x_2336; lean_object* x_2337; lean_object* x_2338; 
x_2335 = lean_ctor_get(x_2328, 0);
lean_inc(x_2335);
x_2336 = lean_ctor_get(x_2328, 1);
lean_inc(x_2336);
if (lean_is_exclusive(x_2328)) {
 lean_ctor_release(x_2328, 0);
 lean_ctor_release(x_2328, 1);
 x_2337 = x_2328;
} else {
 lean_dec_ref(x_2328);
 x_2337 = lean_box(0);
}
if (lean_is_scalar(x_2337)) {
 x_2338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2338 = x_2337;
}
lean_ctor_set(x_2338, 0, x_2335);
lean_ctor_set(x_2338, 1, x_2336);
return x_2338;
}
}
else
{
lean_object* x_2339; lean_object* x_2340; lean_object* x_2341; lean_object* x_2342; 
lean_dec(x_2290);
lean_dec(x_2289);
lean_dec(x_2287);
lean_dec(x_2281);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2339 = lean_ctor_get(x_2293, 0);
lean_inc(x_2339);
x_2340 = lean_ctor_get(x_2293, 1);
lean_inc(x_2340);
if (lean_is_exclusive(x_2293)) {
 lean_ctor_release(x_2293, 0);
 lean_ctor_release(x_2293, 1);
 x_2341 = x_2293;
} else {
 lean_dec_ref(x_2293);
 x_2341 = lean_box(0);
}
if (lean_is_scalar(x_2341)) {
 x_2342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2342 = x_2341;
}
lean_ctor_set(x_2342, 0, x_2339);
lean_ctor_set(x_2342, 1, x_2340);
return x_2342;
}
}
}
else
{
lean_object* x_2343; lean_object* x_2344; lean_object* x_2345; lean_object* x_2346; 
lean_dec(x_2281);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2343 = lean_ctor_get(x_2286, 0);
lean_inc(x_2343);
x_2344 = lean_ctor_get(x_2286, 1);
lean_inc(x_2344);
if (lean_is_exclusive(x_2286)) {
 lean_ctor_release(x_2286, 0);
 lean_ctor_release(x_2286, 1);
 x_2345 = x_2286;
} else {
 lean_dec_ref(x_2286);
 x_2345 = lean_box(0);
}
if (lean_is_scalar(x_2345)) {
 x_2346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2346 = x_2345;
}
lean_ctor_set(x_2346, 0, x_2343);
lean_ctor_set(x_2346, 1, x_2344);
return x_2346;
}
}
else
{
lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; lean_object* x_2350; lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; lean_object* x_2354; 
x_2347 = l_Int_Linear_Poly_div(x_2281, x_2091);
lean_inc(x_2347);
x_2348 = l_Int_Linear_Poly_denoteExpr(x_11, x_2347, x_5, x_6, x_7, x_8, x_2088);
x_2349 = lean_ctor_get(x_2348, 0);
lean_inc(x_2349);
x_2350 = lean_ctor_get(x_2348, 1);
lean_inc(x_2350);
if (lean_is_exclusive(x_2348)) {
 lean_ctor_release(x_2348, 0);
 lean_ctor_release(x_2348, 1);
 x_2351 = x_2348;
} else {
 lean_dec_ref(x_2348);
 x_2351 = lean_box(0);
}
x_2352 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_2353 = l_Lean_mkAppB(x_2089, x_2349, x_2352);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2354 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2350);
if (lean_obj_tag(x_2354) == 0)
{
lean_object* x_2355; lean_object* x_2356; lean_object* x_2357; lean_object* x_2358; lean_object* x_2359; lean_object* x_2360; uint8_t x_2361; lean_object* x_2362; 
x_2355 = lean_ctor_get(x_2354, 0);
lean_inc(x_2355);
x_2356 = lean_ctor_get(x_2354, 1);
lean_inc(x_2356);
lean_dec(x_2354);
x_2357 = lean_box(0);
x_2358 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2359 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2360 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_2347);
x_2361 = lean_int_dec_le(x_2283, x_2281);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2353);
x_2362 = l_Lean_Meta_mkEq(x_2090, x_2353, x_5, x_6, x_7, x_8, x_2356);
if (x_2361 == 0)
{
if (lean_obj_tag(x_2362) == 0)
{
lean_object* x_2363; lean_object* x_2364; lean_object* x_2365; lean_object* x_2366; lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; lean_object* x_2375; 
x_2363 = lean_ctor_get(x_2362, 0);
lean_inc(x_2363);
x_2364 = lean_ctor_get(x_2362, 1);
lean_inc(x_2364);
lean_dec(x_2362);
x_2365 = l_Lean_Expr_const___override(x_3, x_2357);
x_2366 = lean_int_neg(x_2281);
lean_dec(x_2281);
x_2367 = l_Int_toNat(x_2366);
lean_dec(x_2366);
x_2368 = l_Lean_instToExprInt_mkNat(x_2367);
x_2369 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_2370 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_2371 = l_Lean_mkApp3(x_2369, x_2365, x_2370, x_2368);
x_2372 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_2373 = l_Lean_reflBoolTrue;
x_2374 = l_Lean_mkApp6(x_2372, x_2355, x_2358, x_2359, x_2360, x_2371, x_2373);
x_2375 = l_Lean_Meta_mkExpectedTypeHint(x_2374, x_2363, x_5, x_6, x_7, x_8, x_2364);
if (lean_obj_tag(x_2375) == 0)
{
lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; lean_object* x_2380; lean_object* x_2381; 
x_2376 = lean_ctor_get(x_2375, 0);
lean_inc(x_2376);
x_2377 = lean_ctor_get(x_2375, 1);
lean_inc(x_2377);
if (lean_is_exclusive(x_2375)) {
 lean_ctor_release(x_2375, 0);
 lean_ctor_release(x_2375, 1);
 x_2378 = x_2375;
} else {
 lean_dec_ref(x_2375);
 x_2378 = lean_box(0);
}
if (lean_is_scalar(x_2351)) {
 x_2379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2379 = x_2351;
}
lean_ctor_set(x_2379, 0, x_2353);
lean_ctor_set(x_2379, 1, x_2376);
x_2380 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2380, 0, x_2379);
if (lean_is_scalar(x_2378)) {
 x_2381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2381 = x_2378;
}
lean_ctor_set(x_2381, 0, x_2380);
lean_ctor_set(x_2381, 1, x_2377);
return x_2381;
}
else
{
lean_object* x_2382; lean_object* x_2383; lean_object* x_2384; lean_object* x_2385; 
lean_dec(x_2353);
lean_dec(x_2351);
x_2382 = lean_ctor_get(x_2375, 0);
lean_inc(x_2382);
x_2383 = lean_ctor_get(x_2375, 1);
lean_inc(x_2383);
if (lean_is_exclusive(x_2375)) {
 lean_ctor_release(x_2375, 0);
 lean_ctor_release(x_2375, 1);
 x_2384 = x_2375;
} else {
 lean_dec_ref(x_2375);
 x_2384 = lean_box(0);
}
if (lean_is_scalar(x_2384)) {
 x_2385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2385 = x_2384;
}
lean_ctor_set(x_2385, 0, x_2382);
lean_ctor_set(x_2385, 1, x_2383);
return x_2385;
}
}
else
{
lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; 
lean_dec(x_2360);
lean_dec(x_2359);
lean_dec(x_2358);
lean_dec(x_2355);
lean_dec(x_2353);
lean_dec(x_2351);
lean_dec(x_2281);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_2386 = lean_ctor_get(x_2362, 0);
lean_inc(x_2386);
x_2387 = lean_ctor_get(x_2362, 1);
lean_inc(x_2387);
if (lean_is_exclusive(x_2362)) {
 lean_ctor_release(x_2362, 0);
 lean_ctor_release(x_2362, 1);
 x_2388 = x_2362;
} else {
 lean_dec_ref(x_2362);
 x_2388 = lean_box(0);
}
if (lean_is_scalar(x_2388)) {
 x_2389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2389 = x_2388;
}
lean_ctor_set(x_2389, 0, x_2386);
lean_ctor_set(x_2389, 1, x_2387);
return x_2389;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2362) == 0)
{
lean_object* x_2390; lean_object* x_2391; lean_object* x_2392; lean_object* x_2393; lean_object* x_2394; lean_object* x_2395; lean_object* x_2396; lean_object* x_2397; 
x_2390 = lean_ctor_get(x_2362, 0);
lean_inc(x_2390);
x_2391 = lean_ctor_get(x_2362, 1);
lean_inc(x_2391);
lean_dec(x_2362);
x_2392 = l_Int_toNat(x_2281);
lean_dec(x_2281);
x_2393 = l_Lean_instToExprInt_mkNat(x_2392);
x_2394 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_2395 = l_Lean_reflBoolTrue;
x_2396 = l_Lean_mkApp6(x_2394, x_2355, x_2358, x_2359, x_2360, x_2393, x_2395);
x_2397 = l_Lean_Meta_mkExpectedTypeHint(x_2396, x_2390, x_5, x_6, x_7, x_8, x_2391);
if (lean_obj_tag(x_2397) == 0)
{
lean_object* x_2398; lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; lean_object* x_2403; 
x_2398 = lean_ctor_get(x_2397, 0);
lean_inc(x_2398);
x_2399 = lean_ctor_get(x_2397, 1);
lean_inc(x_2399);
if (lean_is_exclusive(x_2397)) {
 lean_ctor_release(x_2397, 0);
 lean_ctor_release(x_2397, 1);
 x_2400 = x_2397;
} else {
 lean_dec_ref(x_2397);
 x_2400 = lean_box(0);
}
if (lean_is_scalar(x_2351)) {
 x_2401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2401 = x_2351;
}
lean_ctor_set(x_2401, 0, x_2353);
lean_ctor_set(x_2401, 1, x_2398);
x_2402 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2402, 0, x_2401);
if (lean_is_scalar(x_2400)) {
 x_2403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2403 = x_2400;
}
lean_ctor_set(x_2403, 0, x_2402);
lean_ctor_set(x_2403, 1, x_2399);
return x_2403;
}
else
{
lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; 
lean_dec(x_2353);
lean_dec(x_2351);
x_2404 = lean_ctor_get(x_2397, 0);
lean_inc(x_2404);
x_2405 = lean_ctor_get(x_2397, 1);
lean_inc(x_2405);
if (lean_is_exclusive(x_2397)) {
 lean_ctor_release(x_2397, 0);
 lean_ctor_release(x_2397, 1);
 x_2406 = x_2397;
} else {
 lean_dec_ref(x_2397);
 x_2406 = lean_box(0);
}
if (lean_is_scalar(x_2406)) {
 x_2407 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2407 = x_2406;
}
lean_ctor_set(x_2407, 0, x_2404);
lean_ctor_set(x_2407, 1, x_2405);
return x_2407;
}
}
else
{
lean_object* x_2408; lean_object* x_2409; lean_object* x_2410; lean_object* x_2411; 
lean_dec(x_2360);
lean_dec(x_2359);
lean_dec(x_2358);
lean_dec(x_2355);
lean_dec(x_2353);
lean_dec(x_2351);
lean_dec(x_2281);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2408 = lean_ctor_get(x_2362, 0);
lean_inc(x_2408);
x_2409 = lean_ctor_get(x_2362, 1);
lean_inc(x_2409);
if (lean_is_exclusive(x_2362)) {
 lean_ctor_release(x_2362, 0);
 lean_ctor_release(x_2362, 1);
 x_2410 = x_2362;
} else {
 lean_dec_ref(x_2362);
 x_2410 = lean_box(0);
}
if (lean_is_scalar(x_2410)) {
 x_2411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2411 = x_2410;
}
lean_ctor_set(x_2411, 0, x_2408);
lean_ctor_set(x_2411, 1, x_2409);
return x_2411;
}
}
}
else
{
lean_object* x_2412; lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; 
lean_dec(x_2353);
lean_dec(x_2351);
lean_dec(x_2347);
lean_dec(x_2281);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2412 = lean_ctor_get(x_2354, 0);
lean_inc(x_2412);
x_2413 = lean_ctor_get(x_2354, 1);
lean_inc(x_2413);
if (lean_is_exclusive(x_2354)) {
 lean_ctor_release(x_2354, 0);
 lean_ctor_release(x_2354, 1);
 x_2414 = x_2354;
} else {
 lean_dec_ref(x_2354);
 x_2414 = lean_box(0);
}
if (lean_is_scalar(x_2414)) {
 x_2415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2415 = x_2414;
}
lean_ctor_set(x_2415, 0, x_2412);
lean_ctor_set(x_2415, 1, x_2413);
return x_2415;
}
}
}
else
{
lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; lean_object* x_2422; 
lean_dec(x_2277);
lean_dec(x_3);
lean_inc(x_2091);
x_2416 = l_Int_Linear_Poly_denoteExpr(x_11, x_2091, x_5, x_6, x_7, x_8, x_2088);
x_2417 = lean_ctor_get(x_2416, 0);
lean_inc(x_2417);
x_2418 = lean_ctor_get(x_2416, 1);
lean_inc(x_2418);
if (lean_is_exclusive(x_2416)) {
 lean_ctor_release(x_2416, 0);
 lean_ctor_release(x_2416, 1);
 x_2419 = x_2416;
} else {
 lean_dec_ref(x_2416);
 x_2419 = lean_box(0);
}
x_2420 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_2421 = l_Lean_mkAppB(x_2089, x_2417, x_2420);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2422 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2418);
if (lean_obj_tag(x_2422) == 0)
{
lean_object* x_2423; lean_object* x_2424; lean_object* x_2425; lean_object* x_2426; lean_object* x_2427; lean_object* x_2428; lean_object* x_2429; lean_object* x_2430; lean_object* x_2431; 
x_2423 = lean_ctor_get(x_2422, 0);
lean_inc(x_2423);
x_2424 = lean_ctor_get(x_2422, 1);
lean_inc(x_2424);
lean_dec(x_2422);
x_2425 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2426 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2427 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_2091);
x_2428 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_2429 = l_Lean_reflBoolTrue;
x_2430 = l_Lean_mkApp5(x_2428, x_2423, x_2425, x_2426, x_2427, x_2429);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2421);
x_2431 = l_Lean_Meta_mkEq(x_2090, x_2421, x_5, x_6, x_7, x_8, x_2424);
if (lean_obj_tag(x_2431) == 0)
{
lean_object* x_2432; lean_object* x_2433; lean_object* x_2434; 
x_2432 = lean_ctor_get(x_2431, 0);
lean_inc(x_2432);
x_2433 = lean_ctor_get(x_2431, 1);
lean_inc(x_2433);
lean_dec(x_2431);
x_2434 = l_Lean_Meta_mkExpectedTypeHint(x_2430, x_2432, x_5, x_6, x_7, x_8, x_2433);
if (lean_obj_tag(x_2434) == 0)
{
lean_object* x_2435; lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; 
x_2435 = lean_ctor_get(x_2434, 0);
lean_inc(x_2435);
x_2436 = lean_ctor_get(x_2434, 1);
lean_inc(x_2436);
if (lean_is_exclusive(x_2434)) {
 lean_ctor_release(x_2434, 0);
 lean_ctor_release(x_2434, 1);
 x_2437 = x_2434;
} else {
 lean_dec_ref(x_2434);
 x_2437 = lean_box(0);
}
if (lean_is_scalar(x_2419)) {
 x_2438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2438 = x_2419;
}
lean_ctor_set(x_2438, 0, x_2421);
lean_ctor_set(x_2438, 1, x_2435);
x_2439 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2439, 0, x_2438);
if (lean_is_scalar(x_2437)) {
 x_2440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2440 = x_2437;
}
lean_ctor_set(x_2440, 0, x_2439);
lean_ctor_set(x_2440, 1, x_2436);
return x_2440;
}
else
{
lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; lean_object* x_2444; 
lean_dec(x_2421);
lean_dec(x_2419);
x_2441 = lean_ctor_get(x_2434, 0);
lean_inc(x_2441);
x_2442 = lean_ctor_get(x_2434, 1);
lean_inc(x_2442);
if (lean_is_exclusive(x_2434)) {
 lean_ctor_release(x_2434, 0);
 lean_ctor_release(x_2434, 1);
 x_2443 = x_2434;
} else {
 lean_dec_ref(x_2434);
 x_2443 = lean_box(0);
}
if (lean_is_scalar(x_2443)) {
 x_2444 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2444 = x_2443;
}
lean_ctor_set(x_2444, 0, x_2441);
lean_ctor_set(x_2444, 1, x_2442);
return x_2444;
}
}
else
{
lean_object* x_2445; lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; 
lean_dec(x_2430);
lean_dec(x_2421);
lean_dec(x_2419);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2445 = lean_ctor_get(x_2431, 0);
lean_inc(x_2445);
x_2446 = lean_ctor_get(x_2431, 1);
lean_inc(x_2446);
if (lean_is_exclusive(x_2431)) {
 lean_ctor_release(x_2431, 0);
 lean_ctor_release(x_2431, 1);
 x_2447 = x_2431;
} else {
 lean_dec_ref(x_2431);
 x_2447 = lean_box(0);
}
if (lean_is_scalar(x_2447)) {
 x_2448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2448 = x_2447;
}
lean_ctor_set(x_2448, 0, x_2445);
lean_ctor_set(x_2448, 1, x_2446);
return x_2448;
}
}
else
{
lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; lean_object* x_2452; 
lean_dec(x_2421);
lean_dec(x_2419);
lean_dec(x_2091);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_2449 = lean_ctor_get(x_2422, 0);
lean_inc(x_2449);
x_2450 = lean_ctor_get(x_2422, 1);
lean_inc(x_2450);
if (lean_is_exclusive(x_2422)) {
 lean_ctor_release(x_2422, 0);
 lean_ctor_release(x_2422, 1);
 x_2451 = x_2422;
} else {
 lean_dec_ref(x_2422);
 x_2451 = lean_box(0);
}
if (lean_is_scalar(x_2451)) {
 x_2452 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2452 = x_2451;
}
lean_ctor_set(x_2452, 0, x_2449);
lean_ctor_set(x_2452, 1, x_2450);
return x_2452;
}
}
}
else
{
if (lean_obj_tag(x_2274) == 0)
{
lean_object* x_2453; lean_object* x_2454; lean_object* x_2455; lean_object* x_2456; lean_object* x_2457; uint8_t x_2458; 
lean_dec(x_2091);
lean_dec(x_11);
x_2453 = lean_ctor_get(x_2274, 0);
lean_inc(x_2453);
if (lean_is_exclusive(x_2274)) {
 lean_ctor_release(x_2274, 0);
 x_2454 = x_2274;
} else {
 lean_dec_ref(x_2274);
 x_2454 = lean_box(0);
}
x_2455 = lean_array_get(x_10, x_4, x_2273);
x_2456 = lean_int_neg(x_2453);
lean_dec(x_2453);
x_2457 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_2458 = lean_int_dec_le(x_2457, x_2456);
if (x_2458 == 0)
{
lean_object* x_2459; lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; lean_object* x_2466; lean_object* x_2467; lean_object* x_2468; 
x_2459 = lean_box(0);
x_2460 = l_Lean_Expr_const___override(x_3, x_2459);
x_2461 = lean_int_neg(x_2456);
lean_dec(x_2456);
x_2462 = l_Int_toNat(x_2461);
lean_dec(x_2461);
x_2463 = l_Lean_instToExprInt_mkNat(x_2462);
x_2464 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__28;
x_2465 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_2466 = l_Lean_mkApp3(x_2464, x_2460, x_2465, x_2463);
lean_inc(x_2466);
x_2467 = l_Lean_mkAppB(x_2089, x_2455, x_2466);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2468 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2088);
if (lean_obj_tag(x_2468) == 0)
{
lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; lean_object* x_2477; 
x_2469 = lean_ctor_get(x_2468, 0);
lean_inc(x_2469);
x_2470 = lean_ctor_get(x_2468, 1);
lean_inc(x_2470);
lean_dec(x_2468);
x_2471 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2472 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2473 = l_Lean_mkNatLit(x_2273);
x_2474 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__31;
x_2475 = l_Lean_reflBoolTrue;
x_2476 = l_Lean_mkApp6(x_2474, x_2469, x_2471, x_2472, x_2473, x_2466, x_2475);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2467);
x_2477 = l_Lean_Meta_mkEq(x_2090, x_2467, x_5, x_6, x_7, x_8, x_2470);
if (lean_obj_tag(x_2477) == 0)
{
lean_object* x_2478; lean_object* x_2479; lean_object* x_2480; 
x_2478 = lean_ctor_get(x_2477, 0);
lean_inc(x_2478);
x_2479 = lean_ctor_get(x_2477, 1);
lean_inc(x_2479);
lean_dec(x_2477);
x_2480 = l_Lean_Meta_mkExpectedTypeHint(x_2476, x_2478, x_5, x_6, x_7, x_8, x_2479);
if (lean_obj_tag(x_2480) == 0)
{
lean_object* x_2481; lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; lean_object* x_2486; 
x_2481 = lean_ctor_get(x_2480, 0);
lean_inc(x_2481);
x_2482 = lean_ctor_get(x_2480, 1);
lean_inc(x_2482);
if (lean_is_exclusive(x_2480)) {
 lean_ctor_release(x_2480, 0);
 lean_ctor_release(x_2480, 1);
 x_2483 = x_2480;
} else {
 lean_dec_ref(x_2480);
 x_2483 = lean_box(0);
}
x_2484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2484, 0, x_2467);
lean_ctor_set(x_2484, 1, x_2481);
if (lean_is_scalar(x_2454)) {
 x_2485 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2485 = x_2454;
 lean_ctor_set_tag(x_2485, 1);
}
lean_ctor_set(x_2485, 0, x_2484);
if (lean_is_scalar(x_2483)) {
 x_2486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2486 = x_2483;
}
lean_ctor_set(x_2486, 0, x_2485);
lean_ctor_set(x_2486, 1, x_2482);
return x_2486;
}
else
{
lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; lean_object* x_2490; 
lean_dec(x_2467);
lean_dec(x_2454);
x_2487 = lean_ctor_get(x_2480, 0);
lean_inc(x_2487);
x_2488 = lean_ctor_get(x_2480, 1);
lean_inc(x_2488);
if (lean_is_exclusive(x_2480)) {
 lean_ctor_release(x_2480, 0);
 lean_ctor_release(x_2480, 1);
 x_2489 = x_2480;
} else {
 lean_dec_ref(x_2480);
 x_2489 = lean_box(0);
}
if (lean_is_scalar(x_2489)) {
 x_2490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2490 = x_2489;
}
lean_ctor_set(x_2490, 0, x_2487);
lean_ctor_set(x_2490, 1, x_2488);
return x_2490;
}
}
else
{
lean_object* x_2491; lean_object* x_2492; lean_object* x_2493; lean_object* x_2494; 
lean_dec(x_2476);
lean_dec(x_2467);
lean_dec(x_2454);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2491 = lean_ctor_get(x_2477, 0);
lean_inc(x_2491);
x_2492 = lean_ctor_get(x_2477, 1);
lean_inc(x_2492);
if (lean_is_exclusive(x_2477)) {
 lean_ctor_release(x_2477, 0);
 lean_ctor_release(x_2477, 1);
 x_2493 = x_2477;
} else {
 lean_dec_ref(x_2477);
 x_2493 = lean_box(0);
}
if (lean_is_scalar(x_2493)) {
 x_2494 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2494 = x_2493;
}
lean_ctor_set(x_2494, 0, x_2491);
lean_ctor_set(x_2494, 1, x_2492);
return x_2494;
}
}
else
{
lean_object* x_2495; lean_object* x_2496; lean_object* x_2497; lean_object* x_2498; 
lean_dec(x_2467);
lean_dec(x_2466);
lean_dec(x_2454);
lean_dec(x_2273);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_2495 = lean_ctor_get(x_2468, 0);
lean_inc(x_2495);
x_2496 = lean_ctor_get(x_2468, 1);
lean_inc(x_2496);
if (lean_is_exclusive(x_2468)) {
 lean_ctor_release(x_2468, 0);
 lean_ctor_release(x_2468, 1);
 x_2497 = x_2468;
} else {
 lean_dec_ref(x_2468);
 x_2497 = lean_box(0);
}
if (lean_is_scalar(x_2497)) {
 x_2498 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2498 = x_2497;
}
lean_ctor_set(x_2498, 0, x_2495);
lean_ctor_set(x_2498, 1, x_2496);
return x_2498;
}
}
else
{
lean_object* x_2499; lean_object* x_2500; lean_object* x_2501; lean_object* x_2502; 
lean_dec(x_3);
x_2499 = l_Int_toNat(x_2456);
lean_dec(x_2456);
x_2500 = l_Lean_instToExprInt_mkNat(x_2499);
lean_inc(x_2500);
x_2501 = l_Lean_mkAppB(x_2089, x_2455, x_2500);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2502 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2088);
if (lean_obj_tag(x_2502) == 0)
{
lean_object* x_2503; lean_object* x_2504; lean_object* x_2505; lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; lean_object* x_2510; lean_object* x_2511; 
x_2503 = lean_ctor_get(x_2502, 0);
lean_inc(x_2503);
x_2504 = lean_ctor_get(x_2502, 1);
lean_inc(x_2504);
lean_dec(x_2502);
x_2505 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2506 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2507 = l_Lean_mkNatLit(x_2273);
x_2508 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__32;
x_2509 = l_Lean_reflBoolTrue;
x_2510 = l_Lean_mkApp6(x_2508, x_2503, x_2505, x_2506, x_2507, x_2500, x_2509);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2501);
x_2511 = l_Lean_Meta_mkEq(x_2090, x_2501, x_5, x_6, x_7, x_8, x_2504);
if (lean_obj_tag(x_2511) == 0)
{
lean_object* x_2512; lean_object* x_2513; lean_object* x_2514; 
x_2512 = lean_ctor_get(x_2511, 0);
lean_inc(x_2512);
x_2513 = lean_ctor_get(x_2511, 1);
lean_inc(x_2513);
lean_dec(x_2511);
x_2514 = l_Lean_Meta_mkExpectedTypeHint(x_2510, x_2512, x_5, x_6, x_7, x_8, x_2513);
if (lean_obj_tag(x_2514) == 0)
{
lean_object* x_2515; lean_object* x_2516; lean_object* x_2517; lean_object* x_2518; lean_object* x_2519; lean_object* x_2520; 
x_2515 = lean_ctor_get(x_2514, 0);
lean_inc(x_2515);
x_2516 = lean_ctor_get(x_2514, 1);
lean_inc(x_2516);
if (lean_is_exclusive(x_2514)) {
 lean_ctor_release(x_2514, 0);
 lean_ctor_release(x_2514, 1);
 x_2517 = x_2514;
} else {
 lean_dec_ref(x_2514);
 x_2517 = lean_box(0);
}
x_2518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2518, 0, x_2501);
lean_ctor_set(x_2518, 1, x_2515);
if (lean_is_scalar(x_2454)) {
 x_2519 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2519 = x_2454;
 lean_ctor_set_tag(x_2519, 1);
}
lean_ctor_set(x_2519, 0, x_2518);
if (lean_is_scalar(x_2517)) {
 x_2520 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2520 = x_2517;
}
lean_ctor_set(x_2520, 0, x_2519);
lean_ctor_set(x_2520, 1, x_2516);
return x_2520;
}
else
{
lean_object* x_2521; lean_object* x_2522; lean_object* x_2523; lean_object* x_2524; 
lean_dec(x_2501);
lean_dec(x_2454);
x_2521 = lean_ctor_get(x_2514, 0);
lean_inc(x_2521);
x_2522 = lean_ctor_get(x_2514, 1);
lean_inc(x_2522);
if (lean_is_exclusive(x_2514)) {
 lean_ctor_release(x_2514, 0);
 lean_ctor_release(x_2514, 1);
 x_2523 = x_2514;
} else {
 lean_dec_ref(x_2514);
 x_2523 = lean_box(0);
}
if (lean_is_scalar(x_2523)) {
 x_2524 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2524 = x_2523;
}
lean_ctor_set(x_2524, 0, x_2521);
lean_ctor_set(x_2524, 1, x_2522);
return x_2524;
}
}
else
{
lean_object* x_2525; lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; 
lean_dec(x_2510);
lean_dec(x_2501);
lean_dec(x_2454);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2525 = lean_ctor_get(x_2511, 0);
lean_inc(x_2525);
x_2526 = lean_ctor_get(x_2511, 1);
lean_inc(x_2526);
if (lean_is_exclusive(x_2511)) {
 lean_ctor_release(x_2511, 0);
 lean_ctor_release(x_2511, 1);
 x_2527 = x_2511;
} else {
 lean_dec_ref(x_2511);
 x_2527 = lean_box(0);
}
if (lean_is_scalar(x_2527)) {
 x_2528 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2528 = x_2527;
}
lean_ctor_set(x_2528, 0, x_2525);
lean_ctor_set(x_2528, 1, x_2526);
return x_2528;
}
}
else
{
lean_object* x_2529; lean_object* x_2530; lean_object* x_2531; lean_object* x_2532; 
lean_dec(x_2501);
lean_dec(x_2500);
lean_dec(x_2454);
lean_dec(x_2273);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_2529 = lean_ctor_get(x_2502, 0);
lean_inc(x_2529);
x_2530 = lean_ctor_get(x_2502, 1);
lean_inc(x_2530);
if (lean_is_exclusive(x_2502)) {
 lean_ctor_release(x_2502, 0);
 lean_ctor_release(x_2502, 1);
 x_2531 = x_2502;
} else {
 lean_dec_ref(x_2502);
 x_2531 = lean_box(0);
}
if (lean_is_scalar(x_2531)) {
 x_2532 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2532 = x_2531;
}
lean_ctor_set(x_2532, 0, x_2529);
lean_ctor_set(x_2532, 1, x_2530);
return x_2532;
}
}
}
else
{
lean_object* x_2533; lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; uint8_t x_2537; 
x_2533 = lean_ctor_get(x_2274, 0);
lean_inc(x_2533);
x_2534 = lean_ctor_get(x_2274, 1);
lean_inc(x_2534);
x_2535 = lean_ctor_get(x_2274, 2);
lean_inc(x_2535);
lean_dec(x_2274);
x_2536 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__33;
x_2537 = lean_int_dec_eq(x_2533, x_2536);
lean_dec(x_2533);
if (x_2537 == 0)
{
lean_object* x_2538; lean_object* x_2539; uint8_t x_2540; 
lean_dec(x_2535);
lean_dec(x_2534);
lean_dec(x_2273);
x_2538 = l_Int_Linear_Poly_gcdCoeffs_x27(x_2091);
x_2539 = lean_unsigned_to_nat(1u);
x_2540 = lean_nat_dec_eq(x_2538, x_2539);
if (x_2540 == 0)
{
lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; lean_object* x_2544; uint8_t x_2545; 
x_2541 = l_Int_Linear_Poly_getConst(x_2091);
x_2542 = lean_nat_to_int(x_2538);
x_2543 = lean_int_emod(x_2541, x_2542);
lean_dec(x_2541);
x_2544 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_2545 = lean_int_dec_eq(x_2543, x_2544);
lean_dec(x_2543);
if (x_2545 == 0)
{
lean_object* x_2546; lean_object* x_2547; 
lean_dec(x_2091);
lean_dec(x_11);
x_2546 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2547 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2088);
if (lean_obj_tag(x_2547) == 0)
{
lean_object* x_2548; lean_object* x_2549; lean_object* x_2550; lean_object* x_2551; uint8_t x_2552; lean_object* x_2553; lean_object* x_2554; 
x_2548 = lean_ctor_get(x_2547, 0);
lean_inc(x_2548);
x_2549 = lean_ctor_get(x_2547, 1);
lean_inc(x_2549);
lean_dec(x_2547);
x_2550 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2551 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2552 = lean_int_dec_le(x_2544, x_2542);
x_2553 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2554 = l_Lean_Meta_mkEq(x_2090, x_2553, x_5, x_6, x_7, x_8, x_2549);
if (x_2552 == 0)
{
if (lean_obj_tag(x_2554) == 0)
{
lean_object* x_2555; lean_object* x_2556; lean_object* x_2557; lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; lean_object* x_2561; lean_object* x_2562; lean_object* x_2563; lean_object* x_2564; lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; 
x_2555 = lean_ctor_get(x_2554, 0);
lean_inc(x_2555);
x_2556 = lean_ctor_get(x_2554, 1);
lean_inc(x_2556);
lean_dec(x_2554);
x_2557 = l_Lean_Expr_const___override(x_3, x_2546);
x_2558 = lean_int_neg(x_2542);
lean_dec(x_2542);
x_2559 = l_Int_toNat(x_2558);
lean_dec(x_2558);
x_2560 = l_Lean_instToExprInt_mkNat(x_2559);
x_2561 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_2562 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_2563 = l_Lean_mkApp3(x_2561, x_2557, x_2562, x_2560);
x_2564 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_2565 = l_Lean_reflBoolTrue;
x_2566 = l_Lean_mkApp5(x_2564, x_2548, x_2550, x_2551, x_2563, x_2565);
x_2567 = l_Lean_Meta_mkExpectedTypeHint(x_2566, x_2555, x_5, x_6, x_7, x_8, x_2556);
if (lean_obj_tag(x_2567) == 0)
{
lean_object* x_2568; lean_object* x_2569; lean_object* x_2570; lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; 
x_2568 = lean_ctor_get(x_2567, 0);
lean_inc(x_2568);
x_2569 = lean_ctor_get(x_2567, 1);
lean_inc(x_2569);
if (lean_is_exclusive(x_2567)) {
 lean_ctor_release(x_2567, 0);
 lean_ctor_release(x_2567, 1);
 x_2570 = x_2567;
} else {
 lean_dec_ref(x_2567);
 x_2570 = lean_box(0);
}
x_2571 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2571, 0, x_2553);
lean_ctor_set(x_2571, 1, x_2568);
x_2572 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2572, 0, x_2571);
if (lean_is_scalar(x_2570)) {
 x_2573 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2573 = x_2570;
}
lean_ctor_set(x_2573, 0, x_2572);
lean_ctor_set(x_2573, 1, x_2569);
return x_2573;
}
else
{
lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; 
x_2574 = lean_ctor_get(x_2567, 0);
lean_inc(x_2574);
x_2575 = lean_ctor_get(x_2567, 1);
lean_inc(x_2575);
if (lean_is_exclusive(x_2567)) {
 lean_ctor_release(x_2567, 0);
 lean_ctor_release(x_2567, 1);
 x_2576 = x_2567;
} else {
 lean_dec_ref(x_2567);
 x_2576 = lean_box(0);
}
if (lean_is_scalar(x_2576)) {
 x_2577 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2577 = x_2576;
}
lean_ctor_set(x_2577, 0, x_2574);
lean_ctor_set(x_2577, 1, x_2575);
return x_2577;
}
}
else
{
lean_object* x_2578; lean_object* x_2579; lean_object* x_2580; lean_object* x_2581; 
lean_dec(x_2551);
lean_dec(x_2550);
lean_dec(x_2548);
lean_dec(x_2542);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_2578 = lean_ctor_get(x_2554, 0);
lean_inc(x_2578);
x_2579 = lean_ctor_get(x_2554, 1);
lean_inc(x_2579);
if (lean_is_exclusive(x_2554)) {
 lean_ctor_release(x_2554, 0);
 lean_ctor_release(x_2554, 1);
 x_2580 = x_2554;
} else {
 lean_dec_ref(x_2554);
 x_2580 = lean_box(0);
}
if (lean_is_scalar(x_2580)) {
 x_2581 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2581 = x_2580;
}
lean_ctor_set(x_2581, 0, x_2578);
lean_ctor_set(x_2581, 1, x_2579);
return x_2581;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2554) == 0)
{
lean_object* x_2582; lean_object* x_2583; lean_object* x_2584; lean_object* x_2585; lean_object* x_2586; lean_object* x_2587; lean_object* x_2588; lean_object* x_2589; 
x_2582 = lean_ctor_get(x_2554, 0);
lean_inc(x_2582);
x_2583 = lean_ctor_get(x_2554, 1);
lean_inc(x_2583);
lean_dec(x_2554);
x_2584 = l_Int_toNat(x_2542);
lean_dec(x_2542);
x_2585 = l_Lean_instToExprInt_mkNat(x_2584);
x_2586 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_2587 = l_Lean_reflBoolTrue;
x_2588 = l_Lean_mkApp5(x_2586, x_2548, x_2550, x_2551, x_2585, x_2587);
x_2589 = l_Lean_Meta_mkExpectedTypeHint(x_2588, x_2582, x_5, x_6, x_7, x_8, x_2583);
if (lean_obj_tag(x_2589) == 0)
{
lean_object* x_2590; lean_object* x_2591; lean_object* x_2592; lean_object* x_2593; lean_object* x_2594; lean_object* x_2595; 
x_2590 = lean_ctor_get(x_2589, 0);
lean_inc(x_2590);
x_2591 = lean_ctor_get(x_2589, 1);
lean_inc(x_2591);
if (lean_is_exclusive(x_2589)) {
 lean_ctor_release(x_2589, 0);
 lean_ctor_release(x_2589, 1);
 x_2592 = x_2589;
} else {
 lean_dec_ref(x_2589);
 x_2592 = lean_box(0);
}
x_2593 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2593, 0, x_2553);
lean_ctor_set(x_2593, 1, x_2590);
x_2594 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2594, 0, x_2593);
if (lean_is_scalar(x_2592)) {
 x_2595 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2595 = x_2592;
}
lean_ctor_set(x_2595, 0, x_2594);
lean_ctor_set(x_2595, 1, x_2591);
return x_2595;
}
else
{
lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; lean_object* x_2599; 
x_2596 = lean_ctor_get(x_2589, 0);
lean_inc(x_2596);
x_2597 = lean_ctor_get(x_2589, 1);
lean_inc(x_2597);
if (lean_is_exclusive(x_2589)) {
 lean_ctor_release(x_2589, 0);
 lean_ctor_release(x_2589, 1);
 x_2598 = x_2589;
} else {
 lean_dec_ref(x_2589);
 x_2598 = lean_box(0);
}
if (lean_is_scalar(x_2598)) {
 x_2599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2599 = x_2598;
}
lean_ctor_set(x_2599, 0, x_2596);
lean_ctor_set(x_2599, 1, x_2597);
return x_2599;
}
}
else
{
lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; lean_object* x_2603; 
lean_dec(x_2551);
lean_dec(x_2550);
lean_dec(x_2548);
lean_dec(x_2542);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2600 = lean_ctor_get(x_2554, 0);
lean_inc(x_2600);
x_2601 = lean_ctor_get(x_2554, 1);
lean_inc(x_2601);
if (lean_is_exclusive(x_2554)) {
 lean_ctor_release(x_2554, 0);
 lean_ctor_release(x_2554, 1);
 x_2602 = x_2554;
} else {
 lean_dec_ref(x_2554);
 x_2602 = lean_box(0);
}
if (lean_is_scalar(x_2602)) {
 x_2603 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2603 = x_2602;
}
lean_ctor_set(x_2603, 0, x_2600);
lean_ctor_set(x_2603, 1, x_2601);
return x_2603;
}
}
}
else
{
lean_object* x_2604; lean_object* x_2605; lean_object* x_2606; lean_object* x_2607; 
lean_dec(x_2542);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2604 = lean_ctor_get(x_2547, 0);
lean_inc(x_2604);
x_2605 = lean_ctor_get(x_2547, 1);
lean_inc(x_2605);
if (lean_is_exclusive(x_2547)) {
 lean_ctor_release(x_2547, 0);
 lean_ctor_release(x_2547, 1);
 x_2606 = x_2547;
} else {
 lean_dec_ref(x_2547);
 x_2606 = lean_box(0);
}
if (lean_is_scalar(x_2606)) {
 x_2607 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2607 = x_2606;
}
lean_ctor_set(x_2607, 0, x_2604);
lean_ctor_set(x_2607, 1, x_2605);
return x_2607;
}
}
else
{
lean_object* x_2608; lean_object* x_2609; lean_object* x_2610; lean_object* x_2611; lean_object* x_2612; lean_object* x_2613; lean_object* x_2614; lean_object* x_2615; 
x_2608 = l_Int_Linear_Poly_div(x_2542, x_2091);
lean_inc(x_2608);
x_2609 = l_Int_Linear_Poly_denoteExpr(x_11, x_2608, x_5, x_6, x_7, x_8, x_2088);
x_2610 = lean_ctor_get(x_2609, 0);
lean_inc(x_2610);
x_2611 = lean_ctor_get(x_2609, 1);
lean_inc(x_2611);
if (lean_is_exclusive(x_2609)) {
 lean_ctor_release(x_2609, 0);
 lean_ctor_release(x_2609, 1);
 x_2612 = x_2609;
} else {
 lean_dec_ref(x_2609);
 x_2612 = lean_box(0);
}
x_2613 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_2614 = l_Lean_mkAppB(x_2089, x_2610, x_2613);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2615 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2611);
if (lean_obj_tag(x_2615) == 0)
{
lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; lean_object* x_2620; lean_object* x_2621; uint8_t x_2622; lean_object* x_2623; 
x_2616 = lean_ctor_get(x_2615, 0);
lean_inc(x_2616);
x_2617 = lean_ctor_get(x_2615, 1);
lean_inc(x_2617);
lean_dec(x_2615);
x_2618 = lean_box(0);
x_2619 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2620 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2621 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_2608);
x_2622 = lean_int_dec_le(x_2544, x_2542);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2614);
x_2623 = l_Lean_Meta_mkEq(x_2090, x_2614, x_5, x_6, x_7, x_8, x_2617);
if (x_2622 == 0)
{
if (lean_obj_tag(x_2623) == 0)
{
lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; lean_object* x_2627; lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; lean_object* x_2632; lean_object* x_2633; lean_object* x_2634; lean_object* x_2635; lean_object* x_2636; 
x_2624 = lean_ctor_get(x_2623, 0);
lean_inc(x_2624);
x_2625 = lean_ctor_get(x_2623, 1);
lean_inc(x_2625);
lean_dec(x_2623);
x_2626 = l_Lean_Expr_const___override(x_3, x_2618);
x_2627 = lean_int_neg(x_2542);
lean_dec(x_2542);
x_2628 = l_Int_toNat(x_2627);
lean_dec(x_2627);
x_2629 = l_Lean_instToExprInt_mkNat(x_2628);
x_2630 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_2631 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_2632 = l_Lean_mkApp3(x_2630, x_2626, x_2631, x_2629);
x_2633 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_2634 = l_Lean_reflBoolTrue;
x_2635 = l_Lean_mkApp6(x_2633, x_2616, x_2619, x_2620, x_2621, x_2632, x_2634);
x_2636 = l_Lean_Meta_mkExpectedTypeHint(x_2635, x_2624, x_5, x_6, x_7, x_8, x_2625);
if (lean_obj_tag(x_2636) == 0)
{
lean_object* x_2637; lean_object* x_2638; lean_object* x_2639; lean_object* x_2640; lean_object* x_2641; lean_object* x_2642; 
x_2637 = lean_ctor_get(x_2636, 0);
lean_inc(x_2637);
x_2638 = lean_ctor_get(x_2636, 1);
lean_inc(x_2638);
if (lean_is_exclusive(x_2636)) {
 lean_ctor_release(x_2636, 0);
 lean_ctor_release(x_2636, 1);
 x_2639 = x_2636;
} else {
 lean_dec_ref(x_2636);
 x_2639 = lean_box(0);
}
if (lean_is_scalar(x_2612)) {
 x_2640 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2640 = x_2612;
}
lean_ctor_set(x_2640, 0, x_2614);
lean_ctor_set(x_2640, 1, x_2637);
x_2641 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2641, 0, x_2640);
if (lean_is_scalar(x_2639)) {
 x_2642 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2642 = x_2639;
}
lean_ctor_set(x_2642, 0, x_2641);
lean_ctor_set(x_2642, 1, x_2638);
return x_2642;
}
else
{
lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; lean_object* x_2646; 
lean_dec(x_2614);
lean_dec(x_2612);
x_2643 = lean_ctor_get(x_2636, 0);
lean_inc(x_2643);
x_2644 = lean_ctor_get(x_2636, 1);
lean_inc(x_2644);
if (lean_is_exclusive(x_2636)) {
 lean_ctor_release(x_2636, 0);
 lean_ctor_release(x_2636, 1);
 x_2645 = x_2636;
} else {
 lean_dec_ref(x_2636);
 x_2645 = lean_box(0);
}
if (lean_is_scalar(x_2645)) {
 x_2646 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2646 = x_2645;
}
lean_ctor_set(x_2646, 0, x_2643);
lean_ctor_set(x_2646, 1, x_2644);
return x_2646;
}
}
else
{
lean_object* x_2647; lean_object* x_2648; lean_object* x_2649; lean_object* x_2650; 
lean_dec(x_2621);
lean_dec(x_2620);
lean_dec(x_2619);
lean_dec(x_2616);
lean_dec(x_2614);
lean_dec(x_2612);
lean_dec(x_2542);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_2647 = lean_ctor_get(x_2623, 0);
lean_inc(x_2647);
x_2648 = lean_ctor_get(x_2623, 1);
lean_inc(x_2648);
if (lean_is_exclusive(x_2623)) {
 lean_ctor_release(x_2623, 0);
 lean_ctor_release(x_2623, 1);
 x_2649 = x_2623;
} else {
 lean_dec_ref(x_2623);
 x_2649 = lean_box(0);
}
if (lean_is_scalar(x_2649)) {
 x_2650 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2650 = x_2649;
}
lean_ctor_set(x_2650, 0, x_2647);
lean_ctor_set(x_2650, 1, x_2648);
return x_2650;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2623) == 0)
{
lean_object* x_2651; lean_object* x_2652; lean_object* x_2653; lean_object* x_2654; lean_object* x_2655; lean_object* x_2656; lean_object* x_2657; lean_object* x_2658; 
x_2651 = lean_ctor_get(x_2623, 0);
lean_inc(x_2651);
x_2652 = lean_ctor_get(x_2623, 1);
lean_inc(x_2652);
lean_dec(x_2623);
x_2653 = l_Int_toNat(x_2542);
lean_dec(x_2542);
x_2654 = l_Lean_instToExprInt_mkNat(x_2653);
x_2655 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_2656 = l_Lean_reflBoolTrue;
x_2657 = l_Lean_mkApp6(x_2655, x_2616, x_2619, x_2620, x_2621, x_2654, x_2656);
x_2658 = l_Lean_Meta_mkExpectedTypeHint(x_2657, x_2651, x_5, x_6, x_7, x_8, x_2652);
if (lean_obj_tag(x_2658) == 0)
{
lean_object* x_2659; lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; lean_object* x_2664; 
x_2659 = lean_ctor_get(x_2658, 0);
lean_inc(x_2659);
x_2660 = lean_ctor_get(x_2658, 1);
lean_inc(x_2660);
if (lean_is_exclusive(x_2658)) {
 lean_ctor_release(x_2658, 0);
 lean_ctor_release(x_2658, 1);
 x_2661 = x_2658;
} else {
 lean_dec_ref(x_2658);
 x_2661 = lean_box(0);
}
if (lean_is_scalar(x_2612)) {
 x_2662 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2662 = x_2612;
}
lean_ctor_set(x_2662, 0, x_2614);
lean_ctor_set(x_2662, 1, x_2659);
x_2663 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2663, 0, x_2662);
if (lean_is_scalar(x_2661)) {
 x_2664 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2664 = x_2661;
}
lean_ctor_set(x_2664, 0, x_2663);
lean_ctor_set(x_2664, 1, x_2660);
return x_2664;
}
else
{
lean_object* x_2665; lean_object* x_2666; lean_object* x_2667; lean_object* x_2668; 
lean_dec(x_2614);
lean_dec(x_2612);
x_2665 = lean_ctor_get(x_2658, 0);
lean_inc(x_2665);
x_2666 = lean_ctor_get(x_2658, 1);
lean_inc(x_2666);
if (lean_is_exclusive(x_2658)) {
 lean_ctor_release(x_2658, 0);
 lean_ctor_release(x_2658, 1);
 x_2667 = x_2658;
} else {
 lean_dec_ref(x_2658);
 x_2667 = lean_box(0);
}
if (lean_is_scalar(x_2667)) {
 x_2668 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2668 = x_2667;
}
lean_ctor_set(x_2668, 0, x_2665);
lean_ctor_set(x_2668, 1, x_2666);
return x_2668;
}
}
else
{
lean_object* x_2669; lean_object* x_2670; lean_object* x_2671; lean_object* x_2672; 
lean_dec(x_2621);
lean_dec(x_2620);
lean_dec(x_2619);
lean_dec(x_2616);
lean_dec(x_2614);
lean_dec(x_2612);
lean_dec(x_2542);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2669 = lean_ctor_get(x_2623, 0);
lean_inc(x_2669);
x_2670 = lean_ctor_get(x_2623, 1);
lean_inc(x_2670);
if (lean_is_exclusive(x_2623)) {
 lean_ctor_release(x_2623, 0);
 lean_ctor_release(x_2623, 1);
 x_2671 = x_2623;
} else {
 lean_dec_ref(x_2623);
 x_2671 = lean_box(0);
}
if (lean_is_scalar(x_2671)) {
 x_2672 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2672 = x_2671;
}
lean_ctor_set(x_2672, 0, x_2669);
lean_ctor_set(x_2672, 1, x_2670);
return x_2672;
}
}
}
else
{
lean_object* x_2673; lean_object* x_2674; lean_object* x_2675; lean_object* x_2676; 
lean_dec(x_2614);
lean_dec(x_2612);
lean_dec(x_2608);
lean_dec(x_2542);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2673 = lean_ctor_get(x_2615, 0);
lean_inc(x_2673);
x_2674 = lean_ctor_get(x_2615, 1);
lean_inc(x_2674);
if (lean_is_exclusive(x_2615)) {
 lean_ctor_release(x_2615, 0);
 lean_ctor_release(x_2615, 1);
 x_2675 = x_2615;
} else {
 lean_dec_ref(x_2615);
 x_2675 = lean_box(0);
}
if (lean_is_scalar(x_2675)) {
 x_2676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2676 = x_2675;
}
lean_ctor_set(x_2676, 0, x_2673);
lean_ctor_set(x_2676, 1, x_2674);
return x_2676;
}
}
}
else
{
lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; lean_object* x_2681; lean_object* x_2682; lean_object* x_2683; 
lean_dec(x_2538);
lean_dec(x_3);
lean_inc(x_2091);
x_2677 = l_Int_Linear_Poly_denoteExpr(x_11, x_2091, x_5, x_6, x_7, x_8, x_2088);
x_2678 = lean_ctor_get(x_2677, 0);
lean_inc(x_2678);
x_2679 = lean_ctor_get(x_2677, 1);
lean_inc(x_2679);
if (lean_is_exclusive(x_2677)) {
 lean_ctor_release(x_2677, 0);
 lean_ctor_release(x_2677, 1);
 x_2680 = x_2677;
} else {
 lean_dec_ref(x_2677);
 x_2680 = lean_box(0);
}
x_2681 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_2682 = l_Lean_mkAppB(x_2089, x_2678, x_2681);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2683 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2679);
if (lean_obj_tag(x_2683) == 0)
{
lean_object* x_2684; lean_object* x_2685; lean_object* x_2686; lean_object* x_2687; lean_object* x_2688; lean_object* x_2689; lean_object* x_2690; lean_object* x_2691; lean_object* x_2692; 
x_2684 = lean_ctor_get(x_2683, 0);
lean_inc(x_2684);
x_2685 = lean_ctor_get(x_2683, 1);
lean_inc(x_2685);
lean_dec(x_2683);
x_2686 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2687 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2688 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_2091);
x_2689 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_2690 = l_Lean_reflBoolTrue;
x_2691 = l_Lean_mkApp5(x_2689, x_2684, x_2686, x_2687, x_2688, x_2690);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2682);
x_2692 = l_Lean_Meta_mkEq(x_2090, x_2682, x_5, x_6, x_7, x_8, x_2685);
if (lean_obj_tag(x_2692) == 0)
{
lean_object* x_2693; lean_object* x_2694; lean_object* x_2695; 
x_2693 = lean_ctor_get(x_2692, 0);
lean_inc(x_2693);
x_2694 = lean_ctor_get(x_2692, 1);
lean_inc(x_2694);
lean_dec(x_2692);
x_2695 = l_Lean_Meta_mkExpectedTypeHint(x_2691, x_2693, x_5, x_6, x_7, x_8, x_2694);
if (lean_obj_tag(x_2695) == 0)
{
lean_object* x_2696; lean_object* x_2697; lean_object* x_2698; lean_object* x_2699; lean_object* x_2700; lean_object* x_2701; 
x_2696 = lean_ctor_get(x_2695, 0);
lean_inc(x_2696);
x_2697 = lean_ctor_get(x_2695, 1);
lean_inc(x_2697);
if (lean_is_exclusive(x_2695)) {
 lean_ctor_release(x_2695, 0);
 lean_ctor_release(x_2695, 1);
 x_2698 = x_2695;
} else {
 lean_dec_ref(x_2695);
 x_2698 = lean_box(0);
}
if (lean_is_scalar(x_2680)) {
 x_2699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2699 = x_2680;
}
lean_ctor_set(x_2699, 0, x_2682);
lean_ctor_set(x_2699, 1, x_2696);
x_2700 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2700, 0, x_2699);
if (lean_is_scalar(x_2698)) {
 x_2701 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2701 = x_2698;
}
lean_ctor_set(x_2701, 0, x_2700);
lean_ctor_set(x_2701, 1, x_2697);
return x_2701;
}
else
{
lean_object* x_2702; lean_object* x_2703; lean_object* x_2704; lean_object* x_2705; 
lean_dec(x_2682);
lean_dec(x_2680);
x_2702 = lean_ctor_get(x_2695, 0);
lean_inc(x_2702);
x_2703 = lean_ctor_get(x_2695, 1);
lean_inc(x_2703);
if (lean_is_exclusive(x_2695)) {
 lean_ctor_release(x_2695, 0);
 lean_ctor_release(x_2695, 1);
 x_2704 = x_2695;
} else {
 lean_dec_ref(x_2695);
 x_2704 = lean_box(0);
}
if (lean_is_scalar(x_2704)) {
 x_2705 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2705 = x_2704;
}
lean_ctor_set(x_2705, 0, x_2702);
lean_ctor_set(x_2705, 1, x_2703);
return x_2705;
}
}
else
{
lean_object* x_2706; lean_object* x_2707; lean_object* x_2708; lean_object* x_2709; 
lean_dec(x_2691);
lean_dec(x_2682);
lean_dec(x_2680);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2706 = lean_ctor_get(x_2692, 0);
lean_inc(x_2706);
x_2707 = lean_ctor_get(x_2692, 1);
lean_inc(x_2707);
if (lean_is_exclusive(x_2692)) {
 lean_ctor_release(x_2692, 0);
 lean_ctor_release(x_2692, 1);
 x_2708 = x_2692;
} else {
 lean_dec_ref(x_2692);
 x_2708 = lean_box(0);
}
if (lean_is_scalar(x_2708)) {
 x_2709 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2709 = x_2708;
}
lean_ctor_set(x_2709, 0, x_2706);
lean_ctor_set(x_2709, 1, x_2707);
return x_2709;
}
}
else
{
lean_object* x_2710; lean_object* x_2711; lean_object* x_2712; lean_object* x_2713; 
lean_dec(x_2682);
lean_dec(x_2680);
lean_dec(x_2091);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_2710 = lean_ctor_get(x_2683, 0);
lean_inc(x_2710);
x_2711 = lean_ctor_get(x_2683, 1);
lean_inc(x_2711);
if (lean_is_exclusive(x_2683)) {
 lean_ctor_release(x_2683, 0);
 lean_ctor_release(x_2683, 1);
 x_2712 = x_2683;
} else {
 lean_dec_ref(x_2683);
 x_2712 = lean_box(0);
}
if (lean_is_scalar(x_2712)) {
 x_2713 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2713 = x_2712;
}
lean_ctor_set(x_2713, 0, x_2710);
lean_ctor_set(x_2713, 1, x_2711);
return x_2713;
}
}
}
else
{
if (lean_obj_tag(x_2535) == 0)
{
lean_object* x_2714; lean_object* x_2715; lean_object* x_2716; uint8_t x_2717; 
x_2714 = lean_ctor_get(x_2535, 0);
lean_inc(x_2714);
if (lean_is_exclusive(x_2535)) {
 lean_ctor_release(x_2535, 0);
 x_2715 = x_2535;
} else {
 lean_dec_ref(x_2535);
 x_2715 = lean_box(0);
}
x_2716 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_2717 = lean_int_dec_eq(x_2714, x_2716);
lean_dec(x_2714);
if (x_2717 == 0)
{
lean_object* x_2718; lean_object* x_2719; uint8_t x_2720; 
lean_dec(x_2534);
lean_dec(x_2273);
x_2718 = l_Int_Linear_Poly_gcdCoeffs_x27(x_2091);
x_2719 = lean_unsigned_to_nat(1u);
x_2720 = lean_nat_dec_eq(x_2718, x_2719);
if (x_2720 == 0)
{
lean_object* x_2721; lean_object* x_2722; lean_object* x_2723; uint8_t x_2724; 
x_2721 = l_Int_Linear_Poly_getConst(x_2091);
x_2722 = lean_nat_to_int(x_2718);
x_2723 = lean_int_emod(x_2721, x_2722);
lean_dec(x_2721);
x_2724 = lean_int_dec_eq(x_2723, x_2716);
lean_dec(x_2723);
if (x_2724 == 0)
{
lean_object* x_2725; lean_object* x_2726; 
lean_dec(x_2091);
lean_dec(x_11);
x_2725 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2726 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2088);
if (lean_obj_tag(x_2726) == 0)
{
lean_object* x_2727; lean_object* x_2728; lean_object* x_2729; lean_object* x_2730; uint8_t x_2731; lean_object* x_2732; lean_object* x_2733; 
x_2727 = lean_ctor_get(x_2726, 0);
lean_inc(x_2727);
x_2728 = lean_ctor_get(x_2726, 1);
lean_inc(x_2728);
lean_dec(x_2726);
x_2729 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2730 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2731 = lean_int_dec_le(x_2716, x_2722);
x_2732 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2733 = l_Lean_Meta_mkEq(x_2090, x_2732, x_5, x_6, x_7, x_8, x_2728);
if (x_2731 == 0)
{
if (lean_obj_tag(x_2733) == 0)
{
lean_object* x_2734; lean_object* x_2735; lean_object* x_2736; lean_object* x_2737; lean_object* x_2738; lean_object* x_2739; lean_object* x_2740; lean_object* x_2741; lean_object* x_2742; lean_object* x_2743; lean_object* x_2744; lean_object* x_2745; lean_object* x_2746; 
x_2734 = lean_ctor_get(x_2733, 0);
lean_inc(x_2734);
x_2735 = lean_ctor_get(x_2733, 1);
lean_inc(x_2735);
lean_dec(x_2733);
x_2736 = l_Lean_Expr_const___override(x_3, x_2725);
x_2737 = lean_int_neg(x_2722);
lean_dec(x_2722);
x_2738 = l_Int_toNat(x_2737);
lean_dec(x_2737);
x_2739 = l_Lean_instToExprInt_mkNat(x_2738);
x_2740 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_2741 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_2742 = l_Lean_mkApp3(x_2740, x_2736, x_2741, x_2739);
x_2743 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_2744 = l_Lean_reflBoolTrue;
x_2745 = l_Lean_mkApp5(x_2743, x_2727, x_2729, x_2730, x_2742, x_2744);
x_2746 = l_Lean_Meta_mkExpectedTypeHint(x_2745, x_2734, x_5, x_6, x_7, x_8, x_2735);
if (lean_obj_tag(x_2746) == 0)
{
lean_object* x_2747; lean_object* x_2748; lean_object* x_2749; lean_object* x_2750; lean_object* x_2751; lean_object* x_2752; 
x_2747 = lean_ctor_get(x_2746, 0);
lean_inc(x_2747);
x_2748 = lean_ctor_get(x_2746, 1);
lean_inc(x_2748);
if (lean_is_exclusive(x_2746)) {
 lean_ctor_release(x_2746, 0);
 lean_ctor_release(x_2746, 1);
 x_2749 = x_2746;
} else {
 lean_dec_ref(x_2746);
 x_2749 = lean_box(0);
}
x_2750 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2750, 0, x_2732);
lean_ctor_set(x_2750, 1, x_2747);
if (lean_is_scalar(x_2715)) {
 x_2751 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2751 = x_2715;
 lean_ctor_set_tag(x_2751, 1);
}
lean_ctor_set(x_2751, 0, x_2750);
if (lean_is_scalar(x_2749)) {
 x_2752 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2752 = x_2749;
}
lean_ctor_set(x_2752, 0, x_2751);
lean_ctor_set(x_2752, 1, x_2748);
return x_2752;
}
else
{
lean_object* x_2753; lean_object* x_2754; lean_object* x_2755; lean_object* x_2756; 
lean_dec(x_2715);
x_2753 = lean_ctor_get(x_2746, 0);
lean_inc(x_2753);
x_2754 = lean_ctor_get(x_2746, 1);
lean_inc(x_2754);
if (lean_is_exclusive(x_2746)) {
 lean_ctor_release(x_2746, 0);
 lean_ctor_release(x_2746, 1);
 x_2755 = x_2746;
} else {
 lean_dec_ref(x_2746);
 x_2755 = lean_box(0);
}
if (lean_is_scalar(x_2755)) {
 x_2756 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2756 = x_2755;
}
lean_ctor_set(x_2756, 0, x_2753);
lean_ctor_set(x_2756, 1, x_2754);
return x_2756;
}
}
else
{
lean_object* x_2757; lean_object* x_2758; lean_object* x_2759; lean_object* x_2760; 
lean_dec(x_2730);
lean_dec(x_2729);
lean_dec(x_2727);
lean_dec(x_2722);
lean_dec(x_2715);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_2757 = lean_ctor_get(x_2733, 0);
lean_inc(x_2757);
x_2758 = lean_ctor_get(x_2733, 1);
lean_inc(x_2758);
if (lean_is_exclusive(x_2733)) {
 lean_ctor_release(x_2733, 0);
 lean_ctor_release(x_2733, 1);
 x_2759 = x_2733;
} else {
 lean_dec_ref(x_2733);
 x_2759 = lean_box(0);
}
if (lean_is_scalar(x_2759)) {
 x_2760 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2760 = x_2759;
}
lean_ctor_set(x_2760, 0, x_2757);
lean_ctor_set(x_2760, 1, x_2758);
return x_2760;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2733) == 0)
{
lean_object* x_2761; lean_object* x_2762; lean_object* x_2763; lean_object* x_2764; lean_object* x_2765; lean_object* x_2766; lean_object* x_2767; lean_object* x_2768; 
x_2761 = lean_ctor_get(x_2733, 0);
lean_inc(x_2761);
x_2762 = lean_ctor_get(x_2733, 1);
lean_inc(x_2762);
lean_dec(x_2733);
x_2763 = l_Int_toNat(x_2722);
lean_dec(x_2722);
x_2764 = l_Lean_instToExprInt_mkNat(x_2763);
x_2765 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_2766 = l_Lean_reflBoolTrue;
x_2767 = l_Lean_mkApp5(x_2765, x_2727, x_2729, x_2730, x_2764, x_2766);
x_2768 = l_Lean_Meta_mkExpectedTypeHint(x_2767, x_2761, x_5, x_6, x_7, x_8, x_2762);
if (lean_obj_tag(x_2768) == 0)
{
lean_object* x_2769; lean_object* x_2770; lean_object* x_2771; lean_object* x_2772; lean_object* x_2773; lean_object* x_2774; 
x_2769 = lean_ctor_get(x_2768, 0);
lean_inc(x_2769);
x_2770 = lean_ctor_get(x_2768, 1);
lean_inc(x_2770);
if (lean_is_exclusive(x_2768)) {
 lean_ctor_release(x_2768, 0);
 lean_ctor_release(x_2768, 1);
 x_2771 = x_2768;
} else {
 lean_dec_ref(x_2768);
 x_2771 = lean_box(0);
}
x_2772 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2772, 0, x_2732);
lean_ctor_set(x_2772, 1, x_2769);
if (lean_is_scalar(x_2715)) {
 x_2773 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2773 = x_2715;
 lean_ctor_set_tag(x_2773, 1);
}
lean_ctor_set(x_2773, 0, x_2772);
if (lean_is_scalar(x_2771)) {
 x_2774 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2774 = x_2771;
}
lean_ctor_set(x_2774, 0, x_2773);
lean_ctor_set(x_2774, 1, x_2770);
return x_2774;
}
else
{
lean_object* x_2775; lean_object* x_2776; lean_object* x_2777; lean_object* x_2778; 
lean_dec(x_2715);
x_2775 = lean_ctor_get(x_2768, 0);
lean_inc(x_2775);
x_2776 = lean_ctor_get(x_2768, 1);
lean_inc(x_2776);
if (lean_is_exclusive(x_2768)) {
 lean_ctor_release(x_2768, 0);
 lean_ctor_release(x_2768, 1);
 x_2777 = x_2768;
} else {
 lean_dec_ref(x_2768);
 x_2777 = lean_box(0);
}
if (lean_is_scalar(x_2777)) {
 x_2778 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2778 = x_2777;
}
lean_ctor_set(x_2778, 0, x_2775);
lean_ctor_set(x_2778, 1, x_2776);
return x_2778;
}
}
else
{
lean_object* x_2779; lean_object* x_2780; lean_object* x_2781; lean_object* x_2782; 
lean_dec(x_2730);
lean_dec(x_2729);
lean_dec(x_2727);
lean_dec(x_2722);
lean_dec(x_2715);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2779 = lean_ctor_get(x_2733, 0);
lean_inc(x_2779);
x_2780 = lean_ctor_get(x_2733, 1);
lean_inc(x_2780);
if (lean_is_exclusive(x_2733)) {
 lean_ctor_release(x_2733, 0);
 lean_ctor_release(x_2733, 1);
 x_2781 = x_2733;
} else {
 lean_dec_ref(x_2733);
 x_2781 = lean_box(0);
}
if (lean_is_scalar(x_2781)) {
 x_2782 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2782 = x_2781;
}
lean_ctor_set(x_2782, 0, x_2779);
lean_ctor_set(x_2782, 1, x_2780);
return x_2782;
}
}
}
else
{
lean_object* x_2783; lean_object* x_2784; lean_object* x_2785; lean_object* x_2786; 
lean_dec(x_2722);
lean_dec(x_2715);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2783 = lean_ctor_get(x_2726, 0);
lean_inc(x_2783);
x_2784 = lean_ctor_get(x_2726, 1);
lean_inc(x_2784);
if (lean_is_exclusive(x_2726)) {
 lean_ctor_release(x_2726, 0);
 lean_ctor_release(x_2726, 1);
 x_2785 = x_2726;
} else {
 lean_dec_ref(x_2726);
 x_2785 = lean_box(0);
}
if (lean_is_scalar(x_2785)) {
 x_2786 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2786 = x_2785;
}
lean_ctor_set(x_2786, 0, x_2783);
lean_ctor_set(x_2786, 1, x_2784);
return x_2786;
}
}
else
{
lean_object* x_2787; lean_object* x_2788; lean_object* x_2789; lean_object* x_2790; lean_object* x_2791; lean_object* x_2792; lean_object* x_2793; lean_object* x_2794; 
x_2787 = l_Int_Linear_Poly_div(x_2722, x_2091);
lean_inc(x_2787);
x_2788 = l_Int_Linear_Poly_denoteExpr(x_11, x_2787, x_5, x_6, x_7, x_8, x_2088);
x_2789 = lean_ctor_get(x_2788, 0);
lean_inc(x_2789);
x_2790 = lean_ctor_get(x_2788, 1);
lean_inc(x_2790);
if (lean_is_exclusive(x_2788)) {
 lean_ctor_release(x_2788, 0);
 lean_ctor_release(x_2788, 1);
 x_2791 = x_2788;
} else {
 lean_dec_ref(x_2788);
 x_2791 = lean_box(0);
}
x_2792 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_2793 = l_Lean_mkAppB(x_2089, x_2789, x_2792);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2794 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2790);
if (lean_obj_tag(x_2794) == 0)
{
lean_object* x_2795; lean_object* x_2796; lean_object* x_2797; lean_object* x_2798; lean_object* x_2799; lean_object* x_2800; uint8_t x_2801; lean_object* x_2802; 
x_2795 = lean_ctor_get(x_2794, 0);
lean_inc(x_2795);
x_2796 = lean_ctor_get(x_2794, 1);
lean_inc(x_2796);
lean_dec(x_2794);
x_2797 = lean_box(0);
x_2798 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2799 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2800 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_2787);
x_2801 = lean_int_dec_le(x_2716, x_2722);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2793);
x_2802 = l_Lean_Meta_mkEq(x_2090, x_2793, x_5, x_6, x_7, x_8, x_2796);
if (x_2801 == 0)
{
if (lean_obj_tag(x_2802) == 0)
{
lean_object* x_2803; lean_object* x_2804; lean_object* x_2805; lean_object* x_2806; lean_object* x_2807; lean_object* x_2808; lean_object* x_2809; lean_object* x_2810; lean_object* x_2811; lean_object* x_2812; lean_object* x_2813; lean_object* x_2814; lean_object* x_2815; 
x_2803 = lean_ctor_get(x_2802, 0);
lean_inc(x_2803);
x_2804 = lean_ctor_get(x_2802, 1);
lean_inc(x_2804);
lean_dec(x_2802);
x_2805 = l_Lean_Expr_const___override(x_3, x_2797);
x_2806 = lean_int_neg(x_2722);
lean_dec(x_2722);
x_2807 = l_Int_toNat(x_2806);
lean_dec(x_2806);
x_2808 = l_Lean_instToExprInt_mkNat(x_2807);
x_2809 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_2810 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_2811 = l_Lean_mkApp3(x_2809, x_2805, x_2810, x_2808);
x_2812 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_2813 = l_Lean_reflBoolTrue;
x_2814 = l_Lean_mkApp6(x_2812, x_2795, x_2798, x_2799, x_2800, x_2811, x_2813);
x_2815 = l_Lean_Meta_mkExpectedTypeHint(x_2814, x_2803, x_5, x_6, x_7, x_8, x_2804);
if (lean_obj_tag(x_2815) == 0)
{
lean_object* x_2816; lean_object* x_2817; lean_object* x_2818; lean_object* x_2819; lean_object* x_2820; lean_object* x_2821; 
x_2816 = lean_ctor_get(x_2815, 0);
lean_inc(x_2816);
x_2817 = lean_ctor_get(x_2815, 1);
lean_inc(x_2817);
if (lean_is_exclusive(x_2815)) {
 lean_ctor_release(x_2815, 0);
 lean_ctor_release(x_2815, 1);
 x_2818 = x_2815;
} else {
 lean_dec_ref(x_2815);
 x_2818 = lean_box(0);
}
if (lean_is_scalar(x_2791)) {
 x_2819 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2819 = x_2791;
}
lean_ctor_set(x_2819, 0, x_2793);
lean_ctor_set(x_2819, 1, x_2816);
if (lean_is_scalar(x_2715)) {
 x_2820 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2820 = x_2715;
 lean_ctor_set_tag(x_2820, 1);
}
lean_ctor_set(x_2820, 0, x_2819);
if (lean_is_scalar(x_2818)) {
 x_2821 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2821 = x_2818;
}
lean_ctor_set(x_2821, 0, x_2820);
lean_ctor_set(x_2821, 1, x_2817);
return x_2821;
}
else
{
lean_object* x_2822; lean_object* x_2823; lean_object* x_2824; lean_object* x_2825; 
lean_dec(x_2793);
lean_dec(x_2791);
lean_dec(x_2715);
x_2822 = lean_ctor_get(x_2815, 0);
lean_inc(x_2822);
x_2823 = lean_ctor_get(x_2815, 1);
lean_inc(x_2823);
if (lean_is_exclusive(x_2815)) {
 lean_ctor_release(x_2815, 0);
 lean_ctor_release(x_2815, 1);
 x_2824 = x_2815;
} else {
 lean_dec_ref(x_2815);
 x_2824 = lean_box(0);
}
if (lean_is_scalar(x_2824)) {
 x_2825 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2825 = x_2824;
}
lean_ctor_set(x_2825, 0, x_2822);
lean_ctor_set(x_2825, 1, x_2823);
return x_2825;
}
}
else
{
lean_object* x_2826; lean_object* x_2827; lean_object* x_2828; lean_object* x_2829; 
lean_dec(x_2800);
lean_dec(x_2799);
lean_dec(x_2798);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2791);
lean_dec(x_2722);
lean_dec(x_2715);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_2826 = lean_ctor_get(x_2802, 0);
lean_inc(x_2826);
x_2827 = lean_ctor_get(x_2802, 1);
lean_inc(x_2827);
if (lean_is_exclusive(x_2802)) {
 lean_ctor_release(x_2802, 0);
 lean_ctor_release(x_2802, 1);
 x_2828 = x_2802;
} else {
 lean_dec_ref(x_2802);
 x_2828 = lean_box(0);
}
if (lean_is_scalar(x_2828)) {
 x_2829 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2829 = x_2828;
}
lean_ctor_set(x_2829, 0, x_2826);
lean_ctor_set(x_2829, 1, x_2827);
return x_2829;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2802) == 0)
{
lean_object* x_2830; lean_object* x_2831; lean_object* x_2832; lean_object* x_2833; lean_object* x_2834; lean_object* x_2835; lean_object* x_2836; lean_object* x_2837; 
x_2830 = lean_ctor_get(x_2802, 0);
lean_inc(x_2830);
x_2831 = lean_ctor_get(x_2802, 1);
lean_inc(x_2831);
lean_dec(x_2802);
x_2832 = l_Int_toNat(x_2722);
lean_dec(x_2722);
x_2833 = l_Lean_instToExprInt_mkNat(x_2832);
x_2834 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_2835 = l_Lean_reflBoolTrue;
x_2836 = l_Lean_mkApp6(x_2834, x_2795, x_2798, x_2799, x_2800, x_2833, x_2835);
x_2837 = l_Lean_Meta_mkExpectedTypeHint(x_2836, x_2830, x_5, x_6, x_7, x_8, x_2831);
if (lean_obj_tag(x_2837) == 0)
{
lean_object* x_2838; lean_object* x_2839; lean_object* x_2840; lean_object* x_2841; lean_object* x_2842; lean_object* x_2843; 
x_2838 = lean_ctor_get(x_2837, 0);
lean_inc(x_2838);
x_2839 = lean_ctor_get(x_2837, 1);
lean_inc(x_2839);
if (lean_is_exclusive(x_2837)) {
 lean_ctor_release(x_2837, 0);
 lean_ctor_release(x_2837, 1);
 x_2840 = x_2837;
} else {
 lean_dec_ref(x_2837);
 x_2840 = lean_box(0);
}
if (lean_is_scalar(x_2791)) {
 x_2841 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2841 = x_2791;
}
lean_ctor_set(x_2841, 0, x_2793);
lean_ctor_set(x_2841, 1, x_2838);
if (lean_is_scalar(x_2715)) {
 x_2842 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2842 = x_2715;
 lean_ctor_set_tag(x_2842, 1);
}
lean_ctor_set(x_2842, 0, x_2841);
if (lean_is_scalar(x_2840)) {
 x_2843 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2843 = x_2840;
}
lean_ctor_set(x_2843, 0, x_2842);
lean_ctor_set(x_2843, 1, x_2839);
return x_2843;
}
else
{
lean_object* x_2844; lean_object* x_2845; lean_object* x_2846; lean_object* x_2847; 
lean_dec(x_2793);
lean_dec(x_2791);
lean_dec(x_2715);
x_2844 = lean_ctor_get(x_2837, 0);
lean_inc(x_2844);
x_2845 = lean_ctor_get(x_2837, 1);
lean_inc(x_2845);
if (lean_is_exclusive(x_2837)) {
 lean_ctor_release(x_2837, 0);
 lean_ctor_release(x_2837, 1);
 x_2846 = x_2837;
} else {
 lean_dec_ref(x_2837);
 x_2846 = lean_box(0);
}
if (lean_is_scalar(x_2846)) {
 x_2847 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2847 = x_2846;
}
lean_ctor_set(x_2847, 0, x_2844);
lean_ctor_set(x_2847, 1, x_2845);
return x_2847;
}
}
else
{
lean_object* x_2848; lean_object* x_2849; lean_object* x_2850; lean_object* x_2851; 
lean_dec(x_2800);
lean_dec(x_2799);
lean_dec(x_2798);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2791);
lean_dec(x_2722);
lean_dec(x_2715);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2848 = lean_ctor_get(x_2802, 0);
lean_inc(x_2848);
x_2849 = lean_ctor_get(x_2802, 1);
lean_inc(x_2849);
if (lean_is_exclusive(x_2802)) {
 lean_ctor_release(x_2802, 0);
 lean_ctor_release(x_2802, 1);
 x_2850 = x_2802;
} else {
 lean_dec_ref(x_2802);
 x_2850 = lean_box(0);
}
if (lean_is_scalar(x_2850)) {
 x_2851 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2851 = x_2850;
}
lean_ctor_set(x_2851, 0, x_2848);
lean_ctor_set(x_2851, 1, x_2849);
return x_2851;
}
}
}
else
{
lean_object* x_2852; lean_object* x_2853; lean_object* x_2854; lean_object* x_2855; 
lean_dec(x_2793);
lean_dec(x_2791);
lean_dec(x_2787);
lean_dec(x_2722);
lean_dec(x_2715);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2852 = lean_ctor_get(x_2794, 0);
lean_inc(x_2852);
x_2853 = lean_ctor_get(x_2794, 1);
lean_inc(x_2853);
if (lean_is_exclusive(x_2794)) {
 lean_ctor_release(x_2794, 0);
 lean_ctor_release(x_2794, 1);
 x_2854 = x_2794;
} else {
 lean_dec_ref(x_2794);
 x_2854 = lean_box(0);
}
if (lean_is_scalar(x_2854)) {
 x_2855 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2855 = x_2854;
}
lean_ctor_set(x_2855, 0, x_2852);
lean_ctor_set(x_2855, 1, x_2853);
return x_2855;
}
}
}
else
{
lean_object* x_2856; lean_object* x_2857; lean_object* x_2858; lean_object* x_2859; lean_object* x_2860; lean_object* x_2861; lean_object* x_2862; 
lean_dec(x_2718);
lean_dec(x_3);
lean_inc(x_2091);
x_2856 = l_Int_Linear_Poly_denoteExpr(x_11, x_2091, x_5, x_6, x_7, x_8, x_2088);
x_2857 = lean_ctor_get(x_2856, 0);
lean_inc(x_2857);
x_2858 = lean_ctor_get(x_2856, 1);
lean_inc(x_2858);
if (lean_is_exclusive(x_2856)) {
 lean_ctor_release(x_2856, 0);
 lean_ctor_release(x_2856, 1);
 x_2859 = x_2856;
} else {
 lean_dec_ref(x_2856);
 x_2859 = lean_box(0);
}
x_2860 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_2861 = l_Lean_mkAppB(x_2089, x_2857, x_2860);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2862 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2858);
if (lean_obj_tag(x_2862) == 0)
{
lean_object* x_2863; lean_object* x_2864; lean_object* x_2865; lean_object* x_2866; lean_object* x_2867; lean_object* x_2868; lean_object* x_2869; lean_object* x_2870; lean_object* x_2871; 
x_2863 = lean_ctor_get(x_2862, 0);
lean_inc(x_2863);
x_2864 = lean_ctor_get(x_2862, 1);
lean_inc(x_2864);
lean_dec(x_2862);
x_2865 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2866 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2867 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_2091);
x_2868 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_2869 = l_Lean_reflBoolTrue;
x_2870 = l_Lean_mkApp5(x_2868, x_2863, x_2865, x_2866, x_2867, x_2869);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2861);
x_2871 = l_Lean_Meta_mkEq(x_2090, x_2861, x_5, x_6, x_7, x_8, x_2864);
if (lean_obj_tag(x_2871) == 0)
{
lean_object* x_2872; lean_object* x_2873; lean_object* x_2874; 
x_2872 = lean_ctor_get(x_2871, 0);
lean_inc(x_2872);
x_2873 = lean_ctor_get(x_2871, 1);
lean_inc(x_2873);
lean_dec(x_2871);
x_2874 = l_Lean_Meta_mkExpectedTypeHint(x_2870, x_2872, x_5, x_6, x_7, x_8, x_2873);
if (lean_obj_tag(x_2874) == 0)
{
lean_object* x_2875; lean_object* x_2876; lean_object* x_2877; lean_object* x_2878; lean_object* x_2879; lean_object* x_2880; 
x_2875 = lean_ctor_get(x_2874, 0);
lean_inc(x_2875);
x_2876 = lean_ctor_get(x_2874, 1);
lean_inc(x_2876);
if (lean_is_exclusive(x_2874)) {
 lean_ctor_release(x_2874, 0);
 lean_ctor_release(x_2874, 1);
 x_2877 = x_2874;
} else {
 lean_dec_ref(x_2874);
 x_2877 = lean_box(0);
}
if (lean_is_scalar(x_2859)) {
 x_2878 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2878 = x_2859;
}
lean_ctor_set(x_2878, 0, x_2861);
lean_ctor_set(x_2878, 1, x_2875);
if (lean_is_scalar(x_2715)) {
 x_2879 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2879 = x_2715;
 lean_ctor_set_tag(x_2879, 1);
}
lean_ctor_set(x_2879, 0, x_2878);
if (lean_is_scalar(x_2877)) {
 x_2880 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2880 = x_2877;
}
lean_ctor_set(x_2880, 0, x_2879);
lean_ctor_set(x_2880, 1, x_2876);
return x_2880;
}
else
{
lean_object* x_2881; lean_object* x_2882; lean_object* x_2883; lean_object* x_2884; 
lean_dec(x_2861);
lean_dec(x_2859);
lean_dec(x_2715);
x_2881 = lean_ctor_get(x_2874, 0);
lean_inc(x_2881);
x_2882 = lean_ctor_get(x_2874, 1);
lean_inc(x_2882);
if (lean_is_exclusive(x_2874)) {
 lean_ctor_release(x_2874, 0);
 lean_ctor_release(x_2874, 1);
 x_2883 = x_2874;
} else {
 lean_dec_ref(x_2874);
 x_2883 = lean_box(0);
}
if (lean_is_scalar(x_2883)) {
 x_2884 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2884 = x_2883;
}
lean_ctor_set(x_2884, 0, x_2881);
lean_ctor_set(x_2884, 1, x_2882);
return x_2884;
}
}
else
{
lean_object* x_2885; lean_object* x_2886; lean_object* x_2887; lean_object* x_2888; 
lean_dec(x_2870);
lean_dec(x_2861);
lean_dec(x_2859);
lean_dec(x_2715);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2885 = lean_ctor_get(x_2871, 0);
lean_inc(x_2885);
x_2886 = lean_ctor_get(x_2871, 1);
lean_inc(x_2886);
if (lean_is_exclusive(x_2871)) {
 lean_ctor_release(x_2871, 0);
 lean_ctor_release(x_2871, 1);
 x_2887 = x_2871;
} else {
 lean_dec_ref(x_2871);
 x_2887 = lean_box(0);
}
if (lean_is_scalar(x_2887)) {
 x_2888 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2888 = x_2887;
}
lean_ctor_set(x_2888, 0, x_2885);
lean_ctor_set(x_2888, 1, x_2886);
return x_2888;
}
}
else
{
lean_object* x_2889; lean_object* x_2890; lean_object* x_2891; lean_object* x_2892; 
lean_dec(x_2861);
lean_dec(x_2859);
lean_dec(x_2715);
lean_dec(x_2091);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_2889 = lean_ctor_get(x_2862, 0);
lean_inc(x_2889);
x_2890 = lean_ctor_get(x_2862, 1);
lean_inc(x_2890);
if (lean_is_exclusive(x_2862)) {
 lean_ctor_release(x_2862, 0);
 lean_ctor_release(x_2862, 1);
 x_2891 = x_2862;
} else {
 lean_dec_ref(x_2862);
 x_2891 = lean_box(0);
}
if (lean_is_scalar(x_2891)) {
 x_2892 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2892 = x_2891;
}
lean_ctor_set(x_2892, 0, x_2889);
lean_ctor_set(x_2892, 1, x_2890);
return x_2892;
}
}
}
else
{
lean_object* x_2893; lean_object* x_2894; lean_object* x_2895; lean_object* x_2896; 
lean_dec(x_2091);
lean_dec(x_11);
lean_dec(x_3);
x_2893 = lean_array_get(x_10, x_4, x_2273);
x_2894 = lean_array_get(x_10, x_4, x_2534);
x_2895 = l_Lean_mkAppB(x_2089, x_2893, x_2894);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2896 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2088);
if (lean_obj_tag(x_2896) == 0)
{
lean_object* x_2897; lean_object* x_2898; lean_object* x_2899; lean_object* x_2900; lean_object* x_2901; lean_object* x_2902; lean_object* x_2903; lean_object* x_2904; lean_object* x_2905; lean_object* x_2906; 
x_2897 = lean_ctor_get(x_2896, 0);
lean_inc(x_2897);
x_2898 = lean_ctor_get(x_2896, 1);
lean_inc(x_2898);
lean_dec(x_2896);
x_2899 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2900 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2901 = l_Lean_mkNatLit(x_2273);
x_2902 = l_Lean_mkNatLit(x_2534);
x_2903 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__36;
x_2904 = l_Lean_reflBoolTrue;
x_2905 = l_Lean_mkApp6(x_2903, x_2897, x_2899, x_2900, x_2901, x_2902, x_2904);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2895);
x_2906 = l_Lean_Meta_mkEq(x_2090, x_2895, x_5, x_6, x_7, x_8, x_2898);
if (lean_obj_tag(x_2906) == 0)
{
lean_object* x_2907; lean_object* x_2908; lean_object* x_2909; 
x_2907 = lean_ctor_get(x_2906, 0);
lean_inc(x_2907);
x_2908 = lean_ctor_get(x_2906, 1);
lean_inc(x_2908);
lean_dec(x_2906);
x_2909 = l_Lean_Meta_mkExpectedTypeHint(x_2905, x_2907, x_5, x_6, x_7, x_8, x_2908);
if (lean_obj_tag(x_2909) == 0)
{
lean_object* x_2910; lean_object* x_2911; lean_object* x_2912; lean_object* x_2913; lean_object* x_2914; lean_object* x_2915; 
x_2910 = lean_ctor_get(x_2909, 0);
lean_inc(x_2910);
x_2911 = lean_ctor_get(x_2909, 1);
lean_inc(x_2911);
if (lean_is_exclusive(x_2909)) {
 lean_ctor_release(x_2909, 0);
 lean_ctor_release(x_2909, 1);
 x_2912 = x_2909;
} else {
 lean_dec_ref(x_2909);
 x_2912 = lean_box(0);
}
x_2913 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2913, 0, x_2895);
lean_ctor_set(x_2913, 1, x_2910);
if (lean_is_scalar(x_2715)) {
 x_2914 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2914 = x_2715;
 lean_ctor_set_tag(x_2914, 1);
}
lean_ctor_set(x_2914, 0, x_2913);
if (lean_is_scalar(x_2912)) {
 x_2915 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2915 = x_2912;
}
lean_ctor_set(x_2915, 0, x_2914);
lean_ctor_set(x_2915, 1, x_2911);
return x_2915;
}
else
{
lean_object* x_2916; lean_object* x_2917; lean_object* x_2918; lean_object* x_2919; 
lean_dec(x_2895);
lean_dec(x_2715);
x_2916 = lean_ctor_get(x_2909, 0);
lean_inc(x_2916);
x_2917 = lean_ctor_get(x_2909, 1);
lean_inc(x_2917);
if (lean_is_exclusive(x_2909)) {
 lean_ctor_release(x_2909, 0);
 lean_ctor_release(x_2909, 1);
 x_2918 = x_2909;
} else {
 lean_dec_ref(x_2909);
 x_2918 = lean_box(0);
}
if (lean_is_scalar(x_2918)) {
 x_2919 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2919 = x_2918;
}
lean_ctor_set(x_2919, 0, x_2916);
lean_ctor_set(x_2919, 1, x_2917);
return x_2919;
}
}
else
{
lean_object* x_2920; lean_object* x_2921; lean_object* x_2922; lean_object* x_2923; 
lean_dec(x_2905);
lean_dec(x_2895);
lean_dec(x_2715);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2920 = lean_ctor_get(x_2906, 0);
lean_inc(x_2920);
x_2921 = lean_ctor_get(x_2906, 1);
lean_inc(x_2921);
if (lean_is_exclusive(x_2906)) {
 lean_ctor_release(x_2906, 0);
 lean_ctor_release(x_2906, 1);
 x_2922 = x_2906;
} else {
 lean_dec_ref(x_2906);
 x_2922 = lean_box(0);
}
if (lean_is_scalar(x_2922)) {
 x_2923 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2923 = x_2922;
}
lean_ctor_set(x_2923, 0, x_2920);
lean_ctor_set(x_2923, 1, x_2921);
return x_2923;
}
}
else
{
lean_object* x_2924; lean_object* x_2925; lean_object* x_2926; lean_object* x_2927; 
lean_dec(x_2895);
lean_dec(x_2715);
lean_dec(x_2534);
lean_dec(x_2273);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_2924 = lean_ctor_get(x_2896, 0);
lean_inc(x_2924);
x_2925 = lean_ctor_get(x_2896, 1);
lean_inc(x_2925);
if (lean_is_exclusive(x_2896)) {
 lean_ctor_release(x_2896, 0);
 lean_ctor_release(x_2896, 1);
 x_2926 = x_2896;
} else {
 lean_dec_ref(x_2896);
 x_2926 = lean_box(0);
}
if (lean_is_scalar(x_2926)) {
 x_2927 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2927 = x_2926;
}
lean_ctor_set(x_2927, 0, x_2924);
lean_ctor_set(x_2927, 1, x_2925);
return x_2927;
}
}
}
else
{
lean_object* x_2928; lean_object* x_2929; uint8_t x_2930; 
lean_dec(x_2535);
lean_dec(x_2534);
lean_dec(x_2273);
x_2928 = l_Int_Linear_Poly_gcdCoeffs_x27(x_2091);
x_2929 = lean_unsigned_to_nat(1u);
x_2930 = lean_nat_dec_eq(x_2928, x_2929);
if (x_2930 == 0)
{
lean_object* x_2931; lean_object* x_2932; lean_object* x_2933; lean_object* x_2934; uint8_t x_2935; 
x_2931 = l_Int_Linear_Poly_getConst(x_2091);
x_2932 = lean_nat_to_int(x_2928);
x_2933 = lean_int_emod(x_2931, x_2932);
lean_dec(x_2931);
x_2934 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_2935 = lean_int_dec_eq(x_2933, x_2934);
lean_dec(x_2933);
if (x_2935 == 0)
{
lean_object* x_2936; lean_object* x_2937; 
lean_dec(x_2091);
lean_dec(x_11);
x_2936 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2937 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_2088);
if (lean_obj_tag(x_2937) == 0)
{
lean_object* x_2938; lean_object* x_2939; lean_object* x_2940; lean_object* x_2941; uint8_t x_2942; lean_object* x_2943; lean_object* x_2944; 
x_2938 = lean_ctor_get(x_2937, 0);
lean_inc(x_2938);
x_2939 = lean_ctor_get(x_2937, 1);
lean_inc(x_2939);
lean_dec(x_2937);
x_2940 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_2941 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_2942 = lean_int_dec_le(x_2934, x_2932);
x_2943 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_2944 = l_Lean_Meta_mkEq(x_2090, x_2943, x_5, x_6, x_7, x_8, x_2939);
if (x_2942 == 0)
{
if (lean_obj_tag(x_2944) == 0)
{
lean_object* x_2945; lean_object* x_2946; lean_object* x_2947; lean_object* x_2948; lean_object* x_2949; lean_object* x_2950; lean_object* x_2951; lean_object* x_2952; lean_object* x_2953; lean_object* x_2954; lean_object* x_2955; lean_object* x_2956; lean_object* x_2957; 
x_2945 = lean_ctor_get(x_2944, 0);
lean_inc(x_2945);
x_2946 = lean_ctor_get(x_2944, 1);
lean_inc(x_2946);
lean_dec(x_2944);
x_2947 = l_Lean_Expr_const___override(x_3, x_2936);
x_2948 = lean_int_neg(x_2932);
lean_dec(x_2932);
x_2949 = l_Int_toNat(x_2948);
lean_dec(x_2948);
x_2950 = l_Lean_instToExprInt_mkNat(x_2949);
x_2951 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_2952 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_2953 = l_Lean_mkApp3(x_2951, x_2947, x_2952, x_2950);
x_2954 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_2955 = l_Lean_reflBoolTrue;
x_2956 = l_Lean_mkApp5(x_2954, x_2938, x_2940, x_2941, x_2953, x_2955);
x_2957 = l_Lean_Meta_mkExpectedTypeHint(x_2956, x_2945, x_5, x_6, x_7, x_8, x_2946);
if (lean_obj_tag(x_2957) == 0)
{
lean_object* x_2958; lean_object* x_2959; lean_object* x_2960; lean_object* x_2961; lean_object* x_2962; lean_object* x_2963; 
x_2958 = lean_ctor_get(x_2957, 0);
lean_inc(x_2958);
x_2959 = lean_ctor_get(x_2957, 1);
lean_inc(x_2959);
if (lean_is_exclusive(x_2957)) {
 lean_ctor_release(x_2957, 0);
 lean_ctor_release(x_2957, 1);
 x_2960 = x_2957;
} else {
 lean_dec_ref(x_2957);
 x_2960 = lean_box(0);
}
x_2961 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2961, 0, x_2943);
lean_ctor_set(x_2961, 1, x_2958);
x_2962 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2962, 0, x_2961);
if (lean_is_scalar(x_2960)) {
 x_2963 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2963 = x_2960;
}
lean_ctor_set(x_2963, 0, x_2962);
lean_ctor_set(x_2963, 1, x_2959);
return x_2963;
}
else
{
lean_object* x_2964; lean_object* x_2965; lean_object* x_2966; lean_object* x_2967; 
x_2964 = lean_ctor_get(x_2957, 0);
lean_inc(x_2964);
x_2965 = lean_ctor_get(x_2957, 1);
lean_inc(x_2965);
if (lean_is_exclusive(x_2957)) {
 lean_ctor_release(x_2957, 0);
 lean_ctor_release(x_2957, 1);
 x_2966 = x_2957;
} else {
 lean_dec_ref(x_2957);
 x_2966 = lean_box(0);
}
if (lean_is_scalar(x_2966)) {
 x_2967 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2967 = x_2966;
}
lean_ctor_set(x_2967, 0, x_2964);
lean_ctor_set(x_2967, 1, x_2965);
return x_2967;
}
}
else
{
lean_object* x_2968; lean_object* x_2969; lean_object* x_2970; lean_object* x_2971; 
lean_dec(x_2941);
lean_dec(x_2940);
lean_dec(x_2938);
lean_dec(x_2932);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_2968 = lean_ctor_get(x_2944, 0);
lean_inc(x_2968);
x_2969 = lean_ctor_get(x_2944, 1);
lean_inc(x_2969);
if (lean_is_exclusive(x_2944)) {
 lean_ctor_release(x_2944, 0);
 lean_ctor_release(x_2944, 1);
 x_2970 = x_2944;
} else {
 lean_dec_ref(x_2944);
 x_2970 = lean_box(0);
}
if (lean_is_scalar(x_2970)) {
 x_2971 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2971 = x_2970;
}
lean_ctor_set(x_2971, 0, x_2968);
lean_ctor_set(x_2971, 1, x_2969);
return x_2971;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2944) == 0)
{
lean_object* x_2972; lean_object* x_2973; lean_object* x_2974; lean_object* x_2975; lean_object* x_2976; lean_object* x_2977; lean_object* x_2978; lean_object* x_2979; 
x_2972 = lean_ctor_get(x_2944, 0);
lean_inc(x_2972);
x_2973 = lean_ctor_get(x_2944, 1);
lean_inc(x_2973);
lean_dec(x_2944);
x_2974 = l_Int_toNat(x_2932);
lean_dec(x_2932);
x_2975 = l_Lean_instToExprInt_mkNat(x_2974);
x_2976 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_2977 = l_Lean_reflBoolTrue;
x_2978 = l_Lean_mkApp5(x_2976, x_2938, x_2940, x_2941, x_2975, x_2977);
x_2979 = l_Lean_Meta_mkExpectedTypeHint(x_2978, x_2972, x_5, x_6, x_7, x_8, x_2973);
if (lean_obj_tag(x_2979) == 0)
{
lean_object* x_2980; lean_object* x_2981; lean_object* x_2982; lean_object* x_2983; lean_object* x_2984; lean_object* x_2985; 
x_2980 = lean_ctor_get(x_2979, 0);
lean_inc(x_2980);
x_2981 = lean_ctor_get(x_2979, 1);
lean_inc(x_2981);
if (lean_is_exclusive(x_2979)) {
 lean_ctor_release(x_2979, 0);
 lean_ctor_release(x_2979, 1);
 x_2982 = x_2979;
} else {
 lean_dec_ref(x_2979);
 x_2982 = lean_box(0);
}
x_2983 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2983, 0, x_2943);
lean_ctor_set(x_2983, 1, x_2980);
x_2984 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2984, 0, x_2983);
if (lean_is_scalar(x_2982)) {
 x_2985 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2985 = x_2982;
}
lean_ctor_set(x_2985, 0, x_2984);
lean_ctor_set(x_2985, 1, x_2981);
return x_2985;
}
else
{
lean_object* x_2986; lean_object* x_2987; lean_object* x_2988; lean_object* x_2989; 
x_2986 = lean_ctor_get(x_2979, 0);
lean_inc(x_2986);
x_2987 = lean_ctor_get(x_2979, 1);
lean_inc(x_2987);
if (lean_is_exclusive(x_2979)) {
 lean_ctor_release(x_2979, 0);
 lean_ctor_release(x_2979, 1);
 x_2988 = x_2979;
} else {
 lean_dec_ref(x_2979);
 x_2988 = lean_box(0);
}
if (lean_is_scalar(x_2988)) {
 x_2989 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2989 = x_2988;
}
lean_ctor_set(x_2989, 0, x_2986);
lean_ctor_set(x_2989, 1, x_2987);
return x_2989;
}
}
else
{
lean_object* x_2990; lean_object* x_2991; lean_object* x_2992; lean_object* x_2993; 
lean_dec(x_2941);
lean_dec(x_2940);
lean_dec(x_2938);
lean_dec(x_2932);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2990 = lean_ctor_get(x_2944, 0);
lean_inc(x_2990);
x_2991 = lean_ctor_get(x_2944, 1);
lean_inc(x_2991);
if (lean_is_exclusive(x_2944)) {
 lean_ctor_release(x_2944, 0);
 lean_ctor_release(x_2944, 1);
 x_2992 = x_2944;
} else {
 lean_dec_ref(x_2944);
 x_2992 = lean_box(0);
}
if (lean_is_scalar(x_2992)) {
 x_2993 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2993 = x_2992;
}
lean_ctor_set(x_2993, 0, x_2990);
lean_ctor_set(x_2993, 1, x_2991);
return x_2993;
}
}
}
else
{
lean_object* x_2994; lean_object* x_2995; lean_object* x_2996; lean_object* x_2997; 
lean_dec(x_2932);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2994 = lean_ctor_get(x_2937, 0);
lean_inc(x_2994);
x_2995 = lean_ctor_get(x_2937, 1);
lean_inc(x_2995);
if (lean_is_exclusive(x_2937)) {
 lean_ctor_release(x_2937, 0);
 lean_ctor_release(x_2937, 1);
 x_2996 = x_2937;
} else {
 lean_dec_ref(x_2937);
 x_2996 = lean_box(0);
}
if (lean_is_scalar(x_2996)) {
 x_2997 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2997 = x_2996;
}
lean_ctor_set(x_2997, 0, x_2994);
lean_ctor_set(x_2997, 1, x_2995);
return x_2997;
}
}
else
{
lean_object* x_2998; lean_object* x_2999; lean_object* x_3000; lean_object* x_3001; lean_object* x_3002; lean_object* x_3003; lean_object* x_3004; lean_object* x_3005; 
x_2998 = l_Int_Linear_Poly_div(x_2932, x_2091);
lean_inc(x_2998);
x_2999 = l_Int_Linear_Poly_denoteExpr(x_11, x_2998, x_5, x_6, x_7, x_8, x_2088);
x_3000 = lean_ctor_get(x_2999, 0);
lean_inc(x_3000);
x_3001 = lean_ctor_get(x_2999, 1);
lean_inc(x_3001);
if (lean_is_exclusive(x_2999)) {
 lean_ctor_release(x_2999, 0);
 lean_ctor_release(x_2999, 1);
 x_3002 = x_2999;
} else {
 lean_dec_ref(x_2999);
 x_3002 = lean_box(0);
}
x_3003 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_3004 = l_Lean_mkAppB(x_2089, x_3000, x_3003);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3005 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3001);
if (lean_obj_tag(x_3005) == 0)
{
lean_object* x_3006; lean_object* x_3007; lean_object* x_3008; lean_object* x_3009; lean_object* x_3010; lean_object* x_3011; uint8_t x_3012; lean_object* x_3013; 
x_3006 = lean_ctor_get(x_3005, 0);
lean_inc(x_3006);
x_3007 = lean_ctor_get(x_3005, 1);
lean_inc(x_3007);
lean_dec(x_3005);
x_3008 = lean_box(0);
x_3009 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3010 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3011 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_2998);
x_3012 = lean_int_dec_le(x_2934, x_2932);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3004);
x_3013 = l_Lean_Meta_mkEq(x_2090, x_3004, x_5, x_6, x_7, x_8, x_3007);
if (x_3012 == 0)
{
if (lean_obj_tag(x_3013) == 0)
{
lean_object* x_3014; lean_object* x_3015; lean_object* x_3016; lean_object* x_3017; lean_object* x_3018; lean_object* x_3019; lean_object* x_3020; lean_object* x_3021; lean_object* x_3022; lean_object* x_3023; lean_object* x_3024; lean_object* x_3025; lean_object* x_3026; 
x_3014 = lean_ctor_get(x_3013, 0);
lean_inc(x_3014);
x_3015 = lean_ctor_get(x_3013, 1);
lean_inc(x_3015);
lean_dec(x_3013);
x_3016 = l_Lean_Expr_const___override(x_3, x_3008);
x_3017 = lean_int_neg(x_2932);
lean_dec(x_2932);
x_3018 = l_Int_toNat(x_3017);
lean_dec(x_3017);
x_3019 = l_Lean_instToExprInt_mkNat(x_3018);
x_3020 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_3021 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_3022 = l_Lean_mkApp3(x_3020, x_3016, x_3021, x_3019);
x_3023 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_3024 = l_Lean_reflBoolTrue;
x_3025 = l_Lean_mkApp6(x_3023, x_3006, x_3009, x_3010, x_3011, x_3022, x_3024);
x_3026 = l_Lean_Meta_mkExpectedTypeHint(x_3025, x_3014, x_5, x_6, x_7, x_8, x_3015);
if (lean_obj_tag(x_3026) == 0)
{
lean_object* x_3027; lean_object* x_3028; lean_object* x_3029; lean_object* x_3030; lean_object* x_3031; lean_object* x_3032; 
x_3027 = lean_ctor_get(x_3026, 0);
lean_inc(x_3027);
x_3028 = lean_ctor_get(x_3026, 1);
lean_inc(x_3028);
if (lean_is_exclusive(x_3026)) {
 lean_ctor_release(x_3026, 0);
 lean_ctor_release(x_3026, 1);
 x_3029 = x_3026;
} else {
 lean_dec_ref(x_3026);
 x_3029 = lean_box(0);
}
if (lean_is_scalar(x_3002)) {
 x_3030 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3030 = x_3002;
}
lean_ctor_set(x_3030, 0, x_3004);
lean_ctor_set(x_3030, 1, x_3027);
x_3031 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3031, 0, x_3030);
if (lean_is_scalar(x_3029)) {
 x_3032 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3032 = x_3029;
}
lean_ctor_set(x_3032, 0, x_3031);
lean_ctor_set(x_3032, 1, x_3028);
return x_3032;
}
else
{
lean_object* x_3033; lean_object* x_3034; lean_object* x_3035; lean_object* x_3036; 
lean_dec(x_3004);
lean_dec(x_3002);
x_3033 = lean_ctor_get(x_3026, 0);
lean_inc(x_3033);
x_3034 = lean_ctor_get(x_3026, 1);
lean_inc(x_3034);
if (lean_is_exclusive(x_3026)) {
 lean_ctor_release(x_3026, 0);
 lean_ctor_release(x_3026, 1);
 x_3035 = x_3026;
} else {
 lean_dec_ref(x_3026);
 x_3035 = lean_box(0);
}
if (lean_is_scalar(x_3035)) {
 x_3036 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3036 = x_3035;
}
lean_ctor_set(x_3036, 0, x_3033);
lean_ctor_set(x_3036, 1, x_3034);
return x_3036;
}
}
else
{
lean_object* x_3037; lean_object* x_3038; lean_object* x_3039; lean_object* x_3040; 
lean_dec(x_3011);
lean_dec(x_3010);
lean_dec(x_3009);
lean_dec(x_3006);
lean_dec(x_3004);
lean_dec(x_3002);
lean_dec(x_2932);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_3037 = lean_ctor_get(x_3013, 0);
lean_inc(x_3037);
x_3038 = lean_ctor_get(x_3013, 1);
lean_inc(x_3038);
if (lean_is_exclusive(x_3013)) {
 lean_ctor_release(x_3013, 0);
 lean_ctor_release(x_3013, 1);
 x_3039 = x_3013;
} else {
 lean_dec_ref(x_3013);
 x_3039 = lean_box(0);
}
if (lean_is_scalar(x_3039)) {
 x_3040 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3040 = x_3039;
}
lean_ctor_set(x_3040, 0, x_3037);
lean_ctor_set(x_3040, 1, x_3038);
return x_3040;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_3013) == 0)
{
lean_object* x_3041; lean_object* x_3042; lean_object* x_3043; lean_object* x_3044; lean_object* x_3045; lean_object* x_3046; lean_object* x_3047; lean_object* x_3048; 
x_3041 = lean_ctor_get(x_3013, 0);
lean_inc(x_3041);
x_3042 = lean_ctor_get(x_3013, 1);
lean_inc(x_3042);
lean_dec(x_3013);
x_3043 = l_Int_toNat(x_2932);
lean_dec(x_2932);
x_3044 = l_Lean_instToExprInt_mkNat(x_3043);
x_3045 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_3046 = l_Lean_reflBoolTrue;
x_3047 = l_Lean_mkApp6(x_3045, x_3006, x_3009, x_3010, x_3011, x_3044, x_3046);
x_3048 = l_Lean_Meta_mkExpectedTypeHint(x_3047, x_3041, x_5, x_6, x_7, x_8, x_3042);
if (lean_obj_tag(x_3048) == 0)
{
lean_object* x_3049; lean_object* x_3050; lean_object* x_3051; lean_object* x_3052; lean_object* x_3053; lean_object* x_3054; 
x_3049 = lean_ctor_get(x_3048, 0);
lean_inc(x_3049);
x_3050 = lean_ctor_get(x_3048, 1);
lean_inc(x_3050);
if (lean_is_exclusive(x_3048)) {
 lean_ctor_release(x_3048, 0);
 lean_ctor_release(x_3048, 1);
 x_3051 = x_3048;
} else {
 lean_dec_ref(x_3048);
 x_3051 = lean_box(0);
}
if (lean_is_scalar(x_3002)) {
 x_3052 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3052 = x_3002;
}
lean_ctor_set(x_3052, 0, x_3004);
lean_ctor_set(x_3052, 1, x_3049);
x_3053 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3053, 0, x_3052);
if (lean_is_scalar(x_3051)) {
 x_3054 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3054 = x_3051;
}
lean_ctor_set(x_3054, 0, x_3053);
lean_ctor_set(x_3054, 1, x_3050);
return x_3054;
}
else
{
lean_object* x_3055; lean_object* x_3056; lean_object* x_3057; lean_object* x_3058; 
lean_dec(x_3004);
lean_dec(x_3002);
x_3055 = lean_ctor_get(x_3048, 0);
lean_inc(x_3055);
x_3056 = lean_ctor_get(x_3048, 1);
lean_inc(x_3056);
if (lean_is_exclusive(x_3048)) {
 lean_ctor_release(x_3048, 0);
 lean_ctor_release(x_3048, 1);
 x_3057 = x_3048;
} else {
 lean_dec_ref(x_3048);
 x_3057 = lean_box(0);
}
if (lean_is_scalar(x_3057)) {
 x_3058 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3058 = x_3057;
}
lean_ctor_set(x_3058, 0, x_3055);
lean_ctor_set(x_3058, 1, x_3056);
return x_3058;
}
}
else
{
lean_object* x_3059; lean_object* x_3060; lean_object* x_3061; lean_object* x_3062; 
lean_dec(x_3011);
lean_dec(x_3010);
lean_dec(x_3009);
lean_dec(x_3006);
lean_dec(x_3004);
lean_dec(x_3002);
lean_dec(x_2932);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3059 = lean_ctor_get(x_3013, 0);
lean_inc(x_3059);
x_3060 = lean_ctor_get(x_3013, 1);
lean_inc(x_3060);
if (lean_is_exclusive(x_3013)) {
 lean_ctor_release(x_3013, 0);
 lean_ctor_release(x_3013, 1);
 x_3061 = x_3013;
} else {
 lean_dec_ref(x_3013);
 x_3061 = lean_box(0);
}
if (lean_is_scalar(x_3061)) {
 x_3062 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3062 = x_3061;
}
lean_ctor_set(x_3062, 0, x_3059);
lean_ctor_set(x_3062, 1, x_3060);
return x_3062;
}
}
}
else
{
lean_object* x_3063; lean_object* x_3064; lean_object* x_3065; lean_object* x_3066; 
lean_dec(x_3004);
lean_dec(x_3002);
lean_dec(x_2998);
lean_dec(x_2932);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3063 = lean_ctor_get(x_3005, 0);
lean_inc(x_3063);
x_3064 = lean_ctor_get(x_3005, 1);
lean_inc(x_3064);
if (lean_is_exclusive(x_3005)) {
 lean_ctor_release(x_3005, 0);
 lean_ctor_release(x_3005, 1);
 x_3065 = x_3005;
} else {
 lean_dec_ref(x_3005);
 x_3065 = lean_box(0);
}
if (lean_is_scalar(x_3065)) {
 x_3066 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3066 = x_3065;
}
lean_ctor_set(x_3066, 0, x_3063);
lean_ctor_set(x_3066, 1, x_3064);
return x_3066;
}
}
}
else
{
lean_object* x_3067; lean_object* x_3068; lean_object* x_3069; lean_object* x_3070; lean_object* x_3071; lean_object* x_3072; lean_object* x_3073; 
lean_dec(x_2928);
lean_dec(x_3);
lean_inc(x_2091);
x_3067 = l_Int_Linear_Poly_denoteExpr(x_11, x_2091, x_5, x_6, x_7, x_8, x_2088);
x_3068 = lean_ctor_get(x_3067, 0);
lean_inc(x_3068);
x_3069 = lean_ctor_get(x_3067, 1);
lean_inc(x_3069);
if (lean_is_exclusive(x_3067)) {
 lean_ctor_release(x_3067, 0);
 lean_ctor_release(x_3067, 1);
 x_3070 = x_3067;
} else {
 lean_dec_ref(x_3067);
 x_3070 = lean_box(0);
}
x_3071 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_3072 = l_Lean_mkAppB(x_2089, x_3068, x_3071);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3073 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3069);
if (lean_obj_tag(x_3073) == 0)
{
lean_object* x_3074; lean_object* x_3075; lean_object* x_3076; lean_object* x_3077; lean_object* x_3078; lean_object* x_3079; lean_object* x_3080; lean_object* x_3081; lean_object* x_3082; 
x_3074 = lean_ctor_get(x_3073, 0);
lean_inc(x_3074);
x_3075 = lean_ctor_get(x_3073, 1);
lean_inc(x_3075);
lean_dec(x_3073);
x_3076 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3077 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3078 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_2091);
x_3079 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_3080 = l_Lean_reflBoolTrue;
x_3081 = l_Lean_mkApp5(x_3079, x_3074, x_3076, x_3077, x_3078, x_3080);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3072);
x_3082 = l_Lean_Meta_mkEq(x_2090, x_3072, x_5, x_6, x_7, x_8, x_3075);
if (lean_obj_tag(x_3082) == 0)
{
lean_object* x_3083; lean_object* x_3084; lean_object* x_3085; 
x_3083 = lean_ctor_get(x_3082, 0);
lean_inc(x_3083);
x_3084 = lean_ctor_get(x_3082, 1);
lean_inc(x_3084);
lean_dec(x_3082);
x_3085 = l_Lean_Meta_mkExpectedTypeHint(x_3081, x_3083, x_5, x_6, x_7, x_8, x_3084);
if (lean_obj_tag(x_3085) == 0)
{
lean_object* x_3086; lean_object* x_3087; lean_object* x_3088; lean_object* x_3089; lean_object* x_3090; lean_object* x_3091; 
x_3086 = lean_ctor_get(x_3085, 0);
lean_inc(x_3086);
x_3087 = lean_ctor_get(x_3085, 1);
lean_inc(x_3087);
if (lean_is_exclusive(x_3085)) {
 lean_ctor_release(x_3085, 0);
 lean_ctor_release(x_3085, 1);
 x_3088 = x_3085;
} else {
 lean_dec_ref(x_3085);
 x_3088 = lean_box(0);
}
if (lean_is_scalar(x_3070)) {
 x_3089 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3089 = x_3070;
}
lean_ctor_set(x_3089, 0, x_3072);
lean_ctor_set(x_3089, 1, x_3086);
x_3090 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3090, 0, x_3089);
if (lean_is_scalar(x_3088)) {
 x_3091 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3091 = x_3088;
}
lean_ctor_set(x_3091, 0, x_3090);
lean_ctor_set(x_3091, 1, x_3087);
return x_3091;
}
else
{
lean_object* x_3092; lean_object* x_3093; lean_object* x_3094; lean_object* x_3095; 
lean_dec(x_3072);
lean_dec(x_3070);
x_3092 = lean_ctor_get(x_3085, 0);
lean_inc(x_3092);
x_3093 = lean_ctor_get(x_3085, 1);
lean_inc(x_3093);
if (lean_is_exclusive(x_3085)) {
 lean_ctor_release(x_3085, 0);
 lean_ctor_release(x_3085, 1);
 x_3094 = x_3085;
} else {
 lean_dec_ref(x_3085);
 x_3094 = lean_box(0);
}
if (lean_is_scalar(x_3094)) {
 x_3095 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3095 = x_3094;
}
lean_ctor_set(x_3095, 0, x_3092);
lean_ctor_set(x_3095, 1, x_3093);
return x_3095;
}
}
else
{
lean_object* x_3096; lean_object* x_3097; lean_object* x_3098; lean_object* x_3099; 
lean_dec(x_3081);
lean_dec(x_3072);
lean_dec(x_3070);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3096 = lean_ctor_get(x_3082, 0);
lean_inc(x_3096);
x_3097 = lean_ctor_get(x_3082, 1);
lean_inc(x_3097);
if (lean_is_exclusive(x_3082)) {
 lean_ctor_release(x_3082, 0);
 lean_ctor_release(x_3082, 1);
 x_3098 = x_3082;
} else {
 lean_dec_ref(x_3082);
 x_3098 = lean_box(0);
}
if (lean_is_scalar(x_3098)) {
 x_3099 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3099 = x_3098;
}
lean_ctor_set(x_3099, 0, x_3096);
lean_ctor_set(x_3099, 1, x_3097);
return x_3099;
}
}
else
{
lean_object* x_3100; lean_object* x_3101; lean_object* x_3102; lean_object* x_3103; 
lean_dec(x_3072);
lean_dec(x_3070);
lean_dec(x_2091);
lean_dec(x_2090);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_3100 = lean_ctor_get(x_3073, 0);
lean_inc(x_3100);
x_3101 = lean_ctor_get(x_3073, 1);
lean_inc(x_3101);
if (lean_is_exclusive(x_3073)) {
 lean_ctor_release(x_3073, 0);
 lean_ctor_release(x_3073, 1);
 x_3102 = x_3073;
} else {
 lean_dec_ref(x_3073);
 x_3102 = lean_box(0);
}
if (lean_is_scalar(x_3102)) {
 x_3103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3103 = x_3102;
}
lean_ctor_set(x_3103, 0, x_3100);
lean_ctor_set(x_3103, 1, x_3101);
return x_3103;
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
else
{
lean_object* x_3177; lean_object* x_3178; lean_object* x_3179; lean_object* x_3180; lean_object* x_3181; lean_object* x_3182; lean_object* x_3183; lean_object* x_3184; lean_object* x_3185; lean_object* x_3186; lean_object* x_3187; uint8_t x_4200; 
x_3177 = lean_ctor_get(x_12, 0);
x_3178 = lean_ctor_get(x_12, 1);
lean_inc(x_3178);
lean_inc(x_3177);
lean_dec(x_12);
lean_inc(x_2);
lean_inc(x_11);
x_3179 = l_Int_Linear_Expr_denoteExpr(x_11, x_2, x_5, x_6, x_7, x_8, x_3178);
x_3180 = lean_ctor_get(x_3179, 0);
lean_inc(x_3180);
x_3181 = lean_ctor_get(x_3179, 1);
lean_inc(x_3181);
if (lean_is_exclusive(x_3179)) {
 lean_ctor_release(x_3179, 0);
 lean_ctor_release(x_3179, 1);
 x_3182 = x_3179;
} else {
 lean_dec_ref(x_3179);
 x_3182 = lean_box(0);
}
x_3183 = l___private_Lean_Expr_0__Lean_intEqPred;
x_3184 = l_Lean_mkAppB(x_3183, x_3177, x_3180);
lean_inc(x_2);
lean_inc(x_1);
x_3185 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3185, 0, x_1);
lean_ctor_set(x_3185, 1, x_2);
x_3186 = l_Int_Linear_Expr_norm(x_3185);
lean_dec(x_3185);
x_4200 = l_Int_Linear_Poly_isUnsatEq(x_3186);
if (x_4200 == 0)
{
uint8_t x_4201; 
x_4201 = l_Int_Linear_Poly_isValidEq(x_3186);
if (x_4201 == 0)
{
lean_object* x_4202; uint8_t x_4203; 
lean_inc(x_3186);
x_4202 = l_Int_Linear_Poly_toExpr(x_3186);
x_4203 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_4202, x_1);
lean_dec(x_4202);
if (x_4203 == 0)
{
lean_object* x_4204; 
lean_dec(x_3182);
x_4204 = lean_box(0);
x_3187 = x_4204;
goto block_4199;
}
else
{
lean_object* x_4205; uint8_t x_4206; 
x_4205 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__37;
x_4206 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_2, x_4205);
if (x_4206 == 0)
{
lean_object* x_4207; 
lean_dec(x_3182);
x_4207 = lean_box(0);
x_3187 = x_4207;
goto block_4199;
}
else
{
lean_object* x_4208; lean_object* x_4209; 
lean_dec(x_3186);
lean_dec(x_3184);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4208 = lean_box(0);
if (lean_is_scalar(x_3182)) {
 x_4209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4209 = x_3182;
}
lean_ctor_set(x_4209, 0, x_4208);
lean_ctor_set(x_4209, 1, x_3181);
return x_4209;
}
}
}
else
{
lean_object* x_4210; 
lean_dec(x_3186);
lean_dec(x_3182);
lean_dec(x_11);
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_4210 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3181);
if (lean_obj_tag(x_4210) == 0)
{
lean_object* x_4211; lean_object* x_4212; lean_object* x_4213; lean_object* x_4214; lean_object* x_4215; lean_object* x_4216; lean_object* x_4217; lean_object* x_4218; lean_object* x_4219; 
x_4211 = lean_ctor_get(x_4210, 0);
lean_inc(x_4211);
x_4212 = lean_ctor_get(x_4210, 1);
lean_inc(x_4212);
lean_dec(x_4210);
x_4213 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_4214 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_4215 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__43;
x_4216 = l_Lean_reflBoolTrue;
x_4217 = l_Lean_mkApp4(x_4215, x_4211, x_4213, x_4214, x_4216);
x_4218 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__40;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_4219 = l_Lean_Meta_mkEq(x_3184, x_4218, x_5, x_6, x_7, x_8, x_4212);
if (lean_obj_tag(x_4219) == 0)
{
lean_object* x_4220; lean_object* x_4221; lean_object* x_4222; 
x_4220 = lean_ctor_get(x_4219, 0);
lean_inc(x_4220);
x_4221 = lean_ctor_get(x_4219, 1);
lean_inc(x_4221);
lean_dec(x_4219);
x_4222 = l_Lean_Meta_mkExpectedTypeHint(x_4217, x_4220, x_5, x_6, x_7, x_8, x_4221);
if (lean_obj_tag(x_4222) == 0)
{
lean_object* x_4223; lean_object* x_4224; lean_object* x_4225; lean_object* x_4226; lean_object* x_4227; lean_object* x_4228; 
x_4223 = lean_ctor_get(x_4222, 0);
lean_inc(x_4223);
x_4224 = lean_ctor_get(x_4222, 1);
lean_inc(x_4224);
if (lean_is_exclusive(x_4222)) {
 lean_ctor_release(x_4222, 0);
 lean_ctor_release(x_4222, 1);
 x_4225 = x_4222;
} else {
 lean_dec_ref(x_4222);
 x_4225 = lean_box(0);
}
x_4226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4226, 0, x_4218);
lean_ctor_set(x_4226, 1, x_4223);
x_4227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4227, 0, x_4226);
if (lean_is_scalar(x_4225)) {
 x_4228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4228 = x_4225;
}
lean_ctor_set(x_4228, 0, x_4227);
lean_ctor_set(x_4228, 1, x_4224);
return x_4228;
}
else
{
lean_object* x_4229; lean_object* x_4230; lean_object* x_4231; lean_object* x_4232; 
x_4229 = lean_ctor_get(x_4222, 0);
lean_inc(x_4229);
x_4230 = lean_ctor_get(x_4222, 1);
lean_inc(x_4230);
if (lean_is_exclusive(x_4222)) {
 lean_ctor_release(x_4222, 0);
 lean_ctor_release(x_4222, 1);
 x_4231 = x_4222;
} else {
 lean_dec_ref(x_4222);
 x_4231 = lean_box(0);
}
if (lean_is_scalar(x_4231)) {
 x_4232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4232 = x_4231;
}
lean_ctor_set(x_4232, 0, x_4229);
lean_ctor_set(x_4232, 1, x_4230);
return x_4232;
}
}
else
{
lean_object* x_4233; lean_object* x_4234; lean_object* x_4235; lean_object* x_4236; 
lean_dec(x_4217);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_4233 = lean_ctor_get(x_4219, 0);
lean_inc(x_4233);
x_4234 = lean_ctor_get(x_4219, 1);
lean_inc(x_4234);
if (lean_is_exclusive(x_4219)) {
 lean_ctor_release(x_4219, 0);
 lean_ctor_release(x_4219, 1);
 x_4235 = x_4219;
} else {
 lean_dec_ref(x_4219);
 x_4235 = lean_box(0);
}
if (lean_is_scalar(x_4235)) {
 x_4236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4236 = x_4235;
}
lean_ctor_set(x_4236, 0, x_4233);
lean_ctor_set(x_4236, 1, x_4234);
return x_4236;
}
}
else
{
lean_object* x_4237; lean_object* x_4238; lean_object* x_4239; lean_object* x_4240; 
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_4237 = lean_ctor_get(x_4210, 0);
lean_inc(x_4237);
x_4238 = lean_ctor_get(x_4210, 1);
lean_inc(x_4238);
if (lean_is_exclusive(x_4210)) {
 lean_ctor_release(x_4210, 0);
 lean_ctor_release(x_4210, 1);
 x_4239 = x_4210;
} else {
 lean_dec_ref(x_4210);
 x_4239 = lean_box(0);
}
if (lean_is_scalar(x_4239)) {
 x_4240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4240 = x_4239;
}
lean_ctor_set(x_4240, 0, x_4237);
lean_ctor_set(x_4240, 1, x_4238);
return x_4240;
}
}
}
else
{
lean_object* x_4241; 
lean_dec(x_3186);
lean_dec(x_3182);
lean_dec(x_11);
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_4241 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3181);
if (lean_obj_tag(x_4241) == 0)
{
lean_object* x_4242; lean_object* x_4243; lean_object* x_4244; lean_object* x_4245; lean_object* x_4246; lean_object* x_4247; lean_object* x_4248; lean_object* x_4249; lean_object* x_4250; 
x_4242 = lean_ctor_get(x_4241, 0);
lean_inc(x_4242);
x_4243 = lean_ctor_get(x_4241, 1);
lean_inc(x_4243);
lean_dec(x_4241);
x_4244 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_4245 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_4246 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__46;
x_4247 = l_Lean_reflBoolTrue;
x_4248 = l_Lean_mkApp4(x_4246, x_4242, x_4244, x_4245, x_4247);
x_4249 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_4250 = l_Lean_Meta_mkEq(x_3184, x_4249, x_5, x_6, x_7, x_8, x_4243);
if (lean_obj_tag(x_4250) == 0)
{
lean_object* x_4251; lean_object* x_4252; lean_object* x_4253; 
x_4251 = lean_ctor_get(x_4250, 0);
lean_inc(x_4251);
x_4252 = lean_ctor_get(x_4250, 1);
lean_inc(x_4252);
lean_dec(x_4250);
x_4253 = l_Lean_Meta_mkExpectedTypeHint(x_4248, x_4251, x_5, x_6, x_7, x_8, x_4252);
if (lean_obj_tag(x_4253) == 0)
{
lean_object* x_4254; lean_object* x_4255; lean_object* x_4256; lean_object* x_4257; lean_object* x_4258; lean_object* x_4259; 
x_4254 = lean_ctor_get(x_4253, 0);
lean_inc(x_4254);
x_4255 = lean_ctor_get(x_4253, 1);
lean_inc(x_4255);
if (lean_is_exclusive(x_4253)) {
 lean_ctor_release(x_4253, 0);
 lean_ctor_release(x_4253, 1);
 x_4256 = x_4253;
} else {
 lean_dec_ref(x_4253);
 x_4256 = lean_box(0);
}
x_4257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4257, 0, x_4249);
lean_ctor_set(x_4257, 1, x_4254);
x_4258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4258, 0, x_4257);
if (lean_is_scalar(x_4256)) {
 x_4259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4259 = x_4256;
}
lean_ctor_set(x_4259, 0, x_4258);
lean_ctor_set(x_4259, 1, x_4255);
return x_4259;
}
else
{
lean_object* x_4260; lean_object* x_4261; lean_object* x_4262; lean_object* x_4263; 
x_4260 = lean_ctor_get(x_4253, 0);
lean_inc(x_4260);
x_4261 = lean_ctor_get(x_4253, 1);
lean_inc(x_4261);
if (lean_is_exclusive(x_4253)) {
 lean_ctor_release(x_4253, 0);
 lean_ctor_release(x_4253, 1);
 x_4262 = x_4253;
} else {
 lean_dec_ref(x_4253);
 x_4262 = lean_box(0);
}
if (lean_is_scalar(x_4262)) {
 x_4263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4263 = x_4262;
}
lean_ctor_set(x_4263, 0, x_4260);
lean_ctor_set(x_4263, 1, x_4261);
return x_4263;
}
}
else
{
lean_object* x_4264; lean_object* x_4265; lean_object* x_4266; lean_object* x_4267; 
lean_dec(x_4248);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_4264 = lean_ctor_get(x_4250, 0);
lean_inc(x_4264);
x_4265 = lean_ctor_get(x_4250, 1);
lean_inc(x_4265);
if (lean_is_exclusive(x_4250)) {
 lean_ctor_release(x_4250, 0);
 lean_ctor_release(x_4250, 1);
 x_4266 = x_4250;
} else {
 lean_dec_ref(x_4250);
 x_4266 = lean_box(0);
}
if (lean_is_scalar(x_4266)) {
 x_4267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4267 = x_4266;
}
lean_ctor_set(x_4267, 0, x_4264);
lean_ctor_set(x_4267, 1, x_4265);
return x_4267;
}
}
else
{
lean_object* x_4268; lean_object* x_4269; lean_object* x_4270; lean_object* x_4271; 
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_4268 = lean_ctor_get(x_4241, 0);
lean_inc(x_4268);
x_4269 = lean_ctor_get(x_4241, 1);
lean_inc(x_4269);
if (lean_is_exclusive(x_4241)) {
 lean_ctor_release(x_4241, 0);
 lean_ctor_release(x_4241, 1);
 x_4270 = x_4241;
} else {
 lean_dec_ref(x_4241);
 x_4270 = lean_box(0);
}
if (lean_is_scalar(x_4270)) {
 x_4271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4271 = x_4270;
}
lean_ctor_set(x_4271, 0, x_4268);
lean_ctor_set(x_4271, 1, x_4269);
return x_4271;
}
}
block_4199:
{
lean_dec(x_3187);
if (lean_obj_tag(x_3186) == 0)
{
lean_object* x_3188; lean_object* x_3189; uint8_t x_3190; 
x_3188 = l_Int_Linear_Poly_gcdCoeffs_x27(x_3186);
x_3189 = lean_unsigned_to_nat(1u);
x_3190 = lean_nat_dec_eq(x_3188, x_3189);
if (x_3190 == 0)
{
lean_object* x_3191; lean_object* x_3192; lean_object* x_3193; lean_object* x_3194; uint8_t x_3195; 
x_3191 = l_Int_Linear_Poly_getConst(x_3186);
x_3192 = lean_nat_to_int(x_3188);
x_3193 = lean_int_emod(x_3191, x_3192);
lean_dec(x_3191);
x_3194 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_3195 = lean_int_dec_eq(x_3193, x_3194);
lean_dec(x_3193);
if (x_3195 == 0)
{
lean_object* x_3196; lean_object* x_3197; lean_object* x_3198; 
lean_dec(x_11);
if (lean_is_exclusive(x_3186)) {
 lean_ctor_release(x_3186, 0);
 x_3196 = x_3186;
} else {
 lean_dec_ref(x_3186);
 x_3196 = lean_box(0);
}
x_3197 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3198 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3181);
if (lean_obj_tag(x_3198) == 0)
{
lean_object* x_3199; lean_object* x_3200; lean_object* x_3201; lean_object* x_3202; uint8_t x_3203; lean_object* x_3204; lean_object* x_3205; 
x_3199 = lean_ctor_get(x_3198, 0);
lean_inc(x_3199);
x_3200 = lean_ctor_get(x_3198, 1);
lean_inc(x_3200);
lean_dec(x_3198);
x_3201 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3202 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3203 = lean_int_dec_le(x_3194, x_3192);
x_3204 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3205 = l_Lean_Meta_mkEq(x_3184, x_3204, x_5, x_6, x_7, x_8, x_3200);
if (x_3203 == 0)
{
if (lean_obj_tag(x_3205) == 0)
{
lean_object* x_3206; lean_object* x_3207; lean_object* x_3208; lean_object* x_3209; lean_object* x_3210; lean_object* x_3211; lean_object* x_3212; lean_object* x_3213; lean_object* x_3214; lean_object* x_3215; lean_object* x_3216; lean_object* x_3217; lean_object* x_3218; 
x_3206 = lean_ctor_get(x_3205, 0);
lean_inc(x_3206);
x_3207 = lean_ctor_get(x_3205, 1);
lean_inc(x_3207);
lean_dec(x_3205);
x_3208 = l_Lean_Expr_const___override(x_3, x_3197);
x_3209 = lean_int_neg(x_3192);
lean_dec(x_3192);
x_3210 = l_Int_toNat(x_3209);
lean_dec(x_3209);
x_3211 = l_Lean_instToExprInt_mkNat(x_3210);
x_3212 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_3213 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_3214 = l_Lean_mkApp3(x_3212, x_3208, x_3213, x_3211);
x_3215 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_3216 = l_Lean_reflBoolTrue;
x_3217 = l_Lean_mkApp5(x_3215, x_3199, x_3201, x_3202, x_3214, x_3216);
x_3218 = l_Lean_Meta_mkExpectedTypeHint(x_3217, x_3206, x_5, x_6, x_7, x_8, x_3207);
if (lean_obj_tag(x_3218) == 0)
{
lean_object* x_3219; lean_object* x_3220; lean_object* x_3221; lean_object* x_3222; lean_object* x_3223; lean_object* x_3224; 
x_3219 = lean_ctor_get(x_3218, 0);
lean_inc(x_3219);
x_3220 = lean_ctor_get(x_3218, 1);
lean_inc(x_3220);
if (lean_is_exclusive(x_3218)) {
 lean_ctor_release(x_3218, 0);
 lean_ctor_release(x_3218, 1);
 x_3221 = x_3218;
} else {
 lean_dec_ref(x_3218);
 x_3221 = lean_box(0);
}
x_3222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3222, 0, x_3204);
lean_ctor_set(x_3222, 1, x_3219);
if (lean_is_scalar(x_3196)) {
 x_3223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3223 = x_3196;
 lean_ctor_set_tag(x_3223, 1);
}
lean_ctor_set(x_3223, 0, x_3222);
if (lean_is_scalar(x_3221)) {
 x_3224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3224 = x_3221;
}
lean_ctor_set(x_3224, 0, x_3223);
lean_ctor_set(x_3224, 1, x_3220);
return x_3224;
}
else
{
lean_object* x_3225; lean_object* x_3226; lean_object* x_3227; lean_object* x_3228; 
lean_dec(x_3196);
x_3225 = lean_ctor_get(x_3218, 0);
lean_inc(x_3225);
x_3226 = lean_ctor_get(x_3218, 1);
lean_inc(x_3226);
if (lean_is_exclusive(x_3218)) {
 lean_ctor_release(x_3218, 0);
 lean_ctor_release(x_3218, 1);
 x_3227 = x_3218;
} else {
 lean_dec_ref(x_3218);
 x_3227 = lean_box(0);
}
if (lean_is_scalar(x_3227)) {
 x_3228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3228 = x_3227;
}
lean_ctor_set(x_3228, 0, x_3225);
lean_ctor_set(x_3228, 1, x_3226);
return x_3228;
}
}
else
{
lean_object* x_3229; lean_object* x_3230; lean_object* x_3231; lean_object* x_3232; 
lean_dec(x_3202);
lean_dec(x_3201);
lean_dec(x_3199);
lean_dec(x_3196);
lean_dec(x_3192);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_3229 = lean_ctor_get(x_3205, 0);
lean_inc(x_3229);
x_3230 = lean_ctor_get(x_3205, 1);
lean_inc(x_3230);
if (lean_is_exclusive(x_3205)) {
 lean_ctor_release(x_3205, 0);
 lean_ctor_release(x_3205, 1);
 x_3231 = x_3205;
} else {
 lean_dec_ref(x_3205);
 x_3231 = lean_box(0);
}
if (lean_is_scalar(x_3231)) {
 x_3232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3232 = x_3231;
}
lean_ctor_set(x_3232, 0, x_3229);
lean_ctor_set(x_3232, 1, x_3230);
return x_3232;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_3205) == 0)
{
lean_object* x_3233; lean_object* x_3234; lean_object* x_3235; lean_object* x_3236; lean_object* x_3237; lean_object* x_3238; lean_object* x_3239; lean_object* x_3240; 
x_3233 = lean_ctor_get(x_3205, 0);
lean_inc(x_3233);
x_3234 = lean_ctor_get(x_3205, 1);
lean_inc(x_3234);
lean_dec(x_3205);
x_3235 = l_Int_toNat(x_3192);
lean_dec(x_3192);
x_3236 = l_Lean_instToExprInt_mkNat(x_3235);
x_3237 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_3238 = l_Lean_reflBoolTrue;
x_3239 = l_Lean_mkApp5(x_3237, x_3199, x_3201, x_3202, x_3236, x_3238);
x_3240 = l_Lean_Meta_mkExpectedTypeHint(x_3239, x_3233, x_5, x_6, x_7, x_8, x_3234);
if (lean_obj_tag(x_3240) == 0)
{
lean_object* x_3241; lean_object* x_3242; lean_object* x_3243; lean_object* x_3244; lean_object* x_3245; lean_object* x_3246; 
x_3241 = lean_ctor_get(x_3240, 0);
lean_inc(x_3241);
x_3242 = lean_ctor_get(x_3240, 1);
lean_inc(x_3242);
if (lean_is_exclusive(x_3240)) {
 lean_ctor_release(x_3240, 0);
 lean_ctor_release(x_3240, 1);
 x_3243 = x_3240;
} else {
 lean_dec_ref(x_3240);
 x_3243 = lean_box(0);
}
x_3244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3244, 0, x_3204);
lean_ctor_set(x_3244, 1, x_3241);
if (lean_is_scalar(x_3196)) {
 x_3245 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3245 = x_3196;
 lean_ctor_set_tag(x_3245, 1);
}
lean_ctor_set(x_3245, 0, x_3244);
if (lean_is_scalar(x_3243)) {
 x_3246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3246 = x_3243;
}
lean_ctor_set(x_3246, 0, x_3245);
lean_ctor_set(x_3246, 1, x_3242);
return x_3246;
}
else
{
lean_object* x_3247; lean_object* x_3248; lean_object* x_3249; lean_object* x_3250; 
lean_dec(x_3196);
x_3247 = lean_ctor_get(x_3240, 0);
lean_inc(x_3247);
x_3248 = lean_ctor_get(x_3240, 1);
lean_inc(x_3248);
if (lean_is_exclusive(x_3240)) {
 lean_ctor_release(x_3240, 0);
 lean_ctor_release(x_3240, 1);
 x_3249 = x_3240;
} else {
 lean_dec_ref(x_3240);
 x_3249 = lean_box(0);
}
if (lean_is_scalar(x_3249)) {
 x_3250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3250 = x_3249;
}
lean_ctor_set(x_3250, 0, x_3247);
lean_ctor_set(x_3250, 1, x_3248);
return x_3250;
}
}
else
{
lean_object* x_3251; lean_object* x_3252; lean_object* x_3253; lean_object* x_3254; 
lean_dec(x_3202);
lean_dec(x_3201);
lean_dec(x_3199);
lean_dec(x_3196);
lean_dec(x_3192);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3251 = lean_ctor_get(x_3205, 0);
lean_inc(x_3251);
x_3252 = lean_ctor_get(x_3205, 1);
lean_inc(x_3252);
if (lean_is_exclusive(x_3205)) {
 lean_ctor_release(x_3205, 0);
 lean_ctor_release(x_3205, 1);
 x_3253 = x_3205;
} else {
 lean_dec_ref(x_3205);
 x_3253 = lean_box(0);
}
if (lean_is_scalar(x_3253)) {
 x_3254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3254 = x_3253;
}
lean_ctor_set(x_3254, 0, x_3251);
lean_ctor_set(x_3254, 1, x_3252);
return x_3254;
}
}
}
else
{
lean_object* x_3255; lean_object* x_3256; lean_object* x_3257; lean_object* x_3258; 
lean_dec(x_3196);
lean_dec(x_3192);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3255 = lean_ctor_get(x_3198, 0);
lean_inc(x_3255);
x_3256 = lean_ctor_get(x_3198, 1);
lean_inc(x_3256);
if (lean_is_exclusive(x_3198)) {
 lean_ctor_release(x_3198, 0);
 lean_ctor_release(x_3198, 1);
 x_3257 = x_3198;
} else {
 lean_dec_ref(x_3198);
 x_3257 = lean_box(0);
}
if (lean_is_scalar(x_3257)) {
 x_3258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3258 = x_3257;
}
lean_ctor_set(x_3258, 0, x_3255);
lean_ctor_set(x_3258, 1, x_3256);
return x_3258;
}
}
else
{
lean_object* x_3259; lean_object* x_3260; lean_object* x_3261; lean_object* x_3262; lean_object* x_3263; lean_object* x_3264; lean_object* x_3265; lean_object* x_3266; lean_object* x_3267; 
lean_inc(x_3186);
x_3259 = l_Int_Linear_Poly_div(x_3192, x_3186);
if (lean_is_exclusive(x_3186)) {
 lean_ctor_release(x_3186, 0);
 x_3260 = x_3186;
} else {
 lean_dec_ref(x_3186);
 x_3260 = lean_box(0);
}
lean_inc(x_3259);
x_3261 = l_Int_Linear_Poly_denoteExpr(x_11, x_3259, x_5, x_6, x_7, x_8, x_3181);
x_3262 = lean_ctor_get(x_3261, 0);
lean_inc(x_3262);
x_3263 = lean_ctor_get(x_3261, 1);
lean_inc(x_3263);
if (lean_is_exclusive(x_3261)) {
 lean_ctor_release(x_3261, 0);
 lean_ctor_release(x_3261, 1);
 x_3264 = x_3261;
} else {
 lean_dec_ref(x_3261);
 x_3264 = lean_box(0);
}
x_3265 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_3266 = l_Lean_mkAppB(x_3183, x_3262, x_3265);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3267 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3263);
if (lean_obj_tag(x_3267) == 0)
{
lean_object* x_3268; lean_object* x_3269; lean_object* x_3270; lean_object* x_3271; lean_object* x_3272; lean_object* x_3273; uint8_t x_3274; lean_object* x_3275; 
x_3268 = lean_ctor_get(x_3267, 0);
lean_inc(x_3268);
x_3269 = lean_ctor_get(x_3267, 1);
lean_inc(x_3269);
lean_dec(x_3267);
x_3270 = lean_box(0);
x_3271 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3272 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3273 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_3259);
x_3274 = lean_int_dec_le(x_3194, x_3192);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3266);
x_3275 = l_Lean_Meta_mkEq(x_3184, x_3266, x_5, x_6, x_7, x_8, x_3269);
if (x_3274 == 0)
{
if (lean_obj_tag(x_3275) == 0)
{
lean_object* x_3276; lean_object* x_3277; lean_object* x_3278; lean_object* x_3279; lean_object* x_3280; lean_object* x_3281; lean_object* x_3282; lean_object* x_3283; lean_object* x_3284; lean_object* x_3285; lean_object* x_3286; lean_object* x_3287; lean_object* x_3288; 
x_3276 = lean_ctor_get(x_3275, 0);
lean_inc(x_3276);
x_3277 = lean_ctor_get(x_3275, 1);
lean_inc(x_3277);
lean_dec(x_3275);
x_3278 = l_Lean_Expr_const___override(x_3, x_3270);
x_3279 = lean_int_neg(x_3192);
lean_dec(x_3192);
x_3280 = l_Int_toNat(x_3279);
lean_dec(x_3279);
x_3281 = l_Lean_instToExprInt_mkNat(x_3280);
x_3282 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_3283 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_3284 = l_Lean_mkApp3(x_3282, x_3278, x_3283, x_3281);
x_3285 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_3286 = l_Lean_reflBoolTrue;
x_3287 = l_Lean_mkApp6(x_3285, x_3268, x_3271, x_3272, x_3273, x_3284, x_3286);
x_3288 = l_Lean_Meta_mkExpectedTypeHint(x_3287, x_3276, x_5, x_6, x_7, x_8, x_3277);
if (lean_obj_tag(x_3288) == 0)
{
lean_object* x_3289; lean_object* x_3290; lean_object* x_3291; lean_object* x_3292; lean_object* x_3293; lean_object* x_3294; 
x_3289 = lean_ctor_get(x_3288, 0);
lean_inc(x_3289);
x_3290 = lean_ctor_get(x_3288, 1);
lean_inc(x_3290);
if (lean_is_exclusive(x_3288)) {
 lean_ctor_release(x_3288, 0);
 lean_ctor_release(x_3288, 1);
 x_3291 = x_3288;
} else {
 lean_dec_ref(x_3288);
 x_3291 = lean_box(0);
}
if (lean_is_scalar(x_3264)) {
 x_3292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3292 = x_3264;
}
lean_ctor_set(x_3292, 0, x_3266);
lean_ctor_set(x_3292, 1, x_3289);
if (lean_is_scalar(x_3260)) {
 x_3293 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3293 = x_3260;
 lean_ctor_set_tag(x_3293, 1);
}
lean_ctor_set(x_3293, 0, x_3292);
if (lean_is_scalar(x_3291)) {
 x_3294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3294 = x_3291;
}
lean_ctor_set(x_3294, 0, x_3293);
lean_ctor_set(x_3294, 1, x_3290);
return x_3294;
}
else
{
lean_object* x_3295; lean_object* x_3296; lean_object* x_3297; lean_object* x_3298; 
lean_dec(x_3266);
lean_dec(x_3264);
lean_dec(x_3260);
x_3295 = lean_ctor_get(x_3288, 0);
lean_inc(x_3295);
x_3296 = lean_ctor_get(x_3288, 1);
lean_inc(x_3296);
if (lean_is_exclusive(x_3288)) {
 lean_ctor_release(x_3288, 0);
 lean_ctor_release(x_3288, 1);
 x_3297 = x_3288;
} else {
 lean_dec_ref(x_3288);
 x_3297 = lean_box(0);
}
if (lean_is_scalar(x_3297)) {
 x_3298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3298 = x_3297;
}
lean_ctor_set(x_3298, 0, x_3295);
lean_ctor_set(x_3298, 1, x_3296);
return x_3298;
}
}
else
{
lean_object* x_3299; lean_object* x_3300; lean_object* x_3301; lean_object* x_3302; 
lean_dec(x_3273);
lean_dec(x_3272);
lean_dec(x_3271);
lean_dec(x_3268);
lean_dec(x_3266);
lean_dec(x_3264);
lean_dec(x_3260);
lean_dec(x_3192);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_3299 = lean_ctor_get(x_3275, 0);
lean_inc(x_3299);
x_3300 = lean_ctor_get(x_3275, 1);
lean_inc(x_3300);
if (lean_is_exclusive(x_3275)) {
 lean_ctor_release(x_3275, 0);
 lean_ctor_release(x_3275, 1);
 x_3301 = x_3275;
} else {
 lean_dec_ref(x_3275);
 x_3301 = lean_box(0);
}
if (lean_is_scalar(x_3301)) {
 x_3302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3302 = x_3301;
}
lean_ctor_set(x_3302, 0, x_3299);
lean_ctor_set(x_3302, 1, x_3300);
return x_3302;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_3275) == 0)
{
lean_object* x_3303; lean_object* x_3304; lean_object* x_3305; lean_object* x_3306; lean_object* x_3307; lean_object* x_3308; lean_object* x_3309; lean_object* x_3310; 
x_3303 = lean_ctor_get(x_3275, 0);
lean_inc(x_3303);
x_3304 = lean_ctor_get(x_3275, 1);
lean_inc(x_3304);
lean_dec(x_3275);
x_3305 = l_Int_toNat(x_3192);
lean_dec(x_3192);
x_3306 = l_Lean_instToExprInt_mkNat(x_3305);
x_3307 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_3308 = l_Lean_reflBoolTrue;
x_3309 = l_Lean_mkApp6(x_3307, x_3268, x_3271, x_3272, x_3273, x_3306, x_3308);
x_3310 = l_Lean_Meta_mkExpectedTypeHint(x_3309, x_3303, x_5, x_6, x_7, x_8, x_3304);
if (lean_obj_tag(x_3310) == 0)
{
lean_object* x_3311; lean_object* x_3312; lean_object* x_3313; lean_object* x_3314; lean_object* x_3315; lean_object* x_3316; 
x_3311 = lean_ctor_get(x_3310, 0);
lean_inc(x_3311);
x_3312 = lean_ctor_get(x_3310, 1);
lean_inc(x_3312);
if (lean_is_exclusive(x_3310)) {
 lean_ctor_release(x_3310, 0);
 lean_ctor_release(x_3310, 1);
 x_3313 = x_3310;
} else {
 lean_dec_ref(x_3310);
 x_3313 = lean_box(0);
}
if (lean_is_scalar(x_3264)) {
 x_3314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3314 = x_3264;
}
lean_ctor_set(x_3314, 0, x_3266);
lean_ctor_set(x_3314, 1, x_3311);
if (lean_is_scalar(x_3260)) {
 x_3315 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3315 = x_3260;
 lean_ctor_set_tag(x_3315, 1);
}
lean_ctor_set(x_3315, 0, x_3314);
if (lean_is_scalar(x_3313)) {
 x_3316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3316 = x_3313;
}
lean_ctor_set(x_3316, 0, x_3315);
lean_ctor_set(x_3316, 1, x_3312);
return x_3316;
}
else
{
lean_object* x_3317; lean_object* x_3318; lean_object* x_3319; lean_object* x_3320; 
lean_dec(x_3266);
lean_dec(x_3264);
lean_dec(x_3260);
x_3317 = lean_ctor_get(x_3310, 0);
lean_inc(x_3317);
x_3318 = lean_ctor_get(x_3310, 1);
lean_inc(x_3318);
if (lean_is_exclusive(x_3310)) {
 lean_ctor_release(x_3310, 0);
 lean_ctor_release(x_3310, 1);
 x_3319 = x_3310;
} else {
 lean_dec_ref(x_3310);
 x_3319 = lean_box(0);
}
if (lean_is_scalar(x_3319)) {
 x_3320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3320 = x_3319;
}
lean_ctor_set(x_3320, 0, x_3317);
lean_ctor_set(x_3320, 1, x_3318);
return x_3320;
}
}
else
{
lean_object* x_3321; lean_object* x_3322; lean_object* x_3323; lean_object* x_3324; 
lean_dec(x_3273);
lean_dec(x_3272);
lean_dec(x_3271);
lean_dec(x_3268);
lean_dec(x_3266);
lean_dec(x_3264);
lean_dec(x_3260);
lean_dec(x_3192);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3321 = lean_ctor_get(x_3275, 0);
lean_inc(x_3321);
x_3322 = lean_ctor_get(x_3275, 1);
lean_inc(x_3322);
if (lean_is_exclusive(x_3275)) {
 lean_ctor_release(x_3275, 0);
 lean_ctor_release(x_3275, 1);
 x_3323 = x_3275;
} else {
 lean_dec_ref(x_3275);
 x_3323 = lean_box(0);
}
if (lean_is_scalar(x_3323)) {
 x_3324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3324 = x_3323;
}
lean_ctor_set(x_3324, 0, x_3321);
lean_ctor_set(x_3324, 1, x_3322);
return x_3324;
}
}
}
else
{
lean_object* x_3325; lean_object* x_3326; lean_object* x_3327; lean_object* x_3328; 
lean_dec(x_3266);
lean_dec(x_3264);
lean_dec(x_3260);
lean_dec(x_3259);
lean_dec(x_3192);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3325 = lean_ctor_get(x_3267, 0);
lean_inc(x_3325);
x_3326 = lean_ctor_get(x_3267, 1);
lean_inc(x_3326);
if (lean_is_exclusive(x_3267)) {
 lean_ctor_release(x_3267, 0);
 lean_ctor_release(x_3267, 1);
 x_3327 = x_3267;
} else {
 lean_dec_ref(x_3267);
 x_3327 = lean_box(0);
}
if (lean_is_scalar(x_3327)) {
 x_3328 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3328 = x_3327;
}
lean_ctor_set(x_3328, 0, x_3325);
lean_ctor_set(x_3328, 1, x_3326);
return x_3328;
}
}
}
else
{
lean_object* x_3329; lean_object* x_3330; lean_object* x_3331; lean_object* x_3332; lean_object* x_3333; lean_object* x_3334; lean_object* x_3335; 
lean_dec(x_3188);
lean_dec(x_3);
lean_inc(x_3186);
x_3329 = l_Int_Linear_Poly_denoteExpr(x_11, x_3186, x_5, x_6, x_7, x_8, x_3181);
x_3330 = lean_ctor_get(x_3329, 0);
lean_inc(x_3330);
x_3331 = lean_ctor_get(x_3329, 1);
lean_inc(x_3331);
if (lean_is_exclusive(x_3329)) {
 lean_ctor_release(x_3329, 0);
 lean_ctor_release(x_3329, 1);
 x_3332 = x_3329;
} else {
 lean_dec_ref(x_3329);
 x_3332 = lean_box(0);
}
x_3333 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_3334 = l_Lean_mkAppB(x_3183, x_3330, x_3333);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3335 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3331);
if (lean_obj_tag(x_3335) == 0)
{
lean_object* x_3336; lean_object* x_3337; lean_object* x_3338; lean_object* x_3339; lean_object* x_3340; lean_object* x_3341; lean_object* x_3342; lean_object* x_3343; lean_object* x_3344; lean_object* x_3345; 
x_3336 = lean_ctor_get(x_3335, 0);
lean_inc(x_3336);
x_3337 = lean_ctor_get(x_3335, 1);
lean_inc(x_3337);
lean_dec(x_3335);
x_3338 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3339 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
lean_inc(x_3186);
x_3340 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_3186);
if (lean_is_exclusive(x_3186)) {
 lean_ctor_release(x_3186, 0);
 x_3341 = x_3186;
} else {
 lean_dec_ref(x_3186);
 x_3341 = lean_box(0);
}
x_3342 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_3343 = l_Lean_reflBoolTrue;
x_3344 = l_Lean_mkApp5(x_3342, x_3336, x_3338, x_3339, x_3340, x_3343);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3334);
x_3345 = l_Lean_Meta_mkEq(x_3184, x_3334, x_5, x_6, x_7, x_8, x_3337);
if (lean_obj_tag(x_3345) == 0)
{
lean_object* x_3346; lean_object* x_3347; lean_object* x_3348; 
x_3346 = lean_ctor_get(x_3345, 0);
lean_inc(x_3346);
x_3347 = lean_ctor_get(x_3345, 1);
lean_inc(x_3347);
lean_dec(x_3345);
x_3348 = l_Lean_Meta_mkExpectedTypeHint(x_3344, x_3346, x_5, x_6, x_7, x_8, x_3347);
if (lean_obj_tag(x_3348) == 0)
{
lean_object* x_3349; lean_object* x_3350; lean_object* x_3351; lean_object* x_3352; lean_object* x_3353; lean_object* x_3354; 
x_3349 = lean_ctor_get(x_3348, 0);
lean_inc(x_3349);
x_3350 = lean_ctor_get(x_3348, 1);
lean_inc(x_3350);
if (lean_is_exclusive(x_3348)) {
 lean_ctor_release(x_3348, 0);
 lean_ctor_release(x_3348, 1);
 x_3351 = x_3348;
} else {
 lean_dec_ref(x_3348);
 x_3351 = lean_box(0);
}
if (lean_is_scalar(x_3332)) {
 x_3352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3352 = x_3332;
}
lean_ctor_set(x_3352, 0, x_3334);
lean_ctor_set(x_3352, 1, x_3349);
if (lean_is_scalar(x_3341)) {
 x_3353 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3353 = x_3341;
 lean_ctor_set_tag(x_3353, 1);
}
lean_ctor_set(x_3353, 0, x_3352);
if (lean_is_scalar(x_3351)) {
 x_3354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3354 = x_3351;
}
lean_ctor_set(x_3354, 0, x_3353);
lean_ctor_set(x_3354, 1, x_3350);
return x_3354;
}
else
{
lean_object* x_3355; lean_object* x_3356; lean_object* x_3357; lean_object* x_3358; 
lean_dec(x_3341);
lean_dec(x_3334);
lean_dec(x_3332);
x_3355 = lean_ctor_get(x_3348, 0);
lean_inc(x_3355);
x_3356 = lean_ctor_get(x_3348, 1);
lean_inc(x_3356);
if (lean_is_exclusive(x_3348)) {
 lean_ctor_release(x_3348, 0);
 lean_ctor_release(x_3348, 1);
 x_3357 = x_3348;
} else {
 lean_dec_ref(x_3348);
 x_3357 = lean_box(0);
}
if (lean_is_scalar(x_3357)) {
 x_3358 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3358 = x_3357;
}
lean_ctor_set(x_3358, 0, x_3355);
lean_ctor_set(x_3358, 1, x_3356);
return x_3358;
}
}
else
{
lean_object* x_3359; lean_object* x_3360; lean_object* x_3361; lean_object* x_3362; 
lean_dec(x_3344);
lean_dec(x_3341);
lean_dec(x_3334);
lean_dec(x_3332);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3359 = lean_ctor_get(x_3345, 0);
lean_inc(x_3359);
x_3360 = lean_ctor_get(x_3345, 1);
lean_inc(x_3360);
if (lean_is_exclusive(x_3345)) {
 lean_ctor_release(x_3345, 0);
 lean_ctor_release(x_3345, 1);
 x_3361 = x_3345;
} else {
 lean_dec_ref(x_3345);
 x_3361 = lean_box(0);
}
if (lean_is_scalar(x_3361)) {
 x_3362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3362 = x_3361;
}
lean_ctor_set(x_3362, 0, x_3359);
lean_ctor_set(x_3362, 1, x_3360);
return x_3362;
}
}
else
{
lean_object* x_3363; lean_object* x_3364; lean_object* x_3365; lean_object* x_3366; 
lean_dec(x_3334);
lean_dec(x_3332);
lean_dec(x_3186);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_3363 = lean_ctor_get(x_3335, 0);
lean_inc(x_3363);
x_3364 = lean_ctor_get(x_3335, 1);
lean_inc(x_3364);
if (lean_is_exclusive(x_3335)) {
 lean_ctor_release(x_3335, 0);
 lean_ctor_release(x_3335, 1);
 x_3365 = x_3335;
} else {
 lean_dec_ref(x_3335);
 x_3365 = lean_box(0);
}
if (lean_is_scalar(x_3365)) {
 x_3366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3366 = x_3365;
}
lean_ctor_set(x_3366, 0, x_3363);
lean_ctor_set(x_3366, 1, x_3364);
return x_3366;
}
}
}
else
{
lean_object* x_3367; lean_object* x_3368; lean_object* x_3369; lean_object* x_3370; uint8_t x_3371; 
x_3367 = lean_ctor_get(x_3186, 0);
lean_inc(x_3367);
x_3368 = lean_ctor_get(x_3186, 1);
lean_inc(x_3368);
x_3369 = lean_ctor_get(x_3186, 2);
lean_inc(x_3369);
x_3370 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__26;
x_3371 = lean_int_dec_eq(x_3367, x_3370);
lean_dec(x_3367);
if (x_3371 == 0)
{
lean_object* x_3372; lean_object* x_3373; uint8_t x_3374; 
lean_dec(x_3369);
lean_dec(x_3368);
x_3372 = l_Int_Linear_Poly_gcdCoeffs_x27(x_3186);
x_3373 = lean_unsigned_to_nat(1u);
x_3374 = lean_nat_dec_eq(x_3372, x_3373);
if (x_3374 == 0)
{
lean_object* x_3375; lean_object* x_3376; lean_object* x_3377; lean_object* x_3378; uint8_t x_3379; 
x_3375 = l_Int_Linear_Poly_getConst(x_3186);
x_3376 = lean_nat_to_int(x_3372);
x_3377 = lean_int_emod(x_3375, x_3376);
lean_dec(x_3375);
x_3378 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_3379 = lean_int_dec_eq(x_3377, x_3378);
lean_dec(x_3377);
if (x_3379 == 0)
{
lean_object* x_3380; lean_object* x_3381; 
lean_dec(x_3186);
lean_dec(x_11);
x_3380 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3381 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3181);
if (lean_obj_tag(x_3381) == 0)
{
lean_object* x_3382; lean_object* x_3383; lean_object* x_3384; lean_object* x_3385; uint8_t x_3386; lean_object* x_3387; lean_object* x_3388; 
x_3382 = lean_ctor_get(x_3381, 0);
lean_inc(x_3382);
x_3383 = lean_ctor_get(x_3381, 1);
lean_inc(x_3383);
lean_dec(x_3381);
x_3384 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3385 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3386 = lean_int_dec_le(x_3378, x_3376);
x_3387 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3388 = l_Lean_Meta_mkEq(x_3184, x_3387, x_5, x_6, x_7, x_8, x_3383);
if (x_3386 == 0)
{
if (lean_obj_tag(x_3388) == 0)
{
lean_object* x_3389; lean_object* x_3390; lean_object* x_3391; lean_object* x_3392; lean_object* x_3393; lean_object* x_3394; lean_object* x_3395; lean_object* x_3396; lean_object* x_3397; lean_object* x_3398; lean_object* x_3399; lean_object* x_3400; lean_object* x_3401; 
x_3389 = lean_ctor_get(x_3388, 0);
lean_inc(x_3389);
x_3390 = lean_ctor_get(x_3388, 1);
lean_inc(x_3390);
lean_dec(x_3388);
x_3391 = l_Lean_Expr_const___override(x_3, x_3380);
x_3392 = lean_int_neg(x_3376);
lean_dec(x_3376);
x_3393 = l_Int_toNat(x_3392);
lean_dec(x_3392);
x_3394 = l_Lean_instToExprInt_mkNat(x_3393);
x_3395 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_3396 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_3397 = l_Lean_mkApp3(x_3395, x_3391, x_3396, x_3394);
x_3398 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_3399 = l_Lean_reflBoolTrue;
x_3400 = l_Lean_mkApp5(x_3398, x_3382, x_3384, x_3385, x_3397, x_3399);
x_3401 = l_Lean_Meta_mkExpectedTypeHint(x_3400, x_3389, x_5, x_6, x_7, x_8, x_3390);
if (lean_obj_tag(x_3401) == 0)
{
lean_object* x_3402; lean_object* x_3403; lean_object* x_3404; lean_object* x_3405; lean_object* x_3406; lean_object* x_3407; 
x_3402 = lean_ctor_get(x_3401, 0);
lean_inc(x_3402);
x_3403 = lean_ctor_get(x_3401, 1);
lean_inc(x_3403);
if (lean_is_exclusive(x_3401)) {
 lean_ctor_release(x_3401, 0);
 lean_ctor_release(x_3401, 1);
 x_3404 = x_3401;
} else {
 lean_dec_ref(x_3401);
 x_3404 = lean_box(0);
}
x_3405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3405, 0, x_3387);
lean_ctor_set(x_3405, 1, x_3402);
x_3406 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3406, 0, x_3405);
if (lean_is_scalar(x_3404)) {
 x_3407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3407 = x_3404;
}
lean_ctor_set(x_3407, 0, x_3406);
lean_ctor_set(x_3407, 1, x_3403);
return x_3407;
}
else
{
lean_object* x_3408; lean_object* x_3409; lean_object* x_3410; lean_object* x_3411; 
x_3408 = lean_ctor_get(x_3401, 0);
lean_inc(x_3408);
x_3409 = lean_ctor_get(x_3401, 1);
lean_inc(x_3409);
if (lean_is_exclusive(x_3401)) {
 lean_ctor_release(x_3401, 0);
 lean_ctor_release(x_3401, 1);
 x_3410 = x_3401;
} else {
 lean_dec_ref(x_3401);
 x_3410 = lean_box(0);
}
if (lean_is_scalar(x_3410)) {
 x_3411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3411 = x_3410;
}
lean_ctor_set(x_3411, 0, x_3408);
lean_ctor_set(x_3411, 1, x_3409);
return x_3411;
}
}
else
{
lean_object* x_3412; lean_object* x_3413; lean_object* x_3414; lean_object* x_3415; 
lean_dec(x_3385);
lean_dec(x_3384);
lean_dec(x_3382);
lean_dec(x_3376);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_3412 = lean_ctor_get(x_3388, 0);
lean_inc(x_3412);
x_3413 = lean_ctor_get(x_3388, 1);
lean_inc(x_3413);
if (lean_is_exclusive(x_3388)) {
 lean_ctor_release(x_3388, 0);
 lean_ctor_release(x_3388, 1);
 x_3414 = x_3388;
} else {
 lean_dec_ref(x_3388);
 x_3414 = lean_box(0);
}
if (lean_is_scalar(x_3414)) {
 x_3415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3415 = x_3414;
}
lean_ctor_set(x_3415, 0, x_3412);
lean_ctor_set(x_3415, 1, x_3413);
return x_3415;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_3388) == 0)
{
lean_object* x_3416; lean_object* x_3417; lean_object* x_3418; lean_object* x_3419; lean_object* x_3420; lean_object* x_3421; lean_object* x_3422; lean_object* x_3423; 
x_3416 = lean_ctor_get(x_3388, 0);
lean_inc(x_3416);
x_3417 = lean_ctor_get(x_3388, 1);
lean_inc(x_3417);
lean_dec(x_3388);
x_3418 = l_Int_toNat(x_3376);
lean_dec(x_3376);
x_3419 = l_Lean_instToExprInt_mkNat(x_3418);
x_3420 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_3421 = l_Lean_reflBoolTrue;
x_3422 = l_Lean_mkApp5(x_3420, x_3382, x_3384, x_3385, x_3419, x_3421);
x_3423 = l_Lean_Meta_mkExpectedTypeHint(x_3422, x_3416, x_5, x_6, x_7, x_8, x_3417);
if (lean_obj_tag(x_3423) == 0)
{
lean_object* x_3424; lean_object* x_3425; lean_object* x_3426; lean_object* x_3427; lean_object* x_3428; lean_object* x_3429; 
x_3424 = lean_ctor_get(x_3423, 0);
lean_inc(x_3424);
x_3425 = lean_ctor_get(x_3423, 1);
lean_inc(x_3425);
if (lean_is_exclusive(x_3423)) {
 lean_ctor_release(x_3423, 0);
 lean_ctor_release(x_3423, 1);
 x_3426 = x_3423;
} else {
 lean_dec_ref(x_3423);
 x_3426 = lean_box(0);
}
x_3427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3427, 0, x_3387);
lean_ctor_set(x_3427, 1, x_3424);
x_3428 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3428, 0, x_3427);
if (lean_is_scalar(x_3426)) {
 x_3429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3429 = x_3426;
}
lean_ctor_set(x_3429, 0, x_3428);
lean_ctor_set(x_3429, 1, x_3425);
return x_3429;
}
else
{
lean_object* x_3430; lean_object* x_3431; lean_object* x_3432; lean_object* x_3433; 
x_3430 = lean_ctor_get(x_3423, 0);
lean_inc(x_3430);
x_3431 = lean_ctor_get(x_3423, 1);
lean_inc(x_3431);
if (lean_is_exclusive(x_3423)) {
 lean_ctor_release(x_3423, 0);
 lean_ctor_release(x_3423, 1);
 x_3432 = x_3423;
} else {
 lean_dec_ref(x_3423);
 x_3432 = lean_box(0);
}
if (lean_is_scalar(x_3432)) {
 x_3433 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3433 = x_3432;
}
lean_ctor_set(x_3433, 0, x_3430);
lean_ctor_set(x_3433, 1, x_3431);
return x_3433;
}
}
else
{
lean_object* x_3434; lean_object* x_3435; lean_object* x_3436; lean_object* x_3437; 
lean_dec(x_3385);
lean_dec(x_3384);
lean_dec(x_3382);
lean_dec(x_3376);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3434 = lean_ctor_get(x_3388, 0);
lean_inc(x_3434);
x_3435 = lean_ctor_get(x_3388, 1);
lean_inc(x_3435);
if (lean_is_exclusive(x_3388)) {
 lean_ctor_release(x_3388, 0);
 lean_ctor_release(x_3388, 1);
 x_3436 = x_3388;
} else {
 lean_dec_ref(x_3388);
 x_3436 = lean_box(0);
}
if (lean_is_scalar(x_3436)) {
 x_3437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3437 = x_3436;
}
lean_ctor_set(x_3437, 0, x_3434);
lean_ctor_set(x_3437, 1, x_3435);
return x_3437;
}
}
}
else
{
lean_object* x_3438; lean_object* x_3439; lean_object* x_3440; lean_object* x_3441; 
lean_dec(x_3376);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3438 = lean_ctor_get(x_3381, 0);
lean_inc(x_3438);
x_3439 = lean_ctor_get(x_3381, 1);
lean_inc(x_3439);
if (lean_is_exclusive(x_3381)) {
 lean_ctor_release(x_3381, 0);
 lean_ctor_release(x_3381, 1);
 x_3440 = x_3381;
} else {
 lean_dec_ref(x_3381);
 x_3440 = lean_box(0);
}
if (lean_is_scalar(x_3440)) {
 x_3441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3441 = x_3440;
}
lean_ctor_set(x_3441, 0, x_3438);
lean_ctor_set(x_3441, 1, x_3439);
return x_3441;
}
}
else
{
lean_object* x_3442; lean_object* x_3443; lean_object* x_3444; lean_object* x_3445; lean_object* x_3446; lean_object* x_3447; lean_object* x_3448; lean_object* x_3449; 
x_3442 = l_Int_Linear_Poly_div(x_3376, x_3186);
lean_inc(x_3442);
x_3443 = l_Int_Linear_Poly_denoteExpr(x_11, x_3442, x_5, x_6, x_7, x_8, x_3181);
x_3444 = lean_ctor_get(x_3443, 0);
lean_inc(x_3444);
x_3445 = lean_ctor_get(x_3443, 1);
lean_inc(x_3445);
if (lean_is_exclusive(x_3443)) {
 lean_ctor_release(x_3443, 0);
 lean_ctor_release(x_3443, 1);
 x_3446 = x_3443;
} else {
 lean_dec_ref(x_3443);
 x_3446 = lean_box(0);
}
x_3447 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_3448 = l_Lean_mkAppB(x_3183, x_3444, x_3447);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3449 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3445);
if (lean_obj_tag(x_3449) == 0)
{
lean_object* x_3450; lean_object* x_3451; lean_object* x_3452; lean_object* x_3453; lean_object* x_3454; lean_object* x_3455; uint8_t x_3456; lean_object* x_3457; 
x_3450 = lean_ctor_get(x_3449, 0);
lean_inc(x_3450);
x_3451 = lean_ctor_get(x_3449, 1);
lean_inc(x_3451);
lean_dec(x_3449);
x_3452 = lean_box(0);
x_3453 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3454 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3455 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_3442);
x_3456 = lean_int_dec_le(x_3378, x_3376);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3448);
x_3457 = l_Lean_Meta_mkEq(x_3184, x_3448, x_5, x_6, x_7, x_8, x_3451);
if (x_3456 == 0)
{
if (lean_obj_tag(x_3457) == 0)
{
lean_object* x_3458; lean_object* x_3459; lean_object* x_3460; lean_object* x_3461; lean_object* x_3462; lean_object* x_3463; lean_object* x_3464; lean_object* x_3465; lean_object* x_3466; lean_object* x_3467; lean_object* x_3468; lean_object* x_3469; lean_object* x_3470; 
x_3458 = lean_ctor_get(x_3457, 0);
lean_inc(x_3458);
x_3459 = lean_ctor_get(x_3457, 1);
lean_inc(x_3459);
lean_dec(x_3457);
x_3460 = l_Lean_Expr_const___override(x_3, x_3452);
x_3461 = lean_int_neg(x_3376);
lean_dec(x_3376);
x_3462 = l_Int_toNat(x_3461);
lean_dec(x_3461);
x_3463 = l_Lean_instToExprInt_mkNat(x_3462);
x_3464 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_3465 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_3466 = l_Lean_mkApp3(x_3464, x_3460, x_3465, x_3463);
x_3467 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_3468 = l_Lean_reflBoolTrue;
x_3469 = l_Lean_mkApp6(x_3467, x_3450, x_3453, x_3454, x_3455, x_3466, x_3468);
x_3470 = l_Lean_Meta_mkExpectedTypeHint(x_3469, x_3458, x_5, x_6, x_7, x_8, x_3459);
if (lean_obj_tag(x_3470) == 0)
{
lean_object* x_3471; lean_object* x_3472; lean_object* x_3473; lean_object* x_3474; lean_object* x_3475; lean_object* x_3476; 
x_3471 = lean_ctor_get(x_3470, 0);
lean_inc(x_3471);
x_3472 = lean_ctor_get(x_3470, 1);
lean_inc(x_3472);
if (lean_is_exclusive(x_3470)) {
 lean_ctor_release(x_3470, 0);
 lean_ctor_release(x_3470, 1);
 x_3473 = x_3470;
} else {
 lean_dec_ref(x_3470);
 x_3473 = lean_box(0);
}
if (lean_is_scalar(x_3446)) {
 x_3474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3474 = x_3446;
}
lean_ctor_set(x_3474, 0, x_3448);
lean_ctor_set(x_3474, 1, x_3471);
x_3475 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3475, 0, x_3474);
if (lean_is_scalar(x_3473)) {
 x_3476 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3476 = x_3473;
}
lean_ctor_set(x_3476, 0, x_3475);
lean_ctor_set(x_3476, 1, x_3472);
return x_3476;
}
else
{
lean_object* x_3477; lean_object* x_3478; lean_object* x_3479; lean_object* x_3480; 
lean_dec(x_3448);
lean_dec(x_3446);
x_3477 = lean_ctor_get(x_3470, 0);
lean_inc(x_3477);
x_3478 = lean_ctor_get(x_3470, 1);
lean_inc(x_3478);
if (lean_is_exclusive(x_3470)) {
 lean_ctor_release(x_3470, 0);
 lean_ctor_release(x_3470, 1);
 x_3479 = x_3470;
} else {
 lean_dec_ref(x_3470);
 x_3479 = lean_box(0);
}
if (lean_is_scalar(x_3479)) {
 x_3480 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3480 = x_3479;
}
lean_ctor_set(x_3480, 0, x_3477);
lean_ctor_set(x_3480, 1, x_3478);
return x_3480;
}
}
else
{
lean_object* x_3481; lean_object* x_3482; lean_object* x_3483; lean_object* x_3484; 
lean_dec(x_3455);
lean_dec(x_3454);
lean_dec(x_3453);
lean_dec(x_3450);
lean_dec(x_3448);
lean_dec(x_3446);
lean_dec(x_3376);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_3481 = lean_ctor_get(x_3457, 0);
lean_inc(x_3481);
x_3482 = lean_ctor_get(x_3457, 1);
lean_inc(x_3482);
if (lean_is_exclusive(x_3457)) {
 lean_ctor_release(x_3457, 0);
 lean_ctor_release(x_3457, 1);
 x_3483 = x_3457;
} else {
 lean_dec_ref(x_3457);
 x_3483 = lean_box(0);
}
if (lean_is_scalar(x_3483)) {
 x_3484 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3484 = x_3483;
}
lean_ctor_set(x_3484, 0, x_3481);
lean_ctor_set(x_3484, 1, x_3482);
return x_3484;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_3457) == 0)
{
lean_object* x_3485; lean_object* x_3486; lean_object* x_3487; lean_object* x_3488; lean_object* x_3489; lean_object* x_3490; lean_object* x_3491; lean_object* x_3492; 
x_3485 = lean_ctor_get(x_3457, 0);
lean_inc(x_3485);
x_3486 = lean_ctor_get(x_3457, 1);
lean_inc(x_3486);
lean_dec(x_3457);
x_3487 = l_Int_toNat(x_3376);
lean_dec(x_3376);
x_3488 = l_Lean_instToExprInt_mkNat(x_3487);
x_3489 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_3490 = l_Lean_reflBoolTrue;
x_3491 = l_Lean_mkApp6(x_3489, x_3450, x_3453, x_3454, x_3455, x_3488, x_3490);
x_3492 = l_Lean_Meta_mkExpectedTypeHint(x_3491, x_3485, x_5, x_6, x_7, x_8, x_3486);
if (lean_obj_tag(x_3492) == 0)
{
lean_object* x_3493; lean_object* x_3494; lean_object* x_3495; lean_object* x_3496; lean_object* x_3497; lean_object* x_3498; 
x_3493 = lean_ctor_get(x_3492, 0);
lean_inc(x_3493);
x_3494 = lean_ctor_get(x_3492, 1);
lean_inc(x_3494);
if (lean_is_exclusive(x_3492)) {
 lean_ctor_release(x_3492, 0);
 lean_ctor_release(x_3492, 1);
 x_3495 = x_3492;
} else {
 lean_dec_ref(x_3492);
 x_3495 = lean_box(0);
}
if (lean_is_scalar(x_3446)) {
 x_3496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3496 = x_3446;
}
lean_ctor_set(x_3496, 0, x_3448);
lean_ctor_set(x_3496, 1, x_3493);
x_3497 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3497, 0, x_3496);
if (lean_is_scalar(x_3495)) {
 x_3498 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3498 = x_3495;
}
lean_ctor_set(x_3498, 0, x_3497);
lean_ctor_set(x_3498, 1, x_3494);
return x_3498;
}
else
{
lean_object* x_3499; lean_object* x_3500; lean_object* x_3501; lean_object* x_3502; 
lean_dec(x_3448);
lean_dec(x_3446);
x_3499 = lean_ctor_get(x_3492, 0);
lean_inc(x_3499);
x_3500 = lean_ctor_get(x_3492, 1);
lean_inc(x_3500);
if (lean_is_exclusive(x_3492)) {
 lean_ctor_release(x_3492, 0);
 lean_ctor_release(x_3492, 1);
 x_3501 = x_3492;
} else {
 lean_dec_ref(x_3492);
 x_3501 = lean_box(0);
}
if (lean_is_scalar(x_3501)) {
 x_3502 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3502 = x_3501;
}
lean_ctor_set(x_3502, 0, x_3499);
lean_ctor_set(x_3502, 1, x_3500);
return x_3502;
}
}
else
{
lean_object* x_3503; lean_object* x_3504; lean_object* x_3505; lean_object* x_3506; 
lean_dec(x_3455);
lean_dec(x_3454);
lean_dec(x_3453);
lean_dec(x_3450);
lean_dec(x_3448);
lean_dec(x_3446);
lean_dec(x_3376);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3503 = lean_ctor_get(x_3457, 0);
lean_inc(x_3503);
x_3504 = lean_ctor_get(x_3457, 1);
lean_inc(x_3504);
if (lean_is_exclusive(x_3457)) {
 lean_ctor_release(x_3457, 0);
 lean_ctor_release(x_3457, 1);
 x_3505 = x_3457;
} else {
 lean_dec_ref(x_3457);
 x_3505 = lean_box(0);
}
if (lean_is_scalar(x_3505)) {
 x_3506 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3506 = x_3505;
}
lean_ctor_set(x_3506, 0, x_3503);
lean_ctor_set(x_3506, 1, x_3504);
return x_3506;
}
}
}
else
{
lean_object* x_3507; lean_object* x_3508; lean_object* x_3509; lean_object* x_3510; 
lean_dec(x_3448);
lean_dec(x_3446);
lean_dec(x_3442);
lean_dec(x_3376);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3507 = lean_ctor_get(x_3449, 0);
lean_inc(x_3507);
x_3508 = lean_ctor_get(x_3449, 1);
lean_inc(x_3508);
if (lean_is_exclusive(x_3449)) {
 lean_ctor_release(x_3449, 0);
 lean_ctor_release(x_3449, 1);
 x_3509 = x_3449;
} else {
 lean_dec_ref(x_3449);
 x_3509 = lean_box(0);
}
if (lean_is_scalar(x_3509)) {
 x_3510 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3510 = x_3509;
}
lean_ctor_set(x_3510, 0, x_3507);
lean_ctor_set(x_3510, 1, x_3508);
return x_3510;
}
}
}
else
{
lean_object* x_3511; lean_object* x_3512; lean_object* x_3513; lean_object* x_3514; lean_object* x_3515; lean_object* x_3516; lean_object* x_3517; 
lean_dec(x_3372);
lean_dec(x_3);
lean_inc(x_3186);
x_3511 = l_Int_Linear_Poly_denoteExpr(x_11, x_3186, x_5, x_6, x_7, x_8, x_3181);
x_3512 = lean_ctor_get(x_3511, 0);
lean_inc(x_3512);
x_3513 = lean_ctor_get(x_3511, 1);
lean_inc(x_3513);
if (lean_is_exclusive(x_3511)) {
 lean_ctor_release(x_3511, 0);
 lean_ctor_release(x_3511, 1);
 x_3514 = x_3511;
} else {
 lean_dec_ref(x_3511);
 x_3514 = lean_box(0);
}
x_3515 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_3516 = l_Lean_mkAppB(x_3183, x_3512, x_3515);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3517 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3513);
if (lean_obj_tag(x_3517) == 0)
{
lean_object* x_3518; lean_object* x_3519; lean_object* x_3520; lean_object* x_3521; lean_object* x_3522; lean_object* x_3523; lean_object* x_3524; lean_object* x_3525; lean_object* x_3526; 
x_3518 = lean_ctor_get(x_3517, 0);
lean_inc(x_3518);
x_3519 = lean_ctor_get(x_3517, 1);
lean_inc(x_3519);
lean_dec(x_3517);
x_3520 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3521 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3522 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_3186);
x_3523 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_3524 = l_Lean_reflBoolTrue;
x_3525 = l_Lean_mkApp5(x_3523, x_3518, x_3520, x_3521, x_3522, x_3524);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3516);
x_3526 = l_Lean_Meta_mkEq(x_3184, x_3516, x_5, x_6, x_7, x_8, x_3519);
if (lean_obj_tag(x_3526) == 0)
{
lean_object* x_3527; lean_object* x_3528; lean_object* x_3529; 
x_3527 = lean_ctor_get(x_3526, 0);
lean_inc(x_3527);
x_3528 = lean_ctor_get(x_3526, 1);
lean_inc(x_3528);
lean_dec(x_3526);
x_3529 = l_Lean_Meta_mkExpectedTypeHint(x_3525, x_3527, x_5, x_6, x_7, x_8, x_3528);
if (lean_obj_tag(x_3529) == 0)
{
lean_object* x_3530; lean_object* x_3531; lean_object* x_3532; lean_object* x_3533; lean_object* x_3534; lean_object* x_3535; 
x_3530 = lean_ctor_get(x_3529, 0);
lean_inc(x_3530);
x_3531 = lean_ctor_get(x_3529, 1);
lean_inc(x_3531);
if (lean_is_exclusive(x_3529)) {
 lean_ctor_release(x_3529, 0);
 lean_ctor_release(x_3529, 1);
 x_3532 = x_3529;
} else {
 lean_dec_ref(x_3529);
 x_3532 = lean_box(0);
}
if (lean_is_scalar(x_3514)) {
 x_3533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3533 = x_3514;
}
lean_ctor_set(x_3533, 0, x_3516);
lean_ctor_set(x_3533, 1, x_3530);
x_3534 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3534, 0, x_3533);
if (lean_is_scalar(x_3532)) {
 x_3535 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3535 = x_3532;
}
lean_ctor_set(x_3535, 0, x_3534);
lean_ctor_set(x_3535, 1, x_3531);
return x_3535;
}
else
{
lean_object* x_3536; lean_object* x_3537; lean_object* x_3538; lean_object* x_3539; 
lean_dec(x_3516);
lean_dec(x_3514);
x_3536 = lean_ctor_get(x_3529, 0);
lean_inc(x_3536);
x_3537 = lean_ctor_get(x_3529, 1);
lean_inc(x_3537);
if (lean_is_exclusive(x_3529)) {
 lean_ctor_release(x_3529, 0);
 lean_ctor_release(x_3529, 1);
 x_3538 = x_3529;
} else {
 lean_dec_ref(x_3529);
 x_3538 = lean_box(0);
}
if (lean_is_scalar(x_3538)) {
 x_3539 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3539 = x_3538;
}
lean_ctor_set(x_3539, 0, x_3536);
lean_ctor_set(x_3539, 1, x_3537);
return x_3539;
}
}
else
{
lean_object* x_3540; lean_object* x_3541; lean_object* x_3542; lean_object* x_3543; 
lean_dec(x_3525);
lean_dec(x_3516);
lean_dec(x_3514);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3540 = lean_ctor_get(x_3526, 0);
lean_inc(x_3540);
x_3541 = lean_ctor_get(x_3526, 1);
lean_inc(x_3541);
if (lean_is_exclusive(x_3526)) {
 lean_ctor_release(x_3526, 0);
 lean_ctor_release(x_3526, 1);
 x_3542 = x_3526;
} else {
 lean_dec_ref(x_3526);
 x_3542 = lean_box(0);
}
if (lean_is_scalar(x_3542)) {
 x_3543 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3543 = x_3542;
}
lean_ctor_set(x_3543, 0, x_3540);
lean_ctor_set(x_3543, 1, x_3541);
return x_3543;
}
}
else
{
lean_object* x_3544; lean_object* x_3545; lean_object* x_3546; lean_object* x_3547; 
lean_dec(x_3516);
lean_dec(x_3514);
lean_dec(x_3186);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_3544 = lean_ctor_get(x_3517, 0);
lean_inc(x_3544);
x_3545 = lean_ctor_get(x_3517, 1);
lean_inc(x_3545);
if (lean_is_exclusive(x_3517)) {
 lean_ctor_release(x_3517, 0);
 lean_ctor_release(x_3517, 1);
 x_3546 = x_3517;
} else {
 lean_dec_ref(x_3517);
 x_3546 = lean_box(0);
}
if (lean_is_scalar(x_3546)) {
 x_3547 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3547 = x_3546;
}
lean_ctor_set(x_3547, 0, x_3544);
lean_ctor_set(x_3547, 1, x_3545);
return x_3547;
}
}
}
else
{
if (lean_obj_tag(x_3369) == 0)
{
lean_object* x_3548; lean_object* x_3549; lean_object* x_3550; lean_object* x_3551; lean_object* x_3552; uint8_t x_3553; 
lean_dec(x_3186);
lean_dec(x_11);
x_3548 = lean_ctor_get(x_3369, 0);
lean_inc(x_3548);
if (lean_is_exclusive(x_3369)) {
 lean_ctor_release(x_3369, 0);
 x_3549 = x_3369;
} else {
 lean_dec_ref(x_3369);
 x_3549 = lean_box(0);
}
x_3550 = lean_array_get(x_10, x_4, x_3368);
x_3551 = lean_int_neg(x_3548);
lean_dec(x_3548);
x_3552 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_3553 = lean_int_dec_le(x_3552, x_3551);
if (x_3553 == 0)
{
lean_object* x_3554; lean_object* x_3555; lean_object* x_3556; lean_object* x_3557; lean_object* x_3558; lean_object* x_3559; lean_object* x_3560; lean_object* x_3561; lean_object* x_3562; lean_object* x_3563; 
x_3554 = lean_box(0);
x_3555 = l_Lean_Expr_const___override(x_3, x_3554);
x_3556 = lean_int_neg(x_3551);
lean_dec(x_3551);
x_3557 = l_Int_toNat(x_3556);
lean_dec(x_3556);
x_3558 = l_Lean_instToExprInt_mkNat(x_3557);
x_3559 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__28;
x_3560 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_3561 = l_Lean_mkApp3(x_3559, x_3555, x_3560, x_3558);
lean_inc(x_3561);
x_3562 = l_Lean_mkAppB(x_3183, x_3550, x_3561);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3563 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3181);
if (lean_obj_tag(x_3563) == 0)
{
lean_object* x_3564; lean_object* x_3565; lean_object* x_3566; lean_object* x_3567; lean_object* x_3568; lean_object* x_3569; lean_object* x_3570; lean_object* x_3571; lean_object* x_3572; 
x_3564 = lean_ctor_get(x_3563, 0);
lean_inc(x_3564);
x_3565 = lean_ctor_get(x_3563, 1);
lean_inc(x_3565);
lean_dec(x_3563);
x_3566 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3567 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3568 = l_Lean_mkNatLit(x_3368);
x_3569 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__31;
x_3570 = l_Lean_reflBoolTrue;
x_3571 = l_Lean_mkApp6(x_3569, x_3564, x_3566, x_3567, x_3568, x_3561, x_3570);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3562);
x_3572 = l_Lean_Meta_mkEq(x_3184, x_3562, x_5, x_6, x_7, x_8, x_3565);
if (lean_obj_tag(x_3572) == 0)
{
lean_object* x_3573; lean_object* x_3574; lean_object* x_3575; 
x_3573 = lean_ctor_get(x_3572, 0);
lean_inc(x_3573);
x_3574 = lean_ctor_get(x_3572, 1);
lean_inc(x_3574);
lean_dec(x_3572);
x_3575 = l_Lean_Meta_mkExpectedTypeHint(x_3571, x_3573, x_5, x_6, x_7, x_8, x_3574);
if (lean_obj_tag(x_3575) == 0)
{
lean_object* x_3576; lean_object* x_3577; lean_object* x_3578; lean_object* x_3579; lean_object* x_3580; lean_object* x_3581; 
x_3576 = lean_ctor_get(x_3575, 0);
lean_inc(x_3576);
x_3577 = lean_ctor_get(x_3575, 1);
lean_inc(x_3577);
if (lean_is_exclusive(x_3575)) {
 lean_ctor_release(x_3575, 0);
 lean_ctor_release(x_3575, 1);
 x_3578 = x_3575;
} else {
 lean_dec_ref(x_3575);
 x_3578 = lean_box(0);
}
x_3579 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3579, 0, x_3562);
lean_ctor_set(x_3579, 1, x_3576);
if (lean_is_scalar(x_3549)) {
 x_3580 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3580 = x_3549;
 lean_ctor_set_tag(x_3580, 1);
}
lean_ctor_set(x_3580, 0, x_3579);
if (lean_is_scalar(x_3578)) {
 x_3581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3581 = x_3578;
}
lean_ctor_set(x_3581, 0, x_3580);
lean_ctor_set(x_3581, 1, x_3577);
return x_3581;
}
else
{
lean_object* x_3582; lean_object* x_3583; lean_object* x_3584; lean_object* x_3585; 
lean_dec(x_3562);
lean_dec(x_3549);
x_3582 = lean_ctor_get(x_3575, 0);
lean_inc(x_3582);
x_3583 = lean_ctor_get(x_3575, 1);
lean_inc(x_3583);
if (lean_is_exclusive(x_3575)) {
 lean_ctor_release(x_3575, 0);
 lean_ctor_release(x_3575, 1);
 x_3584 = x_3575;
} else {
 lean_dec_ref(x_3575);
 x_3584 = lean_box(0);
}
if (lean_is_scalar(x_3584)) {
 x_3585 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3585 = x_3584;
}
lean_ctor_set(x_3585, 0, x_3582);
lean_ctor_set(x_3585, 1, x_3583);
return x_3585;
}
}
else
{
lean_object* x_3586; lean_object* x_3587; lean_object* x_3588; lean_object* x_3589; 
lean_dec(x_3571);
lean_dec(x_3562);
lean_dec(x_3549);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3586 = lean_ctor_get(x_3572, 0);
lean_inc(x_3586);
x_3587 = lean_ctor_get(x_3572, 1);
lean_inc(x_3587);
if (lean_is_exclusive(x_3572)) {
 lean_ctor_release(x_3572, 0);
 lean_ctor_release(x_3572, 1);
 x_3588 = x_3572;
} else {
 lean_dec_ref(x_3572);
 x_3588 = lean_box(0);
}
if (lean_is_scalar(x_3588)) {
 x_3589 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3589 = x_3588;
}
lean_ctor_set(x_3589, 0, x_3586);
lean_ctor_set(x_3589, 1, x_3587);
return x_3589;
}
}
else
{
lean_object* x_3590; lean_object* x_3591; lean_object* x_3592; lean_object* x_3593; 
lean_dec(x_3562);
lean_dec(x_3561);
lean_dec(x_3549);
lean_dec(x_3368);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_3590 = lean_ctor_get(x_3563, 0);
lean_inc(x_3590);
x_3591 = lean_ctor_get(x_3563, 1);
lean_inc(x_3591);
if (lean_is_exclusive(x_3563)) {
 lean_ctor_release(x_3563, 0);
 lean_ctor_release(x_3563, 1);
 x_3592 = x_3563;
} else {
 lean_dec_ref(x_3563);
 x_3592 = lean_box(0);
}
if (lean_is_scalar(x_3592)) {
 x_3593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3593 = x_3592;
}
lean_ctor_set(x_3593, 0, x_3590);
lean_ctor_set(x_3593, 1, x_3591);
return x_3593;
}
}
else
{
lean_object* x_3594; lean_object* x_3595; lean_object* x_3596; lean_object* x_3597; 
lean_dec(x_3);
x_3594 = l_Int_toNat(x_3551);
lean_dec(x_3551);
x_3595 = l_Lean_instToExprInt_mkNat(x_3594);
lean_inc(x_3595);
x_3596 = l_Lean_mkAppB(x_3183, x_3550, x_3595);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3597 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3181);
if (lean_obj_tag(x_3597) == 0)
{
lean_object* x_3598; lean_object* x_3599; lean_object* x_3600; lean_object* x_3601; lean_object* x_3602; lean_object* x_3603; lean_object* x_3604; lean_object* x_3605; lean_object* x_3606; 
x_3598 = lean_ctor_get(x_3597, 0);
lean_inc(x_3598);
x_3599 = lean_ctor_get(x_3597, 1);
lean_inc(x_3599);
lean_dec(x_3597);
x_3600 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3601 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3602 = l_Lean_mkNatLit(x_3368);
x_3603 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__32;
x_3604 = l_Lean_reflBoolTrue;
x_3605 = l_Lean_mkApp6(x_3603, x_3598, x_3600, x_3601, x_3602, x_3595, x_3604);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3596);
x_3606 = l_Lean_Meta_mkEq(x_3184, x_3596, x_5, x_6, x_7, x_8, x_3599);
if (lean_obj_tag(x_3606) == 0)
{
lean_object* x_3607; lean_object* x_3608; lean_object* x_3609; 
x_3607 = lean_ctor_get(x_3606, 0);
lean_inc(x_3607);
x_3608 = lean_ctor_get(x_3606, 1);
lean_inc(x_3608);
lean_dec(x_3606);
x_3609 = l_Lean_Meta_mkExpectedTypeHint(x_3605, x_3607, x_5, x_6, x_7, x_8, x_3608);
if (lean_obj_tag(x_3609) == 0)
{
lean_object* x_3610; lean_object* x_3611; lean_object* x_3612; lean_object* x_3613; lean_object* x_3614; lean_object* x_3615; 
x_3610 = lean_ctor_get(x_3609, 0);
lean_inc(x_3610);
x_3611 = lean_ctor_get(x_3609, 1);
lean_inc(x_3611);
if (lean_is_exclusive(x_3609)) {
 lean_ctor_release(x_3609, 0);
 lean_ctor_release(x_3609, 1);
 x_3612 = x_3609;
} else {
 lean_dec_ref(x_3609);
 x_3612 = lean_box(0);
}
x_3613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3613, 0, x_3596);
lean_ctor_set(x_3613, 1, x_3610);
if (lean_is_scalar(x_3549)) {
 x_3614 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3614 = x_3549;
 lean_ctor_set_tag(x_3614, 1);
}
lean_ctor_set(x_3614, 0, x_3613);
if (lean_is_scalar(x_3612)) {
 x_3615 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3615 = x_3612;
}
lean_ctor_set(x_3615, 0, x_3614);
lean_ctor_set(x_3615, 1, x_3611);
return x_3615;
}
else
{
lean_object* x_3616; lean_object* x_3617; lean_object* x_3618; lean_object* x_3619; 
lean_dec(x_3596);
lean_dec(x_3549);
x_3616 = lean_ctor_get(x_3609, 0);
lean_inc(x_3616);
x_3617 = lean_ctor_get(x_3609, 1);
lean_inc(x_3617);
if (lean_is_exclusive(x_3609)) {
 lean_ctor_release(x_3609, 0);
 lean_ctor_release(x_3609, 1);
 x_3618 = x_3609;
} else {
 lean_dec_ref(x_3609);
 x_3618 = lean_box(0);
}
if (lean_is_scalar(x_3618)) {
 x_3619 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3619 = x_3618;
}
lean_ctor_set(x_3619, 0, x_3616);
lean_ctor_set(x_3619, 1, x_3617);
return x_3619;
}
}
else
{
lean_object* x_3620; lean_object* x_3621; lean_object* x_3622; lean_object* x_3623; 
lean_dec(x_3605);
lean_dec(x_3596);
lean_dec(x_3549);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3620 = lean_ctor_get(x_3606, 0);
lean_inc(x_3620);
x_3621 = lean_ctor_get(x_3606, 1);
lean_inc(x_3621);
if (lean_is_exclusive(x_3606)) {
 lean_ctor_release(x_3606, 0);
 lean_ctor_release(x_3606, 1);
 x_3622 = x_3606;
} else {
 lean_dec_ref(x_3606);
 x_3622 = lean_box(0);
}
if (lean_is_scalar(x_3622)) {
 x_3623 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3623 = x_3622;
}
lean_ctor_set(x_3623, 0, x_3620);
lean_ctor_set(x_3623, 1, x_3621);
return x_3623;
}
}
else
{
lean_object* x_3624; lean_object* x_3625; lean_object* x_3626; lean_object* x_3627; 
lean_dec(x_3596);
lean_dec(x_3595);
lean_dec(x_3549);
lean_dec(x_3368);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_3624 = lean_ctor_get(x_3597, 0);
lean_inc(x_3624);
x_3625 = lean_ctor_get(x_3597, 1);
lean_inc(x_3625);
if (lean_is_exclusive(x_3597)) {
 lean_ctor_release(x_3597, 0);
 lean_ctor_release(x_3597, 1);
 x_3626 = x_3597;
} else {
 lean_dec_ref(x_3597);
 x_3626 = lean_box(0);
}
if (lean_is_scalar(x_3626)) {
 x_3627 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3627 = x_3626;
}
lean_ctor_set(x_3627, 0, x_3624);
lean_ctor_set(x_3627, 1, x_3625);
return x_3627;
}
}
}
else
{
lean_object* x_3628; lean_object* x_3629; lean_object* x_3630; lean_object* x_3631; uint8_t x_3632; 
x_3628 = lean_ctor_get(x_3369, 0);
lean_inc(x_3628);
x_3629 = lean_ctor_get(x_3369, 1);
lean_inc(x_3629);
x_3630 = lean_ctor_get(x_3369, 2);
lean_inc(x_3630);
lean_dec(x_3369);
x_3631 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__33;
x_3632 = lean_int_dec_eq(x_3628, x_3631);
lean_dec(x_3628);
if (x_3632 == 0)
{
lean_object* x_3633; lean_object* x_3634; uint8_t x_3635; 
lean_dec(x_3630);
lean_dec(x_3629);
lean_dec(x_3368);
x_3633 = l_Int_Linear_Poly_gcdCoeffs_x27(x_3186);
x_3634 = lean_unsigned_to_nat(1u);
x_3635 = lean_nat_dec_eq(x_3633, x_3634);
if (x_3635 == 0)
{
lean_object* x_3636; lean_object* x_3637; lean_object* x_3638; lean_object* x_3639; uint8_t x_3640; 
x_3636 = l_Int_Linear_Poly_getConst(x_3186);
x_3637 = lean_nat_to_int(x_3633);
x_3638 = lean_int_emod(x_3636, x_3637);
lean_dec(x_3636);
x_3639 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_3640 = lean_int_dec_eq(x_3638, x_3639);
lean_dec(x_3638);
if (x_3640 == 0)
{
lean_object* x_3641; lean_object* x_3642; 
lean_dec(x_3186);
lean_dec(x_11);
x_3641 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3642 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3181);
if (lean_obj_tag(x_3642) == 0)
{
lean_object* x_3643; lean_object* x_3644; lean_object* x_3645; lean_object* x_3646; uint8_t x_3647; lean_object* x_3648; lean_object* x_3649; 
x_3643 = lean_ctor_get(x_3642, 0);
lean_inc(x_3643);
x_3644 = lean_ctor_get(x_3642, 1);
lean_inc(x_3644);
lean_dec(x_3642);
x_3645 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3646 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3647 = lean_int_dec_le(x_3639, x_3637);
x_3648 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3649 = l_Lean_Meta_mkEq(x_3184, x_3648, x_5, x_6, x_7, x_8, x_3644);
if (x_3647 == 0)
{
if (lean_obj_tag(x_3649) == 0)
{
lean_object* x_3650; lean_object* x_3651; lean_object* x_3652; lean_object* x_3653; lean_object* x_3654; lean_object* x_3655; lean_object* x_3656; lean_object* x_3657; lean_object* x_3658; lean_object* x_3659; lean_object* x_3660; lean_object* x_3661; lean_object* x_3662; 
x_3650 = lean_ctor_get(x_3649, 0);
lean_inc(x_3650);
x_3651 = lean_ctor_get(x_3649, 1);
lean_inc(x_3651);
lean_dec(x_3649);
x_3652 = l_Lean_Expr_const___override(x_3, x_3641);
x_3653 = lean_int_neg(x_3637);
lean_dec(x_3637);
x_3654 = l_Int_toNat(x_3653);
lean_dec(x_3653);
x_3655 = l_Lean_instToExprInt_mkNat(x_3654);
x_3656 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_3657 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_3658 = l_Lean_mkApp3(x_3656, x_3652, x_3657, x_3655);
x_3659 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_3660 = l_Lean_reflBoolTrue;
x_3661 = l_Lean_mkApp5(x_3659, x_3643, x_3645, x_3646, x_3658, x_3660);
x_3662 = l_Lean_Meta_mkExpectedTypeHint(x_3661, x_3650, x_5, x_6, x_7, x_8, x_3651);
if (lean_obj_tag(x_3662) == 0)
{
lean_object* x_3663; lean_object* x_3664; lean_object* x_3665; lean_object* x_3666; lean_object* x_3667; lean_object* x_3668; 
x_3663 = lean_ctor_get(x_3662, 0);
lean_inc(x_3663);
x_3664 = lean_ctor_get(x_3662, 1);
lean_inc(x_3664);
if (lean_is_exclusive(x_3662)) {
 lean_ctor_release(x_3662, 0);
 lean_ctor_release(x_3662, 1);
 x_3665 = x_3662;
} else {
 lean_dec_ref(x_3662);
 x_3665 = lean_box(0);
}
x_3666 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3666, 0, x_3648);
lean_ctor_set(x_3666, 1, x_3663);
x_3667 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3667, 0, x_3666);
if (lean_is_scalar(x_3665)) {
 x_3668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3668 = x_3665;
}
lean_ctor_set(x_3668, 0, x_3667);
lean_ctor_set(x_3668, 1, x_3664);
return x_3668;
}
else
{
lean_object* x_3669; lean_object* x_3670; lean_object* x_3671; lean_object* x_3672; 
x_3669 = lean_ctor_get(x_3662, 0);
lean_inc(x_3669);
x_3670 = lean_ctor_get(x_3662, 1);
lean_inc(x_3670);
if (lean_is_exclusive(x_3662)) {
 lean_ctor_release(x_3662, 0);
 lean_ctor_release(x_3662, 1);
 x_3671 = x_3662;
} else {
 lean_dec_ref(x_3662);
 x_3671 = lean_box(0);
}
if (lean_is_scalar(x_3671)) {
 x_3672 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3672 = x_3671;
}
lean_ctor_set(x_3672, 0, x_3669);
lean_ctor_set(x_3672, 1, x_3670);
return x_3672;
}
}
else
{
lean_object* x_3673; lean_object* x_3674; lean_object* x_3675; lean_object* x_3676; 
lean_dec(x_3646);
lean_dec(x_3645);
lean_dec(x_3643);
lean_dec(x_3637);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_3673 = lean_ctor_get(x_3649, 0);
lean_inc(x_3673);
x_3674 = lean_ctor_get(x_3649, 1);
lean_inc(x_3674);
if (lean_is_exclusive(x_3649)) {
 lean_ctor_release(x_3649, 0);
 lean_ctor_release(x_3649, 1);
 x_3675 = x_3649;
} else {
 lean_dec_ref(x_3649);
 x_3675 = lean_box(0);
}
if (lean_is_scalar(x_3675)) {
 x_3676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3676 = x_3675;
}
lean_ctor_set(x_3676, 0, x_3673);
lean_ctor_set(x_3676, 1, x_3674);
return x_3676;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_3649) == 0)
{
lean_object* x_3677; lean_object* x_3678; lean_object* x_3679; lean_object* x_3680; lean_object* x_3681; lean_object* x_3682; lean_object* x_3683; lean_object* x_3684; 
x_3677 = lean_ctor_get(x_3649, 0);
lean_inc(x_3677);
x_3678 = lean_ctor_get(x_3649, 1);
lean_inc(x_3678);
lean_dec(x_3649);
x_3679 = l_Int_toNat(x_3637);
lean_dec(x_3637);
x_3680 = l_Lean_instToExprInt_mkNat(x_3679);
x_3681 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_3682 = l_Lean_reflBoolTrue;
x_3683 = l_Lean_mkApp5(x_3681, x_3643, x_3645, x_3646, x_3680, x_3682);
x_3684 = l_Lean_Meta_mkExpectedTypeHint(x_3683, x_3677, x_5, x_6, x_7, x_8, x_3678);
if (lean_obj_tag(x_3684) == 0)
{
lean_object* x_3685; lean_object* x_3686; lean_object* x_3687; lean_object* x_3688; lean_object* x_3689; lean_object* x_3690; 
x_3685 = lean_ctor_get(x_3684, 0);
lean_inc(x_3685);
x_3686 = lean_ctor_get(x_3684, 1);
lean_inc(x_3686);
if (lean_is_exclusive(x_3684)) {
 lean_ctor_release(x_3684, 0);
 lean_ctor_release(x_3684, 1);
 x_3687 = x_3684;
} else {
 lean_dec_ref(x_3684);
 x_3687 = lean_box(0);
}
x_3688 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3688, 0, x_3648);
lean_ctor_set(x_3688, 1, x_3685);
x_3689 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3689, 0, x_3688);
if (lean_is_scalar(x_3687)) {
 x_3690 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3690 = x_3687;
}
lean_ctor_set(x_3690, 0, x_3689);
lean_ctor_set(x_3690, 1, x_3686);
return x_3690;
}
else
{
lean_object* x_3691; lean_object* x_3692; lean_object* x_3693; lean_object* x_3694; 
x_3691 = lean_ctor_get(x_3684, 0);
lean_inc(x_3691);
x_3692 = lean_ctor_get(x_3684, 1);
lean_inc(x_3692);
if (lean_is_exclusive(x_3684)) {
 lean_ctor_release(x_3684, 0);
 lean_ctor_release(x_3684, 1);
 x_3693 = x_3684;
} else {
 lean_dec_ref(x_3684);
 x_3693 = lean_box(0);
}
if (lean_is_scalar(x_3693)) {
 x_3694 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3694 = x_3693;
}
lean_ctor_set(x_3694, 0, x_3691);
lean_ctor_set(x_3694, 1, x_3692);
return x_3694;
}
}
else
{
lean_object* x_3695; lean_object* x_3696; lean_object* x_3697; lean_object* x_3698; 
lean_dec(x_3646);
lean_dec(x_3645);
lean_dec(x_3643);
lean_dec(x_3637);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3695 = lean_ctor_get(x_3649, 0);
lean_inc(x_3695);
x_3696 = lean_ctor_get(x_3649, 1);
lean_inc(x_3696);
if (lean_is_exclusive(x_3649)) {
 lean_ctor_release(x_3649, 0);
 lean_ctor_release(x_3649, 1);
 x_3697 = x_3649;
} else {
 lean_dec_ref(x_3649);
 x_3697 = lean_box(0);
}
if (lean_is_scalar(x_3697)) {
 x_3698 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3698 = x_3697;
}
lean_ctor_set(x_3698, 0, x_3695);
lean_ctor_set(x_3698, 1, x_3696);
return x_3698;
}
}
}
else
{
lean_object* x_3699; lean_object* x_3700; lean_object* x_3701; lean_object* x_3702; 
lean_dec(x_3637);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3699 = lean_ctor_get(x_3642, 0);
lean_inc(x_3699);
x_3700 = lean_ctor_get(x_3642, 1);
lean_inc(x_3700);
if (lean_is_exclusive(x_3642)) {
 lean_ctor_release(x_3642, 0);
 lean_ctor_release(x_3642, 1);
 x_3701 = x_3642;
} else {
 lean_dec_ref(x_3642);
 x_3701 = lean_box(0);
}
if (lean_is_scalar(x_3701)) {
 x_3702 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3702 = x_3701;
}
lean_ctor_set(x_3702, 0, x_3699);
lean_ctor_set(x_3702, 1, x_3700);
return x_3702;
}
}
else
{
lean_object* x_3703; lean_object* x_3704; lean_object* x_3705; lean_object* x_3706; lean_object* x_3707; lean_object* x_3708; lean_object* x_3709; lean_object* x_3710; 
x_3703 = l_Int_Linear_Poly_div(x_3637, x_3186);
lean_inc(x_3703);
x_3704 = l_Int_Linear_Poly_denoteExpr(x_11, x_3703, x_5, x_6, x_7, x_8, x_3181);
x_3705 = lean_ctor_get(x_3704, 0);
lean_inc(x_3705);
x_3706 = lean_ctor_get(x_3704, 1);
lean_inc(x_3706);
if (lean_is_exclusive(x_3704)) {
 lean_ctor_release(x_3704, 0);
 lean_ctor_release(x_3704, 1);
 x_3707 = x_3704;
} else {
 lean_dec_ref(x_3704);
 x_3707 = lean_box(0);
}
x_3708 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_3709 = l_Lean_mkAppB(x_3183, x_3705, x_3708);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3710 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3706);
if (lean_obj_tag(x_3710) == 0)
{
lean_object* x_3711; lean_object* x_3712; lean_object* x_3713; lean_object* x_3714; lean_object* x_3715; lean_object* x_3716; uint8_t x_3717; lean_object* x_3718; 
x_3711 = lean_ctor_get(x_3710, 0);
lean_inc(x_3711);
x_3712 = lean_ctor_get(x_3710, 1);
lean_inc(x_3712);
lean_dec(x_3710);
x_3713 = lean_box(0);
x_3714 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3715 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3716 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_3703);
x_3717 = lean_int_dec_le(x_3639, x_3637);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3709);
x_3718 = l_Lean_Meta_mkEq(x_3184, x_3709, x_5, x_6, x_7, x_8, x_3712);
if (x_3717 == 0)
{
if (lean_obj_tag(x_3718) == 0)
{
lean_object* x_3719; lean_object* x_3720; lean_object* x_3721; lean_object* x_3722; lean_object* x_3723; lean_object* x_3724; lean_object* x_3725; lean_object* x_3726; lean_object* x_3727; lean_object* x_3728; lean_object* x_3729; lean_object* x_3730; lean_object* x_3731; 
x_3719 = lean_ctor_get(x_3718, 0);
lean_inc(x_3719);
x_3720 = lean_ctor_get(x_3718, 1);
lean_inc(x_3720);
lean_dec(x_3718);
x_3721 = l_Lean_Expr_const___override(x_3, x_3713);
x_3722 = lean_int_neg(x_3637);
lean_dec(x_3637);
x_3723 = l_Int_toNat(x_3722);
lean_dec(x_3722);
x_3724 = l_Lean_instToExprInt_mkNat(x_3723);
x_3725 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_3726 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_3727 = l_Lean_mkApp3(x_3725, x_3721, x_3726, x_3724);
x_3728 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_3729 = l_Lean_reflBoolTrue;
x_3730 = l_Lean_mkApp6(x_3728, x_3711, x_3714, x_3715, x_3716, x_3727, x_3729);
x_3731 = l_Lean_Meta_mkExpectedTypeHint(x_3730, x_3719, x_5, x_6, x_7, x_8, x_3720);
if (lean_obj_tag(x_3731) == 0)
{
lean_object* x_3732; lean_object* x_3733; lean_object* x_3734; lean_object* x_3735; lean_object* x_3736; lean_object* x_3737; 
x_3732 = lean_ctor_get(x_3731, 0);
lean_inc(x_3732);
x_3733 = lean_ctor_get(x_3731, 1);
lean_inc(x_3733);
if (lean_is_exclusive(x_3731)) {
 lean_ctor_release(x_3731, 0);
 lean_ctor_release(x_3731, 1);
 x_3734 = x_3731;
} else {
 lean_dec_ref(x_3731);
 x_3734 = lean_box(0);
}
if (lean_is_scalar(x_3707)) {
 x_3735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3735 = x_3707;
}
lean_ctor_set(x_3735, 0, x_3709);
lean_ctor_set(x_3735, 1, x_3732);
x_3736 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3736, 0, x_3735);
if (lean_is_scalar(x_3734)) {
 x_3737 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3737 = x_3734;
}
lean_ctor_set(x_3737, 0, x_3736);
lean_ctor_set(x_3737, 1, x_3733);
return x_3737;
}
else
{
lean_object* x_3738; lean_object* x_3739; lean_object* x_3740; lean_object* x_3741; 
lean_dec(x_3709);
lean_dec(x_3707);
x_3738 = lean_ctor_get(x_3731, 0);
lean_inc(x_3738);
x_3739 = lean_ctor_get(x_3731, 1);
lean_inc(x_3739);
if (lean_is_exclusive(x_3731)) {
 lean_ctor_release(x_3731, 0);
 lean_ctor_release(x_3731, 1);
 x_3740 = x_3731;
} else {
 lean_dec_ref(x_3731);
 x_3740 = lean_box(0);
}
if (lean_is_scalar(x_3740)) {
 x_3741 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3741 = x_3740;
}
lean_ctor_set(x_3741, 0, x_3738);
lean_ctor_set(x_3741, 1, x_3739);
return x_3741;
}
}
else
{
lean_object* x_3742; lean_object* x_3743; lean_object* x_3744; lean_object* x_3745; 
lean_dec(x_3716);
lean_dec(x_3715);
lean_dec(x_3714);
lean_dec(x_3711);
lean_dec(x_3709);
lean_dec(x_3707);
lean_dec(x_3637);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_3742 = lean_ctor_get(x_3718, 0);
lean_inc(x_3742);
x_3743 = lean_ctor_get(x_3718, 1);
lean_inc(x_3743);
if (lean_is_exclusive(x_3718)) {
 lean_ctor_release(x_3718, 0);
 lean_ctor_release(x_3718, 1);
 x_3744 = x_3718;
} else {
 lean_dec_ref(x_3718);
 x_3744 = lean_box(0);
}
if (lean_is_scalar(x_3744)) {
 x_3745 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3745 = x_3744;
}
lean_ctor_set(x_3745, 0, x_3742);
lean_ctor_set(x_3745, 1, x_3743);
return x_3745;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_3718) == 0)
{
lean_object* x_3746; lean_object* x_3747; lean_object* x_3748; lean_object* x_3749; lean_object* x_3750; lean_object* x_3751; lean_object* x_3752; lean_object* x_3753; 
x_3746 = lean_ctor_get(x_3718, 0);
lean_inc(x_3746);
x_3747 = lean_ctor_get(x_3718, 1);
lean_inc(x_3747);
lean_dec(x_3718);
x_3748 = l_Int_toNat(x_3637);
lean_dec(x_3637);
x_3749 = l_Lean_instToExprInt_mkNat(x_3748);
x_3750 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_3751 = l_Lean_reflBoolTrue;
x_3752 = l_Lean_mkApp6(x_3750, x_3711, x_3714, x_3715, x_3716, x_3749, x_3751);
x_3753 = l_Lean_Meta_mkExpectedTypeHint(x_3752, x_3746, x_5, x_6, x_7, x_8, x_3747);
if (lean_obj_tag(x_3753) == 0)
{
lean_object* x_3754; lean_object* x_3755; lean_object* x_3756; lean_object* x_3757; lean_object* x_3758; lean_object* x_3759; 
x_3754 = lean_ctor_get(x_3753, 0);
lean_inc(x_3754);
x_3755 = lean_ctor_get(x_3753, 1);
lean_inc(x_3755);
if (lean_is_exclusive(x_3753)) {
 lean_ctor_release(x_3753, 0);
 lean_ctor_release(x_3753, 1);
 x_3756 = x_3753;
} else {
 lean_dec_ref(x_3753);
 x_3756 = lean_box(0);
}
if (lean_is_scalar(x_3707)) {
 x_3757 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3757 = x_3707;
}
lean_ctor_set(x_3757, 0, x_3709);
lean_ctor_set(x_3757, 1, x_3754);
x_3758 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3758, 0, x_3757);
if (lean_is_scalar(x_3756)) {
 x_3759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3759 = x_3756;
}
lean_ctor_set(x_3759, 0, x_3758);
lean_ctor_set(x_3759, 1, x_3755);
return x_3759;
}
else
{
lean_object* x_3760; lean_object* x_3761; lean_object* x_3762; lean_object* x_3763; 
lean_dec(x_3709);
lean_dec(x_3707);
x_3760 = lean_ctor_get(x_3753, 0);
lean_inc(x_3760);
x_3761 = lean_ctor_get(x_3753, 1);
lean_inc(x_3761);
if (lean_is_exclusive(x_3753)) {
 lean_ctor_release(x_3753, 0);
 lean_ctor_release(x_3753, 1);
 x_3762 = x_3753;
} else {
 lean_dec_ref(x_3753);
 x_3762 = lean_box(0);
}
if (lean_is_scalar(x_3762)) {
 x_3763 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3763 = x_3762;
}
lean_ctor_set(x_3763, 0, x_3760);
lean_ctor_set(x_3763, 1, x_3761);
return x_3763;
}
}
else
{
lean_object* x_3764; lean_object* x_3765; lean_object* x_3766; lean_object* x_3767; 
lean_dec(x_3716);
lean_dec(x_3715);
lean_dec(x_3714);
lean_dec(x_3711);
lean_dec(x_3709);
lean_dec(x_3707);
lean_dec(x_3637);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3764 = lean_ctor_get(x_3718, 0);
lean_inc(x_3764);
x_3765 = lean_ctor_get(x_3718, 1);
lean_inc(x_3765);
if (lean_is_exclusive(x_3718)) {
 lean_ctor_release(x_3718, 0);
 lean_ctor_release(x_3718, 1);
 x_3766 = x_3718;
} else {
 lean_dec_ref(x_3718);
 x_3766 = lean_box(0);
}
if (lean_is_scalar(x_3766)) {
 x_3767 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3767 = x_3766;
}
lean_ctor_set(x_3767, 0, x_3764);
lean_ctor_set(x_3767, 1, x_3765);
return x_3767;
}
}
}
else
{
lean_object* x_3768; lean_object* x_3769; lean_object* x_3770; lean_object* x_3771; 
lean_dec(x_3709);
lean_dec(x_3707);
lean_dec(x_3703);
lean_dec(x_3637);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3768 = lean_ctor_get(x_3710, 0);
lean_inc(x_3768);
x_3769 = lean_ctor_get(x_3710, 1);
lean_inc(x_3769);
if (lean_is_exclusive(x_3710)) {
 lean_ctor_release(x_3710, 0);
 lean_ctor_release(x_3710, 1);
 x_3770 = x_3710;
} else {
 lean_dec_ref(x_3710);
 x_3770 = lean_box(0);
}
if (lean_is_scalar(x_3770)) {
 x_3771 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3771 = x_3770;
}
lean_ctor_set(x_3771, 0, x_3768);
lean_ctor_set(x_3771, 1, x_3769);
return x_3771;
}
}
}
else
{
lean_object* x_3772; lean_object* x_3773; lean_object* x_3774; lean_object* x_3775; lean_object* x_3776; lean_object* x_3777; lean_object* x_3778; 
lean_dec(x_3633);
lean_dec(x_3);
lean_inc(x_3186);
x_3772 = l_Int_Linear_Poly_denoteExpr(x_11, x_3186, x_5, x_6, x_7, x_8, x_3181);
x_3773 = lean_ctor_get(x_3772, 0);
lean_inc(x_3773);
x_3774 = lean_ctor_get(x_3772, 1);
lean_inc(x_3774);
if (lean_is_exclusive(x_3772)) {
 lean_ctor_release(x_3772, 0);
 lean_ctor_release(x_3772, 1);
 x_3775 = x_3772;
} else {
 lean_dec_ref(x_3772);
 x_3775 = lean_box(0);
}
x_3776 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_3777 = l_Lean_mkAppB(x_3183, x_3773, x_3776);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3778 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3774);
if (lean_obj_tag(x_3778) == 0)
{
lean_object* x_3779; lean_object* x_3780; lean_object* x_3781; lean_object* x_3782; lean_object* x_3783; lean_object* x_3784; lean_object* x_3785; lean_object* x_3786; lean_object* x_3787; 
x_3779 = lean_ctor_get(x_3778, 0);
lean_inc(x_3779);
x_3780 = lean_ctor_get(x_3778, 1);
lean_inc(x_3780);
lean_dec(x_3778);
x_3781 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3782 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3783 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_3186);
x_3784 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_3785 = l_Lean_reflBoolTrue;
x_3786 = l_Lean_mkApp5(x_3784, x_3779, x_3781, x_3782, x_3783, x_3785);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3777);
x_3787 = l_Lean_Meta_mkEq(x_3184, x_3777, x_5, x_6, x_7, x_8, x_3780);
if (lean_obj_tag(x_3787) == 0)
{
lean_object* x_3788; lean_object* x_3789; lean_object* x_3790; 
x_3788 = lean_ctor_get(x_3787, 0);
lean_inc(x_3788);
x_3789 = lean_ctor_get(x_3787, 1);
lean_inc(x_3789);
lean_dec(x_3787);
x_3790 = l_Lean_Meta_mkExpectedTypeHint(x_3786, x_3788, x_5, x_6, x_7, x_8, x_3789);
if (lean_obj_tag(x_3790) == 0)
{
lean_object* x_3791; lean_object* x_3792; lean_object* x_3793; lean_object* x_3794; lean_object* x_3795; lean_object* x_3796; 
x_3791 = lean_ctor_get(x_3790, 0);
lean_inc(x_3791);
x_3792 = lean_ctor_get(x_3790, 1);
lean_inc(x_3792);
if (lean_is_exclusive(x_3790)) {
 lean_ctor_release(x_3790, 0);
 lean_ctor_release(x_3790, 1);
 x_3793 = x_3790;
} else {
 lean_dec_ref(x_3790);
 x_3793 = lean_box(0);
}
if (lean_is_scalar(x_3775)) {
 x_3794 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3794 = x_3775;
}
lean_ctor_set(x_3794, 0, x_3777);
lean_ctor_set(x_3794, 1, x_3791);
x_3795 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3795, 0, x_3794);
if (lean_is_scalar(x_3793)) {
 x_3796 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3796 = x_3793;
}
lean_ctor_set(x_3796, 0, x_3795);
lean_ctor_set(x_3796, 1, x_3792);
return x_3796;
}
else
{
lean_object* x_3797; lean_object* x_3798; lean_object* x_3799; lean_object* x_3800; 
lean_dec(x_3777);
lean_dec(x_3775);
x_3797 = lean_ctor_get(x_3790, 0);
lean_inc(x_3797);
x_3798 = lean_ctor_get(x_3790, 1);
lean_inc(x_3798);
if (lean_is_exclusive(x_3790)) {
 lean_ctor_release(x_3790, 0);
 lean_ctor_release(x_3790, 1);
 x_3799 = x_3790;
} else {
 lean_dec_ref(x_3790);
 x_3799 = lean_box(0);
}
if (lean_is_scalar(x_3799)) {
 x_3800 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3800 = x_3799;
}
lean_ctor_set(x_3800, 0, x_3797);
lean_ctor_set(x_3800, 1, x_3798);
return x_3800;
}
}
else
{
lean_object* x_3801; lean_object* x_3802; lean_object* x_3803; lean_object* x_3804; 
lean_dec(x_3786);
lean_dec(x_3777);
lean_dec(x_3775);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3801 = lean_ctor_get(x_3787, 0);
lean_inc(x_3801);
x_3802 = lean_ctor_get(x_3787, 1);
lean_inc(x_3802);
if (lean_is_exclusive(x_3787)) {
 lean_ctor_release(x_3787, 0);
 lean_ctor_release(x_3787, 1);
 x_3803 = x_3787;
} else {
 lean_dec_ref(x_3787);
 x_3803 = lean_box(0);
}
if (lean_is_scalar(x_3803)) {
 x_3804 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3804 = x_3803;
}
lean_ctor_set(x_3804, 0, x_3801);
lean_ctor_set(x_3804, 1, x_3802);
return x_3804;
}
}
else
{
lean_object* x_3805; lean_object* x_3806; lean_object* x_3807; lean_object* x_3808; 
lean_dec(x_3777);
lean_dec(x_3775);
lean_dec(x_3186);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_3805 = lean_ctor_get(x_3778, 0);
lean_inc(x_3805);
x_3806 = lean_ctor_get(x_3778, 1);
lean_inc(x_3806);
if (lean_is_exclusive(x_3778)) {
 lean_ctor_release(x_3778, 0);
 lean_ctor_release(x_3778, 1);
 x_3807 = x_3778;
} else {
 lean_dec_ref(x_3778);
 x_3807 = lean_box(0);
}
if (lean_is_scalar(x_3807)) {
 x_3808 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3808 = x_3807;
}
lean_ctor_set(x_3808, 0, x_3805);
lean_ctor_set(x_3808, 1, x_3806);
return x_3808;
}
}
}
else
{
if (lean_obj_tag(x_3630) == 0)
{
lean_object* x_3809; lean_object* x_3810; lean_object* x_3811; uint8_t x_3812; 
x_3809 = lean_ctor_get(x_3630, 0);
lean_inc(x_3809);
if (lean_is_exclusive(x_3630)) {
 lean_ctor_release(x_3630, 0);
 x_3810 = x_3630;
} else {
 lean_dec_ref(x_3630);
 x_3810 = lean_box(0);
}
x_3811 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_3812 = lean_int_dec_eq(x_3809, x_3811);
lean_dec(x_3809);
if (x_3812 == 0)
{
lean_object* x_3813; lean_object* x_3814; uint8_t x_3815; 
lean_dec(x_3629);
lean_dec(x_3368);
x_3813 = l_Int_Linear_Poly_gcdCoeffs_x27(x_3186);
x_3814 = lean_unsigned_to_nat(1u);
x_3815 = lean_nat_dec_eq(x_3813, x_3814);
if (x_3815 == 0)
{
lean_object* x_3816; lean_object* x_3817; lean_object* x_3818; uint8_t x_3819; 
x_3816 = l_Int_Linear_Poly_getConst(x_3186);
x_3817 = lean_nat_to_int(x_3813);
x_3818 = lean_int_emod(x_3816, x_3817);
lean_dec(x_3816);
x_3819 = lean_int_dec_eq(x_3818, x_3811);
lean_dec(x_3818);
if (x_3819 == 0)
{
lean_object* x_3820; lean_object* x_3821; 
lean_dec(x_3186);
lean_dec(x_11);
x_3820 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3821 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3181);
if (lean_obj_tag(x_3821) == 0)
{
lean_object* x_3822; lean_object* x_3823; lean_object* x_3824; lean_object* x_3825; uint8_t x_3826; lean_object* x_3827; lean_object* x_3828; 
x_3822 = lean_ctor_get(x_3821, 0);
lean_inc(x_3822);
x_3823 = lean_ctor_get(x_3821, 1);
lean_inc(x_3823);
lean_dec(x_3821);
x_3824 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3825 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3826 = lean_int_dec_le(x_3811, x_3817);
x_3827 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3828 = l_Lean_Meta_mkEq(x_3184, x_3827, x_5, x_6, x_7, x_8, x_3823);
if (x_3826 == 0)
{
if (lean_obj_tag(x_3828) == 0)
{
lean_object* x_3829; lean_object* x_3830; lean_object* x_3831; lean_object* x_3832; lean_object* x_3833; lean_object* x_3834; lean_object* x_3835; lean_object* x_3836; lean_object* x_3837; lean_object* x_3838; lean_object* x_3839; lean_object* x_3840; lean_object* x_3841; 
x_3829 = lean_ctor_get(x_3828, 0);
lean_inc(x_3829);
x_3830 = lean_ctor_get(x_3828, 1);
lean_inc(x_3830);
lean_dec(x_3828);
x_3831 = l_Lean_Expr_const___override(x_3, x_3820);
x_3832 = lean_int_neg(x_3817);
lean_dec(x_3817);
x_3833 = l_Int_toNat(x_3832);
lean_dec(x_3832);
x_3834 = l_Lean_instToExprInt_mkNat(x_3833);
x_3835 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_3836 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_3837 = l_Lean_mkApp3(x_3835, x_3831, x_3836, x_3834);
x_3838 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_3839 = l_Lean_reflBoolTrue;
x_3840 = l_Lean_mkApp5(x_3838, x_3822, x_3824, x_3825, x_3837, x_3839);
x_3841 = l_Lean_Meta_mkExpectedTypeHint(x_3840, x_3829, x_5, x_6, x_7, x_8, x_3830);
if (lean_obj_tag(x_3841) == 0)
{
lean_object* x_3842; lean_object* x_3843; lean_object* x_3844; lean_object* x_3845; lean_object* x_3846; lean_object* x_3847; 
x_3842 = lean_ctor_get(x_3841, 0);
lean_inc(x_3842);
x_3843 = lean_ctor_get(x_3841, 1);
lean_inc(x_3843);
if (lean_is_exclusive(x_3841)) {
 lean_ctor_release(x_3841, 0);
 lean_ctor_release(x_3841, 1);
 x_3844 = x_3841;
} else {
 lean_dec_ref(x_3841);
 x_3844 = lean_box(0);
}
x_3845 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3845, 0, x_3827);
lean_ctor_set(x_3845, 1, x_3842);
if (lean_is_scalar(x_3810)) {
 x_3846 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3846 = x_3810;
 lean_ctor_set_tag(x_3846, 1);
}
lean_ctor_set(x_3846, 0, x_3845);
if (lean_is_scalar(x_3844)) {
 x_3847 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3847 = x_3844;
}
lean_ctor_set(x_3847, 0, x_3846);
lean_ctor_set(x_3847, 1, x_3843);
return x_3847;
}
else
{
lean_object* x_3848; lean_object* x_3849; lean_object* x_3850; lean_object* x_3851; 
lean_dec(x_3810);
x_3848 = lean_ctor_get(x_3841, 0);
lean_inc(x_3848);
x_3849 = lean_ctor_get(x_3841, 1);
lean_inc(x_3849);
if (lean_is_exclusive(x_3841)) {
 lean_ctor_release(x_3841, 0);
 lean_ctor_release(x_3841, 1);
 x_3850 = x_3841;
} else {
 lean_dec_ref(x_3841);
 x_3850 = lean_box(0);
}
if (lean_is_scalar(x_3850)) {
 x_3851 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3851 = x_3850;
}
lean_ctor_set(x_3851, 0, x_3848);
lean_ctor_set(x_3851, 1, x_3849);
return x_3851;
}
}
else
{
lean_object* x_3852; lean_object* x_3853; lean_object* x_3854; lean_object* x_3855; 
lean_dec(x_3825);
lean_dec(x_3824);
lean_dec(x_3822);
lean_dec(x_3817);
lean_dec(x_3810);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_3852 = lean_ctor_get(x_3828, 0);
lean_inc(x_3852);
x_3853 = lean_ctor_get(x_3828, 1);
lean_inc(x_3853);
if (lean_is_exclusive(x_3828)) {
 lean_ctor_release(x_3828, 0);
 lean_ctor_release(x_3828, 1);
 x_3854 = x_3828;
} else {
 lean_dec_ref(x_3828);
 x_3854 = lean_box(0);
}
if (lean_is_scalar(x_3854)) {
 x_3855 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3855 = x_3854;
}
lean_ctor_set(x_3855, 0, x_3852);
lean_ctor_set(x_3855, 1, x_3853);
return x_3855;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_3828) == 0)
{
lean_object* x_3856; lean_object* x_3857; lean_object* x_3858; lean_object* x_3859; lean_object* x_3860; lean_object* x_3861; lean_object* x_3862; lean_object* x_3863; 
x_3856 = lean_ctor_get(x_3828, 0);
lean_inc(x_3856);
x_3857 = lean_ctor_get(x_3828, 1);
lean_inc(x_3857);
lean_dec(x_3828);
x_3858 = l_Int_toNat(x_3817);
lean_dec(x_3817);
x_3859 = l_Lean_instToExprInt_mkNat(x_3858);
x_3860 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_3861 = l_Lean_reflBoolTrue;
x_3862 = l_Lean_mkApp5(x_3860, x_3822, x_3824, x_3825, x_3859, x_3861);
x_3863 = l_Lean_Meta_mkExpectedTypeHint(x_3862, x_3856, x_5, x_6, x_7, x_8, x_3857);
if (lean_obj_tag(x_3863) == 0)
{
lean_object* x_3864; lean_object* x_3865; lean_object* x_3866; lean_object* x_3867; lean_object* x_3868; lean_object* x_3869; 
x_3864 = lean_ctor_get(x_3863, 0);
lean_inc(x_3864);
x_3865 = lean_ctor_get(x_3863, 1);
lean_inc(x_3865);
if (lean_is_exclusive(x_3863)) {
 lean_ctor_release(x_3863, 0);
 lean_ctor_release(x_3863, 1);
 x_3866 = x_3863;
} else {
 lean_dec_ref(x_3863);
 x_3866 = lean_box(0);
}
x_3867 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3867, 0, x_3827);
lean_ctor_set(x_3867, 1, x_3864);
if (lean_is_scalar(x_3810)) {
 x_3868 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3868 = x_3810;
 lean_ctor_set_tag(x_3868, 1);
}
lean_ctor_set(x_3868, 0, x_3867);
if (lean_is_scalar(x_3866)) {
 x_3869 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3869 = x_3866;
}
lean_ctor_set(x_3869, 0, x_3868);
lean_ctor_set(x_3869, 1, x_3865);
return x_3869;
}
else
{
lean_object* x_3870; lean_object* x_3871; lean_object* x_3872; lean_object* x_3873; 
lean_dec(x_3810);
x_3870 = lean_ctor_get(x_3863, 0);
lean_inc(x_3870);
x_3871 = lean_ctor_get(x_3863, 1);
lean_inc(x_3871);
if (lean_is_exclusive(x_3863)) {
 lean_ctor_release(x_3863, 0);
 lean_ctor_release(x_3863, 1);
 x_3872 = x_3863;
} else {
 lean_dec_ref(x_3863);
 x_3872 = lean_box(0);
}
if (lean_is_scalar(x_3872)) {
 x_3873 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3873 = x_3872;
}
lean_ctor_set(x_3873, 0, x_3870);
lean_ctor_set(x_3873, 1, x_3871);
return x_3873;
}
}
else
{
lean_object* x_3874; lean_object* x_3875; lean_object* x_3876; lean_object* x_3877; 
lean_dec(x_3825);
lean_dec(x_3824);
lean_dec(x_3822);
lean_dec(x_3817);
lean_dec(x_3810);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3874 = lean_ctor_get(x_3828, 0);
lean_inc(x_3874);
x_3875 = lean_ctor_get(x_3828, 1);
lean_inc(x_3875);
if (lean_is_exclusive(x_3828)) {
 lean_ctor_release(x_3828, 0);
 lean_ctor_release(x_3828, 1);
 x_3876 = x_3828;
} else {
 lean_dec_ref(x_3828);
 x_3876 = lean_box(0);
}
if (lean_is_scalar(x_3876)) {
 x_3877 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3877 = x_3876;
}
lean_ctor_set(x_3877, 0, x_3874);
lean_ctor_set(x_3877, 1, x_3875);
return x_3877;
}
}
}
else
{
lean_object* x_3878; lean_object* x_3879; lean_object* x_3880; lean_object* x_3881; 
lean_dec(x_3817);
lean_dec(x_3810);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3878 = lean_ctor_get(x_3821, 0);
lean_inc(x_3878);
x_3879 = lean_ctor_get(x_3821, 1);
lean_inc(x_3879);
if (lean_is_exclusive(x_3821)) {
 lean_ctor_release(x_3821, 0);
 lean_ctor_release(x_3821, 1);
 x_3880 = x_3821;
} else {
 lean_dec_ref(x_3821);
 x_3880 = lean_box(0);
}
if (lean_is_scalar(x_3880)) {
 x_3881 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3881 = x_3880;
}
lean_ctor_set(x_3881, 0, x_3878);
lean_ctor_set(x_3881, 1, x_3879);
return x_3881;
}
}
else
{
lean_object* x_3882; lean_object* x_3883; lean_object* x_3884; lean_object* x_3885; lean_object* x_3886; lean_object* x_3887; lean_object* x_3888; lean_object* x_3889; 
x_3882 = l_Int_Linear_Poly_div(x_3817, x_3186);
lean_inc(x_3882);
x_3883 = l_Int_Linear_Poly_denoteExpr(x_11, x_3882, x_5, x_6, x_7, x_8, x_3181);
x_3884 = lean_ctor_get(x_3883, 0);
lean_inc(x_3884);
x_3885 = lean_ctor_get(x_3883, 1);
lean_inc(x_3885);
if (lean_is_exclusive(x_3883)) {
 lean_ctor_release(x_3883, 0);
 lean_ctor_release(x_3883, 1);
 x_3886 = x_3883;
} else {
 lean_dec_ref(x_3883);
 x_3886 = lean_box(0);
}
x_3887 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_3888 = l_Lean_mkAppB(x_3183, x_3884, x_3887);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3889 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3885);
if (lean_obj_tag(x_3889) == 0)
{
lean_object* x_3890; lean_object* x_3891; lean_object* x_3892; lean_object* x_3893; lean_object* x_3894; lean_object* x_3895; uint8_t x_3896; lean_object* x_3897; 
x_3890 = lean_ctor_get(x_3889, 0);
lean_inc(x_3890);
x_3891 = lean_ctor_get(x_3889, 1);
lean_inc(x_3891);
lean_dec(x_3889);
x_3892 = lean_box(0);
x_3893 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3894 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3895 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_3882);
x_3896 = lean_int_dec_le(x_3811, x_3817);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3888);
x_3897 = l_Lean_Meta_mkEq(x_3184, x_3888, x_5, x_6, x_7, x_8, x_3891);
if (x_3896 == 0)
{
if (lean_obj_tag(x_3897) == 0)
{
lean_object* x_3898; lean_object* x_3899; lean_object* x_3900; lean_object* x_3901; lean_object* x_3902; lean_object* x_3903; lean_object* x_3904; lean_object* x_3905; lean_object* x_3906; lean_object* x_3907; lean_object* x_3908; lean_object* x_3909; lean_object* x_3910; 
x_3898 = lean_ctor_get(x_3897, 0);
lean_inc(x_3898);
x_3899 = lean_ctor_get(x_3897, 1);
lean_inc(x_3899);
lean_dec(x_3897);
x_3900 = l_Lean_Expr_const___override(x_3, x_3892);
x_3901 = lean_int_neg(x_3817);
lean_dec(x_3817);
x_3902 = l_Int_toNat(x_3901);
lean_dec(x_3901);
x_3903 = l_Lean_instToExprInt_mkNat(x_3902);
x_3904 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_3905 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_3906 = l_Lean_mkApp3(x_3904, x_3900, x_3905, x_3903);
x_3907 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_3908 = l_Lean_reflBoolTrue;
x_3909 = l_Lean_mkApp6(x_3907, x_3890, x_3893, x_3894, x_3895, x_3906, x_3908);
x_3910 = l_Lean_Meta_mkExpectedTypeHint(x_3909, x_3898, x_5, x_6, x_7, x_8, x_3899);
if (lean_obj_tag(x_3910) == 0)
{
lean_object* x_3911; lean_object* x_3912; lean_object* x_3913; lean_object* x_3914; lean_object* x_3915; lean_object* x_3916; 
x_3911 = lean_ctor_get(x_3910, 0);
lean_inc(x_3911);
x_3912 = lean_ctor_get(x_3910, 1);
lean_inc(x_3912);
if (lean_is_exclusive(x_3910)) {
 lean_ctor_release(x_3910, 0);
 lean_ctor_release(x_3910, 1);
 x_3913 = x_3910;
} else {
 lean_dec_ref(x_3910);
 x_3913 = lean_box(0);
}
if (lean_is_scalar(x_3886)) {
 x_3914 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3914 = x_3886;
}
lean_ctor_set(x_3914, 0, x_3888);
lean_ctor_set(x_3914, 1, x_3911);
if (lean_is_scalar(x_3810)) {
 x_3915 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3915 = x_3810;
 lean_ctor_set_tag(x_3915, 1);
}
lean_ctor_set(x_3915, 0, x_3914);
if (lean_is_scalar(x_3913)) {
 x_3916 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3916 = x_3913;
}
lean_ctor_set(x_3916, 0, x_3915);
lean_ctor_set(x_3916, 1, x_3912);
return x_3916;
}
else
{
lean_object* x_3917; lean_object* x_3918; lean_object* x_3919; lean_object* x_3920; 
lean_dec(x_3888);
lean_dec(x_3886);
lean_dec(x_3810);
x_3917 = lean_ctor_get(x_3910, 0);
lean_inc(x_3917);
x_3918 = lean_ctor_get(x_3910, 1);
lean_inc(x_3918);
if (lean_is_exclusive(x_3910)) {
 lean_ctor_release(x_3910, 0);
 lean_ctor_release(x_3910, 1);
 x_3919 = x_3910;
} else {
 lean_dec_ref(x_3910);
 x_3919 = lean_box(0);
}
if (lean_is_scalar(x_3919)) {
 x_3920 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3920 = x_3919;
}
lean_ctor_set(x_3920, 0, x_3917);
lean_ctor_set(x_3920, 1, x_3918);
return x_3920;
}
}
else
{
lean_object* x_3921; lean_object* x_3922; lean_object* x_3923; lean_object* x_3924; 
lean_dec(x_3895);
lean_dec(x_3894);
lean_dec(x_3893);
lean_dec(x_3890);
lean_dec(x_3888);
lean_dec(x_3886);
lean_dec(x_3817);
lean_dec(x_3810);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_3921 = lean_ctor_get(x_3897, 0);
lean_inc(x_3921);
x_3922 = lean_ctor_get(x_3897, 1);
lean_inc(x_3922);
if (lean_is_exclusive(x_3897)) {
 lean_ctor_release(x_3897, 0);
 lean_ctor_release(x_3897, 1);
 x_3923 = x_3897;
} else {
 lean_dec_ref(x_3897);
 x_3923 = lean_box(0);
}
if (lean_is_scalar(x_3923)) {
 x_3924 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3924 = x_3923;
}
lean_ctor_set(x_3924, 0, x_3921);
lean_ctor_set(x_3924, 1, x_3922);
return x_3924;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_3897) == 0)
{
lean_object* x_3925; lean_object* x_3926; lean_object* x_3927; lean_object* x_3928; lean_object* x_3929; lean_object* x_3930; lean_object* x_3931; lean_object* x_3932; 
x_3925 = lean_ctor_get(x_3897, 0);
lean_inc(x_3925);
x_3926 = lean_ctor_get(x_3897, 1);
lean_inc(x_3926);
lean_dec(x_3897);
x_3927 = l_Int_toNat(x_3817);
lean_dec(x_3817);
x_3928 = l_Lean_instToExprInt_mkNat(x_3927);
x_3929 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_3930 = l_Lean_reflBoolTrue;
x_3931 = l_Lean_mkApp6(x_3929, x_3890, x_3893, x_3894, x_3895, x_3928, x_3930);
x_3932 = l_Lean_Meta_mkExpectedTypeHint(x_3931, x_3925, x_5, x_6, x_7, x_8, x_3926);
if (lean_obj_tag(x_3932) == 0)
{
lean_object* x_3933; lean_object* x_3934; lean_object* x_3935; lean_object* x_3936; lean_object* x_3937; lean_object* x_3938; 
x_3933 = lean_ctor_get(x_3932, 0);
lean_inc(x_3933);
x_3934 = lean_ctor_get(x_3932, 1);
lean_inc(x_3934);
if (lean_is_exclusive(x_3932)) {
 lean_ctor_release(x_3932, 0);
 lean_ctor_release(x_3932, 1);
 x_3935 = x_3932;
} else {
 lean_dec_ref(x_3932);
 x_3935 = lean_box(0);
}
if (lean_is_scalar(x_3886)) {
 x_3936 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3936 = x_3886;
}
lean_ctor_set(x_3936, 0, x_3888);
lean_ctor_set(x_3936, 1, x_3933);
if (lean_is_scalar(x_3810)) {
 x_3937 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3937 = x_3810;
 lean_ctor_set_tag(x_3937, 1);
}
lean_ctor_set(x_3937, 0, x_3936);
if (lean_is_scalar(x_3935)) {
 x_3938 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3938 = x_3935;
}
lean_ctor_set(x_3938, 0, x_3937);
lean_ctor_set(x_3938, 1, x_3934);
return x_3938;
}
else
{
lean_object* x_3939; lean_object* x_3940; lean_object* x_3941; lean_object* x_3942; 
lean_dec(x_3888);
lean_dec(x_3886);
lean_dec(x_3810);
x_3939 = lean_ctor_get(x_3932, 0);
lean_inc(x_3939);
x_3940 = lean_ctor_get(x_3932, 1);
lean_inc(x_3940);
if (lean_is_exclusive(x_3932)) {
 lean_ctor_release(x_3932, 0);
 lean_ctor_release(x_3932, 1);
 x_3941 = x_3932;
} else {
 lean_dec_ref(x_3932);
 x_3941 = lean_box(0);
}
if (lean_is_scalar(x_3941)) {
 x_3942 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3942 = x_3941;
}
lean_ctor_set(x_3942, 0, x_3939);
lean_ctor_set(x_3942, 1, x_3940);
return x_3942;
}
}
else
{
lean_object* x_3943; lean_object* x_3944; lean_object* x_3945; lean_object* x_3946; 
lean_dec(x_3895);
lean_dec(x_3894);
lean_dec(x_3893);
lean_dec(x_3890);
lean_dec(x_3888);
lean_dec(x_3886);
lean_dec(x_3817);
lean_dec(x_3810);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3943 = lean_ctor_get(x_3897, 0);
lean_inc(x_3943);
x_3944 = lean_ctor_get(x_3897, 1);
lean_inc(x_3944);
if (lean_is_exclusive(x_3897)) {
 lean_ctor_release(x_3897, 0);
 lean_ctor_release(x_3897, 1);
 x_3945 = x_3897;
} else {
 lean_dec_ref(x_3897);
 x_3945 = lean_box(0);
}
if (lean_is_scalar(x_3945)) {
 x_3946 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3946 = x_3945;
}
lean_ctor_set(x_3946, 0, x_3943);
lean_ctor_set(x_3946, 1, x_3944);
return x_3946;
}
}
}
else
{
lean_object* x_3947; lean_object* x_3948; lean_object* x_3949; lean_object* x_3950; 
lean_dec(x_3888);
lean_dec(x_3886);
lean_dec(x_3882);
lean_dec(x_3817);
lean_dec(x_3810);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_3947 = lean_ctor_get(x_3889, 0);
lean_inc(x_3947);
x_3948 = lean_ctor_get(x_3889, 1);
lean_inc(x_3948);
if (lean_is_exclusive(x_3889)) {
 lean_ctor_release(x_3889, 0);
 lean_ctor_release(x_3889, 1);
 x_3949 = x_3889;
} else {
 lean_dec_ref(x_3889);
 x_3949 = lean_box(0);
}
if (lean_is_scalar(x_3949)) {
 x_3950 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3950 = x_3949;
}
lean_ctor_set(x_3950, 0, x_3947);
lean_ctor_set(x_3950, 1, x_3948);
return x_3950;
}
}
}
else
{
lean_object* x_3951; lean_object* x_3952; lean_object* x_3953; lean_object* x_3954; lean_object* x_3955; lean_object* x_3956; lean_object* x_3957; 
lean_dec(x_3813);
lean_dec(x_3);
lean_inc(x_3186);
x_3951 = l_Int_Linear_Poly_denoteExpr(x_11, x_3186, x_5, x_6, x_7, x_8, x_3181);
x_3952 = lean_ctor_get(x_3951, 0);
lean_inc(x_3952);
x_3953 = lean_ctor_get(x_3951, 1);
lean_inc(x_3953);
if (lean_is_exclusive(x_3951)) {
 lean_ctor_release(x_3951, 0);
 lean_ctor_release(x_3951, 1);
 x_3954 = x_3951;
} else {
 lean_dec_ref(x_3951);
 x_3954 = lean_box(0);
}
x_3955 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_3956 = l_Lean_mkAppB(x_3183, x_3952, x_3955);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3957 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3953);
if (lean_obj_tag(x_3957) == 0)
{
lean_object* x_3958; lean_object* x_3959; lean_object* x_3960; lean_object* x_3961; lean_object* x_3962; lean_object* x_3963; lean_object* x_3964; lean_object* x_3965; lean_object* x_3966; 
x_3958 = lean_ctor_get(x_3957, 0);
lean_inc(x_3958);
x_3959 = lean_ctor_get(x_3957, 1);
lean_inc(x_3959);
lean_dec(x_3957);
x_3960 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3961 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3962 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_3186);
x_3963 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_3964 = l_Lean_reflBoolTrue;
x_3965 = l_Lean_mkApp5(x_3963, x_3958, x_3960, x_3961, x_3962, x_3964);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3956);
x_3966 = l_Lean_Meta_mkEq(x_3184, x_3956, x_5, x_6, x_7, x_8, x_3959);
if (lean_obj_tag(x_3966) == 0)
{
lean_object* x_3967; lean_object* x_3968; lean_object* x_3969; 
x_3967 = lean_ctor_get(x_3966, 0);
lean_inc(x_3967);
x_3968 = lean_ctor_get(x_3966, 1);
lean_inc(x_3968);
lean_dec(x_3966);
x_3969 = l_Lean_Meta_mkExpectedTypeHint(x_3965, x_3967, x_5, x_6, x_7, x_8, x_3968);
if (lean_obj_tag(x_3969) == 0)
{
lean_object* x_3970; lean_object* x_3971; lean_object* x_3972; lean_object* x_3973; lean_object* x_3974; lean_object* x_3975; 
x_3970 = lean_ctor_get(x_3969, 0);
lean_inc(x_3970);
x_3971 = lean_ctor_get(x_3969, 1);
lean_inc(x_3971);
if (lean_is_exclusive(x_3969)) {
 lean_ctor_release(x_3969, 0);
 lean_ctor_release(x_3969, 1);
 x_3972 = x_3969;
} else {
 lean_dec_ref(x_3969);
 x_3972 = lean_box(0);
}
if (lean_is_scalar(x_3954)) {
 x_3973 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3973 = x_3954;
}
lean_ctor_set(x_3973, 0, x_3956);
lean_ctor_set(x_3973, 1, x_3970);
if (lean_is_scalar(x_3810)) {
 x_3974 = lean_alloc_ctor(1, 1, 0);
} else {
 x_3974 = x_3810;
 lean_ctor_set_tag(x_3974, 1);
}
lean_ctor_set(x_3974, 0, x_3973);
if (lean_is_scalar(x_3972)) {
 x_3975 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3975 = x_3972;
}
lean_ctor_set(x_3975, 0, x_3974);
lean_ctor_set(x_3975, 1, x_3971);
return x_3975;
}
else
{
lean_object* x_3976; lean_object* x_3977; lean_object* x_3978; lean_object* x_3979; 
lean_dec(x_3956);
lean_dec(x_3954);
lean_dec(x_3810);
x_3976 = lean_ctor_get(x_3969, 0);
lean_inc(x_3976);
x_3977 = lean_ctor_get(x_3969, 1);
lean_inc(x_3977);
if (lean_is_exclusive(x_3969)) {
 lean_ctor_release(x_3969, 0);
 lean_ctor_release(x_3969, 1);
 x_3978 = x_3969;
} else {
 lean_dec_ref(x_3969);
 x_3978 = lean_box(0);
}
if (lean_is_scalar(x_3978)) {
 x_3979 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3979 = x_3978;
}
lean_ctor_set(x_3979, 0, x_3976);
lean_ctor_set(x_3979, 1, x_3977);
return x_3979;
}
}
else
{
lean_object* x_3980; lean_object* x_3981; lean_object* x_3982; lean_object* x_3983; 
lean_dec(x_3965);
lean_dec(x_3956);
lean_dec(x_3954);
lean_dec(x_3810);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_3980 = lean_ctor_get(x_3966, 0);
lean_inc(x_3980);
x_3981 = lean_ctor_get(x_3966, 1);
lean_inc(x_3981);
if (lean_is_exclusive(x_3966)) {
 lean_ctor_release(x_3966, 0);
 lean_ctor_release(x_3966, 1);
 x_3982 = x_3966;
} else {
 lean_dec_ref(x_3966);
 x_3982 = lean_box(0);
}
if (lean_is_scalar(x_3982)) {
 x_3983 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3983 = x_3982;
}
lean_ctor_set(x_3983, 0, x_3980);
lean_ctor_set(x_3983, 1, x_3981);
return x_3983;
}
}
else
{
lean_object* x_3984; lean_object* x_3985; lean_object* x_3986; lean_object* x_3987; 
lean_dec(x_3956);
lean_dec(x_3954);
lean_dec(x_3810);
lean_dec(x_3186);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_3984 = lean_ctor_get(x_3957, 0);
lean_inc(x_3984);
x_3985 = lean_ctor_get(x_3957, 1);
lean_inc(x_3985);
if (lean_is_exclusive(x_3957)) {
 lean_ctor_release(x_3957, 0);
 lean_ctor_release(x_3957, 1);
 x_3986 = x_3957;
} else {
 lean_dec_ref(x_3957);
 x_3986 = lean_box(0);
}
if (lean_is_scalar(x_3986)) {
 x_3987 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3987 = x_3986;
}
lean_ctor_set(x_3987, 0, x_3984);
lean_ctor_set(x_3987, 1, x_3985);
return x_3987;
}
}
}
else
{
lean_object* x_3988; lean_object* x_3989; lean_object* x_3990; lean_object* x_3991; 
lean_dec(x_3186);
lean_dec(x_11);
lean_dec(x_3);
x_3988 = lean_array_get(x_10, x_4, x_3368);
x_3989 = lean_array_get(x_10, x_4, x_3629);
x_3990 = l_Lean_mkAppB(x_3183, x_3988, x_3989);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_3991 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3181);
if (lean_obj_tag(x_3991) == 0)
{
lean_object* x_3992; lean_object* x_3993; lean_object* x_3994; lean_object* x_3995; lean_object* x_3996; lean_object* x_3997; lean_object* x_3998; lean_object* x_3999; lean_object* x_4000; lean_object* x_4001; 
x_3992 = lean_ctor_get(x_3991, 0);
lean_inc(x_3992);
x_3993 = lean_ctor_get(x_3991, 1);
lean_inc(x_3993);
lean_dec(x_3991);
x_3994 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_3995 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_3996 = l_Lean_mkNatLit(x_3368);
x_3997 = l_Lean_mkNatLit(x_3629);
x_3998 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__36;
x_3999 = l_Lean_reflBoolTrue;
x_4000 = l_Lean_mkApp6(x_3998, x_3992, x_3994, x_3995, x_3996, x_3997, x_3999);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3990);
x_4001 = l_Lean_Meta_mkEq(x_3184, x_3990, x_5, x_6, x_7, x_8, x_3993);
if (lean_obj_tag(x_4001) == 0)
{
lean_object* x_4002; lean_object* x_4003; lean_object* x_4004; 
x_4002 = lean_ctor_get(x_4001, 0);
lean_inc(x_4002);
x_4003 = lean_ctor_get(x_4001, 1);
lean_inc(x_4003);
lean_dec(x_4001);
x_4004 = l_Lean_Meta_mkExpectedTypeHint(x_4000, x_4002, x_5, x_6, x_7, x_8, x_4003);
if (lean_obj_tag(x_4004) == 0)
{
lean_object* x_4005; lean_object* x_4006; lean_object* x_4007; lean_object* x_4008; lean_object* x_4009; lean_object* x_4010; 
x_4005 = lean_ctor_get(x_4004, 0);
lean_inc(x_4005);
x_4006 = lean_ctor_get(x_4004, 1);
lean_inc(x_4006);
if (lean_is_exclusive(x_4004)) {
 lean_ctor_release(x_4004, 0);
 lean_ctor_release(x_4004, 1);
 x_4007 = x_4004;
} else {
 lean_dec_ref(x_4004);
 x_4007 = lean_box(0);
}
x_4008 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4008, 0, x_3990);
lean_ctor_set(x_4008, 1, x_4005);
if (lean_is_scalar(x_3810)) {
 x_4009 = lean_alloc_ctor(1, 1, 0);
} else {
 x_4009 = x_3810;
 lean_ctor_set_tag(x_4009, 1);
}
lean_ctor_set(x_4009, 0, x_4008);
if (lean_is_scalar(x_4007)) {
 x_4010 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4010 = x_4007;
}
lean_ctor_set(x_4010, 0, x_4009);
lean_ctor_set(x_4010, 1, x_4006);
return x_4010;
}
else
{
lean_object* x_4011; lean_object* x_4012; lean_object* x_4013; lean_object* x_4014; 
lean_dec(x_3990);
lean_dec(x_3810);
x_4011 = lean_ctor_get(x_4004, 0);
lean_inc(x_4011);
x_4012 = lean_ctor_get(x_4004, 1);
lean_inc(x_4012);
if (lean_is_exclusive(x_4004)) {
 lean_ctor_release(x_4004, 0);
 lean_ctor_release(x_4004, 1);
 x_4013 = x_4004;
} else {
 lean_dec_ref(x_4004);
 x_4013 = lean_box(0);
}
if (lean_is_scalar(x_4013)) {
 x_4014 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4014 = x_4013;
}
lean_ctor_set(x_4014, 0, x_4011);
lean_ctor_set(x_4014, 1, x_4012);
return x_4014;
}
}
else
{
lean_object* x_4015; lean_object* x_4016; lean_object* x_4017; lean_object* x_4018; 
lean_dec(x_4000);
lean_dec(x_3990);
lean_dec(x_3810);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_4015 = lean_ctor_get(x_4001, 0);
lean_inc(x_4015);
x_4016 = lean_ctor_get(x_4001, 1);
lean_inc(x_4016);
if (lean_is_exclusive(x_4001)) {
 lean_ctor_release(x_4001, 0);
 lean_ctor_release(x_4001, 1);
 x_4017 = x_4001;
} else {
 lean_dec_ref(x_4001);
 x_4017 = lean_box(0);
}
if (lean_is_scalar(x_4017)) {
 x_4018 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4018 = x_4017;
}
lean_ctor_set(x_4018, 0, x_4015);
lean_ctor_set(x_4018, 1, x_4016);
return x_4018;
}
}
else
{
lean_object* x_4019; lean_object* x_4020; lean_object* x_4021; lean_object* x_4022; 
lean_dec(x_3990);
lean_dec(x_3810);
lean_dec(x_3629);
lean_dec(x_3368);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_4019 = lean_ctor_get(x_3991, 0);
lean_inc(x_4019);
x_4020 = lean_ctor_get(x_3991, 1);
lean_inc(x_4020);
if (lean_is_exclusive(x_3991)) {
 lean_ctor_release(x_3991, 0);
 lean_ctor_release(x_3991, 1);
 x_4021 = x_3991;
} else {
 lean_dec_ref(x_3991);
 x_4021 = lean_box(0);
}
if (lean_is_scalar(x_4021)) {
 x_4022 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4022 = x_4021;
}
lean_ctor_set(x_4022, 0, x_4019);
lean_ctor_set(x_4022, 1, x_4020);
return x_4022;
}
}
}
else
{
lean_object* x_4023; lean_object* x_4024; uint8_t x_4025; 
lean_dec(x_3630);
lean_dec(x_3629);
lean_dec(x_3368);
x_4023 = l_Int_Linear_Poly_gcdCoeffs_x27(x_3186);
x_4024 = lean_unsigned_to_nat(1u);
x_4025 = lean_nat_dec_eq(x_4023, x_4024);
if (x_4025 == 0)
{
lean_object* x_4026; lean_object* x_4027; lean_object* x_4028; lean_object* x_4029; uint8_t x_4030; 
x_4026 = l_Int_Linear_Poly_getConst(x_3186);
x_4027 = lean_nat_to_int(x_4023);
x_4028 = lean_int_emod(x_4026, x_4027);
lean_dec(x_4026);
x_4029 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_4030 = lean_int_dec_eq(x_4028, x_4029);
lean_dec(x_4028);
if (x_4030 == 0)
{
lean_object* x_4031; lean_object* x_4032; 
lean_dec(x_3186);
lean_dec(x_11);
x_4031 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_4032 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_3181);
if (lean_obj_tag(x_4032) == 0)
{
lean_object* x_4033; lean_object* x_4034; lean_object* x_4035; lean_object* x_4036; uint8_t x_4037; lean_object* x_4038; lean_object* x_4039; 
x_4033 = lean_ctor_get(x_4032, 0);
lean_inc(x_4033);
x_4034 = lean_ctor_get(x_4032, 1);
lean_inc(x_4034);
lean_dec(x_4032);
x_4035 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_4036 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_4037 = lean_int_dec_le(x_4029, x_4027);
x_4038 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_4039 = l_Lean_Meta_mkEq(x_3184, x_4038, x_5, x_6, x_7, x_8, x_4034);
if (x_4037 == 0)
{
if (lean_obj_tag(x_4039) == 0)
{
lean_object* x_4040; lean_object* x_4041; lean_object* x_4042; lean_object* x_4043; lean_object* x_4044; lean_object* x_4045; lean_object* x_4046; lean_object* x_4047; lean_object* x_4048; lean_object* x_4049; lean_object* x_4050; lean_object* x_4051; lean_object* x_4052; 
x_4040 = lean_ctor_get(x_4039, 0);
lean_inc(x_4040);
x_4041 = lean_ctor_get(x_4039, 1);
lean_inc(x_4041);
lean_dec(x_4039);
x_4042 = l_Lean_Expr_const___override(x_3, x_4031);
x_4043 = lean_int_neg(x_4027);
lean_dec(x_4027);
x_4044 = l_Int_toNat(x_4043);
lean_dec(x_4043);
x_4045 = l_Lean_instToExprInt_mkNat(x_4044);
x_4046 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_4047 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_4048 = l_Lean_mkApp3(x_4046, x_4042, x_4047, x_4045);
x_4049 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_4050 = l_Lean_reflBoolTrue;
x_4051 = l_Lean_mkApp5(x_4049, x_4033, x_4035, x_4036, x_4048, x_4050);
x_4052 = l_Lean_Meta_mkExpectedTypeHint(x_4051, x_4040, x_5, x_6, x_7, x_8, x_4041);
if (lean_obj_tag(x_4052) == 0)
{
lean_object* x_4053; lean_object* x_4054; lean_object* x_4055; lean_object* x_4056; lean_object* x_4057; lean_object* x_4058; 
x_4053 = lean_ctor_get(x_4052, 0);
lean_inc(x_4053);
x_4054 = lean_ctor_get(x_4052, 1);
lean_inc(x_4054);
if (lean_is_exclusive(x_4052)) {
 lean_ctor_release(x_4052, 0);
 lean_ctor_release(x_4052, 1);
 x_4055 = x_4052;
} else {
 lean_dec_ref(x_4052);
 x_4055 = lean_box(0);
}
x_4056 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4056, 0, x_4038);
lean_ctor_set(x_4056, 1, x_4053);
x_4057 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4057, 0, x_4056);
if (lean_is_scalar(x_4055)) {
 x_4058 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4058 = x_4055;
}
lean_ctor_set(x_4058, 0, x_4057);
lean_ctor_set(x_4058, 1, x_4054);
return x_4058;
}
else
{
lean_object* x_4059; lean_object* x_4060; lean_object* x_4061; lean_object* x_4062; 
x_4059 = lean_ctor_get(x_4052, 0);
lean_inc(x_4059);
x_4060 = lean_ctor_get(x_4052, 1);
lean_inc(x_4060);
if (lean_is_exclusive(x_4052)) {
 lean_ctor_release(x_4052, 0);
 lean_ctor_release(x_4052, 1);
 x_4061 = x_4052;
} else {
 lean_dec_ref(x_4052);
 x_4061 = lean_box(0);
}
if (lean_is_scalar(x_4061)) {
 x_4062 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4062 = x_4061;
}
lean_ctor_set(x_4062, 0, x_4059);
lean_ctor_set(x_4062, 1, x_4060);
return x_4062;
}
}
else
{
lean_object* x_4063; lean_object* x_4064; lean_object* x_4065; lean_object* x_4066; 
lean_dec(x_4036);
lean_dec(x_4035);
lean_dec(x_4033);
lean_dec(x_4027);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_4063 = lean_ctor_get(x_4039, 0);
lean_inc(x_4063);
x_4064 = lean_ctor_get(x_4039, 1);
lean_inc(x_4064);
if (lean_is_exclusive(x_4039)) {
 lean_ctor_release(x_4039, 0);
 lean_ctor_release(x_4039, 1);
 x_4065 = x_4039;
} else {
 lean_dec_ref(x_4039);
 x_4065 = lean_box(0);
}
if (lean_is_scalar(x_4065)) {
 x_4066 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4066 = x_4065;
}
lean_ctor_set(x_4066, 0, x_4063);
lean_ctor_set(x_4066, 1, x_4064);
return x_4066;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_4039) == 0)
{
lean_object* x_4067; lean_object* x_4068; lean_object* x_4069; lean_object* x_4070; lean_object* x_4071; lean_object* x_4072; lean_object* x_4073; lean_object* x_4074; 
x_4067 = lean_ctor_get(x_4039, 0);
lean_inc(x_4067);
x_4068 = lean_ctor_get(x_4039, 1);
lean_inc(x_4068);
lean_dec(x_4039);
x_4069 = l_Int_toNat(x_4027);
lean_dec(x_4027);
x_4070 = l_Lean_instToExprInt_mkNat(x_4069);
x_4071 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9;
x_4072 = l_Lean_reflBoolTrue;
x_4073 = l_Lean_mkApp5(x_4071, x_4033, x_4035, x_4036, x_4070, x_4072);
x_4074 = l_Lean_Meta_mkExpectedTypeHint(x_4073, x_4067, x_5, x_6, x_7, x_8, x_4068);
if (lean_obj_tag(x_4074) == 0)
{
lean_object* x_4075; lean_object* x_4076; lean_object* x_4077; lean_object* x_4078; lean_object* x_4079; lean_object* x_4080; 
x_4075 = lean_ctor_get(x_4074, 0);
lean_inc(x_4075);
x_4076 = lean_ctor_get(x_4074, 1);
lean_inc(x_4076);
if (lean_is_exclusive(x_4074)) {
 lean_ctor_release(x_4074, 0);
 lean_ctor_release(x_4074, 1);
 x_4077 = x_4074;
} else {
 lean_dec_ref(x_4074);
 x_4077 = lean_box(0);
}
x_4078 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4078, 0, x_4038);
lean_ctor_set(x_4078, 1, x_4075);
x_4079 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4079, 0, x_4078);
if (lean_is_scalar(x_4077)) {
 x_4080 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4080 = x_4077;
}
lean_ctor_set(x_4080, 0, x_4079);
lean_ctor_set(x_4080, 1, x_4076);
return x_4080;
}
else
{
lean_object* x_4081; lean_object* x_4082; lean_object* x_4083; lean_object* x_4084; 
x_4081 = lean_ctor_get(x_4074, 0);
lean_inc(x_4081);
x_4082 = lean_ctor_get(x_4074, 1);
lean_inc(x_4082);
if (lean_is_exclusive(x_4074)) {
 lean_ctor_release(x_4074, 0);
 lean_ctor_release(x_4074, 1);
 x_4083 = x_4074;
} else {
 lean_dec_ref(x_4074);
 x_4083 = lean_box(0);
}
if (lean_is_scalar(x_4083)) {
 x_4084 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4084 = x_4083;
}
lean_ctor_set(x_4084, 0, x_4081);
lean_ctor_set(x_4084, 1, x_4082);
return x_4084;
}
}
else
{
lean_object* x_4085; lean_object* x_4086; lean_object* x_4087; lean_object* x_4088; 
lean_dec(x_4036);
lean_dec(x_4035);
lean_dec(x_4033);
lean_dec(x_4027);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_4085 = lean_ctor_get(x_4039, 0);
lean_inc(x_4085);
x_4086 = lean_ctor_get(x_4039, 1);
lean_inc(x_4086);
if (lean_is_exclusive(x_4039)) {
 lean_ctor_release(x_4039, 0);
 lean_ctor_release(x_4039, 1);
 x_4087 = x_4039;
} else {
 lean_dec_ref(x_4039);
 x_4087 = lean_box(0);
}
if (lean_is_scalar(x_4087)) {
 x_4088 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4088 = x_4087;
}
lean_ctor_set(x_4088, 0, x_4085);
lean_ctor_set(x_4088, 1, x_4086);
return x_4088;
}
}
}
else
{
lean_object* x_4089; lean_object* x_4090; lean_object* x_4091; lean_object* x_4092; 
lean_dec(x_4027);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4089 = lean_ctor_get(x_4032, 0);
lean_inc(x_4089);
x_4090 = lean_ctor_get(x_4032, 1);
lean_inc(x_4090);
if (lean_is_exclusive(x_4032)) {
 lean_ctor_release(x_4032, 0);
 lean_ctor_release(x_4032, 1);
 x_4091 = x_4032;
} else {
 lean_dec_ref(x_4032);
 x_4091 = lean_box(0);
}
if (lean_is_scalar(x_4091)) {
 x_4092 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4092 = x_4091;
}
lean_ctor_set(x_4092, 0, x_4089);
lean_ctor_set(x_4092, 1, x_4090);
return x_4092;
}
}
else
{
lean_object* x_4093; lean_object* x_4094; lean_object* x_4095; lean_object* x_4096; lean_object* x_4097; lean_object* x_4098; lean_object* x_4099; lean_object* x_4100; 
x_4093 = l_Int_Linear_Poly_div(x_4027, x_3186);
lean_inc(x_4093);
x_4094 = l_Int_Linear_Poly_denoteExpr(x_11, x_4093, x_5, x_6, x_7, x_8, x_3181);
x_4095 = lean_ctor_get(x_4094, 0);
lean_inc(x_4095);
x_4096 = lean_ctor_get(x_4094, 1);
lean_inc(x_4096);
if (lean_is_exclusive(x_4094)) {
 lean_ctor_release(x_4094, 0);
 lean_ctor_release(x_4094, 1);
 x_4097 = x_4094;
} else {
 lean_dec_ref(x_4094);
 x_4097 = lean_box(0);
}
x_4098 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_4099 = l_Lean_mkAppB(x_3183, x_4095, x_4098);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_4100 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_4096);
if (lean_obj_tag(x_4100) == 0)
{
lean_object* x_4101; lean_object* x_4102; lean_object* x_4103; lean_object* x_4104; lean_object* x_4105; lean_object* x_4106; uint8_t x_4107; lean_object* x_4108; 
x_4101 = lean_ctor_get(x_4100, 0);
lean_inc(x_4101);
x_4102 = lean_ctor_get(x_4100, 1);
lean_inc(x_4102);
lean_dec(x_4100);
x_4103 = lean_box(0);
x_4104 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_4105 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_4106 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_4093);
x_4107 = lean_int_dec_le(x_4029, x_4027);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4099);
x_4108 = l_Lean_Meta_mkEq(x_3184, x_4099, x_5, x_6, x_7, x_8, x_4102);
if (x_4107 == 0)
{
if (lean_obj_tag(x_4108) == 0)
{
lean_object* x_4109; lean_object* x_4110; lean_object* x_4111; lean_object* x_4112; lean_object* x_4113; lean_object* x_4114; lean_object* x_4115; lean_object* x_4116; lean_object* x_4117; lean_object* x_4118; lean_object* x_4119; lean_object* x_4120; lean_object* x_4121; 
x_4109 = lean_ctor_get(x_4108, 0);
lean_inc(x_4109);
x_4110 = lean_ctor_get(x_4108, 1);
lean_inc(x_4110);
lean_dec(x_4108);
x_4111 = l_Lean_Expr_const___override(x_3, x_4103);
x_4112 = lean_int_neg(x_4027);
lean_dec(x_4027);
x_4113 = l_Int_toNat(x_4112);
lean_dec(x_4112);
x_4114 = l_Lean_instToExprInt_mkNat(x_4113);
x_4115 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_4116 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_4117 = l_Lean_mkApp3(x_4115, x_4111, x_4116, x_4114);
x_4118 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_4119 = l_Lean_reflBoolTrue;
x_4120 = l_Lean_mkApp6(x_4118, x_4101, x_4104, x_4105, x_4106, x_4117, x_4119);
x_4121 = l_Lean_Meta_mkExpectedTypeHint(x_4120, x_4109, x_5, x_6, x_7, x_8, x_4110);
if (lean_obj_tag(x_4121) == 0)
{
lean_object* x_4122; lean_object* x_4123; lean_object* x_4124; lean_object* x_4125; lean_object* x_4126; lean_object* x_4127; 
x_4122 = lean_ctor_get(x_4121, 0);
lean_inc(x_4122);
x_4123 = lean_ctor_get(x_4121, 1);
lean_inc(x_4123);
if (lean_is_exclusive(x_4121)) {
 lean_ctor_release(x_4121, 0);
 lean_ctor_release(x_4121, 1);
 x_4124 = x_4121;
} else {
 lean_dec_ref(x_4121);
 x_4124 = lean_box(0);
}
if (lean_is_scalar(x_4097)) {
 x_4125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4125 = x_4097;
}
lean_ctor_set(x_4125, 0, x_4099);
lean_ctor_set(x_4125, 1, x_4122);
x_4126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4126, 0, x_4125);
if (lean_is_scalar(x_4124)) {
 x_4127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4127 = x_4124;
}
lean_ctor_set(x_4127, 0, x_4126);
lean_ctor_set(x_4127, 1, x_4123);
return x_4127;
}
else
{
lean_object* x_4128; lean_object* x_4129; lean_object* x_4130; lean_object* x_4131; 
lean_dec(x_4099);
lean_dec(x_4097);
x_4128 = lean_ctor_get(x_4121, 0);
lean_inc(x_4128);
x_4129 = lean_ctor_get(x_4121, 1);
lean_inc(x_4129);
if (lean_is_exclusive(x_4121)) {
 lean_ctor_release(x_4121, 0);
 lean_ctor_release(x_4121, 1);
 x_4130 = x_4121;
} else {
 lean_dec_ref(x_4121);
 x_4130 = lean_box(0);
}
if (lean_is_scalar(x_4130)) {
 x_4131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4131 = x_4130;
}
lean_ctor_set(x_4131, 0, x_4128);
lean_ctor_set(x_4131, 1, x_4129);
return x_4131;
}
}
else
{
lean_object* x_4132; lean_object* x_4133; lean_object* x_4134; lean_object* x_4135; 
lean_dec(x_4106);
lean_dec(x_4105);
lean_dec(x_4104);
lean_dec(x_4101);
lean_dec(x_4099);
lean_dec(x_4097);
lean_dec(x_4027);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_4132 = lean_ctor_get(x_4108, 0);
lean_inc(x_4132);
x_4133 = lean_ctor_get(x_4108, 1);
lean_inc(x_4133);
if (lean_is_exclusive(x_4108)) {
 lean_ctor_release(x_4108, 0);
 lean_ctor_release(x_4108, 1);
 x_4134 = x_4108;
} else {
 lean_dec_ref(x_4108);
 x_4134 = lean_box(0);
}
if (lean_is_scalar(x_4134)) {
 x_4135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4135 = x_4134;
}
lean_ctor_set(x_4135, 0, x_4132);
lean_ctor_set(x_4135, 1, x_4133);
return x_4135;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_4108) == 0)
{
lean_object* x_4136; lean_object* x_4137; lean_object* x_4138; lean_object* x_4139; lean_object* x_4140; lean_object* x_4141; lean_object* x_4142; lean_object* x_4143; 
x_4136 = lean_ctor_get(x_4108, 0);
lean_inc(x_4136);
x_4137 = lean_ctor_get(x_4108, 1);
lean_inc(x_4137);
lean_dec(x_4108);
x_4138 = l_Int_toNat(x_4027);
lean_dec(x_4027);
x_4139 = l_Lean_instToExprInt_mkNat(x_4138);
x_4140 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22;
x_4141 = l_Lean_reflBoolTrue;
x_4142 = l_Lean_mkApp6(x_4140, x_4101, x_4104, x_4105, x_4106, x_4139, x_4141);
x_4143 = l_Lean_Meta_mkExpectedTypeHint(x_4142, x_4136, x_5, x_6, x_7, x_8, x_4137);
if (lean_obj_tag(x_4143) == 0)
{
lean_object* x_4144; lean_object* x_4145; lean_object* x_4146; lean_object* x_4147; lean_object* x_4148; lean_object* x_4149; 
x_4144 = lean_ctor_get(x_4143, 0);
lean_inc(x_4144);
x_4145 = lean_ctor_get(x_4143, 1);
lean_inc(x_4145);
if (lean_is_exclusive(x_4143)) {
 lean_ctor_release(x_4143, 0);
 lean_ctor_release(x_4143, 1);
 x_4146 = x_4143;
} else {
 lean_dec_ref(x_4143);
 x_4146 = lean_box(0);
}
if (lean_is_scalar(x_4097)) {
 x_4147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4147 = x_4097;
}
lean_ctor_set(x_4147, 0, x_4099);
lean_ctor_set(x_4147, 1, x_4144);
x_4148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4148, 0, x_4147);
if (lean_is_scalar(x_4146)) {
 x_4149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4149 = x_4146;
}
lean_ctor_set(x_4149, 0, x_4148);
lean_ctor_set(x_4149, 1, x_4145);
return x_4149;
}
else
{
lean_object* x_4150; lean_object* x_4151; lean_object* x_4152; lean_object* x_4153; 
lean_dec(x_4099);
lean_dec(x_4097);
x_4150 = lean_ctor_get(x_4143, 0);
lean_inc(x_4150);
x_4151 = lean_ctor_get(x_4143, 1);
lean_inc(x_4151);
if (lean_is_exclusive(x_4143)) {
 lean_ctor_release(x_4143, 0);
 lean_ctor_release(x_4143, 1);
 x_4152 = x_4143;
} else {
 lean_dec_ref(x_4143);
 x_4152 = lean_box(0);
}
if (lean_is_scalar(x_4152)) {
 x_4153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4153 = x_4152;
}
lean_ctor_set(x_4153, 0, x_4150);
lean_ctor_set(x_4153, 1, x_4151);
return x_4153;
}
}
else
{
lean_object* x_4154; lean_object* x_4155; lean_object* x_4156; lean_object* x_4157; 
lean_dec(x_4106);
lean_dec(x_4105);
lean_dec(x_4104);
lean_dec(x_4101);
lean_dec(x_4099);
lean_dec(x_4097);
lean_dec(x_4027);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_4154 = lean_ctor_get(x_4108, 0);
lean_inc(x_4154);
x_4155 = lean_ctor_get(x_4108, 1);
lean_inc(x_4155);
if (lean_is_exclusive(x_4108)) {
 lean_ctor_release(x_4108, 0);
 lean_ctor_release(x_4108, 1);
 x_4156 = x_4108;
} else {
 lean_dec_ref(x_4108);
 x_4156 = lean_box(0);
}
if (lean_is_scalar(x_4156)) {
 x_4157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4157 = x_4156;
}
lean_ctor_set(x_4157, 0, x_4154);
lean_ctor_set(x_4157, 1, x_4155);
return x_4157;
}
}
}
else
{
lean_object* x_4158; lean_object* x_4159; lean_object* x_4160; lean_object* x_4161; 
lean_dec(x_4099);
lean_dec(x_4097);
lean_dec(x_4093);
lean_dec(x_4027);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_4158 = lean_ctor_get(x_4100, 0);
lean_inc(x_4158);
x_4159 = lean_ctor_get(x_4100, 1);
lean_inc(x_4159);
if (lean_is_exclusive(x_4100)) {
 lean_ctor_release(x_4100, 0);
 lean_ctor_release(x_4100, 1);
 x_4160 = x_4100;
} else {
 lean_dec_ref(x_4100);
 x_4160 = lean_box(0);
}
if (lean_is_scalar(x_4160)) {
 x_4161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4161 = x_4160;
}
lean_ctor_set(x_4161, 0, x_4158);
lean_ctor_set(x_4161, 1, x_4159);
return x_4161;
}
}
}
else
{
lean_object* x_4162; lean_object* x_4163; lean_object* x_4164; lean_object* x_4165; lean_object* x_4166; lean_object* x_4167; lean_object* x_4168; 
lean_dec(x_4023);
lean_dec(x_3);
lean_inc(x_3186);
x_4162 = l_Int_Linear_Poly_denoteExpr(x_11, x_3186, x_5, x_6, x_7, x_8, x_3181);
x_4163 = lean_ctor_get(x_4162, 0);
lean_inc(x_4163);
x_4164 = lean_ctor_get(x_4162, 1);
lean_inc(x_4164);
if (lean_is_exclusive(x_4162)) {
 lean_ctor_release(x_4162, 0);
 lean_ctor_release(x_4162, 1);
 x_4165 = x_4162;
} else {
 lean_dec_ref(x_4162);
 x_4165 = lean_box(0);
}
x_4166 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_4167 = l_Lean_mkAppB(x_3183, x_4163, x_4166);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_4168 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_4164);
if (lean_obj_tag(x_4168) == 0)
{
lean_object* x_4169; lean_object* x_4170; lean_object* x_4171; lean_object* x_4172; lean_object* x_4173; lean_object* x_4174; lean_object* x_4175; lean_object* x_4176; lean_object* x_4177; 
x_4169 = lean_ctor_get(x_4168, 0);
lean_inc(x_4169);
x_4170 = lean_ctor_get(x_4168, 1);
lean_inc(x_4170);
lean_dec(x_4168);
x_4171 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_4172 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_4173 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_3186);
x_4174 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25;
x_4175 = l_Lean_reflBoolTrue;
x_4176 = l_Lean_mkApp5(x_4174, x_4169, x_4171, x_4172, x_4173, x_4175);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4167);
x_4177 = l_Lean_Meta_mkEq(x_3184, x_4167, x_5, x_6, x_7, x_8, x_4170);
if (lean_obj_tag(x_4177) == 0)
{
lean_object* x_4178; lean_object* x_4179; lean_object* x_4180; 
x_4178 = lean_ctor_get(x_4177, 0);
lean_inc(x_4178);
x_4179 = lean_ctor_get(x_4177, 1);
lean_inc(x_4179);
lean_dec(x_4177);
x_4180 = l_Lean_Meta_mkExpectedTypeHint(x_4176, x_4178, x_5, x_6, x_7, x_8, x_4179);
if (lean_obj_tag(x_4180) == 0)
{
lean_object* x_4181; lean_object* x_4182; lean_object* x_4183; lean_object* x_4184; lean_object* x_4185; lean_object* x_4186; 
x_4181 = lean_ctor_get(x_4180, 0);
lean_inc(x_4181);
x_4182 = lean_ctor_get(x_4180, 1);
lean_inc(x_4182);
if (lean_is_exclusive(x_4180)) {
 lean_ctor_release(x_4180, 0);
 lean_ctor_release(x_4180, 1);
 x_4183 = x_4180;
} else {
 lean_dec_ref(x_4180);
 x_4183 = lean_box(0);
}
if (lean_is_scalar(x_4165)) {
 x_4184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4184 = x_4165;
}
lean_ctor_set(x_4184, 0, x_4167);
lean_ctor_set(x_4184, 1, x_4181);
x_4185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4185, 0, x_4184);
if (lean_is_scalar(x_4183)) {
 x_4186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_4186 = x_4183;
}
lean_ctor_set(x_4186, 0, x_4185);
lean_ctor_set(x_4186, 1, x_4182);
return x_4186;
}
else
{
lean_object* x_4187; lean_object* x_4188; lean_object* x_4189; lean_object* x_4190; 
lean_dec(x_4167);
lean_dec(x_4165);
x_4187 = lean_ctor_get(x_4180, 0);
lean_inc(x_4187);
x_4188 = lean_ctor_get(x_4180, 1);
lean_inc(x_4188);
if (lean_is_exclusive(x_4180)) {
 lean_ctor_release(x_4180, 0);
 lean_ctor_release(x_4180, 1);
 x_4189 = x_4180;
} else {
 lean_dec_ref(x_4180);
 x_4189 = lean_box(0);
}
if (lean_is_scalar(x_4189)) {
 x_4190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4190 = x_4189;
}
lean_ctor_set(x_4190, 0, x_4187);
lean_ctor_set(x_4190, 1, x_4188);
return x_4190;
}
}
else
{
lean_object* x_4191; lean_object* x_4192; lean_object* x_4193; lean_object* x_4194; 
lean_dec(x_4176);
lean_dec(x_4167);
lean_dec(x_4165);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_4191 = lean_ctor_get(x_4177, 0);
lean_inc(x_4191);
x_4192 = lean_ctor_get(x_4177, 1);
lean_inc(x_4192);
if (lean_is_exclusive(x_4177)) {
 lean_ctor_release(x_4177, 0);
 lean_ctor_release(x_4177, 1);
 x_4193 = x_4177;
} else {
 lean_dec_ref(x_4177);
 x_4193 = lean_box(0);
}
if (lean_is_scalar(x_4193)) {
 x_4194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4194 = x_4193;
}
lean_ctor_set(x_4194, 0, x_4191);
lean_ctor_set(x_4194, 1, x_4192);
return x_4194;
}
}
else
{
lean_object* x_4195; lean_object* x_4196; lean_object* x_4197; lean_object* x_4198; 
lean_dec(x_4167);
lean_dec(x_4165);
lean_dec(x_3186);
lean_dec(x_3184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_4195 = lean_ctor_get(x_4168, 0);
lean_inc(x_4195);
x_4196 = lean_ctor_get(x_4168, 1);
lean_inc(x_4196);
if (lean_is_exclusive(x_4168)) {
 lean_ctor_release(x_4168, 0);
 lean_ctor_release(x_4168, 1);
 x_4197 = x_4168;
} else {
 lean_dec_ref(x_4168);
 x_4197 = lean_box(0);
}
if (lean_is_scalar(x_4197)) {
 x_4198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_4198 = x_4197;
}
lean_ctor_set(x_4198, 0, x_4195);
lean_ctor_set(x_4198, 1, x_4196);
return x_4198;
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
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1), 9, 3);
lean_closure_set(x_22, 0, x_18);
lean_closure_set(x_22, 1, x_19);
lean_closure_set(x_22, 2, x_21);
x_23 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_20, x_21, x_22, x_2, x_3, x_4, x_5, x_17);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_9 = l_Lean_Meta_mkEq(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_mkExpectedTypeHint(x_3, x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_le_coeff", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_le_coeff_tight", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_le", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__7;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__8;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_eq_true", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__10;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__11;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_eq_false", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__13;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__14;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_instInhabitedExpr;
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Array_get_x21Internal___boxed), 4, 3);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_5);
lean_inc(x_1);
lean_inc(x_12);
x_13 = l_Int_Linear_Expr_denoteExpr(x_12, x_1, x_6, x_7, x_8, x_9, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_2);
lean_inc(x_12);
x_17 = l_Int_Linear_Expr_denoteExpr(x_12, x_2, x_6, x_7, x_8, x_9, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_175; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l___private_Lean_Expr_0__Lean_intLEPred;
x_22 = l_Lean_mkAppB(x_21, x_15, x_19);
lean_inc(x_2);
lean_inc(x_1);
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 0, x_1);
x_23 = l_Int_Linear_Expr_norm(x_13);
lean_dec(x_13);
x_175 = l_Int_Linear_Poly_isUnsatLe(x_23);
if (x_175 == 0)
{
uint8_t x_176; 
x_176 = l_Int_Linear_Poly_isValidLe(x_23);
if (x_176 == 0)
{
if (x_4 == 0)
{
lean_object* x_177; 
lean_free_object(x_17);
x_177 = lean_box(0);
x_24 = x_177;
goto block_174;
}
else
{
lean_object* x_178; uint8_t x_179; 
lean_inc(x_23);
x_178 = l_Int_Linear_Poly_toExpr(x_23);
x_179 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_178, x_1);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
lean_free_object(x_17);
x_180 = lean_box(0);
x_24 = x_180;
goto block_174;
}
else
{
lean_object* x_181; uint8_t x_182; 
x_181 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__37;
x_182 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_2, x_181);
if (x_182 == 0)
{
lean_object* x_183; 
lean_free_object(x_17);
x_183 = lean_box(0);
x_24 = x_183;
goto block_174;
}
else
{
lean_object* x_184; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_184 = lean_box(0);
lean_ctor_set(x_17, 0, x_184);
return x_17;
}
}
}
}
else
{
lean_object* x_185; 
lean_dec(x_23);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_185 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_189 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_190 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__12;
x_191 = l_Lean_reflBoolTrue;
x_192 = l_Lean_mkApp4(x_190, x_186, x_188, x_189, x_191);
x_193 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__40;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_194 = l_Lean_Meta_mkEq(x_22, x_193, x_6, x_7, x_8, x_9, x_187);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = l_Lean_Meta_mkExpectedTypeHint(x_192, x_195, x_6, x_7, x_8, x_9, x_196);
if (lean_obj_tag(x_197) == 0)
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_197, 0);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_193);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_197, 0, x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_197, 0);
x_203 = lean_ctor_get(x_197, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_197);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_193);
lean_ctor_set(x_204, 1, x_202);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_203);
return x_206;
}
}
else
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_197);
if (x_207 == 0)
{
return x_197;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_197, 0);
x_209 = lean_ctor_get(x_197, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_197);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_192);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_211 = !lean_is_exclusive(x_194);
if (x_211 == 0)
{
return x_194;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_194, 0);
x_213 = lean_ctor_get(x_194, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_194);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_215 = !lean_is_exclusive(x_185);
if (x_215 == 0)
{
return x_185;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_185, 0);
x_217 = lean_ctor_get(x_185, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_185);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
}
else
{
lean_object* x_219; 
lean_dec(x_23);
lean_free_object(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_219 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_223 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_224 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__15;
x_225 = l_Lean_reflBoolTrue;
x_226 = l_Lean_mkApp4(x_224, x_220, x_222, x_223, x_225);
x_227 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_228 = l_Lean_Meta_mkEq(x_22, x_227, x_6, x_7, x_8, x_9, x_221);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = l_Lean_Meta_mkExpectedTypeHint(x_226, x_229, x_6, x_7, x_8, x_9, x_230);
if (lean_obj_tag(x_231) == 0)
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_231, 0);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_227);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_231, 0, x_235);
return x_231;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_236 = lean_ctor_get(x_231, 0);
x_237 = lean_ctor_get(x_231, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_231);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_227);
lean_ctor_set(x_238, 1, x_236);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_238);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
return x_240;
}
}
else
{
uint8_t x_241; 
x_241 = !lean_is_exclusive(x_231);
if (x_241 == 0)
{
return x_231;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_231, 0);
x_243 = lean_ctor_get(x_231, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_231);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_226);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_245 = !lean_is_exclusive(x_228);
if (x_245 == 0)
{
return x_228;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_228, 0);
x_247 = lean_ctor_get(x_228, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_228);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_249 = !lean_is_exclusive(x_219);
if (x_249 == 0)
{
return x_219;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_219, 0);
x_251 = lean_ctor_get(x_219, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_219);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
block_174:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_24);
x_25 = l_Int_Linear_Poly_gcdCoeffs_x27(x_23);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; 
x_28 = l_Int_Linear_Poly_getConst(x_23);
x_29 = lean_nat_to_int(x_25);
x_30 = lean_int_emod(x_28, x_29);
lean_dec(x_28);
x_31 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_32 = lean_int_dec_eq(x_30, x_31);
lean_dec(x_30);
x_33 = l_Int_Linear_Poly_div(x_29, x_23);
if (x_32 == 0)
{
uint8_t x_99; 
x_99 = 1;
x_34 = x_99;
goto block_98;
}
else
{
uint8_t x_100; 
x_100 = 0;
x_34 = x_100;
goto block_98;
}
block_98:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc(x_33);
x_35 = l_Int_Linear_Poly_denoteExpr(x_12, x_33, x_6, x_7, x_8, x_9, x_20);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_39 = l_Lean_mkAppB(x_21, x_36, x_38);
if (x_34 == 0)
{
lean_object* x_40; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_40 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_box(0);
x_44 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_45 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_46 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_33);
x_47 = lean_int_dec_le(x_31, x_29);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = l_Lean_Expr_const___override(x_3, x_43);
x_49 = lean_int_neg(x_29);
lean_dec(x_29);
x_50 = l_Int_toNat(x_49);
lean_dec(x_49);
x_51 = l_Lean_instToExprInt_mkNat(x_50);
x_52 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_53 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_54 = l_Lean_mkApp3(x_52, x_48, x_53, x_51);
x_55 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__3;
x_56 = l_Lean_reflBoolTrue;
x_57 = l_Lean_mkApp6(x_55, x_41, x_44, x_45, x_46, x_54, x_56);
x_58 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_22, x_39, x_57, x_6, x_7, x_8, x_9, x_42);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_3);
x_59 = l_Int_toNat(x_29);
lean_dec(x_29);
x_60 = l_Lean_instToExprInt_mkNat(x_59);
x_61 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__3;
x_62 = l_Lean_reflBoolTrue;
x_63 = l_Lean_mkApp6(x_61, x_41, x_44, x_45, x_46, x_60, x_62);
x_64 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_22, x_39, x_63, x_6, x_7, x_8, x_9, x_42);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_40);
if (x_65 == 0)
{
return x_40;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_40, 0);
x_67 = lean_ctor_get(x_40, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_40);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_69 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_box(0);
x_73 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_74 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_75 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_33);
x_76 = lean_int_dec_le(x_31, x_29);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_77 = l_Lean_Expr_const___override(x_3, x_72);
x_78 = lean_int_neg(x_29);
lean_dec(x_29);
x_79 = l_Int_toNat(x_78);
lean_dec(x_78);
x_80 = l_Lean_instToExprInt_mkNat(x_79);
x_81 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_82 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_83 = l_Lean_mkApp3(x_81, x_77, x_82, x_80);
x_84 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__6;
x_85 = l_Lean_reflBoolTrue;
x_86 = l_Lean_mkApp6(x_84, x_70, x_73, x_74, x_75, x_83, x_85);
x_87 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_22, x_39, x_86, x_6, x_7, x_8, x_9, x_71);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_3);
x_88 = l_Int_toNat(x_29);
lean_dec(x_29);
x_89 = l_Lean_instToExprInt_mkNat(x_88);
x_90 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__6;
x_91 = l_Lean_reflBoolTrue;
x_92 = l_Lean_mkApp6(x_90, x_70, x_73, x_74, x_75, x_89, x_91);
x_93 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_22, x_39, x_92, x_6, x_7, x_8, x_9, x_71);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_69);
if (x_94 == 0)
{
return x_69;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_69, 0);
x_96 = lean_ctor_get(x_69, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_69);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
else
{
lean_object* x_101; uint8_t x_102; 
lean_dec(x_25);
lean_dec(x_3);
lean_inc(x_23);
x_101 = l_Int_Linear_Poly_denoteExpr(x_12, x_23, x_6, x_7, x_8, x_9, x_20);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_ctor_get(x_101, 1);
x_105 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_106 = l_Lean_mkAppB(x_21, x_103, x_105);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_107 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_104);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_111 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_112 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_23);
x_113 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__9;
x_114 = l_Lean_reflBoolTrue;
x_115 = l_Lean_mkApp5(x_113, x_108, x_110, x_111, x_112, x_114);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_106);
x_116 = l_Lean_Meta_mkEq(x_22, x_106, x_6, x_7, x_8, x_9, x_109);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Meta_mkExpectedTypeHint(x_115, x_117, x_6, x_7, x_8, x_9, x_118);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_119, 0);
lean_ctor_set(x_101, 1, x_121);
lean_ctor_set(x_101, 0, x_106);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_101);
lean_ctor_set(x_119, 0, x_122);
return x_119;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_119, 0);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_119);
lean_ctor_set(x_101, 1, x_123);
lean_ctor_set(x_101, 0, x_106);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_101);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
uint8_t x_127; 
lean_dec(x_106);
lean_free_object(x_101);
x_127 = !lean_is_exclusive(x_119);
if (x_127 == 0)
{
return x_119;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_119, 0);
x_129 = lean_ctor_get(x_119, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_119);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_115);
lean_dec(x_106);
lean_free_object(x_101);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_131 = !lean_is_exclusive(x_116);
if (x_131 == 0)
{
return x_116;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_116, 0);
x_133 = lean_ctor_get(x_116, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_116);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_106);
lean_free_object(x_101);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_107);
if (x_135 == 0)
{
return x_107;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_107, 0);
x_137 = lean_ctor_get(x_107, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_107);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_101, 0);
x_140 = lean_ctor_get(x_101, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_101);
x_141 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_142 = l_Lean_mkAppB(x_21, x_139, x_141);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_143 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_140);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_147 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_148 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_23);
x_149 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__9;
x_150 = l_Lean_reflBoolTrue;
x_151 = l_Lean_mkApp5(x_149, x_144, x_146, x_147, x_148, x_150);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_142);
x_152 = l_Lean_Meta_mkEq(x_22, x_142, x_6, x_7, x_8, x_9, x_145);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Meta_mkExpectedTypeHint(x_151, x_153, x_6, x_7, x_8, x_9, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_142);
lean_ctor_set(x_159, 1, x_156);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
if (lean_is_scalar(x_158)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_158;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_157);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_142);
x_162 = lean_ctor_get(x_155, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_155, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_164 = x_155;
} else {
 lean_dec_ref(x_155);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_151);
lean_dec(x_142);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_166 = lean_ctor_get(x_152, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_152, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_168 = x_152;
} else {
 lean_dec_ref(x_152);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_142);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_ctor_get(x_143, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_143, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_172 = x_143;
} else {
 lean_dec_ref(x_143);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_373; 
x_253 = lean_ctor_get(x_17, 0);
x_254 = lean_ctor_get(x_17, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_17);
x_255 = l___private_Lean_Expr_0__Lean_intLEPred;
x_256 = l_Lean_mkAppB(x_255, x_15, x_253);
lean_inc(x_2);
lean_inc(x_1);
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 0, x_1);
x_257 = l_Int_Linear_Expr_norm(x_13);
lean_dec(x_13);
x_373 = l_Int_Linear_Poly_isUnsatLe(x_257);
if (x_373 == 0)
{
uint8_t x_374; 
x_374 = l_Int_Linear_Poly_isValidLe(x_257);
if (x_374 == 0)
{
if (x_4 == 0)
{
lean_object* x_375; 
x_375 = lean_box(0);
x_258 = x_375;
goto block_372;
}
else
{
lean_object* x_376; uint8_t x_377; 
lean_inc(x_257);
x_376 = l_Int_Linear_Poly_toExpr(x_257);
x_377 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_376, x_1);
lean_dec(x_376);
if (x_377 == 0)
{
lean_object* x_378; 
x_378 = lean_box(0);
x_258 = x_378;
goto block_372;
}
else
{
lean_object* x_379; uint8_t x_380; 
x_379 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__37;
x_380 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_2, x_379);
if (x_380 == 0)
{
lean_object* x_381; 
x_381 = lean_box(0);
x_258 = x_381;
goto block_372;
}
else
{
lean_object* x_382; lean_object* x_383; 
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_382 = lean_box(0);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_254);
return x_383;
}
}
}
}
else
{
lean_object* x_384; 
lean_dec(x_257);
lean_dec(x_12);
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_384 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_254);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_388 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_389 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__12;
x_390 = l_Lean_reflBoolTrue;
x_391 = l_Lean_mkApp4(x_389, x_385, x_387, x_388, x_390);
x_392 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__40;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_393 = l_Lean_Meta_mkEq(x_256, x_392, x_6, x_7, x_8, x_9, x_386);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = l_Lean_Meta_mkExpectedTypeHint(x_391, x_394, x_6, x_7, x_8, x_9, x_395);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_399 = x_396;
} else {
 lean_dec_ref(x_396);
 x_399 = lean_box(0);
}
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_392);
lean_ctor_set(x_400, 1, x_397);
x_401 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_401, 0, x_400);
if (lean_is_scalar(x_399)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_399;
}
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_398);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_403 = lean_ctor_get(x_396, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_396, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_405 = x_396;
} else {
 lean_dec_ref(x_396);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_404);
return x_406;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_391);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_407 = lean_ctor_get(x_393, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_393, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_409 = x_393;
} else {
 lean_dec_ref(x_393);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_256);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_411 = lean_ctor_get(x_384, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_384, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_413 = x_384;
} else {
 lean_dec_ref(x_384);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 2, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_412);
return x_414;
}
}
}
else
{
lean_object* x_415; 
lean_dec(x_257);
lean_dec(x_12);
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_415 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_254);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec(x_415);
x_418 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_419 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_420 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__15;
x_421 = l_Lean_reflBoolTrue;
x_422 = l_Lean_mkApp4(x_420, x_416, x_418, x_419, x_421);
x_423 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_424 = l_Lean_Meta_mkEq(x_256, x_423, x_6, x_7, x_8, x_9, x_417);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_427 = l_Lean_Meta_mkExpectedTypeHint(x_422, x_425, x_6, x_7, x_8, x_9, x_426);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 x_430 = x_427;
} else {
 lean_dec_ref(x_427);
 x_430 = lean_box(0);
}
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_423);
lean_ctor_set(x_431, 1, x_428);
x_432 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_432, 0, x_431);
if (lean_is_scalar(x_430)) {
 x_433 = lean_alloc_ctor(0, 2, 0);
} else {
 x_433 = x_430;
}
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_429);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_ctor_get(x_427, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_427, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 x_436 = x_427;
} else {
 lean_dec_ref(x_427);
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
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_422);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_438 = lean_ctor_get(x_424, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_424, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_440 = x_424;
} else {
 lean_dec_ref(x_424);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_256);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_442 = lean_ctor_get(x_415, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_415, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_444 = x_415;
} else {
 lean_dec_ref(x_415);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
block_372:
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; 
lean_dec(x_258);
x_259 = l_Int_Linear_Poly_gcdCoeffs_x27(x_257);
x_260 = lean_unsigned_to_nat(1u);
x_261 = lean_nat_dec_eq(x_259, x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; uint8_t x_268; 
x_262 = l_Int_Linear_Poly_getConst(x_257);
x_263 = lean_nat_to_int(x_259);
x_264 = lean_int_emod(x_262, x_263);
lean_dec(x_262);
x_265 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_266 = lean_int_dec_eq(x_264, x_265);
lean_dec(x_264);
x_267 = l_Int_Linear_Poly_div(x_263, x_257);
if (x_266 == 0)
{
uint8_t x_333; 
x_333 = 1;
x_268 = x_333;
goto block_332;
}
else
{
uint8_t x_334; 
x_334 = 0;
x_268 = x_334;
goto block_332;
}
block_332:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_inc(x_267);
x_269 = l_Int_Linear_Poly_denoteExpr(x_12, x_267, x_6, x_7, x_8, x_9, x_254);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_273 = l_Lean_mkAppB(x_255, x_270, x_272);
if (x_268 == 0)
{
lean_object* x_274; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_274 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_271);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = lean_box(0);
x_278 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_279 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_280 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_267);
x_281 = lean_int_dec_le(x_265, x_263);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_282 = l_Lean_Expr_const___override(x_3, x_277);
x_283 = lean_int_neg(x_263);
lean_dec(x_263);
x_284 = l_Int_toNat(x_283);
lean_dec(x_283);
x_285 = l_Lean_instToExprInt_mkNat(x_284);
x_286 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_287 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_288 = l_Lean_mkApp3(x_286, x_282, x_287, x_285);
x_289 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__3;
x_290 = l_Lean_reflBoolTrue;
x_291 = l_Lean_mkApp6(x_289, x_275, x_278, x_279, x_280, x_288, x_290);
x_292 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_256, x_273, x_291, x_6, x_7, x_8, x_9, x_276);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_3);
x_293 = l_Int_toNat(x_263);
lean_dec(x_263);
x_294 = l_Lean_instToExprInt_mkNat(x_293);
x_295 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__3;
x_296 = l_Lean_reflBoolTrue;
x_297 = l_Lean_mkApp6(x_295, x_275, x_278, x_279, x_280, x_294, x_296);
x_298 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_256, x_273, x_297, x_6, x_7, x_8, x_9, x_276);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_273);
lean_dec(x_267);
lean_dec(x_263);
lean_dec(x_256);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_299 = lean_ctor_get(x_274, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_274, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_301 = x_274;
} else {
 lean_dec_ref(x_274);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
else
{
lean_object* x_303; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_303 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_271);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = lean_box(0);
x_307 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_308 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_309 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_267);
x_310 = lean_int_dec_le(x_265, x_263);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_311 = l_Lean_Expr_const___override(x_3, x_306);
x_312 = lean_int_neg(x_263);
lean_dec(x_263);
x_313 = l_Int_toNat(x_312);
lean_dec(x_312);
x_314 = l_Lean_instToExprInt_mkNat(x_313);
x_315 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_316 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_317 = l_Lean_mkApp3(x_315, x_311, x_316, x_314);
x_318 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__6;
x_319 = l_Lean_reflBoolTrue;
x_320 = l_Lean_mkApp6(x_318, x_304, x_307, x_308, x_309, x_317, x_319);
x_321 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_256, x_273, x_320, x_6, x_7, x_8, x_9, x_305);
return x_321;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_3);
x_322 = l_Int_toNat(x_263);
lean_dec(x_263);
x_323 = l_Lean_instToExprInt_mkNat(x_322);
x_324 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__6;
x_325 = l_Lean_reflBoolTrue;
x_326 = l_Lean_mkApp6(x_324, x_304, x_307, x_308, x_309, x_323, x_325);
x_327 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_256, x_273, x_326, x_6, x_7, x_8, x_9, x_305);
return x_327;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_273);
lean_dec(x_267);
lean_dec(x_263);
lean_dec(x_256);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_328 = lean_ctor_get(x_303, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_303, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_330 = x_303;
} else {
 lean_dec_ref(x_303);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_329);
return x_331;
}
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_259);
lean_dec(x_3);
lean_inc(x_257);
x_335 = l_Int_Linear_Poly_denoteExpr(x_12, x_257, x_6, x_7, x_8, x_9, x_254);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_338 = x_335;
} else {
 lean_dec_ref(x_335);
 x_338 = lean_box(0);
}
x_339 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_340 = l_Lean_mkAppB(x_255, x_336, x_339);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_341 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_337);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_345 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_346 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_257);
x_347 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__9;
x_348 = l_Lean_reflBoolTrue;
x_349 = l_Lean_mkApp5(x_347, x_342, x_344, x_345, x_346, x_348);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_340);
x_350 = l_Lean_Meta_mkEq(x_256, x_340, x_6, x_7, x_8, x_9, x_343);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = l_Lean_Meta_mkExpectedTypeHint(x_349, x_351, x_6, x_7, x_8, x_9, x_352);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_356 = x_353;
} else {
 lean_dec_ref(x_353);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_338;
}
lean_ctor_set(x_357, 0, x_340);
lean_ctor_set(x_357, 1, x_354);
x_358 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_358, 0, x_357);
if (lean_is_scalar(x_356)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_356;
}
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_355);
return x_359;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_340);
lean_dec(x_338);
x_360 = lean_ctor_get(x_353, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_353, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_362 = x_353;
} else {
 lean_dec_ref(x_353);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_349);
lean_dec(x_340);
lean_dec(x_338);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_364 = lean_ctor_get(x_350, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_350, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_366 = x_350;
} else {
 lean_dec_ref(x_350);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(1, 2, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_364);
lean_ctor_set(x_367, 1, x_365);
return x_367;
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_340);
lean_dec(x_338);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_368 = lean_ctor_get(x_341, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_341, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_370 = x_341;
} else {
 lean_dec_ref(x_341);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
}
}
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_571; 
x_446 = lean_ctor_get(x_13, 0);
x_447 = lean_ctor_get(x_13, 1);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_13);
lean_inc(x_2);
lean_inc(x_12);
x_448 = l_Int_Linear_Expr_denoteExpr(x_12, x_2, x_6, x_7, x_8, x_9, x_447);
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_451 = x_448;
} else {
 lean_dec_ref(x_448);
 x_451 = lean_box(0);
}
x_452 = l___private_Lean_Expr_0__Lean_intLEPred;
x_453 = l_Lean_mkAppB(x_452, x_446, x_449);
lean_inc(x_2);
lean_inc(x_1);
x_454 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_454, 0, x_1);
lean_ctor_set(x_454, 1, x_2);
x_455 = l_Int_Linear_Expr_norm(x_454);
lean_dec(x_454);
x_571 = l_Int_Linear_Poly_isUnsatLe(x_455);
if (x_571 == 0)
{
uint8_t x_572; 
x_572 = l_Int_Linear_Poly_isValidLe(x_455);
if (x_572 == 0)
{
if (x_4 == 0)
{
lean_object* x_573; 
lean_dec(x_451);
x_573 = lean_box(0);
x_456 = x_573;
goto block_570;
}
else
{
lean_object* x_574; uint8_t x_575; 
lean_inc(x_455);
x_574 = l_Int_Linear_Poly_toExpr(x_455);
x_575 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_574, x_1);
lean_dec(x_574);
if (x_575 == 0)
{
lean_object* x_576; 
lean_dec(x_451);
x_576 = lean_box(0);
x_456 = x_576;
goto block_570;
}
else
{
lean_object* x_577; uint8_t x_578; 
x_577 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__37;
x_578 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_2, x_577);
if (x_578 == 0)
{
lean_object* x_579; 
lean_dec(x_451);
x_579 = lean_box(0);
x_456 = x_579;
goto block_570;
}
else
{
lean_object* x_580; lean_object* x_581; 
lean_dec(x_455);
lean_dec(x_453);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_580 = lean_box(0);
if (lean_is_scalar(x_451)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_451;
}
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_450);
return x_581;
}
}
}
}
else
{
lean_object* x_582; 
lean_dec(x_455);
lean_dec(x_451);
lean_dec(x_12);
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_582 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_450);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
lean_dec(x_582);
x_585 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_586 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_587 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__12;
x_588 = l_Lean_reflBoolTrue;
x_589 = l_Lean_mkApp4(x_587, x_583, x_585, x_586, x_588);
x_590 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__40;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_591 = l_Lean_Meta_mkEq(x_453, x_590, x_6, x_7, x_8, x_9, x_584);
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_591, 1);
lean_inc(x_593);
lean_dec(x_591);
x_594 = l_Lean_Meta_mkExpectedTypeHint(x_589, x_592, x_6, x_7, x_8, x_9, x_593);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_594, 1);
lean_inc(x_596);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_597 = x_594;
} else {
 lean_dec_ref(x_594);
 x_597 = lean_box(0);
}
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_590);
lean_ctor_set(x_598, 1, x_595);
x_599 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_599, 0, x_598);
if (lean_is_scalar(x_597)) {
 x_600 = lean_alloc_ctor(0, 2, 0);
} else {
 x_600 = x_597;
}
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_596);
return x_600;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_601 = lean_ctor_get(x_594, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_594, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_603 = x_594;
} else {
 lean_dec_ref(x_594);
 x_603 = lean_box(0);
}
if (lean_is_scalar(x_603)) {
 x_604 = lean_alloc_ctor(1, 2, 0);
} else {
 x_604 = x_603;
}
lean_ctor_set(x_604, 0, x_601);
lean_ctor_set(x_604, 1, x_602);
return x_604;
}
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
lean_dec(x_589);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_605 = lean_ctor_get(x_591, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_591, 1);
lean_inc(x_606);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 lean_ctor_release(x_591, 1);
 x_607 = x_591;
} else {
 lean_dec_ref(x_591);
 x_607 = lean_box(0);
}
if (lean_is_scalar(x_607)) {
 x_608 = lean_alloc_ctor(1, 2, 0);
} else {
 x_608 = x_607;
}
lean_ctor_set(x_608, 0, x_605);
lean_ctor_set(x_608, 1, x_606);
return x_608;
}
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_453);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_609 = lean_ctor_get(x_582, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_582, 1);
lean_inc(x_610);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_611 = x_582;
} else {
 lean_dec_ref(x_582);
 x_611 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_612 = lean_alloc_ctor(1, 2, 0);
} else {
 x_612 = x_611;
}
lean_ctor_set(x_612, 0, x_609);
lean_ctor_set(x_612, 1, x_610);
return x_612;
}
}
}
else
{
lean_object* x_613; 
lean_dec(x_455);
lean_dec(x_451);
lean_dec(x_12);
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_613 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_450);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec(x_613);
x_616 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_617 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_618 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__15;
x_619 = l_Lean_reflBoolTrue;
x_620 = l_Lean_mkApp4(x_618, x_614, x_616, x_617, x_619);
x_621 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_622 = l_Lean_Meta_mkEq(x_453, x_621, x_6, x_7, x_8, x_9, x_615);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
lean_dec(x_622);
x_625 = l_Lean_Meta_mkExpectedTypeHint(x_620, x_623, x_6, x_7, x_8, x_9, x_624);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_625, 1);
lean_inc(x_627);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_628 = x_625;
} else {
 lean_dec_ref(x_625);
 x_628 = lean_box(0);
}
x_629 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_629, 0, x_621);
lean_ctor_set(x_629, 1, x_626);
x_630 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_630, 0, x_629);
if (lean_is_scalar(x_628)) {
 x_631 = lean_alloc_ctor(0, 2, 0);
} else {
 x_631 = x_628;
}
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_627);
return x_631;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_632 = lean_ctor_get(x_625, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_625, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_634 = x_625;
} else {
 lean_dec_ref(x_625);
 x_634 = lean_box(0);
}
if (lean_is_scalar(x_634)) {
 x_635 = lean_alloc_ctor(1, 2, 0);
} else {
 x_635 = x_634;
}
lean_ctor_set(x_635, 0, x_632);
lean_ctor_set(x_635, 1, x_633);
return x_635;
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_620);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_636 = lean_ctor_get(x_622, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_622, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_638 = x_622;
} else {
 lean_dec_ref(x_622);
 x_638 = lean_box(0);
}
if (lean_is_scalar(x_638)) {
 x_639 = lean_alloc_ctor(1, 2, 0);
} else {
 x_639 = x_638;
}
lean_ctor_set(x_639, 0, x_636);
lean_ctor_set(x_639, 1, x_637);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_453);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_640 = lean_ctor_get(x_613, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_613, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_642 = x_613;
} else {
 lean_dec_ref(x_613);
 x_642 = lean_box(0);
}
if (lean_is_scalar(x_642)) {
 x_643 = lean_alloc_ctor(1, 2, 0);
} else {
 x_643 = x_642;
}
lean_ctor_set(x_643, 0, x_640);
lean_ctor_set(x_643, 1, x_641);
return x_643;
}
}
block_570:
{
lean_object* x_457; lean_object* x_458; uint8_t x_459; 
lean_dec(x_456);
x_457 = l_Int_Linear_Poly_gcdCoeffs_x27(x_455);
x_458 = lean_unsigned_to_nat(1u);
x_459 = lean_nat_dec_eq(x_457, x_458);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; uint8_t x_466; 
x_460 = l_Int_Linear_Poly_getConst(x_455);
x_461 = lean_nat_to_int(x_457);
x_462 = lean_int_emod(x_460, x_461);
lean_dec(x_460);
x_463 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_464 = lean_int_dec_eq(x_462, x_463);
lean_dec(x_462);
x_465 = l_Int_Linear_Poly_div(x_461, x_455);
if (x_464 == 0)
{
uint8_t x_531; 
x_531 = 1;
x_466 = x_531;
goto block_530;
}
else
{
uint8_t x_532; 
x_532 = 0;
x_466 = x_532;
goto block_530;
}
block_530:
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_inc(x_465);
x_467 = l_Int_Linear_Poly_denoteExpr(x_12, x_465, x_6, x_7, x_8, x_9, x_450);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
x_470 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_471 = l_Lean_mkAppB(x_452, x_468, x_470);
if (x_466 == 0)
{
lean_object* x_472; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_472 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_469);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec(x_472);
x_475 = lean_box(0);
x_476 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_477 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_478 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_465);
x_479 = lean_int_dec_le(x_463, x_461);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_480 = l_Lean_Expr_const___override(x_3, x_475);
x_481 = lean_int_neg(x_461);
lean_dec(x_461);
x_482 = l_Int_toNat(x_481);
lean_dec(x_481);
x_483 = l_Lean_instToExprInt_mkNat(x_482);
x_484 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_485 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_486 = l_Lean_mkApp3(x_484, x_480, x_485, x_483);
x_487 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__3;
x_488 = l_Lean_reflBoolTrue;
x_489 = l_Lean_mkApp6(x_487, x_473, x_476, x_477, x_478, x_486, x_488);
x_490 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_453, x_471, x_489, x_6, x_7, x_8, x_9, x_474);
return x_490;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_3);
x_491 = l_Int_toNat(x_461);
lean_dec(x_461);
x_492 = l_Lean_instToExprInt_mkNat(x_491);
x_493 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__3;
x_494 = l_Lean_reflBoolTrue;
x_495 = l_Lean_mkApp6(x_493, x_473, x_476, x_477, x_478, x_492, x_494);
x_496 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_453, x_471, x_495, x_6, x_7, x_8, x_9, x_474);
return x_496;
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_471);
lean_dec(x_465);
lean_dec(x_461);
lean_dec(x_453);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_497 = lean_ctor_get(x_472, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_472, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_499 = x_472;
} else {
 lean_dec_ref(x_472);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
}
else
{
lean_object* x_501; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_501 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_469);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; uint8_t x_508; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
lean_dec(x_501);
x_504 = lean_box(0);
x_505 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_506 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_507 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_465);
x_508 = lean_int_dec_le(x_463, x_461);
if (x_508 == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_509 = l_Lean_Expr_const___override(x_3, x_504);
x_510 = lean_int_neg(x_461);
lean_dec(x_461);
x_511 = l_Int_toNat(x_510);
lean_dec(x_510);
x_512 = l_Lean_instToExprInt_mkNat(x_511);
x_513 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_514 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_515 = l_Lean_mkApp3(x_513, x_509, x_514, x_512);
x_516 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__6;
x_517 = l_Lean_reflBoolTrue;
x_518 = l_Lean_mkApp6(x_516, x_502, x_505, x_506, x_507, x_515, x_517);
x_519 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_453, x_471, x_518, x_6, x_7, x_8, x_9, x_503);
return x_519;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec(x_3);
x_520 = l_Int_toNat(x_461);
lean_dec(x_461);
x_521 = l_Lean_instToExprInt_mkNat(x_520);
x_522 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__6;
x_523 = l_Lean_reflBoolTrue;
x_524 = l_Lean_mkApp6(x_522, x_502, x_505, x_506, x_507, x_521, x_523);
x_525 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_453, x_471, x_524, x_6, x_7, x_8, x_9, x_503);
return x_525;
}
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_471);
lean_dec(x_465);
lean_dec(x_461);
lean_dec(x_453);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_526 = lean_ctor_get(x_501, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_501, 1);
lean_inc(x_527);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_528 = x_501;
} else {
 lean_dec_ref(x_501);
 x_528 = lean_box(0);
}
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 2, 0);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_526);
lean_ctor_set(x_529, 1, x_527);
return x_529;
}
}
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_457);
lean_dec(x_3);
lean_inc(x_455);
x_533 = l_Int_Linear_Poly_denoteExpr(x_12, x_455, x_6, x_7, x_8, x_9, x_450);
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 x_536 = x_533;
} else {
 lean_dec_ref(x_533);
 x_536 = lean_box(0);
}
x_537 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19;
x_538 = l_Lean_mkAppB(x_452, x_534, x_537);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_539 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_535);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec(x_539);
x_542 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_543 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_544 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_455);
x_545 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__9;
x_546 = l_Lean_reflBoolTrue;
x_547 = l_Lean_mkApp5(x_545, x_540, x_542, x_543, x_544, x_546);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_538);
x_548 = l_Lean_Meta_mkEq(x_453, x_538, x_6, x_7, x_8, x_9, x_541);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
x_551 = l_Lean_Meta_mkExpectedTypeHint(x_547, x_549, x_6, x_7, x_8, x_9, x_550);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 x_554 = x_551;
} else {
 lean_dec_ref(x_551);
 x_554 = lean_box(0);
}
if (lean_is_scalar(x_536)) {
 x_555 = lean_alloc_ctor(0, 2, 0);
} else {
 x_555 = x_536;
}
lean_ctor_set(x_555, 0, x_538);
lean_ctor_set(x_555, 1, x_552);
x_556 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_556, 0, x_555);
if (lean_is_scalar(x_554)) {
 x_557 = lean_alloc_ctor(0, 2, 0);
} else {
 x_557 = x_554;
}
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_557, 1, x_553);
return x_557;
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
lean_dec(x_538);
lean_dec(x_536);
x_558 = lean_ctor_get(x_551, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_551, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 x_560 = x_551;
} else {
 lean_dec_ref(x_551);
 x_560 = lean_box(0);
}
if (lean_is_scalar(x_560)) {
 x_561 = lean_alloc_ctor(1, 2, 0);
} else {
 x_561 = x_560;
}
lean_ctor_set(x_561, 0, x_558);
lean_ctor_set(x_561, 1, x_559);
return x_561;
}
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec(x_547);
lean_dec(x_538);
lean_dec(x_536);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_562 = lean_ctor_get(x_548, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_548, 1);
lean_inc(x_563);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 x_564 = x_548;
} else {
 lean_dec_ref(x_548);
 x_564 = lean_box(0);
}
if (lean_is_scalar(x_564)) {
 x_565 = lean_alloc_ctor(1, 2, 0);
} else {
 x_565 = x_564;
}
lean_ctor_set(x_565, 0, x_562);
lean_ctor_set(x_565, 1, x_563);
return x_565;
}
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_538);
lean_dec(x_536);
lean_dec(x_455);
lean_dec(x_453);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_566 = lean_ctor_get(x_539, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_539, 1);
lean_inc(x_567);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_568 = x_539;
} else {
 lean_dec_ref(x_539);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(1, 2, 0);
} else {
 x_569 = x_568;
}
lean_ctor_set(x_569, 0, x_566);
lean_ctor_set(x_569, 1, x_567);
return x_569;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3;
x_24 = l_Lean_Expr_isAppOf(x_1, x_23);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
if (x_24 == 0)
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 0;
x_8 = x_28;
x_9 = x_26;
x_10 = x_27;
goto block_22;
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_8 = x_2;
x_9 = x_33;
x_10 = x_34;
goto block_22;
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_22:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_19 = lean_box(x_8);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___boxed), 10, 4);
lean_closure_set(x_20, 0, x_15);
lean_closure_set(x_20, 1, x_16);
lean_closure_set(x_20, 2, x_18);
lean_closure_set(x_20, 3, x_19);
x_21 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_17, x_18, x_20, x_3, x_4, x_5, x_6, x_10);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trans", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__1;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__4() {
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__3;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_box(0);
x_16 = l_Lean_Expr_const___override(x_5, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_17);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_sub(x_18, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_23 = l_Lean_Expr_getRevArg_x21(x_2, x_22);
x_24 = lean_unsigned_to_nat(3u);
x_25 = lean_nat_sub(x_18, x_24);
lean_dec(x_18);
x_26 = lean_nat_sub(x_25, x_21);
lean_dec(x_25);
x_27 = l_Lean_Expr_getRevArg_x21(x_2, x_26);
x_28 = l_Lean_mkAppB(x_16, x_23, x_27);
x_29 = 0;
lean_inc(x_14);
x_30 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_14, x_29, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_4, 0, x_34);
lean_ctor_set(x_30, 0, x_4);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_14);
lean_ctor_set(x_36, 1, x_28);
lean_ctor_set(x_4, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_free_object(x_4);
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_30, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
x_45 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__5;
x_46 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__6;
lean_inc(x_43);
x_47 = l_Lean_mkApp6(x_45, x_46, x_3, x_14, x_43, x_28, x_44);
lean_ctor_set(x_40, 1, x_47);
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_40);
x_50 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__5;
x_51 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__6;
lean_inc(x_48);
x_52 = l_Lean_mkApp6(x_50, x_51, x_3, x_14, x_48, x_28, x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_31, 0, x_53);
return x_30;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_31, 0);
x_55 = lean_ctor_get(x_30, 1);
lean_inc(x_55);
lean_dec(x_30);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_58 = x_54;
} else {
 lean_dec_ref(x_54);
 x_58 = lean_box(0);
}
x_59 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__5;
x_60 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__6;
lean_inc(x_56);
x_61 = l_Lean_mkApp6(x_59, x_60, x_3, x_14, x_56, x_28, x_57);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_31, 0, x_62);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_31);
lean_ctor_set(x_63, 1, x_55);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = lean_ctor_get(x_31, 0);
lean_inc(x_64);
lean_dec(x_31);
x_65 = lean_ctor_get(x_30, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_66 = x_30;
} else {
 lean_dec_ref(x_30);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_69 = x_64;
} else {
 lean_dec_ref(x_64);
 x_69 = lean_box(0);
}
x_70 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__5;
x_71 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__6;
lean_inc(x_67);
x_72 = l_Lean_mkApp6(x_70, x_71, x_3, x_14, x_67, x_28, x_68);
if (lean_is_scalar(x_69)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_69;
}
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
if (lean_is_scalar(x_66)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_66;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_65);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_28);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_3);
x_76 = !lean_is_exclusive(x_30);
if (x_76 == 0)
{
return x_30;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_30, 0);
x_78 = lean_ctor_get(x_30, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_30);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_80 = lean_ctor_get(x_4, 0);
lean_inc(x_80);
lean_dec(x_4);
x_81 = lean_box(0);
x_82 = l_Lean_Expr_const___override(x_5, x_81);
x_83 = lean_unsigned_to_nat(0u);
x_84 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_83);
x_85 = lean_unsigned_to_nat(2u);
x_86 = lean_nat_sub(x_84, x_85);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_sub(x_86, x_87);
lean_dec(x_86);
x_89 = l_Lean_Expr_getRevArg_x21(x_2, x_88);
x_90 = lean_unsigned_to_nat(3u);
x_91 = lean_nat_sub(x_84, x_90);
lean_dec(x_84);
x_92 = lean_nat_sub(x_91, x_87);
lean_dec(x_91);
x_93 = l_Lean_Expr_getRevArg_x21(x_2, x_92);
x_94 = l_Lean_mkAppB(x_82, x_89, x_93);
x_95 = 0;
lean_inc(x_80);
x_96 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_80, x_95, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_3);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_80);
lean_ctor_set(x_100, 1, x_94);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_98);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_104 = x_97;
} else {
 lean_dec_ref(x_97);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_96, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_106 = x_96;
} else {
 lean_dec_ref(x_96);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__5;
x_111 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__6;
lean_inc(x_107);
x_112 = l_Lean_mkApp6(x_110, x_111, x_3, x_80, x_107, x_94, x_108);
if (lean_is_scalar(x_109)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_109;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_112);
if (lean_is_scalar(x_104)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_104;
}
lean_ctor_set(x_114, 0, x_113);
if (lean_is_scalar(x_106)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_106;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_105);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_94);
lean_dec(x_80);
lean_dec(x_3);
x_116 = lean_ctor_get(x_96, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_96, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_118 = x_96;
} else {
 lean_dec_ref(x_96);
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
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_gt_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l___private_Lean_Expr_0__Lean_intLEPred;
x_11 = l_Lean_mkAppB(x_10, x_1, x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___closed__2;
x_14 = lean_box(0);
x_15 = lean_apply_8(x_3, x_12, x_13, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = lean_box(0);
x_11 = lean_apply_8(x_1, x_2, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_3, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_cleanupAnnotations(x_12);
x_15 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_16 = l_Lean_Expr_isConstOf(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_apply_8(x_1, x_2, x_17, x_18, x_6, x_7, x_8, x_9, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2(x_4, x_5, x_1, x_20, x_6, x_7, x_8, x_9, x_13);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_lt_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l___private_Lean_Expr_0__Lean_intLEPred;
x_11 = l_Lean_mkAppB(x_10, x_1, x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___closed__2;
x_14 = lean_box(0);
x_15 = lean_apply_8(x_3, x_12, x_13, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_3, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_cleanupAnnotations(x_12);
x_15 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_16 = l_Lean_Expr_isConstOf(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_apply_8(x_1, x_2, x_17, x_18, x_6, x_7, x_8, x_9, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5(x_5, x_4, x_1, x_20, x_6, x_7, x_8, x_9, x_13);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__26;
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_ge_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l___private_Lean_Expr_0__Lean_intAddFn;
x_11 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__1;
x_12 = l_Lean_mkAppB(x_10, x_1, x_11);
x_13 = l___private_Lean_Expr_0__Lean_intLEPred;
x_14 = l_Lean_mkAppB(x_13, x_12, x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__3;
x_17 = lean_box(0);
x_18 = lean_apply_8(x_3, x_15, x_16, x_17, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_3, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_cleanupAnnotations(x_12);
x_15 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_16 = l_Lean_Expr_isConstOf(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_apply_8(x_1, x_2, x_17, x_18, x_6, x_7, x_8, x_9, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7(x_4, x_5, x_1, x_20, x_6, x_7, x_8, x_9, x_13);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_le_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l___private_Lean_Expr_0__Lean_intAddFn;
x_11 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__1;
x_12 = l_Lean_mkAppB(x_10, x_1, x_11);
x_13 = l___private_Lean_Expr_0__Lean_intLEPred;
x_14 = l_Lean_mkAppB(x_13, x_12, x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___closed__2;
x_17 = lean_box(0);
x_18 = lean_apply_8(x_3, x_15, x_16, x_17, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_3, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_cleanupAnnotations(x_12);
x_15 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_16 = l_Lean_Expr_isConstOf(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_apply_8(x_1, x_2, x_17, x_18, x_6, x_7, x_8, x_9, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9(x_5, x_4, x_1, x_20, x_6, x_7, x_8, x_9, x_13);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ge", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = l_Lean_Expr_appArg_x21(x_1);
x_13 = lean_box(0);
lean_inc(x_1);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___boxed), 11, 3);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_1);
lean_inc(x_12);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_12, x_2, x_3, x_4, x_5, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_cleanupAnnotations(x_16);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1(x_13, x_12, x_1, x_13, x_20, x_21, x_2, x_3, x_4, x_5, x_17);
lean_dec(x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Expr_appArg(x_18, lean_box(0));
x_24 = l_Lean_Expr_appFnCleanup(x_18, lean_box(0));
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_14);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1(x_13, x_12, x_1, x_13, x_26, x_27, x_2, x_3, x_4, x_5, x_17);
lean_dec(x_12);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Expr_appArg(x_24, lean_box(0));
x_30 = l_Lean_Expr_appFnCleanup(x_24, lean_box(0));
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_14);
x_32 = lean_box(0);
x_33 = lean_box(0);
x_34 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1(x_13, x_12, x_1, x_13, x_32, x_33, x_2, x_3, x_4, x_5, x_17);
lean_dec(x_12);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Expr_appFnCleanup(x_30, lean_box(0));
x_36 = l_Lean_Expr_isApp(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_14);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1(x_13, x_12, x_1, x_13, x_37, x_38, x_2, x_3, x_4, x_5, x_17);
lean_dec(x_12);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = l_Lean_Expr_appArg(x_35, lean_box(0));
x_41 = l_Lean_Expr_appFnCleanup(x_35, lean_box(0));
x_42 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
x_43 = l_Lean_Expr_isConstOf(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8;
x_45 = l_Lean_Expr_isConstOf(x_41, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11;
x_47 = l_Lean_Expr_isConstOf(x_41, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3;
x_49 = l_Lean_Expr_isConstOf(x_41, x_48);
lean_dec(x_41);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_14);
x_50 = lean_box(0);
x_51 = lean_box(0);
x_52 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1(x_13, x_12, x_1, x_13, x_50, x_51, x_2, x_3, x_4, x_5, x_17);
lean_dec(x_12);
return x_52;
}
else
{
lean_object* x_53; 
lean_dec(x_12);
lean_dec(x_1);
x_53 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__10(x_14, x_13, x_40, x_29, x_23, x_2, x_3, x_4, x_5, x_17);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_41);
lean_dec(x_12);
lean_dec(x_1);
x_54 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__8(x_14, x_13, x_40, x_29, x_23, x_2, x_3, x_4, x_5, x_17);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_41);
lean_dec(x_12);
lean_dec(x_1);
x_55 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__6(x_14, x_13, x_40, x_29, x_23, x_2, x_3, x_4, x_5, x_17);
return x_55;
}
}
else
{
lean_object* x_56; 
lean_dec(x_41);
lean_dec(x_12);
lean_dec(x_1);
x_56 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__4(x_14, x_13, x_40, x_29, x_23, x_2, x_3, x_4, x_5, x_17);
return x_56;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_dvd_gcd", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_dvd", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
lean_inc(x_2);
x_17 = l_Int_Linear_Poly_denoteExpr(x_1, x_2, x_12, x_13, x_14, x_15, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_int_dec_le(x_3, x_4);
x_21 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__26;
x_22 = lean_int_dec_eq(x_5, x_21);
if (x_20 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_box(0);
lean_inc(x_9);
x_68 = l_Lean_Expr_const___override(x_9, x_67);
x_69 = lean_int_neg(x_4);
x_70 = l_Int_toNat(x_69);
lean_dec(x_69);
x_71 = l_Lean_instToExprInt_mkNat(x_70);
x_72 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__28;
x_73 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_74 = l_Lean_mkApp3(x_72, x_68, x_73, x_71);
x_23 = x_74;
goto block_66;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Int_toNat(x_4);
x_76 = l_Lean_instToExprInt_mkNat(x_75);
x_23 = x_76;
goto block_66;
}
block_66:
{
lean_object* x_24; 
lean_inc(x_23);
x_24 = l_Lean_mkIntDvd(x_23, x_18);
if (x_22 == 0)
{
lean_object* x_25; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_25 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_7, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_8);
x_30 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_2);
x_31 = lean_int_dec_le(x_3, x_5);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = l_Lean_Expr_const___override(x_9, x_28);
x_33 = lean_int_neg(x_5);
x_34 = l_Int_toNat(x_33);
lean_dec(x_33);
x_35 = l_Lean_instToExprInt_mkNat(x_34);
x_36 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15;
x_37 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_38 = l_Lean_mkApp3(x_36, x_32, x_37, x_35);
x_39 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__3;
x_40 = l_Lean_reflBoolTrue;
x_41 = l_Lean_mkApp7(x_39, x_26, x_10, x_29, x_23, x_30, x_38, x_40);
x_42 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_6, x_24, x_41, x_12, x_13, x_14, x_15, x_27);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_9);
x_43 = l_Int_toNat(x_5);
x_44 = l_Lean_instToExprInt_mkNat(x_43);
x_45 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__3;
x_46 = l_Lean_reflBoolTrue;
x_47 = l_Lean_mkApp7(x_45, x_26, x_10, x_29, x_23, x_30, x_44, x_46);
x_48 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_6, x_24, x_47, x_12, x_13, x_14, x_15, x_27);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_25);
if (x_49 == 0)
{
return x_25;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_25, 0);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_25);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_23);
lean_dec(x_9);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_53 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_7, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_8);
x_57 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_2);
x_58 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__6;
x_59 = l_Lean_reflBoolTrue;
x_60 = l_Lean_mkApp5(x_58, x_54, x_10, x_56, x_57, x_59);
x_61 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__1(x_6, x_24, x_60, x_12, x_13, x_14, x_15, x_55);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_53);
if (x_62 == 0)
{
return x_53;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_53, 0);
x_64 = lean_ctor_get(x_53, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_53);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dvd_eq_false", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_10 = l_Lean_instInhabitedExpr;
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Array_get_x21Internal___boxed), 4, 3);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_4);
lean_inc(x_1);
lean_inc(x_11);
x_12 = l_Int_Linear_Expr_denoteExpr(x_11, x_1, x_5, x_6, x_7, x_8, x_9);
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
x_16 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_17 = lean_int_dec_le(x_16, x_2);
x_18 = l_Int_Linear_Expr_norm(x_1);
lean_inc(x_2);
x_19 = l_Int_Linear_Poly_gcdCoeffs(x_18, x_2);
x_20 = l_Int_Linear_Poly_getConst(x_18);
x_21 = lean_int_emod(x_20, x_19);
lean_dec(x_20);
x_22 = lean_int_dec_eq(x_21, x_16);
lean_dec(x_21);
if (x_17 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_box(0);
lean_inc(x_3);
x_68 = l_Lean_Expr_const___override(x_3, x_67);
x_69 = lean_int_neg(x_2);
x_70 = l_Int_toNat(x_69);
lean_dec(x_69);
x_71 = l_Lean_instToExprInt_mkNat(x_70);
x_72 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__28;
x_73 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18;
x_74 = l_Lean_mkApp3(x_72, x_68, x_73, x_71);
x_23 = x_74;
goto block_66;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Int_toNat(x_2);
x_76 = l_Lean_instToExprInt_mkNat(x_75);
x_23 = x_76;
goto block_66;
}
block_66:
{
lean_object* x_24; 
lean_inc(x_23);
x_24 = l_Lean_mkIntDvd(x_23, x_13);
if (x_22 == 0)
{
lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_29 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__3;
x_30 = l_Lean_reflBoolTrue;
x_31 = l_Lean_mkApp4(x_29, x_26, x_23, x_28, x_30);
x_32 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Meta_mkEq(x_24, x_32, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_mkExpectedTypeHint(x_31, x_34, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_36);
if (x_46 == 0)
{
return x_36;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_36, 0);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_36);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_33);
if (x_50 == 0)
{
return x_33;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_33, 0);
x_52 = lean_ctor_get(x_33, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_33);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_25);
if (x_54 == 0)
{
return x_25;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_25, 0);
x_56 = lean_ctor_get(x_25, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_25);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = l_Int_Linear_Poly_div(x_19, x_18);
x_59 = lean_int_ediv(x_2, x_19);
lean_dec(x_2);
lean_inc(x_58);
x_60 = l_Int_Linear_Poly_toExpr(x_58);
x_61 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_1, x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_15);
x_62 = lean_box(0);
x_63 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1(x_11, x_58, x_16, x_59, x_19, x_24, x_4, x_1, x_3, x_23, x_62, x_5, x_6, x_7, x_8, x_14);
lean_dec(x_19);
lean_dec(x_59);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = lean_box(0);
if (lean_is_scalar(x_15)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_15;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_14);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2), 9, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_3, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
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
x_23 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_24 = lean_int_dec_eq(x_20, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_7);
x_25 = lean_box(0);
x_26 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__3(x_21, x_20, x_22, x_25, x_2, x_3, x_4, x_5, x_18);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
lean_ctor_set(x_7, 0, x_27);
return x_7;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_32 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1;
x_33 = lean_int_dec_eq(x_29, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__3(x_30, x_29, x_31, x_34, x_2, x_3, x_4, x_5, x_28);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_28);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_7);
if (x_38 == 0)
{
return x_7;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_7);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_of_norm_eq", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = l_Int_Linear_Expr_norm(x_12);
lean_inc(x_14);
x_15 = l_Int_Linear_Poly_toExpr(x_14);
x_16 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_12, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_17 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_13, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_12);
lean_inc(x_14);
x_21 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_14);
x_22 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__4;
x_23 = l_Lean_reflBoolTrue;
x_24 = l_Lean_mkApp4(x_22, x_18, x_20, x_21, x_23);
x_25 = l_Lean_instInhabitedExpr;
x_26 = lean_alloc_closure((void*)(l_Array_get_x21Internal___boxed), 4, 3);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, x_25);
lean_closure_set(x_26, 2, x_13);
x_27 = l_Int_Linear_Poly_denoteExpr(x_26, x_14, x_2, x_3, x_4, x_5, x_19);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_28);
x_30 = l_Lean_Meta_mkEq(x_1, x_28, x_2, x_3, x_4, x_5, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_mkExpectedTypeHint(x_24, x_31, x_2, x_3, x_4, x_5, x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_9, 1, x_35);
lean_ctor_set(x_9, 0, x_28);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
lean_ctor_set(x_9, 1, x_37);
lean_ctor_set(x_9, 0, x_28);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_28);
lean_free_object(x_9);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_28);
lean_dec(x_24);
lean_free_object(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
return x_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_30, 0);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_30);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_14);
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_17);
if (x_49 == 0)
{
return x_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_14);
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_box(0);
lean_ctor_set(x_7, 0, x_53);
return x_7;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_7, 1);
x_55 = lean_ctor_get(x_9, 0);
x_56 = lean_ctor_get(x_9, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_9);
x_57 = l_Int_Linear_Expr_norm(x_55);
lean_inc(x_57);
x_58 = l_Int_Linear_Poly_toExpr(x_57);
x_59 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_55, x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_free_object(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_56);
x_60 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_56, x_2, x_3, x_4, x_5, x_54);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_55);
lean_inc(x_57);
x_64 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_57);
x_65 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__4;
x_66 = l_Lean_reflBoolTrue;
x_67 = l_Lean_mkApp4(x_65, x_61, x_63, x_64, x_66);
x_68 = l_Lean_instInhabitedExpr;
x_69 = lean_alloc_closure((void*)(l_Array_get_x21Internal___boxed), 4, 3);
lean_closure_set(x_69, 0, lean_box(0));
lean_closure_set(x_69, 1, x_68);
lean_closure_set(x_69, 2, x_56);
x_70 = l_Int_Linear_Poly_denoteExpr(x_69, x_57, x_2, x_3, x_4, x_5, x_62);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_71);
x_73 = l_Lean_Meta_mkEq(x_1, x_71, x_2, x_3, x_4, x_5, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Meta_mkExpectedTypeHint(x_67, x_74, x_2, x_3, x_4, x_5, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_71);
lean_ctor_set(x_80, 1, x_77);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_71);
x_83 = lean_ctor_get(x_76, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_85 = x_76;
} else {
 lean_dec_ref(x_76);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_71);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = lean_ctor_get(x_73, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_89 = x_73;
} else {
 lean_dec_ref(x_73);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = lean_ctor_get(x_60, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_60, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_93 = x_60;
} else {
 lean_dec_ref(x_60);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_box(0);
lean_ctor_set(x_7, 0, x_95);
return x_7;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_96 = lean_ctor_get(x_7, 0);
x_97 = lean_ctor_get(x_7, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_7);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
 x_100 = lean_box(0);
}
x_101 = l_Int_Linear_Expr_norm(x_98);
lean_inc(x_101);
x_102 = l_Int_Linear_Poly_toExpr(x_101);
x_103 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_98, x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_99);
x_104 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_99, x_2, x_3, x_4, x_5, x_97);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_98);
lean_inc(x_101);
x_108 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_101);
x_109 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__4;
x_110 = l_Lean_reflBoolTrue;
x_111 = l_Lean_mkApp4(x_109, x_105, x_107, x_108, x_110);
x_112 = l_Lean_instInhabitedExpr;
x_113 = lean_alloc_closure((void*)(l_Array_get_x21Internal___boxed), 4, 3);
lean_closure_set(x_113, 0, lean_box(0));
lean_closure_set(x_113, 1, x_112);
lean_closure_set(x_113, 2, x_99);
x_114 = l_Int_Linear_Poly_denoteExpr(x_113, x_101, x_2, x_3, x_4, x_5, x_106);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_115);
x_117 = l_Lean_Meta_mkEq(x_1, x_115, x_2, x_3, x_4, x_5, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = l_Lean_Meta_mkExpectedTypeHint(x_111, x_118, x_2, x_3, x_4, x_5, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_100;
}
lean_ctor_set(x_124, 0, x_115);
lean_ctor_set(x_124, 1, x_121);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
if (lean_is_scalar(x_123)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_123;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_122);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_115);
lean_dec(x_100);
x_127 = lean_ctor_get(x_120, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_120, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_129 = x_120;
} else {
 lean_dec_ref(x_120);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_115);
lean_dec(x_111);
lean_dec(x_100);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_131 = lean_ctor_get(x_117, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_117, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_133 = x_117;
} else {
 lean_dec_ref(x_117);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = lean_ctor_get(x_104, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_104, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_137 = x_104;
} else {
 lean_dec_ref(x_104);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_97);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_7);
if (x_141 == 0)
{
return x_7;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_7, 0);
x_143 = lean_ctor_get(x_7, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_7);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
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
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__4);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__5);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__6);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__7 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__7);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__8 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__8);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__9);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__10 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__10);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__11 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__11);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__12 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__12);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__13 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__13);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__14 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__14);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__15);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__16 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__16);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__17 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__17);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__18);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__19);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__20 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__20();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__20);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__21 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__21();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__21);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__22);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__23 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__23();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__23);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__24 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__24();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__24);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__25);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__26 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__26();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__26);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__27 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__27();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__27);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__28 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__28();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__28);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__29 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__29();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__29);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__30 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__30();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__30);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__31 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__31();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__31);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__32 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__32();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__32);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__33 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__33();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__33);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__34 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__34();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__34);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__35 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__35();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__35);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__36 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__36();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__36);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__37 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__37();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__37);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__38 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__38();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__38);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__39 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__39();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__39);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__40 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__40();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__40);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__41 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__41();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__41);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__42 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__42();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__42);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__43 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__43();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__43);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__44 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__44();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__44);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__45 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__45();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__45);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__46 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__46();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lambda__1___closed__46);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__4);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__5);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__6);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__7 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__7);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__8 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__8);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__9 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__9);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__10 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__10);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__11 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__11);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__12 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__12);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__13 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__13);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__14 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__14);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__15 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lambda__2___closed__15);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__4);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__5);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__1___closed__6);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__2___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__5___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__7___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lambda__9___closed__2);
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
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__4);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__5);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__1___closed__6);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lambda__2___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
