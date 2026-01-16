// Lean compiler output
// Module: Init.Grind.Ring.CommSolver
// Imports: public import Init.Data.Hashable public import Init.Data.Ord.Basic public import Init.Grind.Ring.Field public import Init.Grind.Ordered.Ring public import Init.GrindInstances.Ring.Int import all Init.Data.Ord.Basic import Init.LawfulBEqTactics
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
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__16;
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11;
uint8_t l_Int_decidableDvd(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instHashablePoly___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc(lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_varLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPoly_beq(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__20;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1;
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedPower_default;
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_natCast_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineC(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_mul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPoly;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedPoly_default;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isSorted___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_normEq0(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPoly___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__gcd__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__26;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7;
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow__nc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ofVar(lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__27;
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexWF(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower___closed__0;
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__18;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_neg_elim___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__14;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__28;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_hugeFuel;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower;
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePower_hash(lean_object*);
static lean_object* l_Lean_Grind_CommRing_instBEqExpr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlex(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqMon_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedPoly;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul__nc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instHashableMon___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_concat(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexWF___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_pow_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqMon_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_powerRevlex(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableMon_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_sub_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__24;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprMon_repr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__10;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqExpr;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_powerRevlex___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__17;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_revlex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprMon_repr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3;
static lean_object* l_Lean_Grind_CommRing_instBEqPoly___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableExpr;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree___boxed(lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly__nc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprExpr;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_natCast_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__19;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPower;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_revlex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_mul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePower;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedMon_default;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__gcd__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16;
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__8;
static lean_object* l_Lean_Grind_CommRing_instReprMon_repr___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__12;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePoly;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprMon___closed__0;
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexFuel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instHashableExpr___closed__0;
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8;
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPower_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly;
static lean_object* l_Lean_Grind_CommRing_instReprMon_repr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprMon_repr___closed__0;
static lean_object* l_Lean_Grind_CommRing_Expr_toPoly___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__15;
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Var_revlex(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashableExpr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlex___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePoly_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_intCast_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_varLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedMon;
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC_go(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6;
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__21;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__25;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedExpr_default;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__6;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_sub_elim___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPower_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePower_hash___boxed(lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqExpr_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPoly_beq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__13;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashableMon_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePoly_hash(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__11;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableExpr_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableMon;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__22;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_isSorted(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqMon;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instHashablePower___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4;
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_pow_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_grevlex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_intCast_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instBEqMon___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexFuel___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Grind_CommRing_Poly_pow___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__9;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC_go(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqExpr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__23;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprExpr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_instReprPower_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_neg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_instBEqPower___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedPower;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_toIntModule___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_revlex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
default: 
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(8u);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_CommRing_Expr_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 5:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
case 6:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_2(x_2, x_8, x_9);
return x_10;
}
case 7:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_2(x_2, x_11, x_12);
return x_13;
}
case 8:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_apply_2(x_2, x_14, x_15);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = lean_apply_1(x_2, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Expr_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_num_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_num_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_natCast_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_natCast_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_intCast_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_intCast_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_var_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_var_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_neg_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_neg_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_add_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_add_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_sub_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_sub_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_mul_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_mul_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_pow_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_pow_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedExpr_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instInhabitedExpr_default;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqExpr_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_int_dec_eq(x_10, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_nat_dec_eq(x_14, x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_int_dec_eq(x_18, x_19);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_nat_dec_eq(x_22, x_23);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_2, 0);
x_1 = x_26;
x_2 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_1, 1);
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
x_3 = x_30;
x_4 = x_31;
x_5 = x_32;
x_6 = x_33;
goto block_9;
}
else
{
uint8_t x_34; 
x_34 = 0;
return x_34;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
x_3 = x_35;
x_4 = x_36;
x_5 = x_37;
x_6 = x_38;
goto block_9;
}
else
{
uint8_t x_39; 
x_39 = 0;
return x_39;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get(x_1, 1);
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_3 = x_40;
x_4 = x_41;
x_5 = x_42;
x_6 = x_43;
goto block_9;
}
else
{
uint8_t x_44; 
x_44 = 0;
return x_44;
}
}
default: 
{
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_1, 1);
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_ctor_get(x_2, 1);
x_49 = l_Lean_Grind_CommRing_instBEqExpr_beq(x_45, x_47);
if (x_49 == 0)
{
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_eq(x_46, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = 0;
return x_51;
}
}
}
block_9:
{
uint8_t x_7; 
x_7 = l_Lean_Grind_CommRing_instBEqExpr_beq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqExpr_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_instBEqExpr_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instBEqExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_instBEqExpr_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instBEqExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instBEqExpr___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashableExpr_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint64_t x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_5 = lean_int_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; 
x_6 = lean_nat_abs(x_2);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_mul(x_7, x_6);
lean_dec(x_6);
x_9 = lean_uint64_of_nat(x_8);
lean_dec(x_8);
x_10 = lean_uint64_mix_hash(x_3, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; 
x_11 = lean_nat_abs(x_2);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_mul(x_14, x_13);
lean_dec(x_13);
x_16 = lean_nat_add(x_15, x_12);
lean_dec(x_15);
x_17 = lean_uint64_of_nat(x_16);
lean_dec(x_16);
x_18 = lean_uint64_mix_hash(x_3, x_17);
return x_18;
}
}
case 1:
{
lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = 1;
x_21 = lean_uint64_of_nat(x_19);
x_22 = lean_uint64_mix_hash(x_20, x_21);
return x_22;
}
case 2:
{
lean_object* x_23; uint64_t x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = 2;
x_25 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_26 = lean_int_dec_lt(x_23, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; 
x_27 = lean_nat_abs(x_23);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_nat_mul(x_28, x_27);
lean_dec(x_27);
x_30 = lean_uint64_of_nat(x_29);
lean_dec(x_29);
x_31 = lean_uint64_mix_hash(x_24, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; 
x_32 = lean_nat_abs(x_23);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_32, x_33);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_nat_mul(x_35, x_34);
lean_dec(x_34);
x_37 = lean_nat_add(x_36, x_33);
lean_dec(x_36);
x_38 = lean_uint64_of_nat(x_37);
lean_dec(x_37);
x_39 = lean_uint64_mix_hash(x_24, x_38);
return x_39;
}
}
case 3:
{
lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = 3;
x_42 = lean_uint64_of_nat(x_40);
x_43 = lean_uint64_mix_hash(x_41, x_42);
return x_43;
}
case 4:
{
lean_object* x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = 4;
x_46 = l_Lean_Grind_CommRing_instHashableExpr_hash(x_44);
x_47 = lean_uint64_mix_hash(x_45, x_46);
return x_47;
}
case 5:
{
lean_object* x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; 
x_48 = lean_ctor_get(x_1, 0);
x_49 = lean_ctor_get(x_1, 1);
x_50 = 5;
x_51 = l_Lean_Grind_CommRing_instHashableExpr_hash(x_48);
x_52 = lean_uint64_mix_hash(x_50, x_51);
x_53 = l_Lean_Grind_CommRing_instHashableExpr_hash(x_49);
x_54 = lean_uint64_mix_hash(x_52, x_53);
return x_54;
}
case 6:
{
lean_object* x_55; lean_object* x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; 
x_55 = lean_ctor_get(x_1, 0);
x_56 = lean_ctor_get(x_1, 1);
x_57 = 6;
x_58 = l_Lean_Grind_CommRing_instHashableExpr_hash(x_55);
x_59 = lean_uint64_mix_hash(x_57, x_58);
x_60 = l_Lean_Grind_CommRing_instHashableExpr_hash(x_56);
x_61 = lean_uint64_mix_hash(x_59, x_60);
return x_61;
}
case 7:
{
lean_object* x_62; lean_object* x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; 
x_62 = lean_ctor_get(x_1, 0);
x_63 = lean_ctor_get(x_1, 1);
x_64 = 7;
x_65 = l_Lean_Grind_CommRing_instHashableExpr_hash(x_62);
x_66 = lean_uint64_mix_hash(x_64, x_65);
x_67 = l_Lean_Grind_CommRing_instHashableExpr_hash(x_63);
x_68 = lean_uint64_mix_hash(x_66, x_67);
return x_68;
}
default: 
{
lean_object* x_69; lean_object* x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; 
x_69 = lean_ctor_get(x_1, 0);
x_70 = lean_ctor_get(x_1, 1);
x_71 = 8;
x_72 = l_Lean_Grind_CommRing_instHashableExpr_hash(x_69);
x_73 = lean_uint64_mix_hash(x_71, x_72);
x_74 = lean_uint64_of_nat(x_70);
x_75 = lean_uint64_mix_hash(x_73, x_74);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableExpr_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_CommRing_instHashableExpr_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instHashableExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_instHashableExpr_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instHashableExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instHashableExpr___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Grind.CommRing.Expr.num", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__1;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Grind.CommRing.Expr.natCast", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__6;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Grind.CommRing.Expr.intCast", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__9;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Grind.CommRing.Expr.var", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__12;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Grind.CommRing.Expr.neg", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__15;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Grind.CommRing.Expr.add", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__17;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__18;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Grind.CommRing.Expr.sub", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__20;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__21;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Grind.CommRing.Expr.mul", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__23;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__24;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Grind.CommRing.Expr.pow", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__26;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__27;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprExpr_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_34; uint8_t x_35; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_22 = x_1;
} else {
 lean_dec_ref(x_1);
 x_22 = lean_box(0);
}
x_34 = lean_unsigned_to_nat(1024u);
x_35 = lean_nat_dec_le(x_34, x_2);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
x_23 = x_36;
goto block_33;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_23 = x_37;
goto block_33;
}
block_33:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__2;
x_25 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_26 = lean_int_dec_lt(x_21, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Int_repr(x_21);
lean_dec(x_21);
if (lean_is_scalar(x_22)) {
 x_28 = lean_alloc_ctor(3, 1, 0);
} else {
 x_28 = x_22;
 lean_ctor_set_tag(x_28, 3);
}
lean_ctor_set(x_28, 0, x_27);
x_12 = x_24;
x_13 = x_23;
x_14 = x_28;
goto block_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_unsigned_to_nat(1024u);
x_30 = l_Int_repr(x_21);
lean_dec(x_21);
if (lean_is_scalar(x_22)) {
 x_31 = lean_alloc_ctor(3, 1, 0);
} else {
 x_31 = x_22;
 lean_ctor_set_tag(x_31, 3);
}
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Repr_addAppParen(x_31, x_29);
x_12 = x_24;
x_13 = x_23;
x_14 = x_32;
goto block_20;
}
}
}
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_50; uint8_t x_51; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_39 = x_1;
} else {
 lean_dec_ref(x_1);
 x_39 = lean_box(0);
}
x_50 = lean_unsigned_to_nat(1024u);
x_51 = lean_nat_dec_le(x_50, x_2);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
x_40 = x_52;
goto block_49;
}
else
{
lean_object* x_53; 
x_53 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_40 = x_53;
goto block_49;
}
block_49:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_41 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__7;
x_42 = l_Nat_reprFast(x_38);
if (lean_is_scalar(x_39)) {
 x_43 = lean_alloc_ctor(3, 1, 0);
} else {
 x_43 = x_39;
 lean_ctor_set_tag(x_43, 3);
}
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
x_46 = 0;
x_47 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = l_Repr_addAppParen(x_47, x_2);
return x_48;
}
}
case 2:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_67; uint8_t x_68; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_55 = x_1;
} else {
 lean_dec_ref(x_1);
 x_55 = lean_box(0);
}
x_67 = lean_unsigned_to_nat(1024u);
x_68 = lean_nat_dec_le(x_67, x_2);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
x_56 = x_69;
goto block_66;
}
else
{
lean_object* x_70; 
x_70 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_56 = x_70;
goto block_66;
}
block_66:
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__10;
x_58 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_59 = lean_int_dec_lt(x_54, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Int_repr(x_54);
lean_dec(x_54);
if (lean_is_scalar(x_55)) {
 x_61 = lean_alloc_ctor(3, 1, 0);
} else {
 x_61 = x_55;
 lean_ctor_set_tag(x_61, 3);
}
lean_ctor_set(x_61, 0, x_60);
x_3 = x_57;
x_4 = x_56;
x_5 = x_61;
goto block_11;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_unsigned_to_nat(1024u);
x_63 = l_Int_repr(x_54);
lean_dec(x_54);
if (lean_is_scalar(x_55)) {
 x_64 = lean_alloc_ctor(3, 1, 0);
} else {
 x_64 = x_55;
 lean_ctor_set_tag(x_64, 3);
}
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Repr_addAppParen(x_64, x_62);
x_3 = x_57;
x_4 = x_56;
x_5 = x_65;
goto block_11;
}
}
}
case 3:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_83; uint8_t x_84; 
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_72 = x_1;
} else {
 lean_dec_ref(x_1);
 x_72 = lean_box(0);
}
x_83 = lean_unsigned_to_nat(1024u);
x_84 = lean_nat_dec_le(x_83, x_2);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
x_73 = x_85;
goto block_82;
}
else
{
lean_object* x_86; 
x_86 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_73 = x_86;
goto block_82;
}
block_82:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
x_74 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__13;
x_75 = l_Nat_reprFast(x_71);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(3, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_77);
x_79 = 0;
x_80 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
x_81 = l_Repr_addAppParen(x_80, x_2);
return x_81;
}
}
case 4:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_98; 
x_87 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_87);
lean_dec_ref(x_1);
x_88 = lean_unsigned_to_nat(1024u);
x_98 = lean_nat_dec_le(x_88, x_2);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
x_89 = x_99;
goto block_97;
}
else
{
lean_object* x_100; 
x_100 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_89 = x_100;
goto block_97;
}
block_97:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_90 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__16;
x_91 = l_Lean_Grind_CommRing_instReprExpr_repr(x_87, x_88);
x_92 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_92);
x_94 = 0;
x_95 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
x_96 = l_Repr_addAppParen(x_95, x_2);
return x_96;
}
}
case 5:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_118; 
x_101 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_102);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_103 = x_1;
} else {
 lean_dec_ref(x_1);
 x_103 = lean_box(0);
}
x_104 = lean_unsigned_to_nat(1024u);
x_118 = lean_nat_dec_le(x_104, x_2);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
x_105 = x_119;
goto block_117;
}
else
{
lean_object* x_120; 
x_120 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_105 = x_120;
goto block_117;
}
block_117:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_106 = lean_box(1);
x_107 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__19;
x_108 = l_Lean_Grind_CommRing_instReprExpr_repr(x_101, x_104);
if (lean_is_scalar(x_103)) {
 x_109 = lean_alloc_ctor(5, 2, 0);
} else {
 x_109 = x_103;
}
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_106);
x_111 = l_Lean_Grind_CommRing_instReprExpr_repr(x_102, x_104);
x_112 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_113, 0, x_105);
lean_ctor_set(x_113, 1, x_112);
x_114 = 0;
x_115 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_114);
x_116 = l_Repr_addAppParen(x_115, x_2);
return x_116;
}
}
case 6:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_138; 
x_121 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_122);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_123 = x_1;
} else {
 lean_dec_ref(x_1);
 x_123 = lean_box(0);
}
x_124 = lean_unsigned_to_nat(1024u);
x_138 = lean_nat_dec_le(x_124, x_2);
if (x_138 == 0)
{
lean_object* x_139; 
x_139 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
x_125 = x_139;
goto block_137;
}
else
{
lean_object* x_140; 
x_140 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_125 = x_140;
goto block_137;
}
block_137:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; 
x_126 = lean_box(1);
x_127 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__22;
x_128 = l_Lean_Grind_CommRing_instReprExpr_repr(x_121, x_124);
if (lean_is_scalar(x_123)) {
 x_129 = lean_alloc_ctor(5, 2, 0);
} else {
 x_129 = x_123;
 lean_ctor_set_tag(x_129, 5);
}
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_126);
x_131 = l_Lean_Grind_CommRing_instReprExpr_repr(x_122, x_124);
x_132 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_133, 0, x_125);
lean_ctor_set(x_133, 1, x_132);
x_134 = 0;
x_135 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*1, x_134);
x_136 = l_Repr_addAppParen(x_135, x_2);
return x_136;
}
}
case 7:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_158; 
x_141 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_142);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_143 = x_1;
} else {
 lean_dec_ref(x_1);
 x_143 = lean_box(0);
}
x_144 = lean_unsigned_to_nat(1024u);
x_158 = lean_nat_dec_le(x_144, x_2);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
x_145 = x_159;
goto block_157;
}
else
{
lean_object* x_160; 
x_160 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_145 = x_160;
goto block_157;
}
block_157:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_146 = lean_box(1);
x_147 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__25;
x_148 = l_Lean_Grind_CommRing_instReprExpr_repr(x_141, x_144);
if (lean_is_scalar(x_143)) {
 x_149 = lean_alloc_ctor(5, 2, 0);
} else {
 x_149 = x_143;
 lean_ctor_set_tag(x_149, 5);
}
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_146);
x_151 = l_Lean_Grind_CommRing_instReprExpr_repr(x_142, x_144);
x_152 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_153, 0, x_145);
lean_ctor_set(x_153, 1, x_152);
x_154 = 0;
x_155 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_154);
x_156 = l_Repr_addAppParen(x_155, x_2);
return x_156;
}
}
default: 
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_179; 
x_161 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_1, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_163 = x_1;
} else {
 lean_dec_ref(x_1);
 x_163 = lean_box(0);
}
x_164 = lean_unsigned_to_nat(1024u);
x_179 = lean_nat_dec_le(x_164, x_2);
if (x_179 == 0)
{
lean_object* x_180; 
x_180 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
x_165 = x_180;
goto block_178;
}
else
{
lean_object* x_181; 
x_181 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_165 = x_181;
goto block_178;
}
block_178:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; 
x_166 = lean_box(1);
x_167 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__28;
x_168 = l_Lean_Grind_CommRing_instReprExpr_repr(x_161, x_164);
if (lean_is_scalar(x_163)) {
 x_169 = lean_alloc_ctor(5, 2, 0);
} else {
 x_169 = x_163;
 lean_ctor_set_tag(x_169, 5);
}
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_166);
x_171 = l_Nat_reprFast(x_162);
x_172 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_174, 0, x_165);
lean_ctor_set(x_174, 1, x_173);
x_175 = 0;
x_176 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_175);
x_177 = l_Repr_addAppParen(x_176, x_2);
return x_177;
}
}
}
block_11:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l_Repr_addAppParen(x_9, x_2);
return x_10;
}
block_20:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = 0;
x_18 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = l_Repr_addAppParen(x_18, x_2);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_instReprExpr_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_instReprExpr_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instReprExpr___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RArray_getImpl___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Var_denote___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RArray_getImpl___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Var_denote(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPower_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_nat_dec_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPower_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_instBEqPower_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instBEqPower___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_instBEqPower_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instBEqPower() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instBEqPower___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_apply_4(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = lean_apply_4(x_4, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_instReprPower_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5;
x_2 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("k", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5;
x_6 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6;
x_7 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7;
x_8 = l_Nat_reprFast(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_tag(x_1, 4);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_7);
x_10 = 0;
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
x_20 = l_Nat_reprFast(x_4);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_10);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14;
x_26 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15;
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
x_28 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16;
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_10);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_34 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5;
x_35 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6;
x_36 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7;
x_37 = l_Nat_reprFast(x_32);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = 0;
x_41 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9;
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_box(1);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11;
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_34);
x_50 = l_Nat_reprFast(x_33);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_52, 0, x_36);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_40);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14;
x_56 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15;
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_58 = l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16;
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_40);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_instReprPower_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_instReprPower_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_instReprPower_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instReprPower___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPower_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPower() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instInhabitedPower_default;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePower_hash(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = 0;
x_5 = lean_uint64_of_nat(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
x_7 = lean_uint64_of_nat(x_3);
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePower_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_CommRing_instHashablePower_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instHashablePower___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_instHashablePower_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instHashablePower() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instHashablePower___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_varLt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Nat_blt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_varLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_Power_varLt(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_4);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_RArray_getImpl___redArg(x_2, x_6);
lean_dec(x_6);
x_13 = lean_apply_2(x_5, x_12, x_7);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
x_14 = l_Lean_RArray_getImpl___redArg(x_2, x_6);
lean_dec(x_6);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Power_denote___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 5);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_eq(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_RArray_getImpl___redArg(x_3, x_7);
lean_dec(x_7);
x_14 = lean_apply_2(x_6, x_13, x_8);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
x_15 = l_Lean_RArray_getImpl___redArg(x_3, x_7);
lean_dec(x_7);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_apply_1(x_5, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Power_denote(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_CommRing_Mon_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Mon_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqMon_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_Grind_CommRing_instBEqPower_beq(x_5, x_7);
if (x_9 == 0)
{
return x_9;
}
else
{
x_1 = x_6;
x_2 = x_8;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqMon_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_instBEqMon_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instBEqMon___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_instBEqMon_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instBEqMon() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instBEqMon___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_apply_4(x_5, x_1, x_2, lean_box(0), lean_box(0));
return x_8;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_apply_4(x_4, x_9, x_10, x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = lean_apply_4(x_5, x_1, x_2, lean_box(0), lean_box(0));
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_5);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_4, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_apply_4(x_6, x_2, x_3, lean_box(0), lean_box(0));
return x_9;
}
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec_ref(x_3);
x_14 = lean_apply_4(x_5, x_10, x_11, x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_apply_4(x_6, x_2, x_3, lean_box(0), lean_box(0));
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprMon_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Grind.CommRing.Mon.unit", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprMon_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprMon_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprMon_repr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Grind.CommRing.Mon.mult", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprMon_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprMon_repr___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprMon_repr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Grind_CommRing_instReprMon_repr___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(1024u);
x_11 = lean_nat_dec_le(x_10, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
x_3 = x_12;
goto block_9;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_3 = x_13;
goto block_9;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_31; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_16 = x_1;
} else {
 lean_dec_ref(x_1);
 x_16 = lean_box(0);
}
x_17 = lean_unsigned_to_nat(1024u);
x_31 = lean_nat_dec_le(x_17, x_2);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
x_18 = x_32;
goto block_30;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_18 = x_33;
goto block_30;
}
block_30:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_box(1);
x_20 = l_Lean_Grind_CommRing_instReprMon_repr___closed__4;
x_21 = l_Lean_Grind_CommRing_instReprPower_repr___redArg(x_14);
if (lean_is_scalar(x_16)) {
 x_22 = lean_alloc_ctor(5, 2, 0);
} else {
 x_22 = x_16;
 lean_ctor_set_tag(x_22, 5);
}
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
x_24 = l_Lean_Grind_CommRing_instReprMon_repr(x_15, x_17);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
x_27 = 0;
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = l_Repr_addAppParen(x_28, x_2);
return x_29;
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Grind_CommRing_instReprMon_repr___closed__1;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_instReprMon_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprMon___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_instReprMon_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprMon() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instReprMon___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedMon_default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedMon() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashableMon_hash(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = 1;
x_6 = l_Lean_Grind_CommRing_instHashablePower_hash(x_3);
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = l_Lean_Grind_CommRing_instHashableMon_hash(x_4);
x_9 = lean_uint64_mix_hash(x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableMon_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_CommRing_instHashableMon_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instHashableMon___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_instHashableMon_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instHashableMon() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instHashableMon___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 5);
x_10 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec_ref(x_3);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec_ref(x_10);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_dec_eq(x_17, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_RArray_getImpl___redArg(x_2, x_16);
lean_dec(x_16);
lean_inc(x_9);
x_23 = lean_apply_2(x_9, x_22, x_17);
x_12 = x_23;
goto block_15;
}
else
{
lean_object* x_24; 
lean_dec(x_17);
x_24 = l_Lean_RArray_getImpl___redArg(x_2, x_16);
lean_dec(x_16);
x_12 = x_24;
goto block_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
lean_dec(x_16);
x_25 = lean_unsigned_to_nat(1u);
lean_inc(x_8);
x_26 = lean_apply_1(x_8, x_25);
x_12 = x_26;
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Grind_CommRing_Mon_denote___redArg(x_1, x_2, x_11);
x_14 = lean_apply_2(x_7, x_12, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Mon_denote___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Mon_denote___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Mon_denote(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec_ref(x_8);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_dec_eq(x_15, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_RArray_getImpl___redArg(x_2, x_14);
lean_dec(x_14);
lean_inc(x_7);
x_21 = lean_apply_2(x_7, x_20, x_15);
x_10 = x_21;
goto block_13;
}
else
{
lean_object* x_22; 
lean_dec(x_15);
x_22 = l_Lean_RArray_getImpl___redArg(x_2, x_14);
lean_dec(x_14);
x_10 = x_22;
goto block_13;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_14);
x_23 = lean_unsigned_to_nat(1u);
lean_inc(x_6);
x_24 = lean_apply_1(x_6, x_23);
x_10 = x_24;
goto block_13;
}
block_13:
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = lean_apply_2(x_5, x_4, x_10);
x_3 = x_9;
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Mon_denote_x27_go(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 5);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec_ref(x_7);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_dec_eq(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_RArray_getImpl___redArg(x_2, x_11);
lean_dec(x_11);
lean_inc(x_10);
x_18 = lean_apply_2(x_10, x_17, x_12);
x_19 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_1, x_2, x_8, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
x_20 = l_Lean_RArray_getImpl___redArg(x_2, x_11);
lean_dec(x_11);
x_21 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_1, x_2, x_8, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
x_22 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_23 = lean_apply_1(x_9, x_22);
x_24 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_1, x_2, x_8, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Mon_denote_x27___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_apply_1(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec_ref(x_8);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_dec_eq(x_13, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lean_RArray_getImpl___redArg(x_3, x_12);
lean_dec(x_12);
lean_inc(x_11);
x_19 = lean_apply_2(x_11, x_18, x_13);
x_20 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_2, x_3, x_9, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
x_21 = l_Lean_RArray_getImpl___redArg(x_3, x_12);
lean_dec(x_12);
x_22 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_2, x_3, x_9, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_12);
x_23 = lean_unsigned_to_nat(1u);
lean_inc(x_10);
x_24 = lean_apply_1(x_10, x_23);
x_25 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_2, x_3, x_9, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Mon_denote_x27(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ofVar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Grind_CommRing_Mon_concat(x_4, x_2);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = l_Lean_Grind_CommRing_Mon_concat(x_7, x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Mon_concat(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_Grind_CommRing_Power_varLt(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_5);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
x_10 = l_Lean_Grind_CommRing_Power_varLt(x_4, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
lean_ctor_set(x_4, 1, x_16);
lean_ctor_set(x_4, 0, x_11);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_nat_add(x_12, x_17);
lean_dec(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_2, 0, x_19);
return x_2;
}
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Grind_CommRing_Mon_mulPow(x_1, x_5);
lean_ctor_set(x_2, 1, x_20);
return x_2;
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = l_Lean_Grind_CommRing_Power_varLt(x_4, x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_25 = x_4;
} else {
 lean_dec_ref(x_4);
 x_25 = lean_box(0);
}
x_26 = lean_nat_add(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Grind_CommRing_Mon_mulPow(x_1, x_5);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec_ref(x_4);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow__nc(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_nat_dec_eq(x_7, x_9);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_4);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
else
{
uint8_t x_13; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec_ref(x_1);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_2, 0);
lean_dec(x_15);
x_16 = lean_nat_add(x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_ctor_set(x_4, 1, x_16);
lean_ctor_set(x_4, 0, x_7);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_nat_add(x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_ctor_set(x_4, 1, x_17);
lean_ctor_set(x_4, 0, x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = lean_nat_dec_eq(x_20, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_2);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_26 = x_2;
} else {
 lean_dec_ref(x_2);
 x_26 = lean_box(0);
}
x_27 = lean_nat_add(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Grind_CommRing_Mon_length(x_3);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_CommRing_Mon_length(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_hugeFuel() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1000000u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Mon_concat(x_2, x_3);
lean_dec(x_3);
return x_6;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_1, x_11);
x_13 = l_Lean_Grind_CommRing_Power_varLt(x_9, x_7);
if (x_13 == 0)
{
uint8_t x_14; 
lean_inc(x_8);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_3, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_dec(x_16);
x_17 = l_Lean_Grind_CommRing_Power_varLt(x_7, x_9);
if (x_17 == 0)
{
uint8_t x_18; 
lean_free_object(x_3);
lean_inc(x_10);
lean_inc_ref(x_9);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_2, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_dec_ref(x_9);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 0);
lean_dec(x_25);
x_26 = lean_nat_add(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
lean_ctor_set(x_7, 1, x_26);
lean_ctor_set(x_7, 0, x_21);
x_27 = l_Lean_Grind_CommRing_Mon_mul_go(x_12, x_10, x_8);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_nat_add(x_22, x_28);
lean_dec(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Grind_CommRing_Mon_mul_go(x_12, x_10, x_8);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_2);
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_dec_ref(x_9);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_35 = x_7;
} else {
 lean_dec_ref(x_7);
 x_35 = lean_box(0);
}
x_36 = lean_nat_add(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Grind_CommRing_Mon_mul_go(x_12, x_10, x_8);
lean_dec(x_12);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Grind_CommRing_Mon_mul_go(x_12, x_2, x_8);
lean_dec(x_12);
lean_ctor_set(x_3, 1, x_40);
return x_3;
}
}
else
{
uint8_t x_41; 
lean_dec(x_3);
x_41 = l_Lean_Grind_CommRing_Power_varLt(x_7, x_9);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_inc(x_10);
lean_inc_ref(x_9);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_42 = x_2;
} else {
 lean_dec_ref(x_2);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_9, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_dec_ref(x_9);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_46 = x_7;
} else {
 lean_dec_ref(x_7);
 x_46 = lean_box(0);
}
x_47 = lean_nat_add(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Grind_CommRing_Mon_mul_go(x_12, x_10, x_8);
lean_dec(x_12);
if (lean_is_scalar(x_42)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_42;
}
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = l_Lean_Grind_CommRing_Mon_mul_go(x_12, x_2, x_8);
lean_dec(x_12);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_7);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_dec_ref(x_7);
x_53 = !lean_is_exclusive(x_2);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_2, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_2, 0);
lean_dec(x_55);
x_56 = l_Lean_Grind_CommRing_Mon_mul_go(x_12, x_10, x_3);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_56);
return x_2;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_2);
x_57 = l_Lean_Grind_CommRing_Mon_mul_go(x_12, x_10, x_3);
lean_dec(x_12);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_9);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Mon_mul_go(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1000000u);
x_4 = l_Lean_Grind_CommRing_Mon_mul_go(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_4(x_5, x_10, x_11, x_8, x_9);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_4, x_2);
return x_7;
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_apply_2(x_5, x_3, lean_box(0));
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_apply_4(x_6, x_11, x_12, x_9, x_10);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul__nc(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_Grind_CommRing_Mon_mulPow__nc(x_4, x_2);
return x_5;
}
else
{
uint8_t x_6; 
lean_inc(x_3);
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = l_Lean_Grind_CommRing_Mon_mul__nc(x_3, x_2);
lean_ctor_set(x_1, 1, x_8);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Grind_CommRing_Mon_mul__nc(x_3, x_2);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_Grind_CommRing_Mon_degree(x_4);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_CommRing_Mon_degree(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Var_revlex(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Nat_blt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Nat_blt(x_2, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_revlex___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_Var_revlex(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_powerRevlex(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Nat_blt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Nat_blt(x_2, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_powerRevlex___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_powerRevlex(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_revlex(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Grind_CommRing_Var_revlex(x_3, x_5);
if (x_7 == 1)
{
uint8_t x_8; 
x_8 = l_Lean_Grind_CommRing_powerRevlex(x_4, x_6);
return x_8;
}
else
{
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_revlex___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_Power_revlex(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexWF(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 2;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
x_14 = lean_nat_dec_eq(x_10, x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Nat_blt(x_10, x_12);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Grind_CommRing_Mon_revlexWF(x_1, x_9);
if (x_16 == 1)
{
uint8_t x_17; 
x_17 = 2;
return x_17;
}
else
{
return x_16;
}
}
else
{
uint8_t x_18; 
x_18 = l_Lean_Grind_CommRing_Mon_revlexWF(x_8, x_2);
if (x_18 == 1)
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
else
{
return x_18;
}
}
}
else
{
uint8_t x_20; 
x_20 = l_Lean_Grind_CommRing_Mon_revlexWF(x_8, x_9);
if (x_20 == 1)
{
uint8_t x_21; 
x_21 = l_Lean_Grind_CommRing_powerRevlex(x_11, x_13);
return x_21;
}
else
{
return x_20;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexWF___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_Mon_revlexWF(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_apply_2(x_4, x_9, x_10);
return x_11;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = lean_apply_2(x_5, x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec_ref(x_2);
x_19 = lean_apply_4(x_6, x_15, x_16, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexFuel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
uint8_t x_6; 
x_6 = l_Lean_Grind_CommRing_Mon_revlexWF(x_2, x_3);
return x_6;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 2;
return x_8;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_1, x_18);
x_20 = lean_nat_dec_eq(x_14, x_16);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Nat_blt(x_14, x_16);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Grind_CommRing_Mon_revlexFuel(x_19, x_2, x_13);
lean_dec(x_19);
if (x_22 == 1)
{
uint8_t x_23; 
x_23 = 2;
return x_23;
}
else
{
return x_22;
}
}
else
{
uint8_t x_24; 
x_24 = l_Lean_Grind_CommRing_Mon_revlexFuel(x_19, x_12, x_3);
lean_dec(x_19);
if (x_24 == 1)
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
else
{
return x_24;
}
}
}
else
{
uint8_t x_26; 
x_26 = l_Lean_Grind_CommRing_Mon_revlexFuel(x_19, x_12, x_13);
lean_dec(x_19);
if (x_26 == 1)
{
uint8_t x_27; 
x_27 = l_Lean_Grind_CommRing_powerRevlex(x_15, x_17);
return x_27;
}
else
{
return x_26;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexFuel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Grind_CommRing_Mon_revlexFuel(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlex(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1000000u);
x_4 = l_Lean_Grind_CommRing_Mon_revlexFuel(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlex___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_Mon_revlex(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Grind_CommRing_Mon_degree(x_1);
x_4 = l_Lean_Grind_CommRing_Mon_degree(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_Lean_Grind_CommRing_Mon_revlex(x_1, x_2);
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_grevlex___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_Mon_grevlex(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_CommRing_Poly_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_3(x_2, x_5, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Poly_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPoly_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_int_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_int_dec_eq(x_7, x_10);
if (x_13 == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l_Lean_Grind_CommRing_instBEqMon_beq(x_8, x_11);
if (x_14 == 0)
{
return x_14;
}
else
{
x_1 = x_9;
x_2 = x_12;
goto _start;
}
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPoly_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_instBEqPoly_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instBEqPoly___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_instBEqPoly_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instBEqPoly() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instBEqPoly___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_4(x_5, x_1, x_2, lean_box(0), lean_box(0));
return x_9;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_2);
x_16 = lean_apply_6(x_4, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_4);
x_17 = lean_apply_4(x_5, x_1, x_2, lean_box(0), lean_box(0));
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_5);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_4(x_6, x_2, x_3, lean_box(0), lean_box(0));
return x_10;
}
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_2);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_16);
lean_dec_ref(x_3);
x_17 = lean_apply_6(x_5, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_5);
x_18 = lean_apply_4(x_6, x_2, x_3, lean_box(0), lean_box(0));
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPoly_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Grind.CommRing.Poly.num", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPoly_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprPoly_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPoly_repr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Grind_CommRing_instReprPoly_repr___closed__1;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPoly_repr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Grind.CommRing.Poly.add", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPoly_repr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprPoly_repr___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPoly_repr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Grind_CommRing_instReprPoly_repr___closed__4;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_13 = x_1;
} else {
 lean_dec_ref(x_1);
 x_13 = lean_box(0);
}
x_25 = lean_unsigned_to_nat(1024u);
x_26 = lean_nat_dec_le(x_25, x_2);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
x_14 = x_27;
goto block_24;
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_14 = x_28;
goto block_24;
}
block_24:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_Grind_CommRing_instReprPoly_repr___closed__2;
x_16 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_17 = lean_int_dec_lt(x_12, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Int_repr(x_12);
lean_dec(x_12);
if (lean_is_scalar(x_13)) {
 x_19 = lean_alloc_ctor(3, 1, 0);
} else {
 x_19 = x_13;
 lean_ctor_set_tag(x_19, 3);
}
lean_ctor_set(x_19, 0, x_18);
x_3 = x_15;
x_4 = x_14;
x_5 = x_19;
goto block_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_unsigned_to_nat(1024u);
x_21 = l_Int_repr(x_12);
lean_dec(x_12);
if (lean_is_scalar(x_13)) {
 x_22 = lean_alloc_ctor(3, 1, 0);
} else {
 x_22 = x_13;
 lean_ctor_set_tag(x_22, 3);
}
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Repr_addAppParen(x_22, x_20);
x_3 = x_15;
x_4 = x_14;
x_5 = x_23;
goto block_11;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_49; uint8_t x_60; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_31);
lean_dec_ref(x_1);
x_32 = lean_unsigned_to_nat(1024u);
x_60 = lean_nat_dec_le(x_32, x_2);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
x_49 = x_61;
goto block_59;
}
else
{
lean_object* x_62; 
x_62 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_49 = x_62;
goto block_59;
}
block_48:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_35);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_39 = l_Lean_Grind_CommRing_instReprMon_repr(x_30, x_32);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
x_42 = l_Lean_Grind_CommRing_instReprPoly_repr(x_31, x_32);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_43);
x_45 = 0;
x_46 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = l_Repr_addAppParen(x_46, x_2);
return x_47;
}
block_59:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_box(1);
x_51 = l_Lean_Grind_CommRing_instReprPoly_repr___closed__5;
x_52 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_53 = lean_int_dec_lt(x_29, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Int_repr(x_29);
lean_dec(x_29);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_33 = x_49;
x_34 = x_51;
x_35 = x_50;
x_36 = x_55;
goto block_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = l_Int_repr(x_29);
lean_dec(x_29);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Repr_addAppParen(x_57, x_32);
x_33 = x_49;
x_34 = x_51;
x_35 = x_50;
x_36 = x_58;
goto block_48;
}
}
}
block_11:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l_Repr_addAppParen(x_9, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_instReprPoly_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPoly___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_instReprPoly_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPoly() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instReprPoly___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instInhabitedPoly_default;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePoly_hash(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint64_t x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_5 = lean_int_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; 
x_6 = lean_nat_abs(x_2);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_mul(x_7, x_6);
lean_dec(x_6);
x_9 = lean_uint64_of_nat(x_8);
lean_dec(x_8);
x_10 = lean_uint64_mix_hash(x_3, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; 
x_11 = lean_nat_abs(x_2);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_mul(x_14, x_13);
lean_dec(x_13);
x_16 = lean_nat_add(x_15, x_12);
lean_dec(x_15);
x_17 = lean_uint64_of_nat(x_16);
lean_dec(x_16);
x_18 = lean_uint64_mix_hash(x_3, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; lean_object* x_30; uint8_t x_31; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = 1;
x_30 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_31 = lean_int_dec_lt(x_19, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; 
x_32 = lean_nat_abs(x_19);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_mul(x_33, x_32);
lean_dec(x_32);
x_35 = lean_uint64_of_nat(x_34);
lean_dec(x_34);
x_23 = x_35;
goto block_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; 
x_36 = lean_nat_abs(x_19);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_36, x_37);
lean_dec(x_36);
x_39 = lean_unsigned_to_nat(2u);
x_40 = lean_nat_mul(x_39, x_38);
lean_dec(x_38);
x_41 = lean_nat_add(x_40, x_37);
lean_dec(x_40);
x_42 = lean_uint64_of_nat(x_41);
lean_dec(x_41);
x_23 = x_42;
goto block_29;
}
block_29:
{
uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; 
x_24 = lean_uint64_mix_hash(x_22, x_23);
x_25 = l_Lean_Grind_CommRing_instHashableMon_hash(x_20);
x_26 = lean_uint64_mix_hash(x_24, x_25);
x_27 = l_Lean_Grind_CommRing_instHashablePoly_hash(x_21);
x_28 = lean_uint64_mix_hash(x_26, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePoly_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_CommRing_instHashablePoly_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instHashablePoly___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Grind_CommRing_instHashablePoly_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instHashablePoly() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_CommRing_instHashablePoly___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc_ref(x_1);
x_7 = l_Lean_Grind_Ring_toIntModule___redArg(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_inc(x_5);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_apply_1(x_5, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_3);
lean_inc_ref(x_4);
x_14 = l_Lean_Grind_CommRing_Mon_denote___redArg(x_4, x_2, x_12);
x_15 = lean_apply_2(x_10, x_11, x_14);
x_16 = l_Lean_Grind_CommRing_Poly_denote___redArg(x_1, x_2, x_13);
x_17 = lean_apply_2(x_6, x_15, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Poly_denote___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_denote___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_denote(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = l_Lean_Grind_Ring_toIntModule___redArg(x_1);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_10 = lean_int_dec_eq(x_3, x_9);
if (x_10 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
lean_dec_ref(x_5);
x_12 = lean_apply_1(x_11, x_8);
x_13 = lean_apply_2(x_7, x_3, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec_ref(x_4);
x_16 = lean_ctor_get(x_5, 3);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec_ref(x_14);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_19, x_8);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lean_RArray_getImpl___redArg(x_2, x_18);
lean_dec(x_18);
lean_inc(x_17);
x_24 = lean_apply_2(x_17, x_23, x_19);
x_25 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_5, x_2, x_15, x_24);
x_26 = lean_apply_2(x_7, x_3, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
x_27 = l_Lean_RArray_getImpl___redArg(x_2, x_18);
lean_dec(x_18);
x_28 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_5, x_2, x_15, x_27);
x_29 = lean_apply_2(x_7, x_3, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_19);
lean_dec(x_18);
lean_inc(x_16);
x_30 = lean_apply_1(x_16, x_8);
x_31 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_5, x_2, x_15, x_30);
x_32 = lean_apply_2(x_7, x_3, x_31);
return x_32;
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_5, 3);
lean_inc(x_33);
lean_dec_ref(x_5);
x_34 = lean_apply_1(x_33, x_8);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_dec_ref(x_4);
x_37 = lean_ctor_get(x_5, 3);
x_38 = lean_ctor_get(x_5, 5);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec_ref(x_35);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_eq(x_40, x_41);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = lean_nat_dec_eq(x_40, x_8);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = l_Lean_RArray_getImpl___redArg(x_2, x_39);
lean_dec(x_39);
lean_inc(x_38);
x_45 = lean_apply_2(x_38, x_44, x_40);
x_46 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_5, x_2, x_36, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_40);
x_47 = l_Lean_RArray_getImpl___redArg(x_2, x_39);
lean_dec(x_39);
x_48 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_5, x_2, x_36, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_40);
lean_dec(x_39);
lean_inc(x_37);
x_49 = lean_apply_1(x_37, x_8);
x_50 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_5, x_2, x_36, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_denoteTerm___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_6);
x_7 = l_Lean_Grind_Ring_toIntModule___redArg(x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_11 = lean_int_dec_eq(x_4, x_10);
if (x_11 == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 3);
lean_inc(x_12);
lean_dec_ref(x_6);
x_13 = lean_apply_1(x_12, x_9);
x_14 = lean_apply_2(x_8, x_4, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec_ref(x_5);
x_17 = lean_ctor_get(x_6, 3);
x_18 = lean_ctor_get(x_6, 5);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = lean_nat_dec_eq(x_20, x_9);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_RArray_getImpl___redArg(x_3, x_19);
lean_dec(x_19);
lean_inc(x_18);
x_25 = lean_apply_2(x_18, x_24, x_20);
x_26 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_6, x_3, x_16, x_25);
x_27 = lean_apply_2(x_8, x_4, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
x_28 = l_Lean_RArray_getImpl___redArg(x_3, x_19);
lean_dec(x_19);
x_29 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_6, x_3, x_16, x_28);
x_30 = lean_apply_2(x_8, x_4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
lean_dec(x_19);
lean_inc(x_17);
x_31 = lean_apply_1(x_17, x_9);
x_32 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_6, x_3, x_16, x_31);
x_33 = lean_apply_2(x_8, x_4, x_32);
return x_33;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_6, 3);
lean_inc(x_34);
lean_dec_ref(x_6);
x_35 = lean_apply_1(x_34, x_9);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_dec_ref(x_5);
x_38 = lean_ctor_get(x_6, 3);
x_39 = lean_ctor_get(x_6, 5);
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec_ref(x_36);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_eq(x_41, x_42);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = lean_nat_dec_eq(x_41, x_9);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = l_Lean_RArray_getImpl___redArg(x_3, x_40);
lean_dec(x_40);
lean_inc(x_39);
x_46 = lean_apply_2(x_39, x_45, x_41);
x_47 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_6, x_3, x_37, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_41);
x_48 = l_Lean_RArray_getImpl___redArg(x_3, x_40);
lean_dec(x_40);
x_49 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_6, x_3, x_37, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_41);
lean_dec(x_40);
lean_inc(x_38);
x_50 = lean_apply_1(x_38, x_9);
x_51 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_6, x_3, x_37, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_denoteTerm(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_10 = lean_int_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_1(x_6, x_8);
x_12 = lean_apply_2(x_7, x_4, x_11);
return x_12;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_4;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 3);
x_16 = lean_ctor_get(x_13, 5);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_19);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
x_24 = l_Lean_Grind_Ring_toIntModule___redArg(x_1);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_28 = lean_int_dec_eq(x_17, x_27);
if (x_28 == 0)
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_inc(x_15);
x_29 = lean_apply_1(x_15, x_26);
x_30 = lean_apply_2(x_25, x_17, x_29);
x_20 = x_30;
goto block_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec_ref(x_18);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec_ref(x_31);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_eq(x_34, x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = lean_nat_dec_eq(x_34, x_26);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = l_Lean_RArray_getImpl___redArg(x_2, x_33);
lean_dec(x_33);
lean_inc(x_16);
x_39 = lean_apply_2(x_16, x_38, x_34);
lean_inc_ref(x_13);
x_40 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_13, x_2, x_32, x_39);
x_41 = lean_apply_2(x_25, x_17, x_40);
x_20 = x_41;
goto block_23;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_34);
x_42 = l_Lean_RArray_getImpl___redArg(x_2, x_33);
lean_dec(x_33);
lean_inc_ref(x_13);
x_43 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_13, x_2, x_32, x_42);
x_44 = lean_apply_2(x_25, x_17, x_43);
x_20 = x_44;
goto block_23;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_34);
lean_dec(x_33);
lean_inc(x_15);
x_45 = lean_apply_1(x_15, x_26);
lean_inc_ref(x_13);
x_46 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_13, x_2, x_32, x_45);
x_47 = lean_apply_2(x_25, x_17, x_46);
x_20 = x_47;
goto block_23;
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_48; 
lean_inc(x_15);
x_48 = lean_apply_1(x_15, x_26);
x_20 = x_48;
goto block_23;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_18, 1);
lean_inc(x_50);
lean_dec_ref(x_18);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec_ref(x_49);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_nat_dec_eq(x_52, x_53);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = lean_nat_dec_eq(x_52, x_26);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = l_Lean_RArray_getImpl___redArg(x_2, x_51);
lean_dec(x_51);
lean_inc(x_16);
x_57 = lean_apply_2(x_16, x_56, x_52);
lean_inc_ref(x_13);
x_58 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_13, x_2, x_50, x_57);
x_20 = x_58;
goto block_23;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_52);
x_59 = l_Lean_RArray_getImpl___redArg(x_2, x_51);
lean_dec(x_51);
lean_inc_ref(x_13);
x_60 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_13, x_2, x_50, x_59);
x_20 = x_60;
goto block_23;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_52);
lean_dec(x_51);
lean_inc(x_15);
x_61 = lean_apply_1(x_15, x_26);
lean_inc_ref(x_13);
x_62 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_13, x_2, x_50, x_61);
x_20 = x_62;
goto block_23;
}
}
}
block_23:
{
lean_object* x_21; 
lean_inc(x_14);
x_21 = lean_apply_2(x_14, x_4, x_20);
x_3 = x_19;
x_4 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Poly_denote_x27_go(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_10);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
x_11 = l_Lean_Grind_Ring_toIntModule___redArg(x_1);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_15 = lean_int_dec_eq(x_8, x_14);
if (x_15 == 0)
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_7, 3);
lean_inc(x_16);
x_17 = lean_apply_1(x_16, x_13);
x_18 = lean_apply_2(x_12, x_8, x_17);
x_19 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_1, x_2, x_10, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec_ref(x_9);
x_22 = lean_ctor_get(x_7, 3);
x_23 = lean_ctor_get(x_7, 5);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec_ref(x_20);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_25, x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = lean_nat_dec_eq(x_25, x_13);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = l_Lean_RArray_getImpl___redArg(x_2, x_24);
lean_dec(x_24);
lean_inc(x_23);
x_30 = lean_apply_2(x_23, x_29, x_25);
lean_inc_ref(x_7);
x_31 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_7, x_2, x_21, x_30);
x_32 = lean_apply_2(x_12, x_8, x_31);
x_33 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_1, x_2, x_10, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_25);
x_34 = l_Lean_RArray_getImpl___redArg(x_2, x_24);
lean_dec(x_24);
lean_inc_ref(x_7);
x_35 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_7, x_2, x_21, x_34);
x_36 = lean_apply_2(x_12, x_8, x_35);
x_37 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_1, x_2, x_10, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_25);
lean_dec(x_24);
lean_inc(x_22);
x_38 = lean_apply_1(x_22, x_13);
lean_inc_ref(x_7);
x_39 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_7, x_2, x_21, x_38);
x_40 = lean_apply_2(x_12, x_8, x_39);
x_41 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_1, x_2, x_10, x_40);
return x_41;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_7, 3);
lean_inc(x_42);
x_43 = lean_apply_1(x_42, x_13);
x_44 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_1, x_2, x_10, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_45 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_9, 1);
lean_inc(x_46);
lean_dec_ref(x_9);
x_47 = lean_ctor_get(x_7, 3);
x_48 = lean_ctor_get(x_7, 5);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec_ref(x_45);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_eq(x_50, x_51);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = lean_nat_dec_eq(x_50, x_13);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = l_Lean_RArray_getImpl___redArg(x_2, x_49);
lean_dec(x_49);
lean_inc(x_48);
x_55 = lean_apply_2(x_48, x_54, x_50);
lean_inc_ref(x_7);
x_56 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_7, x_2, x_46, x_55);
x_57 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_1, x_2, x_10, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
x_58 = l_Lean_RArray_getImpl___redArg(x_2, x_49);
lean_dec(x_49);
lean_inc_ref(x_7);
x_59 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_7, x_2, x_46, x_58);
x_60 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_1, x_2, x_10, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_50);
lean_dec(x_49);
lean_inc(x_47);
x_61 = lean_apply_1(x_47, x_13);
lean_inc_ref(x_7);
x_62 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_7, x_2, x_46, x_61);
x_63 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_1, x_2, x_10, x_62);
return x_63;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Poly_denote_x27___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_apply_1(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_11);
lean_dec_ref(x_4);
lean_inc_ref(x_2);
x_12 = l_Lean_Grind_Ring_toIntModule___redArg(x_2);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_16 = lean_int_dec_eq(x_9, x_15);
if (x_16 == 0)
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_8, 3);
lean_inc(x_17);
x_18 = lean_apply_1(x_17, x_14);
x_19 = lean_apply_2(x_13, x_9, x_18);
x_20 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_2, x_3, x_11, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec_ref(x_10);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 5);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec_ref(x_21);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_26, x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = lean_nat_dec_eq(x_26, x_14);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = l_Lean_RArray_getImpl___redArg(x_3, x_25);
lean_dec(x_25);
lean_inc(x_24);
x_31 = lean_apply_2(x_24, x_30, x_26);
lean_inc_ref(x_8);
x_32 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_8, x_3, x_22, x_31);
x_33 = lean_apply_2(x_13, x_9, x_32);
x_34 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_2, x_3, x_11, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_26);
x_35 = l_Lean_RArray_getImpl___redArg(x_3, x_25);
lean_dec(x_25);
lean_inc_ref(x_8);
x_36 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_8, x_3, x_22, x_35);
x_37 = lean_apply_2(x_13, x_9, x_36);
x_38 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_2, x_3, x_11, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_26);
lean_dec(x_25);
lean_inc(x_23);
x_39 = lean_apply_1(x_23, x_14);
lean_inc_ref(x_8);
x_40 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_8, x_3, x_22, x_39);
x_41 = lean_apply_2(x_13, x_9, x_40);
x_42 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_2, x_3, x_11, x_41);
return x_42;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 3);
lean_inc(x_43);
x_44 = lean_apply_1(x_43, x_14);
x_45 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_2, x_3, x_11, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_46 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_10, 1);
lean_inc(x_47);
lean_dec_ref(x_10);
x_48 = lean_ctor_get(x_8, 3);
x_49 = lean_ctor_get(x_8, 5);
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec_ref(x_46);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_eq(x_51, x_52);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = lean_nat_dec_eq(x_51, x_14);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = l_Lean_RArray_getImpl___redArg(x_3, x_50);
lean_dec(x_50);
lean_inc(x_49);
x_56 = lean_apply_2(x_49, x_55, x_51);
lean_inc_ref(x_8);
x_57 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_8, x_3, x_47, x_56);
x_58 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_2, x_3, x_11, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_51);
x_59 = l_Lean_RArray_getImpl___redArg(x_3, x_50);
lean_dec(x_50);
lean_inc_ref(x_8);
x_60 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_8, x_3, x_47, x_59);
x_61 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_2, x_3, x_11, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_51);
lean_dec(x_50);
lean_inc(x_48);
x_62 = lean_apply_1(x_48, x_14);
lean_inc_ref(x_8);
x_63 = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(x_8, x_3, x_47, x_62);
x_64 = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(x_2, x_3, x_11, x_63);
return x_64;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_denote_x27(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_3 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_CommRing_Mon_ofVar(x_1);
x_3 = l_Lean_Grind_CommRing_Poly_ofMon(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_isSorted(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Lean_Grind_CommRing_Mon_grevlex(x_5, x_6);
x_8 = 2;
x_9 = l_instDecidableEqOrdering(x_7, x_8);
if (x_9 == 0)
{
return x_9;
}
else
{
x_1 = x_3;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isSorted___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Grind_CommRing_Poly_isSorted(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_int_add(x_4, x_1);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_int_add(x_6, x_1);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
x_11 = l_Lean_Grind_CommRing_Poly_addConst_go(x_1, x_10);
lean_ctor_set(x_2, 2, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = l_Lean_Grind_CommRing_Poly_addConst_go(x_1, x_14);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Poly_addConst_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_4 = lean_int_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_addConst_go(x_2, x_1);
return x_5;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Poly_addConst(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_3(x_3, x_6, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_Grind_CommRing_Mon_grevlex(x_2, x_6);
switch (x_8) {
case 0:
{
uint8_t x_9; 
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = l_Lean_Grind_CommRing_Poly_insert_go(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = l_Lean_Grind_CommRing_Poly_insert_go(x_1, x_2, x_7);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
case 1:
{
uint8_t x_16; 
lean_inc_ref(x_7);
lean_inc(x_5);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_3, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 0);
lean_dec(x_19);
x_20 = lean_int_add(x_1, x_5);
lean_dec(x_5);
lean_dec(x_1);
x_21 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_22 = lean_int_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_20);
return x_3;
}
else
{
lean_dec(x_20);
lean_free_object(x_3);
lean_dec(x_2);
return x_7;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_3);
x_23 = lean_int_add(x_1, x_5);
lean_dec(x_5);
lean_dec(x_1);
x_24 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_25 = lean_int_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_7);
return x_26;
}
else
{
lean_dec(x_23);
lean_dec(x_2);
return x_7;
}
}
}
default: 
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_3);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_5 = lean_int_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Grind_CommRing_instBEqMon_beq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Grind_CommRing_Poly_insert_go(x_1, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = l_Lean_Grind_CommRing_Poly_addConst(x_3, x_1);
lean_dec(x_1);
return x_9;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_concat(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Grind_CommRing_Poly_addConst(x_2, x_3);
lean_dec(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = l_Lean_Grind_CommRing_Poly_concat(x_6, x_2);
lean_ctor_set(x_1, 2, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = l_Lean_Grind_CommRing_Poly_concat(x_10, x_2);
x_12 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_int_mul(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_int_mul(x_1, x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_int_mul(x_1, x_10);
lean_dec(x_10);
x_13 = l_Lean_Grind_CommRing_Poly_mulConst_go(x_1, x_11);
lean_ctor_set(x_2, 2, x_13);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_17 = lean_int_mul(x_1, x_14);
lean_dec(x_14);
x_18 = l_Lean_Grind_CommRing_Poly_mulConst_go(x_1, x_16);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Poly_mulConst_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_4 = lean_int_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_6 = lean_int_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Grind_CommRing_Poly_mulConst_go(x_1, x_2);
return x_7;
}
else
{
return x_2;
}
}
else
{
lean_object* x_8; 
lean_dec_ref(x_2);
x_8 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Poly_mulConst(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_6 = lean_int_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_int_mul(x_1, x_4);
lean_dec(x_4);
x_8 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
x_9 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_int_mul(x_1, x_12);
lean_dec(x_12);
lean_inc(x_2);
x_16 = l_Lean_Grind_CommRing_Mon_mul(x_2, x_13);
x_17 = l_Lean_Grind_CommRing_Poly_mulMon_go(x_1, x_2, x_14);
lean_ctor_set(x_3, 2, x_17);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_21 = lean_int_mul(x_1, x_18);
lean_dec(x_18);
lean_inc(x_2);
x_22 = l_Lean_Grind_CommRing_Mon_mul(x_2, x_19);
x_23 = l_Lean_Grind_CommRing_Poly_mulMon_go(x_1, x_2, x_20);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Poly_mulMon_go(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_5 = lean_int_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Grind_CommRing_instBEqMon_beq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Grind_CommRing_Poly_mulMon_go(x_1, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = l_Lean_Grind_CommRing_Poly_mulConst(x_1, x_3);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_10 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Poly_mulMon(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_int_mul(x_1, x_5);
lean_dec(x_5);
x_7 = l_Lean_Grind_CommRing_Poly_insert(x_6, x_2, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_10);
lean_dec_ref(x_3);
x_11 = lean_int_mul(x_1, x_8);
lean_dec(x_8);
lean_inc(x_2);
x_12 = l_Lean_Grind_CommRing_Mon_mul__nc(x_2, x_9);
x_13 = l_Lean_Grind_CommRing_Poly_insert(x_11, x_12, x_4);
x_3 = x_10;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_5 = lean_int_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Grind_CommRing_instBEqMon_beq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
x_9 = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(x_1, x_2, x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = l_Lean_Grind_CommRing_Poly_mulConst(x_1, x_3);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_11 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Poly_mulMon__nc(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Grind_CommRing_Poly_concat(x_2, x_3);
return x_6;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_int_add(x_7, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_int_add(x_7, x_11);
lean_dec(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec_ref(x_2);
x_15 = l_Lean_Grind_CommRing_Poly_addConst(x_3, x_14);
lean_dec(x_14);
return x_15;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec_ref(x_3);
x_17 = l_Lean_Grind_CommRing_Poly_addConst(x_2, x_16);
lean_dec(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_1, x_24);
lean_dec(x_1);
x_26 = l_Lean_Grind_CommRing_Mon_grevlex(x_19, x_22);
switch (x_26) {
case 0:
{
uint8_t x_27; 
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_3, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_3, 0);
lean_dec(x_30);
x_31 = l_Lean_Grind_CommRing_Poly_combine_go(x_25, x_2, x_23);
lean_ctor_set(x_3, 2, x_31);
return x_3;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_32 = l_Lean_Grind_CommRing_Poly_combine_go(x_25, x_2, x_23);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_32);
return x_33;
}
}
case 1:
{
uint8_t x_34; 
lean_inc_ref(x_23);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_3, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_3, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_3, 0);
lean_dec(x_37);
x_38 = lean_int_add(x_18, x_21);
lean_dec(x_21);
lean_dec(x_18);
x_39 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_40 = lean_int_dec_eq(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lean_Grind_CommRing_Poly_combine_go(x_25, x_20, x_23);
lean_ctor_set(x_3, 2, x_41);
lean_ctor_set(x_3, 1, x_19);
lean_ctor_set(x_3, 0, x_38);
return x_3;
}
else
{
lean_dec(x_38);
lean_free_object(x_3);
lean_dec(x_19);
x_1 = x_25;
x_2 = x_20;
x_3 = x_23;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_3);
x_43 = lean_int_add(x_18, x_21);
lean_dec(x_21);
lean_dec(x_18);
x_44 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_45 = lean_int_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_Grind_CommRing_Poly_combine_go(x_25, x_20, x_23);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_19);
lean_ctor_set(x_47, 2, x_46);
return x_47;
}
else
{
lean_dec(x_43);
lean_dec(x_19);
x_1 = x_25;
x_2 = x_20;
x_3 = x_23;
goto _start;
}
}
}
default: 
{
uint8_t x_49; 
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_49 = !lean_is_exclusive(x_2);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_2, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_2, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_2, 0);
lean_dec(x_52);
x_53 = l_Lean_Grind_CommRing_Poly_combine_go(x_25, x_20, x_3);
lean_ctor_set(x_2, 2, x_53);
return x_2;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
x_54 = l_Lean_Grind_CommRing_Poly_combine_go(x_25, x_20, x_3);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_18);
lean_ctor_set(x_55, 1, x_19);
lean_ctor_set(x_55, 2, x_54);
return x_55;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1000000u);
x_4 = l_Lean_Grind_CommRing_Poly_combine_go(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_2);
x_14 = lean_apply_4(x_4, x_10, x_11, x_12, x_13);
return x_14;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec_ref(x_2);
x_19 = lean_apply_4(x_5, x_15, x_16, x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_25);
lean_dec_ref(x_2);
x_26 = lean_apply_6(x_6, x_20, x_21, x_22, x_23, x_24, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Grind_CommRing_Poly_mulConst(x_4, x_1);
lean_dec(x_4);
x_6 = l_Lean_Grind_CommRing_Poly_combine(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_10 = l_Lean_Grind_CommRing_Poly_mulMon(x_7, x_8, x_1);
lean_dec(x_7);
x_11 = l_Lean_Grind_CommRing_Poly_combine(x_3, x_10);
x_2 = x_9;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
x_4 = l_Lean_Grind_CommRing_Poly_mul_go(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Grind_CommRing_Poly_mulConst(x_4, x_1);
lean_dec(x_4);
x_6 = l_Lean_Grind_CommRing_Poly_combine(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_10 = l_Lean_Grind_CommRing_Poly_mulMon__nc(x_7, x_8, x_1);
lean_dec(x_7);
x_11 = l_Lean_Grind_CommRing_Poly_combine(x_3, x_10);
x_2 = x_9;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
x_4 = l_Lean_Grind_CommRing_Poly_mul__nc_go(x_2, x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_pow___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = l_Lean_Grind_CommRing_Poly_pow___closed__0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_nat_dec_eq(x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_inc_ref(x_1);
x_9 = l_Lean_Grind_CommRing_Poly_pow(x_1, x_7);
lean_dec(x_7);
x_10 = l_Lean_Grind_CommRing_Poly_mul(x_1, x_9);
return x_10;
}
else
{
lean_dec(x_7);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Poly_pow(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = l_Lean_Grind_CommRing_Poly_pow___closed__0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_nat_dec_eq(x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_inc_ref(x_1);
x_9 = l_Lean_Grind_CommRing_Poly_pow__nc(x_1, x_7);
lean_dec(x_7);
x_10 = l_Lean_Grind_CommRing_Poly_mul__nc(x_9, x_1);
return x_10;
}
else
{
lean_dec(x_7);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Poly_pow__nc(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
case 1:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_nat_to_int(x_6);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_nat_to_int(x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
case 2:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
case 3:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = l_Lean_Grind_CommRing_Poly_ofVar(x_14);
return x_15;
}
case 4:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = l_Lean_Grind_CommRing_Expr_toPoly___closed__0;
x_18 = l_Lean_Grind_CommRing_Expr_toPoly(x_16);
x_19 = l_Lean_Grind_CommRing_Poly_mulConst(x_17, x_18);
return x_19;
}
case 5:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_21);
lean_dec_ref(x_1);
x_22 = l_Lean_Grind_CommRing_Expr_toPoly(x_20);
x_23 = l_Lean_Grind_CommRing_Expr_toPoly(x_21);
x_24 = l_Lean_Grind_CommRing_Poly_combine(x_22, x_23);
return x_24;
}
case 6:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_1);
x_27 = l_Lean_Grind_CommRing_Expr_toPoly(x_25);
x_28 = l_Lean_Grind_CommRing_Expr_toPoly___closed__0;
x_29 = l_Lean_Grind_CommRing_Expr_toPoly(x_26);
x_30 = l_Lean_Grind_CommRing_Poly_mulConst(x_28, x_29);
x_31 = l_Lean_Grind_CommRing_Poly_combine(x_27, x_30);
return x_31;
}
case 7:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_1);
x_34 = l_Lean_Grind_CommRing_Expr_toPoly(x_32);
x_35 = l_Lean_Grind_CommRing_Expr_toPoly(x_33);
x_36 = l_Lean_Grind_CommRing_Poly_mul(x_34, x_35);
return x_36;
}
default: 
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_44; uint8_t x_45; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_39, x_44);
if (x_45 == 0)
{
switch (lean_obj_tag(x_38)) {
case 0:
{
lean_object* x_46; 
lean_free_object(x_1);
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec_ref(x_38);
x_40 = x_46;
goto block_43;
}
case 2:
{
lean_object* x_47; 
lean_free_object(x_1);
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
lean_dec_ref(x_38);
x_40 = x_47;
goto block_43;
}
case 1:
{
uint8_t x_48; 
lean_free_object(x_1);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_nat_to_int(x_49);
x_51 = l_Int_pow(x_50, x_39);
lean_dec(x_39);
lean_dec(x_50);
lean_ctor_set_tag(x_38, 0);
lean_ctor_set(x_38, 0, x_51);
return x_38;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_38, 0);
lean_inc(x_52);
lean_dec(x_38);
x_53 = lean_nat_to_int(x_52);
x_54 = l_Int_pow(x_53, x_39);
lean_dec(x_39);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
case 3:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_38, 0);
lean_inc(x_56);
lean_dec_ref(x_38);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_56);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Grind_CommRing_Poly_ofMon(x_58);
return x_59;
}
default: 
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_1);
x_60 = l_Lean_Grind_CommRing_Expr_toPoly(x_38);
x_61 = l_Lean_Grind_CommRing_Poly_pow(x_60, x_39);
lean_dec(x_39);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_free_object(x_1);
lean_dec(x_39);
lean_dec_ref(x_38);
x_62 = l_Lean_Grind_CommRing_Poly_pow___closed__0;
return x_62;
}
block_43:
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Int_pow(x_40, x_39);
lean_dec(x_39);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_69; uint8_t x_70; 
x_63 = lean_ctor_get(x_1, 0);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_1);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_eq(x_64, x_69);
if (x_70 == 0)
{
switch (lean_obj_tag(x_63)) {
case 0:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
lean_dec_ref(x_63);
x_65 = x_71;
goto block_68;
}
case 2:
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
lean_dec_ref(x_63);
x_65 = x_72;
goto block_68;
}
case 1:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_63, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_74 = x_63;
} else {
 lean_dec_ref(x_63);
 x_74 = lean_box(0);
}
x_75 = lean_nat_to_int(x_73);
x_76 = l_Int_pow(x_75, x_64);
lean_dec(x_64);
lean_dec(x_75);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 1, 0);
} else {
 x_77 = x_74;
 lean_ctor_set_tag(x_77, 0);
}
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
case 3:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_63, 0);
lean_inc(x_78);
lean_dec_ref(x_63);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_64);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Grind_CommRing_Poly_ofMon(x_81);
return x_82;
}
default: 
{
lean_object* x_83; lean_object* x_84; 
x_83 = l_Lean_Grind_CommRing_Expr_toPoly(x_63);
x_84 = l_Lean_Grind_CommRing_Poly_pow(x_83, x_64);
lean_dec(x_64);
return x_84;
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_64);
lean_dec_ref(x_63);
x_85 = l_Lean_Grind_CommRing_Poly_pow___closed__0;
return x_85;
}
block_68:
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Int_pow(x_65, x_64);
lean_dec(x_64);
lean_dec(x_65);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_nat_dec_eq(x_6, x_2);
if (x_8 == 0)
{
x_1 = x_5;
goto _start;
}
else
{
lean_inc(x_7);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Mon_degreeOf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_nat_dec_eq(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Grind_CommRing_Mon_cancelVar(x_5, x_2);
lean_ctor_set(x_1, 1, x_8);
return x_1;
}
else
{
lean_free_object(x_1);
lean_dec_ref(x_4);
return x_5;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_nat_dec_eq(x_11, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Grind_CommRing_Mon_cancelVar(x_10, x_2);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_dec_ref(x_9);
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Mon_cancelVar(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Lean_Grind_CommRing_Poly_addConst(x_4, x_5);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_20; uint8_t x_21; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_9);
lean_dec_ref(x_3);
x_10 = l_Lean_Grind_CommRing_Mon_degreeOf(x_8, x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_10);
if (x_21 == 0)
{
x_11 = x_21;
goto block_19;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Int_pow(x_1, x_10);
x_23 = l_Int_decidableDvd(x_22, x_7);
lean_dec(x_22);
x_11 = x_23;
goto block_19;
}
block_19:
{
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = l_Lean_Grind_CommRing_Poly_insert(x_7, x_8, x_4);
x_3 = x_9;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Int_pow(x_1, x_10);
lean_dec(x_10);
x_15 = lean_int_ediv(x_7, x_14);
lean_dec(x_14);
lean_dec(x_7);
x_16 = l_Lean_Grind_CommRing_Mon_cancelVar(x_8, x_2);
x_17 = l_Lean_Grind_CommRing_Poly_insert(x_15, x_16, x_4);
x_3 = x_9;
x_4 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_cancelVar_x27(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
x_5 = l_Lean_Grind_CommRing_Poly_cancelVar_x27(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Poly_cancelVar(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_1(x_2, x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = lean_apply_1(x_4, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_apply_1(x_3, x_15);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = lean_apply_1(x_5, x_17);
return x_18;
}
case 4:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_1);
x_20 = lean_apply_1(x_8, x_19);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_23 = lean_apply_2(x_6, x_21, x_22);
return x_23;
}
case 6:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_1);
x_26 = lean_apply_2(x_9, x_24, x_25);
return x_26;
}
case 7:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_28);
lean_dec_ref(x_1);
x_29 = lean_apply_2(x_7, x_27, x_28);
return x_29;
}
default: 
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec_ref(x_1);
x_32 = lean_apply_2(x_10, x_30, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = lean_apply_1(x_5, x_13);
return x_14;
}
default: 
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_apply_5(x_6, x_1, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_apply_1(x_5, x_12);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec_ref(x_2);
x_15 = lean_apply_1(x_6, x_14);
return x_15;
}
default: 
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_apply_5(x_7, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly__nc(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
case 1:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_nat_to_int(x_6);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_nat_to_int(x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
case 2:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
case 3:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = l_Lean_Grind_CommRing_Poly_ofVar(x_14);
return x_15;
}
case 4:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = l_Lean_Grind_CommRing_Expr_toPoly___closed__0;
x_18 = l_Lean_Grind_CommRing_Expr_toPoly__nc(x_16);
x_19 = l_Lean_Grind_CommRing_Poly_mulConst(x_17, x_18);
return x_19;
}
case 5:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_21);
lean_dec_ref(x_1);
x_22 = l_Lean_Grind_CommRing_Expr_toPoly__nc(x_20);
x_23 = l_Lean_Grind_CommRing_Expr_toPoly__nc(x_21);
x_24 = l_Lean_Grind_CommRing_Poly_combine(x_22, x_23);
return x_24;
}
case 6:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_1);
x_27 = l_Lean_Grind_CommRing_Expr_toPoly__nc(x_25);
x_28 = l_Lean_Grind_CommRing_Expr_toPoly___closed__0;
x_29 = l_Lean_Grind_CommRing_Expr_toPoly__nc(x_26);
x_30 = l_Lean_Grind_CommRing_Poly_mulConst(x_28, x_29);
x_31 = l_Lean_Grind_CommRing_Poly_combine(x_27, x_30);
return x_31;
}
case 7:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_1);
x_34 = l_Lean_Grind_CommRing_Expr_toPoly__nc(x_32);
x_35 = l_Lean_Grind_CommRing_Expr_toPoly__nc(x_33);
x_36 = l_Lean_Grind_CommRing_Poly_mul__nc(x_34, x_35);
return x_36;
}
default: 
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_44; uint8_t x_45; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_39, x_44);
if (x_45 == 0)
{
switch (lean_obj_tag(x_38)) {
case 0:
{
lean_object* x_46; 
lean_free_object(x_1);
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec_ref(x_38);
x_40 = x_46;
goto block_43;
}
case 2:
{
lean_object* x_47; 
lean_free_object(x_1);
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
lean_dec_ref(x_38);
x_40 = x_47;
goto block_43;
}
case 1:
{
uint8_t x_48; 
lean_free_object(x_1);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_nat_to_int(x_49);
x_51 = l_Int_pow(x_50, x_39);
lean_dec(x_39);
lean_dec(x_50);
lean_ctor_set_tag(x_38, 0);
lean_ctor_set(x_38, 0, x_51);
return x_38;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_38, 0);
lean_inc(x_52);
lean_dec(x_38);
x_53 = lean_nat_to_int(x_52);
x_54 = l_Int_pow(x_53, x_39);
lean_dec(x_39);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
case 3:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_38, 0);
lean_inc(x_56);
lean_dec_ref(x_38);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_56);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Grind_CommRing_Poly_ofMon(x_58);
return x_59;
}
default: 
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_1);
x_60 = l_Lean_Grind_CommRing_Expr_toPoly__nc(x_38);
x_61 = l_Lean_Grind_CommRing_Poly_pow__nc(x_60, x_39);
lean_dec(x_39);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_free_object(x_1);
lean_dec(x_39);
lean_dec_ref(x_38);
x_62 = l_Lean_Grind_CommRing_Poly_pow___closed__0;
return x_62;
}
block_43:
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Int_pow(x_40, x_39);
lean_dec(x_39);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_69; uint8_t x_70; 
x_63 = lean_ctor_get(x_1, 0);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_1);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_eq(x_64, x_69);
if (x_70 == 0)
{
switch (lean_obj_tag(x_63)) {
case 0:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
lean_dec_ref(x_63);
x_65 = x_71;
goto block_68;
}
case 2:
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
lean_dec_ref(x_63);
x_65 = x_72;
goto block_68;
}
case 1:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_63, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_74 = x_63;
} else {
 lean_dec_ref(x_63);
 x_74 = lean_box(0);
}
x_75 = lean_nat_to_int(x_73);
x_76 = l_Int_pow(x_75, x_64);
lean_dec(x_64);
lean_dec(x_75);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 1, 0);
} else {
 x_77 = x_74;
 lean_ctor_set_tag(x_77, 0);
}
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
case 3:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_63, 0);
lean_inc(x_78);
lean_dec_ref(x_63);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_64);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Grind_CommRing_Poly_ofMon(x_81);
return x_82;
}
default: 
{
lean_object* x_83; lean_object* x_84; 
x_83 = l_Lean_Grind_CommRing_Expr_toPoly__nc(x_63);
x_84 = l_Lean_Grind_CommRing_Poly_pow__nc(x_83, x_64);
lean_dec(x_64);
return x_84;
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_64);
lean_dec_ref(x_63);
x_85 = l_Lean_Grind_CommRing_Poly_pow___closed__0;
return x_85;
}
block_68:
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Int_pow(x_65, x_64);
lean_dec(x_64);
lean_dec(x_65);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_normEq0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_nat_to_int(x_2);
x_5 = lean_int_emod(x_3, x_4);
lean_dec(x_4);
x_6 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_7 = lean_int_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
return x_1;
}
else
{
lean_object* x_8; 
lean_dec_ref(x_1);
x_8 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_13 = lean_nat_to_int(x_2);
x_14 = lean_int_emod(x_10, x_13);
lean_dec(x_13);
x_15 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_16 = lean_int_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Grind_CommRing_Poly_normEq0(x_12, x_2);
lean_ctor_set(x_1, 2, x_17);
return x_1;
}
else
{
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
x_1 = x_12;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_2);
x_22 = lean_nat_to_int(x_2);
x_23 = lean_int_emod(x_19, x_22);
lean_dec(x_22);
x_24 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_25 = lean_int_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Grind_CommRing_Poly_normEq0(x_21, x_2);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_20);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
else
{
lean_dec(x_20);
lean_dec(x_19);
x_1 = x_21;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_int_add(x_5, x_2);
lean_dec(x_5);
x_7 = lean_nat_to_int(x_3);
x_8 = lean_int_emod(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_int_add(x_9, x_2);
lean_dec(x_9);
x_11 = lean_nat_to_int(x_3);
x_12 = lean_int_emod(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 2);
x_16 = l_Lean_Grind_CommRing_Poly_addConstC(x_15, x_2, x_3);
lean_ctor_set(x_1, 2, x_16);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_20 = l_Lean_Grind_CommRing_Poly_addConstC(x_19, x_2, x_3);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Poly_addConstC(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
x_9 = l_Lean_Grind_CommRing_Mon_grevlex(x_1, x_7);
switch (x_9) {
case 0:
{
uint8_t x_10; 
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_4, 0);
lean_dec(x_13);
x_14 = l_Lean_Grind_CommRing_Poly_insertC_go(x_1, x_2, x_3, x_8);
lean_ctor_set(x_4, 2, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_15 = l_Lean_Grind_CommRing_Poly_insertC_go(x_1, x_2, x_3, x_8);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
case 1:
{
uint8_t x_17; 
lean_inc_ref(x_8);
lean_inc(x_6);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_4, 2);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 0);
lean_dec(x_20);
x_21 = lean_int_add(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
x_22 = lean_nat_to_int(x_2);
x_23 = lean_int_emod(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_25 = lean_int_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 0, x_23);
return x_4;
}
else
{
lean_dec(x_23);
lean_free_object(x_4);
lean_dec(x_1);
return x_8;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_4);
x_26 = lean_int_add(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
x_27 = lean_nat_to_int(x_2);
x_28 = lean_int_emod(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_29 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_30 = lean_int_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_1);
lean_ctor_set(x_31, 2, x_8);
return x_31;
}
else
{
lean_dec(x_28);
lean_dec(x_1);
return x_8;
}
}
}
default: 
{
lean_object* x_32; 
lean_dec(x_2);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_1);
lean_ctor_set(x_32, 2, x_4);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_int_emod(x_1, x_5);
lean_dec(x_5);
x_7 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_8 = lean_int_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Grind_CommRing_Poly_insertC_go(x_2, x_4, x_6, x_3);
return x_9;
}
else
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_insertC(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_int_mul(x_1, x_5);
lean_dec(x_5);
x_7 = lean_nat_to_int(x_2);
x_8 = lean_int_emod(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_int_mul(x_1, x_9);
lean_dec(x_9);
x_11 = lean_nat_to_int(x_2);
x_12 = lean_int_emod(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_int_mul(x_1, x_15);
lean_dec(x_15);
lean_inc(x_2);
x_19 = lean_nat_to_int(x_2);
x_20 = lean_int_emod(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_22 = lean_int_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_Grind_CommRing_Poly_mulConstC_go(x_1, x_2, x_17);
lean_ctor_set(x_3, 2, x_23);
lean_ctor_set(x_3, 0, x_20);
return x_3;
}
else
{
lean_dec(x_20);
lean_free_object(x_3);
lean_dec(x_16);
x_3 = x_17;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_28 = lean_int_mul(x_1, x_25);
lean_dec(x_25);
lean_inc(x_2);
x_29 = lean_nat_to_int(x_2);
x_30 = lean_int_emod(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
x_31 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_32 = lean_int_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Grind_CommRing_Poly_mulConstC_go(x_1, x_2, x_27);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_33);
return x_34;
}
else
{
lean_dec(x_30);
lean_dec(x_26);
x_3 = x_27;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Poly_mulConstC_go(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_int_emod(x_1, x_4);
lean_dec(x_4);
x_6 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_7 = lean_int_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
x_9 = lean_int_dec_eq(x_5, x_8);
lean_dec(x_5);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Grind_CommRing_Poly_mulConstC_go(x_1, x_3, x_2);
return x_10;
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_11 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Poly_mulConstC(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_int_mul(x_1, x_5);
lean_dec(x_5);
x_7 = lean_nat_to_int(x_3);
x_8 = lean_int_emod(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_9 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_10 = lean_int_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
x_12 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_2);
x_13 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_int_mul(x_1, x_15);
lean_dec(x_15);
lean_inc(x_3);
x_19 = lean_nat_to_int(x_3);
x_20 = lean_int_emod(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_22 = lean_int_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_inc(x_2);
x_23 = l_Lean_Grind_CommRing_Mon_mul(x_2, x_16);
x_24 = l_Lean_Grind_CommRing_Poly_mulMonC_go(x_1, x_2, x_3, x_17);
lean_ctor_set(x_4, 2, x_24);
lean_ctor_set(x_4, 1, x_23);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
else
{
lean_dec(x_20);
lean_free_object(x_4);
lean_dec(x_16);
x_4 = x_17;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
x_28 = lean_ctor_get(x_4, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_29 = lean_int_mul(x_1, x_26);
lean_dec(x_26);
lean_inc(x_3);
x_30 = lean_nat_to_int(x_3);
x_31 = lean_int_emod(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
x_32 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_33 = lean_int_dec_eq(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_2);
x_34 = l_Lean_Grind_CommRing_Mon_mul(x_2, x_27);
x_35 = l_Lean_Grind_CommRing_Poly_mulMonC_go(x_1, x_2, x_3, x_28);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
return x_36;
}
else
{
lean_dec(x_31);
lean_dec(x_27);
x_4 = x_28;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_mulMonC_go(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_int_emod(x_1, x_5);
lean_dec(x_5);
x_7 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_8 = lean_int_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Grind_CommRing_instBEqMon_beq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
x_11 = l_Lean_Grind_CommRing_Poly_mulMonC_go(x_1, x_2, x_4, x_3);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = l_Lean_Grind_CommRing_Poly_mulConstC(x_6, x_3, x_4);
lean_dec(x_6);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_13 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_mulMonC(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_int_mul(x_1, x_6);
lean_dec(x_6);
x_8 = lean_nat_to_int(x_3);
x_9 = lean_int_emod(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = l_Lean_Grind_CommRing_Poly_insert(x_9, x_2, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_4);
x_14 = lean_int_mul(x_1, x_11);
lean_dec(x_11);
lean_inc(x_3);
x_15 = lean_nat_to_int(x_3);
x_16 = lean_int_emod(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
lean_inc(x_2);
x_17 = l_Lean_Grind_CommRing_Mon_mul__nc(x_2, x_12);
x_18 = l_Lean_Grind_CommRing_Poly_insert(x_16, x_17, x_5);
x_4 = x_13;
x_5 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_int_emod(x_1, x_5);
lean_dec(x_5);
x_7 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_8 = lean_int_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Grind_CommRing_instBEqMon_beq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_11 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
x_12 = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(x_1, x_2, x_4, x_3, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = l_Lean_Grind_CommRing_Poly_mulConstC(x_6, x_3, x_4);
lean_dec(x_6);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_14 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_mulMonC__nc(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineC(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_int_add(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
x_8 = lean_nat_to_int(x_3);
x_9 = lean_int_emod(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_int_add(x_4, x_10);
lean_dec(x_10);
lean_dec(x_4);
x_12 = lean_nat_to_int(x_3);
x_13 = lean_int_emod(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = l_Lean_Grind_CommRing_Poly_addConstC(x_2, x_15, x_3);
lean_dec(x_15);
return x_16;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec_ref(x_2);
x_18 = l_Lean_Grind_CommRing_Poly_addConstC(x_1, x_17, x_3);
lean_dec(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = l_Lean_Grind_CommRing_Mon_grevlex(x_20, x_23);
switch (x_25) {
case 0:
{
uint8_t x_26; 
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_2, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_2, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_2, 0);
lean_dec(x_29);
x_30 = l_Lean_Grind_CommRing_Poly_combineC(x_1, x_24, x_3);
lean_ctor_set(x_2, 2, x_30);
return x_2;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_31 = l_Lean_Grind_CommRing_Poly_combineC(x_1, x_24, x_3);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_31);
return x_32;
}
}
case 1:
{
uint8_t x_33; 
lean_inc_ref(x_24);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_34 = lean_ctor_get(x_2, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_2, 0);
lean_dec(x_36);
x_37 = lean_int_add(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
lean_inc(x_3);
x_38 = lean_nat_to_int(x_3);
x_39 = lean_int_emod(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_40 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_41 = lean_int_dec_eq(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_Grind_CommRing_Poly_combineC(x_21, x_24, x_3);
lean_ctor_set(x_2, 2, x_42);
lean_ctor_set(x_2, 1, x_20);
lean_ctor_set(x_2, 0, x_39);
return x_2;
}
else
{
lean_dec(x_39);
lean_free_object(x_2);
lean_dec(x_20);
x_1 = x_21;
x_2 = x_24;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_2);
x_44 = lean_int_add(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
lean_inc(x_3);
x_45 = lean_nat_to_int(x_3);
x_46 = lean_int_emod(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
x_47 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_48 = lean_int_dec_eq(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_Grind_CommRing_Poly_combineC(x_21, x_24, x_3);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_20);
lean_ctor_set(x_50, 2, x_49);
return x_50;
}
else
{
lean_dec(x_46);
lean_dec(x_20);
x_1 = x_21;
x_2 = x_24;
goto _start;
}
}
}
default: 
{
uint8_t x_52; 
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_52 = !lean_is_exclusive(x_1);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_1, 2);
lean_dec(x_53);
x_54 = lean_ctor_get(x_1, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_1, 0);
lean_dec(x_55);
x_56 = l_Lean_Grind_CommRing_Poly_combineC(x_21, x_2, x_3);
lean_ctor_set(x_1, 2, x_56);
return x_1;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_1);
x_57 = l_Lean_Grind_CommRing_Poly_combineC(x_21, x_2, x_3);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_19);
lean_ctor_set(x_58, 1, x_20);
lean_ctor_set(x_58, 2, x_57);
return x_58;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
lean_inc(x_2);
x_6 = l_Lean_Grind_CommRing_Poly_mulConstC(x_5, x_1, x_2);
lean_dec(x_5);
x_7 = l_Lean_Grind_CommRing_Poly_combineC(x_4, x_6, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_10);
lean_dec_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_11 = l_Lean_Grind_CommRing_Poly_mulMonC(x_8, x_9, x_1, x_2);
lean_dec(x_8);
lean_inc(x_2);
x_12 = l_Lean_Grind_CommRing_Poly_combineC(x_4, x_11, x_2);
x_3 = x_10;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
x_5 = l_Lean_Grind_CommRing_Poly_mulC_go(x_2, x_3, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
lean_inc(x_2);
x_6 = l_Lean_Grind_CommRing_Poly_mulConstC(x_5, x_1, x_2);
lean_dec(x_5);
x_7 = l_Lean_Grind_CommRing_Poly_combineC(x_4, x_6, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_10);
lean_dec_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_11 = l_Lean_Grind_CommRing_Poly_mulMonC__nc(x_8, x_9, x_1, x_2);
lean_dec(x_8);
lean_inc(x_2);
x_12 = l_Lean_Grind_CommRing_Poly_combineC(x_4, x_11, x_2);
x_3 = x_10;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
x_5 = l_Lean_Grind_CommRing_Poly_mulC__nc_go(x_2, x_3, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_6 = l_Lean_Grind_CommRing_Poly_pow___closed__0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = lean_nat_dec_eq(x_8, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
lean_inc_ref(x_1);
x_10 = l_Lean_Grind_CommRing_Poly_powC(x_1, x_8, x_3);
lean_dec(x_8);
x_11 = l_Lean_Grind_CommRing_Poly_mulC(x_1, x_10, x_3);
return x_11;
}
else
{
lean_dec(x_8);
lean_dec(x_3);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Poly_powC(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_6 = l_Lean_Grind_CommRing_Poly_pow___closed__0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = lean_nat_dec_eq(x_8, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
lean_inc_ref(x_1);
x_10 = l_Lean_Grind_CommRing_Poly_powC__nc(x_1, x_8, x_3);
lean_dec(x_8);
x_11 = l_Lean_Grind_CommRing_Poly_mulC__nc(x_10, x_1, x_3);
return x_11;
}
else
{
lean_dec(x_8);
lean_dec(x_3);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Poly_powC__nc(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 1:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_nat_to_int(x_9);
x_11 = lean_nat_to_int(x_1);
x_12 = lean_int_emod(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_nat_to_int(x_13);
x_15 = lean_nat_to_int(x_1);
x_16 = lean_int_emod(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
case 3:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec_ref(x_2);
x_19 = l_Lean_Grind_CommRing_Poly_ofVar(x_18);
return x_19;
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_20);
lean_dec_ref(x_2);
x_21 = l_Lean_Grind_CommRing_Expr_toPoly___closed__0;
lean_inc(x_1);
x_22 = l_Lean_Grind_CommRing_Expr_toPolyC_go(x_1, x_20);
x_23 = l_Lean_Grind_CommRing_Poly_mulConstC(x_21, x_22, x_1);
return x_23;
}
case 5:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_2);
lean_inc(x_1);
x_26 = l_Lean_Grind_CommRing_Expr_toPolyC_go(x_1, x_24);
lean_inc(x_1);
x_27 = l_Lean_Grind_CommRing_Expr_toPolyC_go(x_1, x_25);
x_28 = l_Lean_Grind_CommRing_Poly_combineC(x_26, x_27, x_1);
return x_28;
}
case 6:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_2);
lean_inc(x_1);
x_31 = l_Lean_Grind_CommRing_Expr_toPolyC_go(x_1, x_29);
x_32 = l_Lean_Grind_CommRing_Expr_toPoly___closed__0;
lean_inc(x_1);
x_33 = l_Lean_Grind_CommRing_Expr_toPolyC_go(x_1, x_30);
lean_inc(x_1);
x_34 = l_Lean_Grind_CommRing_Poly_mulConstC(x_32, x_33, x_1);
x_35 = l_Lean_Grind_CommRing_Poly_combineC(x_31, x_34, x_1);
return x_35;
}
case 7:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_2);
lean_inc(x_1);
x_38 = l_Lean_Grind_CommRing_Expr_toPolyC_go(x_1, x_36);
lean_inc(x_1);
x_39 = l_Lean_Grind_CommRing_Expr_toPolyC_go(x_1, x_37);
x_40 = l_Lean_Grind_CommRing_Poly_mulC(x_38, x_39, x_1);
return x_40;
}
case 8:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_43, x_44);
if (x_45 == 0)
{
switch (lean_obj_tag(x_42)) {
case 0:
{
uint8_t x_46; 
lean_free_object(x_2);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = l_Int_pow(x_47, x_43);
lean_dec(x_43);
lean_dec(x_47);
x_49 = lean_nat_to_int(x_1);
x_50 = lean_int_emod(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
x_52 = l_Int_pow(x_51, x_43);
lean_dec(x_43);
lean_dec(x_51);
x_53 = lean_nat_to_int(x_1);
x_54 = lean_int_emod(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
case 3:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_56 = lean_ctor_get(x_42, 0);
lean_inc(x_56);
lean_dec_ref(x_42);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_56);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Grind_CommRing_Poly_ofMon(x_58);
return x_59;
}
default: 
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_2);
lean_inc(x_1);
x_60 = l_Lean_Grind_CommRing_Expr_toPolyC_go(x_1, x_42);
x_61 = l_Lean_Grind_CommRing_Poly_powC(x_60, x_43, x_1);
lean_dec(x_43);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_free_object(x_2);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_1);
x_62 = l_Lean_Grind_CommRing_Poly_pow___closed__0;
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_2, 0);
x_64 = lean_ctor_get(x_2, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_2);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_64, x_65);
if (x_66 == 0)
{
switch (lean_obj_tag(x_63)) {
case 0:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_68 = x_63;
} else {
 lean_dec_ref(x_63);
 x_68 = lean_box(0);
}
x_69 = l_Int_pow(x_67, x_64);
lean_dec(x_64);
lean_dec(x_67);
x_70 = lean_nat_to_int(x_1);
x_71 = lean_int_emod(x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
case 3:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_1);
x_73 = lean_ctor_get(x_63, 0);
lean_inc(x_73);
lean_dec_ref(x_63);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_64);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Grind_CommRing_Poly_ofMon(x_76);
return x_77;
}
default: 
{
lean_object* x_78; lean_object* x_79; 
lean_inc(x_1);
x_78 = l_Lean_Grind_CommRing_Expr_toPolyC_go(x_1, x_63);
x_79 = l_Lean_Grind_CommRing_Poly_powC(x_78, x_64, x_1);
lean_dec(x_64);
return x_79;
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_1);
x_80 = l_Lean_Grind_CommRing_Poly_pow___closed__0;
return x_80;
}
}
}
default: 
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
lean_dec_ref(x_2);
x_3 = x_81;
goto block_7;
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_nat_to_int(x_1);
x_5 = lean_int_emod(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Expr_toPolyC_go(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 1:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_nat_to_int(x_9);
x_11 = lean_nat_to_int(x_1);
x_12 = lean_int_emod(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_nat_to_int(x_13);
x_15 = lean_nat_to_int(x_1);
x_16 = lean_int_emod(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
case 3:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec_ref(x_2);
x_19 = l_Lean_Grind_CommRing_Poly_ofVar(x_18);
return x_19;
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_20);
lean_dec_ref(x_2);
x_21 = l_Lean_Grind_CommRing_Expr_toPoly___closed__0;
lean_inc(x_1);
x_22 = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(x_1, x_20);
x_23 = l_Lean_Grind_CommRing_Poly_mulConstC(x_21, x_22, x_1);
return x_23;
}
case 5:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_2);
lean_inc(x_1);
x_26 = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(x_1, x_24);
lean_inc(x_1);
x_27 = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(x_1, x_25);
x_28 = l_Lean_Grind_CommRing_Poly_combineC(x_26, x_27, x_1);
return x_28;
}
case 6:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_2);
lean_inc(x_1);
x_31 = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(x_1, x_29);
x_32 = l_Lean_Grind_CommRing_Expr_toPoly___closed__0;
lean_inc(x_1);
x_33 = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(x_1, x_30);
lean_inc(x_1);
x_34 = l_Lean_Grind_CommRing_Poly_mulConstC(x_32, x_33, x_1);
x_35 = l_Lean_Grind_CommRing_Poly_combineC(x_31, x_34, x_1);
return x_35;
}
case 7:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_2);
lean_inc(x_1);
x_38 = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(x_1, x_36);
lean_inc(x_1);
x_39 = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(x_1, x_37);
x_40 = l_Lean_Grind_CommRing_Poly_mulC__nc(x_38, x_39, x_1);
return x_40;
}
case 8:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_43, x_44);
if (x_45 == 0)
{
switch (lean_obj_tag(x_42)) {
case 0:
{
uint8_t x_46; 
lean_free_object(x_2);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = l_Int_pow(x_47, x_43);
lean_dec(x_43);
lean_dec(x_47);
x_49 = lean_nat_to_int(x_1);
x_50 = lean_int_emod(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
x_52 = l_Int_pow(x_51, x_43);
lean_dec(x_43);
lean_dec(x_51);
x_53 = lean_nat_to_int(x_1);
x_54 = lean_int_emod(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
case 3:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_56 = lean_ctor_get(x_42, 0);
lean_inc(x_56);
lean_dec_ref(x_42);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_56);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Grind_CommRing_Poly_ofMon(x_58);
return x_59;
}
default: 
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_2);
lean_inc(x_1);
x_60 = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(x_1, x_42);
x_61 = l_Lean_Grind_CommRing_Poly_powC__nc(x_60, x_43, x_1);
lean_dec(x_43);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_free_object(x_2);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_1);
x_62 = l_Lean_Grind_CommRing_Poly_pow___closed__0;
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_2, 0);
x_64 = lean_ctor_get(x_2, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_2);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_64, x_65);
if (x_66 == 0)
{
switch (lean_obj_tag(x_63)) {
case 0:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_68 = x_63;
} else {
 lean_dec_ref(x_63);
 x_68 = lean_box(0);
}
x_69 = l_Int_pow(x_67, x_64);
lean_dec(x_64);
lean_dec(x_67);
x_70 = lean_nat_to_int(x_1);
x_71 = lean_int_emod(x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
case 3:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_1);
x_73 = lean_ctor_get(x_63, 0);
lean_inc(x_73);
lean_dec_ref(x_63);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_64);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Grind_CommRing_Poly_ofMon(x_76);
return x_77;
}
default: 
{
lean_object* x_78; lean_object* x_79; 
lean_inc(x_1);
x_78 = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(x_1, x_63);
x_79 = l_Lean_Grind_CommRing_Poly_powC__nc(x_78, x_64, x_1);
lean_dec(x_64);
return x_79;
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_1);
x_80 = l_Lean_Grind_CommRing_Poly_pow___closed__0;
return x_80;
}
}
}
default: 
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
lean_dec_ref(x_2);
x_3 = x_81;
goto block_7;
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_nat_to_int(x_1);
x_5 = lean_int_emod(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_3(x_4, x_1, lean_box(0), lean_box(0));
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_2, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_3(x_5, x_2, lean_box(0), lean_box(0));
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_3, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_7);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_1);
x_11 = lean_apply_3(x_4, x_10, x_7, lean_box(0));
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_8);
lean_dec(x_4);
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_2);
x_12 = lean_apply_3(x_5, x_11, x_8, lean_box(0));
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(x_1);
x_7 = lean_apply_2(x_3, x_6, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_2 == 1)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(x_2);
x_8 = lean_apply_2(x_4, x_7, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_7 = lean_int_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_2(x_3, x_5, lean_box(0));
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = lean_apply_3(x_4, x_11, x_12, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
x_8 = lean_int_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_2(x_4, x_6, lean_box(0));
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_14);
lean_dec_ref(x_2);
x_15 = lean_apply_3(x_5, x_12, x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_2);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_1, x_9);
x_11 = lean_nat_dec_eq(x_10, x_5);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_apply_2(x_4, x_10, lean_box(0));
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_3, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = lean_nat_dec_eq(x_11, x_6);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_apply_2(x_5, x_11, lean_box(0));
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = lean_apply_1(x_4, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_1(x_2, x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = lean_apply_1(x_3, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = lean_apply_1(x_5, x_17);
return x_18;
}
case 4:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_1);
x_20 = lean_apply_1(x_8, x_19);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_23 = lean_apply_2(x_6, x_21, x_22);
return x_23;
}
case 6:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_1);
x_26 = lean_apply_2(x_9, x_24, x_25);
return x_26;
}
case 7:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_28);
lean_dec_ref(x_1);
x_29 = lean_apply_2(x_7, x_27, x_28);
return x_29;
}
default: 
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec_ref(x_1);
x_32 = lean_apply_2(x_10, x_30, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_apply_3(x_4, x_1, lean_box(0), lean_box(0));
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
case 3:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_apply_1(x_4, x_8);
return x_9;
}
default: 
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_apply_3(x_5, x_2, lean_box(0), lean_box(0));
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_ctor_get(x_5, 3);
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec_ref(x_3);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec_ref(x_9);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_dec_eq(x_16, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_RArray_getImpl___redArg(x_2, x_15);
lean_dec(x_15);
lean_inc(x_8);
x_22 = lean_apply_2(x_8, x_21, x_16);
x_11 = x_22;
goto block_14;
}
else
{
lean_object* x_23; 
lean_dec(x_16);
x_23 = l_Lean_RArray_getImpl___redArg(x_2, x_15);
lean_dec(x_15);
x_11 = x_23;
goto block_14;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_15);
x_24 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
x_25 = lean_apply_1(x_7, x_24);
x_11 = x_25;
goto block_14;
}
block_14:
{
lean_object* x_12; 
lean_inc(x_6);
x_12 = lean_apply_2(x_6, x_4, x_11);
x_3 = x_10;
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_apply_1(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = lean_ctor_get(x_8, 3);
x_12 = lean_ctor_get(x_8, 5);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec_ref(x_9);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_dec_eq(x_14, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_RArray_getImpl___redArg(x_2, x_13);
lean_dec(x_13);
lean_inc(x_12);
x_20 = lean_apply_2(x_12, x_19, x_14);
x_21 = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(x_1, x_2, x_10, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
x_22 = l_Lean_RArray_getImpl___redArg(x_2, x_13);
lean_dec(x_13);
x_23 = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(x_1, x_2, x_10, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
lean_dec(x_13);
x_24 = lean_unsigned_to_nat(1u);
lean_inc(x_11);
x_25 = lean_apply_1(x_11, x_24);
x_26 = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(x_1, x_2, x_10, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Mon_denoteAsIntModule(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc_ref(x_1);
x_4 = l_Lean_Grind_Ring_toIntModule___redArg(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_5, 3);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_apply_1(x_7, x_9);
x_11 = lean_apply_2(x_6, x_8, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_13);
lean_dec_ref(x_4);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
x_18 = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(x_1, x_2, x_16);
x_19 = lean_apply_2(x_13, x_15, x_18);
x_20 = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(x_1, x_2, x_17);
x_21 = lean_apply_2(x_14, x_19, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_CommRing_Poly_denoteAsIntModule(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__gcd__cert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_int_mul(x_1, x_6);
x_10 = lean_int_mul(x_2, x_7);
x_11 = lean_int_add(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_int_dec_eq(x_8, x_11);
lean_dec(x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__gcd__cert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_Grind_CommRing_eq__gcd__cert(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_3(x_2, x_6, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_Field(uint8_t builtin);
lean_object* initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* initialize_Init_GrindInstances_Ring_Int(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Ring_CommSolver(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Field(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_Ring_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0 = _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1 = _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1);
l_Lean_Grind_CommRing_instInhabitedExpr_default = _init_l_Lean_Grind_CommRing_instInhabitedExpr_default();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedExpr_default);
l_Lean_Grind_CommRing_instInhabitedExpr = _init_l_Lean_Grind_CommRing_instInhabitedExpr();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedExpr);
l_Lean_Grind_CommRing_instBEqExpr___closed__0 = _init_l_Lean_Grind_CommRing_instBEqExpr___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instBEqExpr___closed__0);
l_Lean_Grind_CommRing_instBEqExpr = _init_l_Lean_Grind_CommRing_instBEqExpr();
lean_mark_persistent(l_Lean_Grind_CommRing_instBEqExpr);
l_Lean_Grind_CommRing_instHashableExpr___closed__0 = _init_l_Lean_Grind_CommRing_instHashableExpr___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instHashableExpr___closed__0);
l_Lean_Grind_CommRing_instHashableExpr = _init_l_Lean_Grind_CommRing_instHashableExpr();
lean_mark_persistent(l_Lean_Grind_CommRing_instHashableExpr);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__0 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__0);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__1 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__1();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__1);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__2 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__2();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__2);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__3 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__4 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__5 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__5();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__5);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__6 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__6();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__6);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__7 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__7();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__7);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__8 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__8();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__8);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__9 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__9();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__9);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__10 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__10();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__10);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__11 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__11();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__11);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__12 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__12();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__12);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__13 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__13();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__13);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__14 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__14();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__14);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__15 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__15();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__15);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__16 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__16();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__16);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__17 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__17();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__17);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__18 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__18();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__18);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__19 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__19();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__19);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__20 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__20();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__20);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__21 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__21();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__21);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__22 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__22();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__22);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__23 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__23();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__23);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__24 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__24();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__24);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__25 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__25();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__25);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__26 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__26();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__26);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__27 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__27();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__27);
l_Lean_Grind_CommRing_instReprExpr_repr___closed__28 = _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__28();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr_repr___closed__28);
l_Lean_Grind_CommRing_instReprExpr___closed__0 = _init_l_Lean_Grind_CommRing_instReprExpr___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr___closed__0);
l_Lean_Grind_CommRing_instReprExpr = _init_l_Lean_Grind_CommRing_instReprExpr();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprExpr);
l_Lean_Grind_CommRing_instBEqPower___closed__0 = _init_l_Lean_Grind_CommRing_instBEqPower___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instBEqPower___closed__0);
l_Lean_Grind_CommRing_instBEqPower = _init_l_Lean_Grind_CommRing_instBEqPower();
lean_mark_persistent(l_Lean_Grind_CommRing_instBEqPower);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15);
l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16 = _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16);
l_Lean_Grind_CommRing_instReprPower___closed__0 = _init_l_Lean_Grind_CommRing_instReprPower___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower___closed__0);
l_Lean_Grind_CommRing_instReprPower = _init_l_Lean_Grind_CommRing_instReprPower();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPower);
l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0 = _init_l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0);
l_Lean_Grind_CommRing_instInhabitedPower_default = _init_l_Lean_Grind_CommRing_instInhabitedPower_default();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPower_default);
l_Lean_Grind_CommRing_instInhabitedPower = _init_l_Lean_Grind_CommRing_instInhabitedPower();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPower);
l_Lean_Grind_CommRing_instHashablePower___closed__0 = _init_l_Lean_Grind_CommRing_instHashablePower___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instHashablePower___closed__0);
l_Lean_Grind_CommRing_instHashablePower = _init_l_Lean_Grind_CommRing_instHashablePower();
lean_mark_persistent(l_Lean_Grind_CommRing_instHashablePower);
l_Lean_Grind_CommRing_instBEqMon___closed__0 = _init_l_Lean_Grind_CommRing_instBEqMon___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instBEqMon___closed__0);
l_Lean_Grind_CommRing_instBEqMon = _init_l_Lean_Grind_CommRing_instBEqMon();
lean_mark_persistent(l_Lean_Grind_CommRing_instBEqMon);
l_Lean_Grind_CommRing_instReprMon_repr___closed__0 = _init_l_Lean_Grind_CommRing_instReprMon_repr___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprMon_repr___closed__0);
l_Lean_Grind_CommRing_instReprMon_repr___closed__1 = _init_l_Lean_Grind_CommRing_instReprMon_repr___closed__1();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprMon_repr___closed__1);
l_Lean_Grind_CommRing_instReprMon_repr___closed__2 = _init_l_Lean_Grind_CommRing_instReprMon_repr___closed__2();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprMon_repr___closed__2);
l_Lean_Grind_CommRing_instReprMon_repr___closed__3 = _init_l_Lean_Grind_CommRing_instReprMon_repr___closed__3();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprMon_repr___closed__3);
l_Lean_Grind_CommRing_instReprMon_repr___closed__4 = _init_l_Lean_Grind_CommRing_instReprMon_repr___closed__4();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprMon_repr___closed__4);
l_Lean_Grind_CommRing_instReprMon___closed__0 = _init_l_Lean_Grind_CommRing_instReprMon___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprMon___closed__0);
l_Lean_Grind_CommRing_instReprMon = _init_l_Lean_Grind_CommRing_instReprMon();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprMon);
l_Lean_Grind_CommRing_instInhabitedMon_default = _init_l_Lean_Grind_CommRing_instInhabitedMon_default();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedMon_default);
l_Lean_Grind_CommRing_instInhabitedMon = _init_l_Lean_Grind_CommRing_instInhabitedMon();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedMon);
l_Lean_Grind_CommRing_instHashableMon___closed__0 = _init_l_Lean_Grind_CommRing_instHashableMon___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instHashableMon___closed__0);
l_Lean_Grind_CommRing_instHashableMon = _init_l_Lean_Grind_CommRing_instHashableMon();
lean_mark_persistent(l_Lean_Grind_CommRing_instHashableMon);
l_Lean_Grind_CommRing_hugeFuel = _init_l_Lean_Grind_CommRing_hugeFuel();
lean_mark_persistent(l_Lean_Grind_CommRing_hugeFuel);
l_Lean_Grind_CommRing_instBEqPoly___closed__0 = _init_l_Lean_Grind_CommRing_instBEqPoly___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instBEqPoly___closed__0);
l_Lean_Grind_CommRing_instBEqPoly = _init_l_Lean_Grind_CommRing_instBEqPoly();
lean_mark_persistent(l_Lean_Grind_CommRing_instBEqPoly);
l_Lean_Grind_CommRing_instReprPoly_repr___closed__0 = _init_l_Lean_Grind_CommRing_instReprPoly_repr___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPoly_repr___closed__0);
l_Lean_Grind_CommRing_instReprPoly_repr___closed__1 = _init_l_Lean_Grind_CommRing_instReprPoly_repr___closed__1();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPoly_repr___closed__1);
l_Lean_Grind_CommRing_instReprPoly_repr___closed__2 = _init_l_Lean_Grind_CommRing_instReprPoly_repr___closed__2();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPoly_repr___closed__2);
l_Lean_Grind_CommRing_instReprPoly_repr___closed__3 = _init_l_Lean_Grind_CommRing_instReprPoly_repr___closed__3();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPoly_repr___closed__3);
l_Lean_Grind_CommRing_instReprPoly_repr___closed__4 = _init_l_Lean_Grind_CommRing_instReprPoly_repr___closed__4();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPoly_repr___closed__4);
l_Lean_Grind_CommRing_instReprPoly_repr___closed__5 = _init_l_Lean_Grind_CommRing_instReprPoly_repr___closed__5();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPoly_repr___closed__5);
l_Lean_Grind_CommRing_instReprPoly___closed__0 = _init_l_Lean_Grind_CommRing_instReprPoly___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPoly___closed__0);
l_Lean_Grind_CommRing_instReprPoly = _init_l_Lean_Grind_CommRing_instReprPoly();
lean_mark_persistent(l_Lean_Grind_CommRing_instReprPoly);
l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0 = _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
l_Lean_Grind_CommRing_instInhabitedPoly_default = _init_l_Lean_Grind_CommRing_instInhabitedPoly_default();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPoly_default);
l_Lean_Grind_CommRing_instInhabitedPoly = _init_l_Lean_Grind_CommRing_instInhabitedPoly();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPoly);
l_Lean_Grind_CommRing_instHashablePoly___closed__0 = _init_l_Lean_Grind_CommRing_instHashablePoly___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_instHashablePoly___closed__0);
l_Lean_Grind_CommRing_instHashablePoly = _init_l_Lean_Grind_CommRing_instHashablePoly();
lean_mark_persistent(l_Lean_Grind_CommRing_instHashablePoly);
l_Lean_Grind_CommRing_Poly_pow___closed__0 = _init_l_Lean_Grind_CommRing_Poly_pow___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_Poly_pow___closed__0);
l_Lean_Grind_CommRing_Expr_toPoly___closed__0 = _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
