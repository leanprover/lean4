// Lean compiler output
// Module: Init.Grind.Ordered.Linarith
// Imports: public import Init.Grind.Ordered.Ring public import Init.Grind.Ring.Field import all Init.Data.Ord.Basic import all Init.Data.AC import Init.LawfulBEqTactics public import Init.Data.Bool public import Init.Data.RArray import Init.Data.Int.DivMod.Lemmas import Init.Data.Nat.Lemmas import Init.Grind.Ordered.Order import Init.Omega import Init.WFTactics import Init.Data.Int.Repr
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Grind_IntModule_toNatModule___redArg(lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_zero_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_zero_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_sub_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_sub_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_neg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_neg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_natMul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_natMul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_intMul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_intMul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instInhabitedExpr_default;
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instInhabitedExpr;
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_instBEqExpr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instBEqExpr_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_Linarith_instBEqExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_Linarith_instBEqExpr_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Linarith_instBEqExpr___closed__0 = (const lean_object*)&l_Lean_Grind_Linarith_instBEqExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Linarith_instBEqExpr = (const lean_object*)&l_Lean_Grind_Linarith_instBEqExpr___closed__0_value;
static const lean_string_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Grind.Linarith.Expr.zero"};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__0 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__0_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__0_value)}};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__1 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__1_value;
static lean_once_cell_t l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__2;
static lean_once_cell_t l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__3;
static const lean_string_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.Linarith.Expr.var"};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__4 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__4_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__4_value)}};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__5 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__5_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__6 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__6_value;
static const lean_string_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.Linarith.Expr.add"};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__7 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__7_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__7_value)}};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__8 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__8_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__9 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__9_value;
static const lean_string_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.Linarith.Expr.sub"};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__10 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__10_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__10_value)}};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__11 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__11_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__12 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__12_value;
static const lean_string_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.Linarith.Expr.neg"};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__13 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__13_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__13_value)}};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__14 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__14_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__14_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__15 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__15_value;
static const lean_string_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Grind.Linarith.Expr.natMul"};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__16 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__16_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__16_value)}};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__17 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__17_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__17_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__18 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__18_value;
static const lean_string_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Grind.Linarith.Expr.intMul"};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__19 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__19_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__19_value)}};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__20 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__20_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprExpr_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__20_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__21 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr_repr___closed__21_value;
static lean_once_cell_t l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___closed__22;
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprExpr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_Linarith_instReprExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_Linarith_instReprExpr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Linarith_instReprExpr___closed__0 = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Linarith_instReprExpr = (const lean_object*)&l_Lean_Grind_Linarith_instReprExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_nil_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_nil_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_instBEqPoly_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instBEqPoly_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_Linarith_instBEqPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_Linarith_instBEqPoly_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Linarith_instBEqPoly___closed__0 = (const lean_object*)&l_Lean_Grind_Linarith_instBEqPoly___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Linarith_instBEqPoly = (const lean_object*)&l_Lean_Grind_Linarith_instBEqPoly___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_Linarith_instReprPoly_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.Linarith.Poly.nil"};
static const lean_object* l_Lean_Grind_Linarith_instReprPoly_repr___closed__0 = (const lean_object*)&l_Lean_Grind_Linarith_instReprPoly_repr___closed__0_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprPoly_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprPoly_repr___closed__0_value)}};
static const lean_object* l_Lean_Grind_Linarith_instReprPoly_repr___closed__1 = (const lean_object*)&l_Lean_Grind_Linarith_instReprPoly_repr___closed__1_value;
static const lean_string_object l_Lean_Grind_Linarith_instReprPoly_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.Linarith.Poly.add"};
static const lean_object* l_Lean_Grind_Linarith_instReprPoly_repr___closed__2 = (const lean_object*)&l_Lean_Grind_Linarith_instReprPoly_repr___closed__2_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprPoly_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprPoly_repr___closed__2_value)}};
static const lean_object* l_Lean_Grind_Linarith_instReprPoly_repr___closed__3 = (const lean_object*)&l_Lean_Grind_Linarith_instReprPoly_repr___closed__3_value;
static const lean_ctor_object l_Lean_Grind_Linarith_instReprPoly_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_Linarith_instReprPoly_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_Linarith_instReprPoly_repr___closed__4 = (const lean_object*)&l_Lean_Grind_Linarith_instReprPoly_repr___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprPoly_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprPoly_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_Linarith_instReprPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_Linarith_instReprPoly_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Linarith_instReprPoly___closed__0 = (const lean_object*)&l_Lean_Grind_Linarith_instReprPoly___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Linarith_instReprPoly = (const lean_object*)&l_Lean_Grind_Linarith_instReprPoly___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_coeff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_coeff___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_append___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Expr_toPoly_x27_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPoly_x27_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPoly_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_leadCoeff(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_leadCoeff___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_le__le__combine__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_le__le__combine__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_le__lt__combine__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_le__lt__combine__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_lt__lt__combine__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_lt__lt__combine__cert___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Linarith_diseq__split__cert___closed__0;
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_diseq__split__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_diseq__split__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_norm__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_norm__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__of__le__ge__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__of__le__ge__cert___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0;
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_zero__lt__one__cert(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__lt__one__cert___boxed(lean_object*);
static lean_once_cell_t l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0;
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_zero__ne__one__cert(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__ne__one__cert___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__neg__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__neg__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__coeff__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__coeff__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_coeff__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_coeff__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__diseq__subst__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__diseq__subst__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__diseq__subst1__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__diseq__subst1__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__le__subst__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__le__subst__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__lt__subst__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__lt__subst__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__eq__subst__cert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__eq__subst__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_imp__eq__cert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_imp__eq__cert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
default: 
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorIdx___boxed(lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Grind_Linarith_Expr_ctorIdx(v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
switch(lean_obj_tag(v_t_11_))
{
case 0:
{
return v_k_12_;
}
case 1:
{
lean_object* v_i_13_; lean_object* v___x_14_; 
v_i_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_i_13_);
lean_dec_ref_known(v_t_11_, 1);
v___x_14_ = lean_apply_1(v_k_12_, v_i_13_);
return v___x_14_;
}
case 4:
{
lean_object* v_a_15_; lean_object* v___x_16_; 
v_a_15_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_15_);
lean_dec_ref_known(v_t_11_, 1);
v___x_16_ = lean_apply_1(v_k_12_, v_a_15_);
return v___x_16_;
}
default: 
{
lean_object* v_a_17_; lean_object* v_b_18_; lean_object* v___x_19_; 
v_a_17_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_17_);
v_b_18_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_b_18_);
lean_dec(v_t_11_);
v___x_19_ = lean_apply_2(v_k_12_, v_a_17_, v_b_18_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorElim(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_22_, v_k_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorElim___boxed(lean_object* v_motive_26_, lean_object* v_ctorIdx_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Grind_Linarith_Expr_ctorElim(v_motive_26_, v_ctorIdx_27_, v_t_28_, v_h_29_, v_k_30_);
lean_dec(v_ctorIdx_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_zero_elim___redArg(lean_object* v_t_32_, lean_object* v_zero_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_32_, v_zero_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_zero_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_zero_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_36_, v_zero_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_var_elim___redArg(lean_object* v_t_40_, lean_object* v_var_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_40_, v_var_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_var_elim(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_var_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_44_, v_var_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_add_elim___redArg(lean_object* v_t_48_, lean_object* v_add_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_48_, v_add_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_add_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_add_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_52_, v_add_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_sub_elim___redArg(lean_object* v_t_56_, lean_object* v_sub_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_56_, v_sub_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_sub_elim(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_sub_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_60_, v_sub_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_neg_elim___redArg(lean_object* v_t_64_, lean_object* v_neg_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_64_, v_neg_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_neg_elim(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_neg_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_68_, v_neg_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_natMul_elim___redArg(lean_object* v_t_72_, lean_object* v_natMul_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_72_, v_natMul_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_natMul_elim(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_natMul_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_76_, v_natMul_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_intMul_elim___redArg(lean_object* v_t_80_, lean_object* v_intMul_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_80_, v_intMul_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_intMul_elim(lean_object* v_motive_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_intMul_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_84_, v_intMul_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_instInhabitedExpr_default(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(0);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_instInhabitedExpr(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(0);
return v___x_89_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_instBEqExpr_beq(lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
lean_object* v_a_93_; lean_object* v_a_94_; lean_object* v_b_95_; lean_object* v_b_96_; 
switch(lean_obj_tag(v_x_90_))
{
case 0:
{
if (lean_obj_tag(v_x_91_) == 0)
{
uint8_t v___x_99_; 
v___x_99_ = 1;
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
}
case 1:
{
if (lean_obj_tag(v_x_91_) == 1)
{
lean_object* v_i_101_; lean_object* v_i_102_; uint8_t v___x_103_; 
v_i_101_ = lean_ctor_get(v_x_90_, 0);
v_i_102_ = lean_ctor_get(v_x_91_, 0);
v___x_103_ = lean_nat_dec_eq(v_i_101_, v_i_102_);
return v___x_103_;
}
else
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
case 2:
{
if (lean_obj_tag(v_x_91_) == 2)
{
lean_object* v_a_105_; lean_object* v_b_106_; lean_object* v_a_107_; lean_object* v_b_108_; 
v_a_105_ = lean_ctor_get(v_x_90_, 0);
v_b_106_ = lean_ctor_get(v_x_90_, 1);
v_a_107_ = lean_ctor_get(v_x_91_, 0);
v_b_108_ = lean_ctor_get(v_x_91_, 1);
v_a_93_ = v_a_105_;
v_a_94_ = v_b_106_;
v_b_95_ = v_a_107_;
v_b_96_ = v_b_108_;
goto v___jp_92_;
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
case 3:
{
if (lean_obj_tag(v_x_91_) == 3)
{
lean_object* v_a_110_; lean_object* v_b_111_; lean_object* v_a_112_; lean_object* v_b_113_; 
v_a_110_ = lean_ctor_get(v_x_90_, 0);
v_b_111_ = lean_ctor_get(v_x_90_, 1);
v_a_112_ = lean_ctor_get(v_x_91_, 0);
v_b_113_ = lean_ctor_get(v_x_91_, 1);
v_a_93_ = v_a_110_;
v_a_94_ = v_b_111_;
v_b_95_ = v_a_112_;
v_b_96_ = v_b_113_;
goto v___jp_92_;
}
else
{
uint8_t v___x_114_; 
v___x_114_ = 0;
return v___x_114_;
}
}
case 4:
{
if (lean_obj_tag(v_x_91_) == 4)
{
lean_object* v_a_115_; lean_object* v_a_116_; 
v_a_115_ = lean_ctor_get(v_x_90_, 0);
v_a_116_ = lean_ctor_get(v_x_91_, 0);
v_x_90_ = v_a_115_;
v_x_91_ = v_a_116_;
goto _start;
}
else
{
uint8_t v___x_118_; 
v___x_118_ = 0;
return v___x_118_;
}
}
case 5:
{
if (lean_obj_tag(v_x_91_) == 5)
{
lean_object* v_k_119_; lean_object* v_a_120_; lean_object* v_k_121_; lean_object* v_a_122_; uint8_t v___x_123_; 
v_k_119_ = lean_ctor_get(v_x_90_, 0);
v_a_120_ = lean_ctor_get(v_x_90_, 1);
v_k_121_ = lean_ctor_get(v_x_91_, 0);
v_a_122_ = lean_ctor_get(v_x_91_, 1);
v___x_123_ = lean_nat_dec_eq(v_k_119_, v_k_121_);
if (v___x_123_ == 0)
{
return v___x_123_;
}
else
{
v_x_90_ = v_a_120_;
v_x_91_ = v_a_122_;
goto _start;
}
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
}
default: 
{
if (lean_obj_tag(v_x_91_) == 6)
{
lean_object* v_k_126_; lean_object* v_a_127_; lean_object* v_k_128_; lean_object* v_a_129_; uint8_t v___x_130_; 
v_k_126_ = lean_ctor_get(v_x_90_, 0);
v_a_127_ = lean_ctor_get(v_x_90_, 1);
v_k_128_ = lean_ctor_get(v_x_91_, 0);
v_a_129_ = lean_ctor_get(v_x_91_, 1);
v___x_130_ = lean_int_dec_eq(v_k_126_, v_k_128_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
v_x_90_ = v_a_127_;
v_x_91_ = v_a_129_;
goto _start;
}
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
}
}
v___jp_92_:
{
uint8_t v___x_97_; 
v___x_97_ = l_Lean_Grind_Linarith_instBEqExpr_beq(v_a_93_, v_b_95_);
if (v___x_97_ == 0)
{
return v___x_97_;
}
else
{
v_x_90_ = v_a_94_;
v_x_91_ = v_b_96_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instBEqExpr_beq___boxed(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Lean_Grind_Linarith_instBEqExpr_beq(v_x_133_, v_x_134_);
lean_dec(v_x_134_);
lean_dec(v_x_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(2u);
v___x_143_ = lean_nat_to_int(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_nat_to_int(v___x_144_);
return v___x_145_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_nat_to_int(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprExpr_repr(lean_object* v_x_184_, lean_object* v_prec_185_){
_start:
{
lean_object* v___y_187_; 
switch(lean_obj_tag(v_x_184_))
{
case 0:
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(1024u);
v___x_194_ = lean_nat_dec_le(v___x_193_, v_prec_185_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_187_ = v___x_195_;
goto v___jp_186_;
}
else
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_187_ = v___x_196_;
goto v___jp_186_;
}
}
case 1:
{
lean_object* v_i_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_217_; 
v_i_197_ = lean_ctor_get(v_x_184_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_217_ == 0)
{
v___x_199_ = v_x_184_;
v_isShared_200_ = v_isSharedCheck_217_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_i_197_);
lean_dec(v_x_184_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_217_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___y_202_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(1024u);
v___x_214_ = lean_nat_dec_le(v___x_213_, v_prec_185_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_202_ = v___x_215_;
goto v___jp_201_;
}
else
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_202_ = v___x_216_;
goto v___jp_201_;
}
v___jp_201_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_203_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__6));
v___x_204_ = l_Nat_reprFast(v_i_197_);
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 3);
lean_ctor_set(v___x_199_, 0, v___x_204_);
v___x_206_ = v___x_199_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_212_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_203_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_inc(v___y_202_);
v___x_208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_208_, 0, v___y_202_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_209_);
v___x_211_ = l_Repr_addAppParen(v___x_210_, v_prec_185_);
return v___x_211_;
}
}
}
}
case 2:
{
lean_object* v_a_218_; lean_object* v_b_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_242_; 
v_a_218_ = lean_ctor_get(v_x_184_, 0);
v_b_219_ = lean_ctor_get(v_x_184_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_242_ == 0)
{
v___x_221_ = v_x_184_;
v_isShared_222_ = v_isSharedCheck_242_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_b_219_);
lean_inc(v_a_218_);
lean_dec(v_x_184_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_242_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___y_225_; uint8_t v___x_239_; 
v___x_223_ = lean_unsigned_to_nat(1024u);
v___x_239_ = lean_nat_dec_le(v___x_223_, v_prec_185_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_225_ = v___x_240_;
goto v___jp_224_;
}
else
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_225_ = v___x_241_;
goto v___jp_224_;
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_226_ = lean_box(1);
v___x_227_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__9));
v___x_228_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_218_, v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set_tag(v___x_221_, 5);
lean_ctor_set(v___x_221_, 1, v___x_228_);
lean_ctor_set(v___x_221_, 0, v___x_227_);
v___x_230_ = v___x_221_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_228_);
v___x_230_ = v_reuseFailAlloc_238_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_226_);
v___x_232_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_b_219_, v___x_223_);
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
lean_inc(v___y_225_);
v___x_234_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_234_, 0, v___y_225_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = 0;
v___x_236_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*1, v___x_235_);
v___x_237_ = l_Repr_addAppParen(v___x_236_, v_prec_185_);
return v___x_237_;
}
}
}
}
case 3:
{
lean_object* v_a_243_; lean_object* v_b_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_267_; 
v_a_243_ = lean_ctor_get(v_x_184_, 0);
v_b_244_ = lean_ctor_get(v_x_184_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_267_ == 0)
{
v___x_246_ = v_x_184_;
v_isShared_247_ = v_isSharedCheck_267_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_b_244_);
lean_inc(v_a_243_);
lean_dec(v_x_184_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_267_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___y_250_; uint8_t v___x_264_; 
v___x_248_ = lean_unsigned_to_nat(1024u);
v___x_264_ = lean_nat_dec_le(v___x_248_, v_prec_185_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_250_ = v___x_265_;
goto v___jp_249_;
}
else
{
lean_object* v___x_266_; 
v___x_266_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_250_ = v___x_266_;
goto v___jp_249_;
}
v___jp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_251_ = lean_box(1);
v___x_252_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__12));
v___x_253_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_243_, v___x_248_);
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 5);
lean_ctor_set(v___x_246_, 1, v___x_253_);
lean_ctor_set(v___x_246_, 0, v___x_252_);
v___x_255_ = v___x_246_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_253_);
v___x_255_ = v_reuseFailAlloc_263_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___x_251_);
v___x_257_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_b_244_, v___x_248_);
v___x_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
lean_inc(v___y_250_);
v___x_259_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_259_, 0, v___y_250_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = 0;
v___x_261_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set_uint8(v___x_261_, sizeof(void*)*1, v___x_260_);
v___x_262_ = l_Repr_addAppParen(v___x_261_, v_prec_185_);
return v___x_262_;
}
}
}
}
case 4:
{
lean_object* v_a_268_; lean_object* v___x_269_; lean_object* v___y_271_; uint8_t v___x_279_; 
v_a_268_ = lean_ctor_get(v_x_184_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v_x_184_, 1);
v___x_269_ = lean_unsigned_to_nat(1024u);
v___x_279_ = lean_nat_dec_le(v___x_269_, v_prec_185_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_271_ = v___x_280_;
goto v___jp_270_;
}
else
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_271_ = v___x_281_;
goto v___jp_270_;
}
v___jp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_272_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__15));
v___x_273_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_268_, v___x_269_);
v___x_274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
lean_inc(v___y_271_);
v___x_275_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_275_, 0, v___y_271_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = 0;
v___x_277_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*1, v___x_276_);
v___x_278_ = l_Repr_addAppParen(v___x_277_, v_prec_185_);
return v___x_278_;
}
}
case 5:
{
lean_object* v_k_282_; lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_307_; 
v_k_282_ = lean_ctor_get(v_x_184_, 0);
v_a_283_ = lean_ctor_get(v_x_184_, 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_307_ == 0)
{
v___x_285_ = v_x_184_;
v_isShared_286_ = v_isSharedCheck_307_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_inc(v_k_282_);
lean_dec(v_x_184_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_307_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v___y_289_; uint8_t v___x_304_; 
v___x_287_ = lean_unsigned_to_nat(1024u);
v___x_304_ = lean_nat_dec_le(v___x_287_, v_prec_185_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_289_ = v___x_305_;
goto v___jp_288_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_289_ = v___x_306_;
goto v___jp_288_;
}
v___jp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_290_ = lean_box(1);
v___x_291_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__18));
v___x_292_ = l_Nat_reprFast(v_k_282_);
v___x_293_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v___x_293_);
lean_ctor_set(v___x_285_, 0, v___x_291_);
v___x_295_ = v___x_285_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_303_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_290_);
v___x_297_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_283_, v___x_287_);
v___x_298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
lean_inc(v___y_289_);
v___x_299_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_299_, 0, v___y_289_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = 0;
v___x_301_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*1, v___x_300_);
v___x_302_ = l_Repr_addAppParen(v___x_301_, v_prec_185_);
return v___x_302_;
}
}
}
}
default: 
{
lean_object* v_k_308_; lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_343_; 
v_k_308_ = lean_ctor_get(v_x_184_, 0);
v_a_309_ = lean_ctor_get(v_x_184_, 1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_343_ == 0)
{
v___x_311_ = v_x_184_;
v_isShared_312_ = v_isSharedCheck_343_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_inc(v_k_308_);
lean_dec(v_x_184_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_343_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_330_; uint8_t v___x_340_; 
v___x_313_ = lean_unsigned_to_nat(1024u);
v___x_340_ = lean_nat_dec_le(v___x_313_, v_prec_185_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
v___x_341_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_330_ = v___x_341_;
goto v___jp_329_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_330_ = v___x_342_;
goto v___jp_329_;
}
v___jp_314_:
{
lean_object* v___x_320_; 
lean_inc(v___y_316_);
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 5);
lean_ctor_set(v___x_311_, 1, v___y_318_);
lean_ctor_set(v___x_311_, 0, v___y_316_);
v___x_320_ = v___x_311_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___y_316_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___y_318_);
v___x_320_ = v_reuseFailAlloc_328_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
lean_inc(v___y_317_);
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___y_317_);
v___x_322_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_309_, v___x_313_);
v___x_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
lean_inc(v___y_315_);
v___x_324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_324_, 0, v___y_315_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = 0;
v___x_326_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*1, v___x_325_);
v___x_327_ = l_Repr_addAppParen(v___x_326_, v_prec_185_);
return v___x_327_;
}
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_331_ = lean_box(1);
v___x_332_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__21));
v___x_333_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_334_ = lean_int_dec_lt(v_k_308_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = l_Int_repr(v_k_308_);
lean_dec(v_k_308_);
v___x_336_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
v___y_315_ = v___y_330_;
v___y_316_ = v___x_332_;
v___y_317_ = v___x_331_;
v___y_318_ = v___x_336_;
goto v___jp_314_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = l_Int_repr(v_k_308_);
lean_dec(v_k_308_);
v___x_338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
v___x_339_ = l_Repr_addAppParen(v___x_338_, v___x_313_);
v___y_315_ = v___y_330_;
v___y_316_ = v___x_332_;
v___y_317_ = v___x_331_;
v___y_318_ = v___x_339_;
goto v___jp_314_;
}
}
}
}
}
v___jp_186_:
{
lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_188_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__1));
lean_inc(v___y_187_);
v___x_189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_189_, 0, v___y_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = 0;
v___x_191_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*1, v___x_190_);
v___x_192_ = l_Repr_addAppParen(v___x_191_, v_prec_185_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___boxed(lean_object* v_x_344_, lean_object* v_prec_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_x_344_, v_prec_345_);
lean_dec(v_prec_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote___redArg(lean_object* v_ctx_349_, lean_object* v_v_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_RArray_getImpl___redArg(v_ctx_349_, v_v_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote___redArg___boxed(lean_object* v_ctx_352_, lean_object* v_v_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Grind_Linarith_Var_denote___redArg(v_ctx_352_, v_v_353_);
lean_dec(v_v_353_);
lean_dec_ref(v_ctx_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote(lean_object* v_00_u03b1_355_, lean_object* v_ctx_356_, lean_object* v_v_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_RArray_getImpl___redArg(v_ctx_356_, v_v_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote___boxed(lean_object* v_00_u03b1_359_, lean_object* v_ctx_360_, lean_object* v_v_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Grind_Linarith_Var_denote(v_00_u03b1_359_, v_ctx_360_, v_v_361_);
lean_dec(v_v_361_);
lean_dec_ref(v_ctx_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___redArg(lean_object* v_inst_363_, lean_object* v_ctx_364_, lean_object* v_x_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_363_);
switch(lean_obj_tag(v_x_365_))
{
case 0:
{
lean_object* v_toAddCommMonoid_367_; lean_object* v_toZero_368_; 
v_toAddCommMonoid_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc_ref(v_toAddCommMonoid_367_);
lean_dec_ref(v___x_366_);
lean_dec_ref(v_inst_363_);
v_toZero_368_ = lean_ctor_get(v_toAddCommMonoid_367_, 0);
lean_inc(v_toZero_368_);
lean_dec_ref(v_toAddCommMonoid_367_);
return v_toZero_368_;
}
case 1:
{
lean_object* v_i_369_; lean_object* v___x_370_; 
lean_dec_ref(v___x_366_);
lean_dec_ref(v_inst_363_);
v_i_369_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_i_369_);
lean_dec_ref_known(v_x_365_, 1);
v___x_370_ = l_Lean_RArray_getImpl___redArg(v_ctx_364_, v_i_369_);
lean_dec(v_i_369_);
return v___x_370_;
}
case 2:
{
lean_object* v_toAddCommMonoid_371_; lean_object* v_toAdd_372_; lean_object* v_a_373_; lean_object* v_b_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_toAddCommMonoid_371_ = lean_ctor_get(v___x_366_, 0);
lean_inc_ref(v_toAddCommMonoid_371_);
lean_dec_ref(v___x_366_);
v_toAdd_372_ = lean_ctor_get(v_toAddCommMonoid_371_, 1);
lean_inc(v_toAdd_372_);
lean_dec_ref(v_toAddCommMonoid_371_);
v_a_373_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_a_373_);
v_b_374_ = lean_ctor_get(v_x_365_, 1);
lean_inc(v_b_374_);
lean_dec_ref_known(v_x_365_, 2);
lean_inc_ref(v_inst_363_);
v___x_375_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_a_373_);
v___x_376_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_b_374_);
v___x_377_ = lean_apply_2(v_toAdd_372_, v___x_375_, v___x_376_);
return v___x_377_;
}
case 3:
{
lean_object* v_toAddCommGroup_378_; lean_object* v_toSub_379_; lean_object* v_a_380_; lean_object* v_b_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_toAddCommGroup_378_ = lean_ctor_get(v_inst_363_, 0);
lean_dec_ref(v___x_366_);
v_toSub_379_ = lean_ctor_get(v_toAddCommGroup_378_, 2);
lean_inc(v_toSub_379_);
v_a_380_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_a_380_);
v_b_381_ = lean_ctor_get(v_x_365_, 1);
lean_inc(v_b_381_);
lean_dec_ref_known(v_x_365_, 2);
lean_inc_ref(v_inst_363_);
v___x_382_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_a_380_);
v___x_383_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_b_381_);
v___x_384_ = lean_apply_2(v_toSub_379_, v___x_382_, v___x_383_);
return v___x_384_;
}
case 4:
{
lean_object* v_toAddCommGroup_385_; lean_object* v_toNeg_386_; lean_object* v_a_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_toAddCommGroup_385_ = lean_ctor_get(v_inst_363_, 0);
lean_dec_ref(v___x_366_);
v_toNeg_386_ = lean_ctor_get(v_toAddCommGroup_385_, 1);
lean_inc(v_toNeg_386_);
v_a_387_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v_x_365_, 1);
v___x_388_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_a_387_);
v___x_389_ = lean_apply_1(v_toNeg_386_, v___x_388_);
return v___x_389_;
}
case 5:
{
lean_object* v_nsmul_390_; lean_object* v_k_391_; lean_object* v_a_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_nsmul_390_ = lean_ctor_get(v___x_366_, 1);
lean_inc(v_nsmul_390_);
lean_dec_ref(v___x_366_);
v_k_391_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_k_391_);
v_a_392_ = lean_ctor_get(v_x_365_, 1);
lean_inc(v_a_392_);
lean_dec_ref_known(v_x_365_, 2);
v___x_393_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_a_392_);
v___x_394_ = lean_apply_2(v_nsmul_390_, v_k_391_, v___x_393_);
return v___x_394_;
}
default: 
{
lean_object* v_zsmul_395_; lean_object* v_k_396_; lean_object* v_a_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec_ref(v___x_366_);
v_zsmul_395_ = lean_ctor_get(v_inst_363_, 2);
lean_inc(v_zsmul_395_);
v_k_396_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_k_396_);
v_a_397_ = lean_ctor_get(v_x_365_, 1);
lean_inc(v_a_397_);
lean_dec_ref_known(v_x_365_, 2);
v___x_398_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_a_397_);
v___x_399_ = lean_apply_2(v_zsmul_395_, v_k_396_, v___x_398_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___redArg___boxed(lean_object* v_inst_400_, lean_object* v_ctx_401_, lean_object* v_x_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_400_, v_ctx_401_, v_x_402_);
lean_dec_ref(v_ctx_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote(lean_object* v_00_u03b1_404_, lean_object* v_inst_405_, lean_object* v_ctx_406_, lean_object* v_x_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_405_, v_ctx_406_, v_x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___boxed(lean_object* v_00_u03b1_409_, lean_object* v_inst_410_, lean_object* v_ctx_411_, lean_object* v_x_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Grind_Linarith_Expr_denote(v_00_u03b1_409_, v_inst_410_, v_ctx_411_, v_x_412_);
lean_dec_ref(v_ctx_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorIdx(lean_object* v_x_414_){
_start:
{
if (lean_obj_tag(v_x_414_) == 0)
{
lean_object* v___x_415_; 
v___x_415_ = lean_unsigned_to_nat(0u);
return v___x_415_;
}
else
{
lean_object* v___x_416_; 
v___x_416_ = lean_unsigned_to_nat(1u);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorIdx___boxed(lean_object* v_x_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Grind_Linarith_Poly_ctorIdx(v_x_417_);
lean_dec(v_x_417_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim___redArg(lean_object* v_t_419_, lean_object* v_k_420_){
_start:
{
if (lean_obj_tag(v_t_419_) == 0)
{
return v_k_420_;
}
else
{
lean_object* v_k_421_; lean_object* v_v_422_; lean_object* v_p_423_; lean_object* v___x_424_; 
v_k_421_ = lean_ctor_get(v_t_419_, 0);
lean_inc(v_k_421_);
v_v_422_ = lean_ctor_get(v_t_419_, 1);
lean_inc(v_v_422_);
v_p_423_ = lean_ctor_get(v_t_419_, 2);
lean_inc(v_p_423_);
lean_dec_ref_known(v_t_419_, 3);
v___x_424_ = lean_apply_3(v_k_420_, v_k_421_, v_v_422_, v_p_423_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim(lean_object* v_motive_425_, lean_object* v_ctorIdx_426_, lean_object* v_t_427_, lean_object* v_h_428_, lean_object* v_k_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_427_, v_k_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim___boxed(lean_object* v_motive_431_, lean_object* v_ctorIdx_432_, lean_object* v_t_433_, lean_object* v_h_434_, lean_object* v_k_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Grind_Linarith_Poly_ctorElim(v_motive_431_, v_ctorIdx_432_, v_t_433_, v_h_434_, v_k_435_);
lean_dec(v_ctorIdx_432_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_nil_elim___redArg(lean_object* v_t_437_, lean_object* v_nil_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_437_, v_nil_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_nil_elim(lean_object* v_motive_440_, lean_object* v_t_441_, lean_object* v_h_442_, lean_object* v_nil_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_441_, v_nil_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_add_elim___redArg(lean_object* v_t_445_, lean_object* v_add_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_445_, v_add_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_add_elim(lean_object* v_motive_448_, lean_object* v_t_449_, lean_object* v_h_450_, lean_object* v_add_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_449_, v_add_451_);
return v___x_452_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_instBEqPoly_beq(lean_object* v_x_453_, lean_object* v_x_454_){
_start:
{
if (lean_obj_tag(v_x_453_) == 0)
{
if (lean_obj_tag(v_x_454_) == 0)
{
uint8_t v___x_455_; 
v___x_455_ = 1;
return v___x_455_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 0;
return v___x_456_;
}
}
else
{
if (lean_obj_tag(v_x_454_) == 1)
{
lean_object* v_k_457_; lean_object* v_v_458_; lean_object* v_p_459_; lean_object* v_k_460_; lean_object* v_v_461_; lean_object* v_p_462_; uint8_t v___x_463_; 
v_k_457_ = lean_ctor_get(v_x_453_, 0);
v_v_458_ = lean_ctor_get(v_x_453_, 1);
v_p_459_ = lean_ctor_get(v_x_453_, 2);
v_k_460_ = lean_ctor_get(v_x_454_, 0);
v_v_461_ = lean_ctor_get(v_x_454_, 1);
v_p_462_ = lean_ctor_get(v_x_454_, 2);
v___x_463_ = lean_int_dec_eq(v_k_457_, v_k_460_);
if (v___x_463_ == 0)
{
return v___x_463_;
}
else
{
uint8_t v___x_464_; 
v___x_464_ = lean_nat_dec_eq(v_v_458_, v_v_461_);
if (v___x_464_ == 0)
{
return v___x_464_;
}
else
{
v_x_453_ = v_p_459_;
v_x_454_ = v_p_462_;
goto _start;
}
}
}
else
{
uint8_t v___x_466_; 
v___x_466_ = 0;
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instBEqPoly_beq___boxed(lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_x_467_, v_x_468_);
lean_dec(v_x_468_);
lean_dec(v_x_467_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_473_, lean_object* v_x_474_, lean_object* v_h__1_475_, lean_object* v_h__2_476_, lean_object* v_h__3_477_){
_start:
{
if (lean_obj_tag(v_x_473_) == 0)
{
lean_dec(v_h__2_476_);
if (lean_obj_tag(v_x_474_) == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v_h__3_477_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_apply_1(v_h__1_475_, v___x_478_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; 
lean_dec(v_h__1_475_);
v___x_480_ = lean_apply_4(v_h__3_477_, v_x_473_, v_x_474_, lean_box(0), lean_box(0));
return v___x_480_;
}
}
else
{
lean_dec(v_h__1_475_);
if (lean_obj_tag(v_x_474_) == 1)
{
lean_object* v_k_481_; lean_object* v_v_482_; lean_object* v_p_483_; lean_object* v_k_484_; lean_object* v_v_485_; lean_object* v_p_486_; lean_object* v___x_487_; 
lean_dec(v_h__3_477_);
v_k_481_ = lean_ctor_get(v_x_473_, 0);
lean_inc(v_k_481_);
v_v_482_ = lean_ctor_get(v_x_473_, 1);
lean_inc(v_v_482_);
v_p_483_ = lean_ctor_get(v_x_473_, 2);
lean_inc(v_p_483_);
lean_dec_ref_known(v_x_473_, 3);
v_k_484_ = lean_ctor_get(v_x_474_, 0);
lean_inc(v_k_484_);
v_v_485_ = lean_ctor_get(v_x_474_, 1);
lean_inc(v_v_485_);
v_p_486_ = lean_ctor_get(v_x_474_, 2);
lean_inc(v_p_486_);
lean_dec_ref_known(v_x_474_, 3);
v___x_487_ = lean_apply_6(v_h__2_476_, v_k_481_, v_v_482_, v_p_483_, v_k_484_, v_v_485_, v_p_486_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; 
lean_dec(v_h__2_476_);
v___x_488_ = lean_apply_4(v_h__3_477_, v_x_473_, v_x_474_, lean_box(0), lean_box(0));
return v___x_488_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_489_, lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_h__1_492_, lean_object* v_h__2_493_, lean_object* v_h__3_494_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
lean_dec(v_h__2_493_);
if (lean_obj_tag(v_x_491_) == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec(v_h__3_494_);
v___x_495_ = lean_box(0);
v___x_496_ = lean_apply_1(v_h__1_492_, v___x_495_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; 
lean_dec(v_h__1_492_);
v___x_497_ = lean_apply_4(v_h__3_494_, v_x_490_, v_x_491_, lean_box(0), lean_box(0));
return v___x_497_;
}
}
else
{
lean_dec(v_h__1_492_);
if (lean_obj_tag(v_x_491_) == 1)
{
lean_object* v_k_498_; lean_object* v_v_499_; lean_object* v_p_500_; lean_object* v_k_501_; lean_object* v_v_502_; lean_object* v_p_503_; lean_object* v___x_504_; 
lean_dec(v_h__3_494_);
v_k_498_ = lean_ctor_get(v_x_490_, 0);
lean_inc(v_k_498_);
v_v_499_ = lean_ctor_get(v_x_490_, 1);
lean_inc(v_v_499_);
v_p_500_ = lean_ctor_get(v_x_490_, 2);
lean_inc(v_p_500_);
lean_dec_ref_known(v_x_490_, 3);
v_k_501_ = lean_ctor_get(v_x_491_, 0);
lean_inc(v_k_501_);
v_v_502_ = lean_ctor_get(v_x_491_, 1);
lean_inc(v_v_502_);
v_p_503_ = lean_ctor_get(v_x_491_, 2);
lean_inc(v_p_503_);
lean_dec_ref_known(v_x_491_, 3);
v___x_504_ = lean_apply_6(v_h__2_493_, v_k_498_, v_v_499_, v_p_500_, v_k_501_, v_v_502_, v_p_503_);
return v___x_504_;
}
else
{
lean_object* v___x_505_; 
lean_dec(v_h__2_493_);
v___x_505_ = lean_apply_4(v_h__3_494_, v_x_490_, v_x_491_, lean_box(0), lean_box(0));
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprPoly_repr(lean_object* v_x_515_, lean_object* v_prec_516_){
_start:
{
lean_object* v___y_518_; 
if (lean_obj_tag(v_x_515_) == 0)
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_unsigned_to_nat(1024u);
v___x_525_ = lean_nat_dec_le(v___x_524_, v_prec_516_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
v___x_526_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_518_ = v___x_526_;
goto v___jp_517_;
}
else
{
lean_object* v___x_527_; 
v___x_527_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_518_ = v___x_527_;
goto v___jp_517_;
}
}
else
{
lean_object* v_k_528_; lean_object* v_v_529_; lean_object* v_p_530_; lean_object* v___x_531_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_550_; uint8_t v___x_560_; 
v_k_528_ = lean_ctor_get(v_x_515_, 0);
lean_inc(v_k_528_);
v_v_529_ = lean_ctor_get(v_x_515_, 1);
lean_inc(v_v_529_);
v_p_530_ = lean_ctor_get(v_x_515_, 2);
lean_inc(v_p_530_);
lean_dec_ref_known(v_x_515_, 3);
v___x_531_ = lean_unsigned_to_nat(1024u);
v___x_560_ = lean_nat_dec_le(v___x_531_, v_prec_516_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_550_ = v___x_561_;
goto v___jp_549_;
}
else
{
lean_object* v___x_562_; 
v___x_562_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_550_ = v___x_562_;
goto v___jp_549_;
}
v___jp_532_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_inc(v___y_533_);
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___y_533_);
lean_ctor_set(v___x_537_, 1, v___y_536_);
lean_inc_n(v___y_534_, 2);
v___x_538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___y_534_);
v___x_539_ = l_Nat_reprFast(v_v_529_);
v___x_540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
v___x_541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_538_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___y_534_);
v___x_543_ = l_Lean_Grind_Linarith_instReprPoly_repr(v_p_530_, v___x_531_);
v___x_544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
lean_inc(v___y_535_);
v___x_545_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_545_, 0, v___y_535_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = 0;
v___x_547_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set_uint8(v___x_547_, sizeof(void*)*1, v___x_546_);
v___x_548_ = l_Repr_addAppParen(v___x_547_, v_prec_516_);
return v___x_548_;
}
v___jp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_551_ = lean_box(1);
v___x_552_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprPoly_repr___closed__4));
v___x_553_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_554_ = lean_int_dec_lt(v_k_528_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = l_Int_repr(v_k_528_);
lean_dec(v_k_528_);
v___x_556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
v___y_533_ = v___x_552_;
v___y_534_ = v___x_551_;
v___y_535_ = v___y_550_;
v___y_536_ = v___x_556_;
goto v___jp_532_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = l_Int_repr(v_k_528_);
lean_dec(v_k_528_);
v___x_558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
v___x_559_ = l_Repr_addAppParen(v___x_558_, v___x_531_);
v___y_533_ = v___x_552_;
v___y_534_ = v___x_551_;
v___y_535_ = v___y_550_;
v___y_536_ = v___x_559_;
goto v___jp_532_;
}
}
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_519_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprPoly_repr___closed__1));
lean_inc(v___y_518_);
v___x_520_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_520_, 0, v___y_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = 0;
v___x_522_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*1, v___x_521_);
v___x_523_ = l_Repr_addAppParen(v___x_522_, v_prec_516_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprPoly_repr___boxed(lean_object* v_x_563_, lean_object* v_prec_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Grind_Linarith_instReprPoly_repr(v_x_563_, v_prec_564_);
lean_dec(v_prec_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___redArg(lean_object* v_inst_568_, lean_object* v_ctx_569_, lean_object* v_p_570_){
_start:
{
lean_object* v___x_571_; lean_object* v_toAddCommMonoid_572_; 
v___x_571_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_568_);
v_toAddCommMonoid_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_toAddCommMonoid_572_);
lean_dec_ref(v___x_571_);
if (lean_obj_tag(v_p_570_) == 0)
{
lean_object* v_toZero_573_; 
lean_dec_ref(v_inst_568_);
v_toZero_573_ = lean_ctor_get(v_toAddCommMonoid_572_, 0);
lean_inc(v_toZero_573_);
lean_dec_ref(v_toAddCommMonoid_572_);
return v_toZero_573_;
}
else
{
lean_object* v_toAdd_574_; lean_object* v_zsmul_575_; lean_object* v_k_576_; lean_object* v_v_577_; lean_object* v_p_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_toAdd_574_ = lean_ctor_get(v_toAddCommMonoid_572_, 1);
lean_inc(v_toAdd_574_);
lean_dec_ref(v_toAddCommMonoid_572_);
v_zsmul_575_ = lean_ctor_get(v_inst_568_, 2);
v_k_576_ = lean_ctor_get(v_p_570_, 0);
lean_inc(v_k_576_);
v_v_577_ = lean_ctor_get(v_p_570_, 1);
lean_inc(v_v_577_);
v_p_578_ = lean_ctor_get(v_p_570_, 2);
lean_inc(v_p_578_);
lean_dec_ref_known(v_p_570_, 3);
v___x_579_ = l_Lean_RArray_getImpl___redArg(v_ctx_569_, v_v_577_);
lean_dec(v_v_577_);
lean_inc(v_zsmul_575_);
v___x_580_ = lean_apply_2(v_zsmul_575_, v_k_576_, v___x_579_);
v___x_581_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_568_, v_ctx_569_, v_p_578_);
v___x_582_ = lean_apply_2(v_toAdd_574_, v___x_580_, v___x_581_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___redArg___boxed(lean_object* v_inst_583_, lean_object* v_ctx_584_, lean_object* v_p_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_583_, v_ctx_584_, v_p_585_);
lean_dec_ref(v_ctx_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote(lean_object* v_00_u03b1_587_, lean_object* v_inst_588_, lean_object* v_ctx_589_, lean_object* v_p_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_588_, v_ctx_589_, v_p_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___boxed(lean_object* v_00_u03b1_592_, lean_object* v_inst_593_, lean_object* v_ctx_594_, lean_object* v_p_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Grind_Linarith_Poly_denote(v_00_u03b1_592_, v_inst_593_, v_ctx_594_, v_p_595_);
lean_dec_ref(v_ctx_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(lean_object* v_inst_597_, lean_object* v_ctx_598_, lean_object* v_r_599_, lean_object* v_p_600_){
_start:
{
lean_object* v___x_601_; lean_object* v_toAddCommMonoid_602_; 
v___x_601_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_597_);
v_toAddCommMonoid_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc_ref(v_toAddCommMonoid_602_);
lean_dec_ref(v___x_601_);
if (lean_obj_tag(v_p_600_) == 0)
{
lean_dec_ref(v_toAddCommMonoid_602_);
lean_dec_ref(v_inst_597_);
return v_r_599_;
}
else
{
lean_object* v_toAdd_603_; lean_object* v_zsmul_604_; lean_object* v_k_605_; lean_object* v_v_606_; lean_object* v_p_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_toAdd_603_ = lean_ctor_get(v_toAddCommMonoid_602_, 1);
lean_inc(v_toAdd_603_);
lean_dec_ref(v_toAddCommMonoid_602_);
v_zsmul_604_ = lean_ctor_get(v_inst_597_, 2);
v_k_605_ = lean_ctor_get(v_p_600_, 0);
lean_inc(v_k_605_);
v_v_606_ = lean_ctor_get(v_p_600_, 1);
lean_inc(v_v_606_);
v_p_607_ = lean_ctor_get(v_p_600_, 2);
lean_inc(v_p_607_);
lean_dec_ref_known(v_p_600_, 3);
v___x_608_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_609_ = lean_int_dec_eq(v_k_605_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = l_Lean_RArray_getImpl___redArg(v_ctx_598_, v_v_606_);
lean_dec(v_v_606_);
lean_inc(v_zsmul_604_);
v___x_611_ = lean_apply_2(v_zsmul_604_, v_k_605_, v___x_610_);
v___x_612_ = lean_apply_2(v_toAdd_603_, v_r_599_, v___x_611_);
v_r_599_ = v___x_612_;
v_p_600_ = v_p_607_;
goto _start;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec(v_k_605_);
v___x_614_ = l_Lean_RArray_getImpl___redArg(v_ctx_598_, v_v_606_);
lean_dec(v_v_606_);
v___x_615_ = lean_apply_2(v_toAdd_603_, v_r_599_, v___x_614_);
v_r_599_ = v___x_615_;
v_p_600_ = v_p_607_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg___boxed(lean_object* v_inst_617_, lean_object* v_ctx_618_, lean_object* v_r_619_, lean_object* v_p_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_617_, v_ctx_618_, v_r_619_, v_p_620_);
lean_dec_ref(v_ctx_618_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go(lean_object* v_00_u03b1_622_, lean_object* v_inst_623_, lean_object* v_ctx_624_, lean_object* v_r_625_, lean_object* v_p_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_623_, v_ctx_624_, v_r_625_, v_p_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___boxed(lean_object* v_00_u03b1_628_, lean_object* v_inst_629_, lean_object* v_ctx_630_, lean_object* v_r_631_, lean_object* v_p_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Grind_Linarith_Poly_denote_x27_go(v_00_u03b1_628_, v_inst_629_, v_ctx_630_, v_r_631_, v_p_632_);
lean_dec_ref(v_ctx_630_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___redArg(lean_object* v_inst_634_, lean_object* v_ctx_635_, lean_object* v_p_636_){
_start:
{
lean_object* v___x_637_; lean_object* v_toAddCommMonoid_638_; 
v___x_637_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_634_);
v_toAddCommMonoid_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc_ref(v_toAddCommMonoid_638_);
lean_dec_ref(v___x_637_);
if (lean_obj_tag(v_p_636_) == 0)
{
lean_object* v_toZero_639_; 
lean_dec_ref(v_inst_634_);
v_toZero_639_ = lean_ctor_get(v_toAddCommMonoid_638_, 0);
lean_inc(v_toZero_639_);
lean_dec_ref(v_toAddCommMonoid_638_);
return v_toZero_639_;
}
else
{
lean_object* v_zsmul_640_; lean_object* v_k_641_; lean_object* v_v_642_; lean_object* v_p_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
lean_dec_ref(v_toAddCommMonoid_638_);
v_zsmul_640_ = lean_ctor_get(v_inst_634_, 2);
v_k_641_ = lean_ctor_get(v_p_636_, 0);
lean_inc(v_k_641_);
v_v_642_ = lean_ctor_get(v_p_636_, 1);
lean_inc(v_v_642_);
v_p_643_ = lean_ctor_get(v_p_636_, 2);
lean_inc(v_p_643_);
lean_dec_ref_known(v_p_636_, 3);
v___x_644_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_645_ = lean_int_dec_eq(v_k_641_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = l_Lean_RArray_getImpl___redArg(v_ctx_635_, v_v_642_);
lean_dec(v_v_642_);
lean_inc(v_zsmul_640_);
v___x_647_ = lean_apply_2(v_zsmul_640_, v_k_641_, v___x_646_);
v___x_648_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_634_, v_ctx_635_, v___x_647_, v_p_643_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec(v_k_641_);
v___x_649_ = l_Lean_RArray_getImpl___redArg(v_ctx_635_, v_v_642_);
lean_dec(v_v_642_);
v___x_650_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_634_, v_ctx_635_, v___x_649_, v_p_643_);
return v___x_650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___redArg___boxed(lean_object* v_inst_651_, lean_object* v_ctx_652_, lean_object* v_p_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Grind_Linarith_Poly_denote_x27___redArg(v_inst_651_, v_ctx_652_, v_p_653_);
lean_dec_ref(v_ctx_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27(lean_object* v_00_u03b1_655_, lean_object* v_inst_656_, lean_object* v_ctx_657_, lean_object* v_p_658_){
_start:
{
lean_object* v___x_659_; lean_object* v_toAddCommMonoid_660_; 
v___x_659_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_656_);
v_toAddCommMonoid_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc_ref(v_toAddCommMonoid_660_);
lean_dec_ref(v___x_659_);
if (lean_obj_tag(v_p_658_) == 0)
{
lean_object* v_toZero_661_; 
lean_dec_ref(v_inst_656_);
v_toZero_661_ = lean_ctor_get(v_toAddCommMonoid_660_, 0);
lean_inc(v_toZero_661_);
lean_dec_ref(v_toAddCommMonoid_660_);
return v_toZero_661_;
}
else
{
lean_object* v_zsmul_662_; lean_object* v_k_663_; lean_object* v_v_664_; lean_object* v_p_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
lean_dec_ref(v_toAddCommMonoid_660_);
v_zsmul_662_ = lean_ctor_get(v_inst_656_, 2);
v_k_663_ = lean_ctor_get(v_p_658_, 0);
lean_inc(v_k_663_);
v_v_664_ = lean_ctor_get(v_p_658_, 1);
lean_inc(v_v_664_);
v_p_665_ = lean_ctor_get(v_p_658_, 2);
lean_inc(v_p_665_);
lean_dec_ref_known(v_p_658_, 3);
v___x_666_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_667_ = lean_int_dec_eq(v_k_663_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = l_Lean_RArray_getImpl___redArg(v_ctx_657_, v_v_664_);
lean_dec(v_v_664_);
lean_inc(v_zsmul_662_);
v___x_669_ = lean_apply_2(v_zsmul_662_, v_k_663_, v___x_668_);
v___x_670_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_656_, v_ctx_657_, v___x_669_, v_p_665_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v_k_663_);
v___x_671_ = l_Lean_RArray_getImpl___redArg(v_ctx_657_, v_v_664_);
lean_dec(v_v_664_);
v___x_672_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_656_, v_ctx_657_, v___x_671_, v_p_665_);
return v___x_672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___boxed(lean_object* v_00_u03b1_673_, lean_object* v_inst_674_, lean_object* v_ctx_675_, lean_object* v_p_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Grind_Linarith_Poly_denote_x27(v_00_u03b1_673_, v_inst_674_, v_ctx_675_, v_p_676_);
lean_dec_ref(v_ctx_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter___redArg(lean_object* v_p_678_, lean_object* v_h__1_679_, lean_object* v_h__2_680_, lean_object* v_h__3_681_){
_start:
{
if (lean_obj_tag(v_p_678_) == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v_h__3_681_);
lean_dec(v_h__2_680_);
v___x_682_ = lean_box(0);
v___x_683_ = lean_apply_1(v_h__1_679_, v___x_682_);
return v___x_683_;
}
else
{
lean_object* v_k_684_; lean_object* v_v_685_; lean_object* v_p_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
lean_dec(v_h__1_679_);
v_k_684_ = lean_ctor_get(v_p_678_, 0);
lean_inc(v_k_684_);
v_v_685_ = lean_ctor_get(v_p_678_, 1);
lean_inc(v_v_685_);
v_p_686_ = lean_ctor_get(v_p_678_, 2);
lean_inc(v_p_686_);
lean_dec_ref_known(v_p_678_, 3);
v___x_687_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_688_ = lean_int_dec_eq(v_k_684_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
lean_dec(v_h__2_680_);
v___x_689_ = lean_apply_4(v_h__3_681_, v_k_684_, v_v_685_, v_p_686_, lean_box(0));
return v___x_689_;
}
else
{
lean_object* v___x_690_; 
lean_dec(v_k_684_);
lean_dec(v_h__3_681_);
v___x_690_ = lean_apply_2(v_h__2_680_, v_v_685_, v_p_686_);
return v___x_690_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter(lean_object* v_motive_691_, lean_object* v_p_692_, lean_object* v_h__1_693_, lean_object* v_h__2_694_, lean_object* v_h__3_695_){
_start:
{
if (lean_obj_tag(v_p_692_) == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v_h__3_695_);
lean_dec(v_h__2_694_);
v___x_696_ = lean_box(0);
v___x_697_ = lean_apply_1(v_h__1_693_, v___x_696_);
return v___x_697_;
}
else
{
lean_object* v_k_698_; lean_object* v_v_699_; lean_object* v_p_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
lean_dec(v_h__1_693_);
v_k_698_ = lean_ctor_get(v_p_692_, 0);
lean_inc(v_k_698_);
v_v_699_ = lean_ctor_get(v_p_692_, 1);
lean_inc(v_v_699_);
v_p_700_ = lean_ctor_get(v_p_692_, 2);
lean_inc(v_p_700_);
lean_dec_ref_known(v_p_692_, 3);
v___x_701_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_702_ = lean_int_dec_eq(v_k_698_, v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
lean_dec(v_h__2_694_);
v___x_703_ = lean_apply_4(v_h__3_695_, v_k_698_, v_v_699_, v_p_700_, lean_box(0));
return v___x_703_;
}
else
{
lean_object* v___x_704_; 
lean_dec(v_k_698_);
lean_dec(v_h__3_695_);
v___x_704_ = lean_apply_2(v_h__2_694_, v_v_699_, v_p_700_);
return v___x_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_coeff(lean_object* v_p_705_, lean_object* v_x_706_){
_start:
{
if (lean_obj_tag(v_p_705_) == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
return v___x_707_;
}
else
{
lean_object* v_k_708_; lean_object* v_v_709_; lean_object* v_p_710_; uint8_t v___x_711_; 
v_k_708_ = lean_ctor_get(v_p_705_, 0);
v_v_709_ = lean_ctor_get(v_p_705_, 1);
v_p_710_ = lean_ctor_get(v_p_705_, 2);
v___x_711_ = lean_nat_dec_eq(v_x_706_, v_v_709_);
if (v___x_711_ == 0)
{
v_p_705_ = v_p_710_;
goto _start;
}
else
{
lean_inc(v_k_708_);
return v_k_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_coeff___boxed(lean_object* v_p_713_, lean_object* v_x_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_713_, v_x_714_);
lean_dec(v_x_714_);
lean_dec(v_p_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_insert(lean_object* v_k_716_, lean_object* v_v_717_, lean_object* v_p_718_){
_start:
{
if (lean_obj_tag(v_p_718_) == 0)
{
lean_object* v___x_719_; 
v___x_719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_719_, 0, v_k_716_);
lean_ctor_set(v___x_719_, 1, v_v_717_);
lean_ctor_set(v___x_719_, 2, v_p_718_);
return v___x_719_;
}
else
{
lean_object* v_k_720_; lean_object* v_v_721_; lean_object* v_p_722_; uint8_t v___x_723_; 
v_k_720_ = lean_ctor_get(v_p_718_, 0);
v_v_721_ = lean_ctor_get(v_p_718_, 1);
v_p_722_ = lean_ctor_get(v_p_718_, 2);
v___x_723_ = l_Nat_blt(v_v_721_, v_v_717_);
if (v___x_723_ == 0)
{
lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_738_; 
lean_inc(v_p_722_);
lean_inc(v_v_721_);
lean_inc(v_k_720_);
v_isSharedCheck_738_ = !lean_is_exclusive(v_p_718_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; lean_object* v_unused_740_; lean_object* v_unused_741_; 
v_unused_739_ = lean_ctor_get(v_p_718_, 2);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_p_718_, 1);
lean_dec(v_unused_740_);
v_unused_741_ = lean_ctor_get(v_p_718_, 0);
lean_dec(v_unused_741_);
v___x_725_ = v_p_718_;
v_isShared_726_ = v_isSharedCheck_738_;
goto v_resetjp_724_;
}
else
{
lean_dec(v_p_718_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_738_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
uint8_t v___x_727_; 
v___x_727_ = lean_nat_dec_eq(v_v_717_, v_v_721_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_728_ = l_Lean_Grind_Linarith_Poly_insert(v_k_716_, v_v_717_, v_p_722_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 2, v___x_728_);
v___x_730_ = v___x_725_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_k_720_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_v_721_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
lean_dec(v_v_717_);
v___x_732_ = lean_int_add(v_k_716_, v_k_720_);
lean_dec(v_k_720_);
lean_dec(v_k_716_);
v___x_733_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_734_ = lean_int_dec_eq(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_736_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_732_);
v___x_736_ = v___x_725_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_v_721_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_p_722_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
else
{
lean_dec(v___x_732_);
lean_del_object(v___x_725_);
lean_dec(v_v_721_);
return v_p_722_;
}
}
}
}
else
{
lean_object* v___x_742_; 
v___x_742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_742_, 0, v_k_716_);
lean_ctor_set(v___x_742_, 1, v_v_717_);
lean_ctor_set(v___x_742_, 2, v_p_718_);
return v___x_742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_norm(lean_object* v_p_743_){
_start:
{
if (lean_obj_tag(v_p_743_) == 0)
{
return v_p_743_;
}
else
{
lean_object* v_k_744_; lean_object* v_v_745_; lean_object* v_p_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_k_744_ = lean_ctor_get(v_p_743_, 0);
lean_inc(v_k_744_);
v_v_745_ = lean_ctor_get(v_p_743_, 1);
lean_inc(v_v_745_);
v_p_746_ = lean_ctor_get(v_p_743_, 2);
lean_inc(v_p_746_);
lean_dec_ref_known(v_p_743_, 3);
v___x_747_ = l_Lean_Grind_Linarith_Poly_norm(v_p_746_);
v___x_748_ = l_Lean_Grind_Linarith_Poly_insert(v_k_744_, v_v_745_, v___x_747_);
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_append(lean_object* v_p_u2081_749_, lean_object* v_p_u2082_750_){
_start:
{
if (lean_obj_tag(v_p_u2081_749_) == 0)
{
lean_inc(v_p_u2082_750_);
return v_p_u2082_750_;
}
else
{
lean_object* v_k_751_; lean_object* v_v_752_; lean_object* v_p_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_761_; 
v_k_751_ = lean_ctor_get(v_p_u2081_749_, 0);
v_v_752_ = lean_ctor_get(v_p_u2081_749_, 1);
v_p_753_ = lean_ctor_get(v_p_u2081_749_, 2);
v_isSharedCheck_761_ = !lean_is_exclusive(v_p_u2081_749_);
if (v_isSharedCheck_761_ == 0)
{
v___x_755_ = v_p_u2081_749_;
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_p_753_);
lean_inc(v_v_752_);
lean_inc(v_k_751_);
lean_dec(v_p_u2081_749_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = l_Lean_Grind_Linarith_Poly_append(v_p_753_, v_p_u2082_750_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 2, v___x_757_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_append___boxed(lean_object* v_p_u2081_762_, lean_object* v_p_u2082_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Grind_Linarith_Poly_append(v_p_u2081_762_, v_p_u2082_763_);
lean_dec(v_p_u2082_763_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_combine(lean_object* v_p_u2081_765_, lean_object* v_p_u2082_766_){
_start:
{
if (lean_obj_tag(v_p_u2081_765_) == 0)
{
return v_p_u2082_766_;
}
else
{
if (lean_obj_tag(v_p_u2082_766_) == 0)
{
return v_p_u2081_765_;
}
else
{
lean_object* v_k_767_; lean_object* v_v_768_; lean_object* v_p_769_; lean_object* v_k_770_; lean_object* v_v_771_; lean_object* v_p_772_; uint8_t v___x_773_; 
v_k_767_ = lean_ctor_get(v_p_u2081_765_, 0);
v_v_768_ = lean_ctor_get(v_p_u2081_765_, 1);
v_p_769_ = lean_ctor_get(v_p_u2081_765_, 2);
v_k_770_ = lean_ctor_get(v_p_u2082_766_, 0);
v_v_771_ = lean_ctor_get(v_p_u2082_766_, 1);
v_p_772_ = lean_ctor_get(v_p_u2082_766_, 2);
v___x_773_ = lean_nat_dec_eq(v_v_768_, v_v_771_);
if (v___x_773_ == 0)
{
uint8_t v___x_774_; 
v___x_774_ = l_Nat_blt(v_v_771_, v_v_768_);
if (v___x_774_ == 0)
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
lean_inc(v_p_772_);
lean_inc(v_v_771_);
lean_inc(v_k_770_);
v_isSharedCheck_782_ = !lean_is_exclusive(v_p_u2082_766_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; lean_object* v_unused_784_; lean_object* v_unused_785_; 
v_unused_783_ = lean_ctor_get(v_p_u2082_766_, 2);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_p_u2082_766_, 1);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_p_u2082_766_, 0);
lean_dec(v_unused_785_);
v___x_776_ = v_p_u2082_766_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_dec(v_p_u2082_766_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = l_Lean_Grind_Linarith_Poly_combine(v_p_u2081_765_, v_p_772_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 2, v___x_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_k_770_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_v_771_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
else
{
lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_793_; 
lean_inc(v_p_769_);
lean_inc(v_v_768_);
lean_inc(v_k_767_);
v_isSharedCheck_793_ = !lean_is_exclusive(v_p_u2081_765_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; lean_object* v_unused_795_; lean_object* v_unused_796_; 
v_unused_794_ = lean_ctor_get(v_p_u2081_765_, 2);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_p_u2081_765_, 1);
lean_dec(v_unused_795_);
v_unused_796_ = lean_ctor_get(v_p_u2081_765_, 0);
lean_dec(v_unused_796_);
v___x_787_ = v_p_u2081_765_;
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
else
{
lean_dec(v_p_u2081_765_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = l_Lean_Grind_Linarith_Poly_combine(v_p_769_, v_p_u2082_766_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 2, v___x_789_);
v___x_791_ = v___x_787_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_808_; 
lean_inc(v_p_772_);
lean_inc(v_k_770_);
lean_inc(v_p_769_);
lean_inc(v_v_768_);
lean_inc(v_k_767_);
lean_dec_ref_known(v_p_u2081_765_, 3);
v_isSharedCheck_808_ = !lean_is_exclusive(v_p_u2082_766_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; lean_object* v_unused_810_; lean_object* v_unused_811_; 
v_unused_809_ = lean_ctor_get(v_p_u2082_766_, 2);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_p_u2082_766_, 1);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_p_u2082_766_, 0);
lean_dec(v_unused_811_);
v___x_798_ = v_p_u2082_766_;
v_isShared_799_ = v_isSharedCheck_808_;
goto v_resetjp_797_;
}
else
{
lean_dec(v_p_u2082_766_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_808_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_a_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_a_800_ = lean_int_add(v_k_767_, v_k_770_);
lean_dec(v_k_770_);
lean_dec(v_k_767_);
v___x_801_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_802_ = lean_int_dec_eq(v_a_800_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = l_Lean_Grind_Linarith_Poly_combine(v_p_769_, v_p_772_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 2, v___x_803_);
lean_ctor_set(v___x_798_, 1, v_v_768_);
lean_ctor_set(v___x_798_, 0, v_a_800_);
v___x_805_ = v___x_798_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
else
{
lean_dec(v_a_800_);
lean_del_object(v___x_798_);
lean_dec(v_v_768_);
v_p_u2081_765_ = v_p_769_;
v_p_u2082_766_ = v_p_772_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter___redArg(lean_object* v_p_u2081_812_, lean_object* v_p_u2082_813_, lean_object* v_h__1_814_, lean_object* v_h__2_815_, lean_object* v_h__3_816_){
_start:
{
if (lean_obj_tag(v_p_u2081_812_) == 0)
{
lean_object* v___x_817_; 
lean_dec(v_h__3_816_);
lean_dec(v_h__2_815_);
v___x_817_ = lean_apply_1(v_h__1_814_, v_p_u2082_813_);
return v___x_817_;
}
else
{
lean_dec(v_h__1_814_);
if (lean_obj_tag(v_p_u2082_813_) == 0)
{
lean_object* v___x_818_; 
lean_dec(v_h__3_816_);
v___x_818_ = lean_apply_2(v_h__2_815_, v_p_u2081_812_, lean_box(0));
return v___x_818_;
}
else
{
lean_object* v_k_819_; lean_object* v_v_820_; lean_object* v_p_821_; lean_object* v_k_822_; lean_object* v_v_823_; lean_object* v_p_824_; lean_object* v___x_825_; 
lean_dec(v_h__2_815_);
v_k_819_ = lean_ctor_get(v_p_u2081_812_, 0);
lean_inc(v_k_819_);
v_v_820_ = lean_ctor_get(v_p_u2081_812_, 1);
lean_inc(v_v_820_);
v_p_821_ = lean_ctor_get(v_p_u2081_812_, 2);
lean_inc(v_p_821_);
lean_dec_ref_known(v_p_u2081_812_, 3);
v_k_822_ = lean_ctor_get(v_p_u2082_813_, 0);
lean_inc(v_k_822_);
v_v_823_ = lean_ctor_get(v_p_u2082_813_, 1);
lean_inc(v_v_823_);
v_p_824_ = lean_ctor_get(v_p_u2082_813_, 2);
lean_inc(v_p_824_);
lean_dec_ref_known(v_p_u2082_813_, 3);
v___x_825_ = lean_apply_6(v_h__3_816_, v_k_819_, v_v_820_, v_p_821_, v_k_822_, v_v_823_, v_p_824_);
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter(lean_object* v_motive_826_, lean_object* v_p_u2081_827_, lean_object* v_p_u2082_828_, lean_object* v_h__1_829_, lean_object* v_h__2_830_, lean_object* v_h__3_831_){
_start:
{
if (lean_obj_tag(v_p_u2081_827_) == 0)
{
lean_object* v___x_832_; 
lean_dec(v_h__3_831_);
lean_dec(v_h__2_830_);
v___x_832_ = lean_apply_1(v_h__1_829_, v_p_u2082_828_);
return v___x_832_;
}
else
{
lean_dec(v_h__1_829_);
if (lean_obj_tag(v_p_u2082_828_) == 0)
{
lean_object* v___x_833_; 
lean_dec(v_h__3_831_);
v___x_833_ = lean_apply_2(v_h__2_830_, v_p_u2081_827_, lean_box(0));
return v___x_833_;
}
else
{
lean_object* v_k_834_; lean_object* v_v_835_; lean_object* v_p_836_; lean_object* v_k_837_; lean_object* v_v_838_; lean_object* v_p_839_; lean_object* v___x_840_; 
lean_dec(v_h__2_830_);
v_k_834_ = lean_ctor_get(v_p_u2081_827_, 0);
lean_inc(v_k_834_);
v_v_835_ = lean_ctor_get(v_p_u2081_827_, 1);
lean_inc(v_v_835_);
v_p_836_ = lean_ctor_get(v_p_u2081_827_, 2);
lean_inc(v_p_836_);
lean_dec_ref_known(v_p_u2081_827_, 3);
v_k_837_ = lean_ctor_get(v_p_u2082_828_, 0);
lean_inc(v_k_837_);
v_v_838_ = lean_ctor_get(v_p_u2082_828_, 1);
lean_inc(v_v_838_);
v_p_839_ = lean_ctor_get(v_p_u2082_828_, 2);
lean_inc(v_p_839_);
lean_dec_ref_known(v_p_u2082_828_, 3);
v___x_840_ = lean_apply_6(v_h__3_831_, v_k_834_, v_v_835_, v_p_836_, v_k_837_, v_v_838_, v_p_839_);
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Expr_toPoly_x27_go_spec__0(lean_object* v_a_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = lean_nat_to_int(v_a_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPoly_x27_go(lean_object* v_coeff_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
switch(lean_obj_tag(v_a_844_))
{
case 0:
{
lean_dec(v_coeff_843_);
return v_a_845_;
}
case 1:
{
lean_object* v_i_846_; lean_object* v___x_847_; 
v_i_846_ = lean_ctor_get(v_a_844_, 0);
lean_inc(v_i_846_);
lean_dec_ref_known(v_a_844_, 1);
v___x_847_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_847_, 0, v_coeff_843_);
lean_ctor_set(v___x_847_, 1, v_i_846_);
lean_ctor_set(v___x_847_, 2, v_a_845_);
return v___x_847_;
}
case 2:
{
lean_object* v_a_848_; lean_object* v_b_849_; lean_object* v___x_850_; 
v_a_848_ = lean_ctor_get(v_a_844_, 0);
lean_inc(v_a_848_);
v_b_849_ = lean_ctor_get(v_a_844_, 1);
lean_inc(v_b_849_);
lean_dec_ref_known(v_a_844_, 2);
lean_inc(v_coeff_843_);
v___x_850_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v_coeff_843_, v_b_849_, v_a_845_);
v_a_844_ = v_a_848_;
v_a_845_ = v___x_850_;
goto _start;
}
case 3:
{
lean_object* v_a_852_; lean_object* v_b_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_a_852_ = lean_ctor_get(v_a_844_, 0);
lean_inc(v_a_852_);
v_b_853_ = lean_ctor_get(v_a_844_, 1);
lean_inc(v_b_853_);
lean_dec_ref_known(v_a_844_, 2);
v___x_854_ = lean_int_neg(v_coeff_843_);
v___x_855_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v___x_854_, v_b_853_, v_a_845_);
v_a_844_ = v_a_852_;
v_a_845_ = v___x_855_;
goto _start;
}
case 4:
{
lean_object* v_a_857_; lean_object* v___x_858_; 
v_a_857_ = lean_ctor_get(v_a_844_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v_a_844_, 1);
v___x_858_ = lean_int_neg(v_coeff_843_);
lean_dec(v_coeff_843_);
v_coeff_843_ = v___x_858_;
v_a_844_ = v_a_857_;
goto _start;
}
case 5:
{
lean_object* v_k_860_; lean_object* v_a_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_k_860_ = lean_ctor_get(v_a_844_, 0);
lean_inc(v_k_860_);
v_a_861_ = lean_ctor_get(v_a_844_, 1);
lean_inc(v_a_861_);
lean_dec_ref_known(v_a_844_, 2);
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_nat_dec_eq(v_k_860_, v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_nat_to_int(v_k_860_);
v___x_865_ = lean_int_mul(v_coeff_843_, v___x_864_);
lean_dec(v___x_864_);
lean_dec(v_coeff_843_);
v_coeff_843_ = v___x_865_;
v_a_844_ = v_a_861_;
goto _start;
}
else
{
lean_dec(v_a_861_);
lean_dec(v_k_860_);
lean_dec(v_coeff_843_);
return v_a_845_;
}
}
default: 
{
lean_object* v_k_867_; lean_object* v_a_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_k_867_ = lean_ctor_get(v_a_844_, 0);
lean_inc(v_k_867_);
v_a_868_ = lean_ctor_get(v_a_844_, 1);
lean_inc(v_a_868_);
lean_dec_ref_known(v_a_844_, 2);
v___x_869_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_870_ = lean_int_dec_eq(v_k_867_, v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
v___x_871_ = lean_int_mul(v_coeff_843_, v_k_867_);
lean_dec(v_k_867_);
lean_dec(v_coeff_843_);
v_coeff_843_ = v___x_871_;
v_a_844_ = v_a_868_;
goto _start;
}
else
{
lean_dec(v_a_868_);
lean_dec(v_k_867_);
lean_dec(v_coeff_843_);
return v_a_845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPoly_x27(lean_object* v_e_873_){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_874_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_875_ = lean_box(0);
v___x_876_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v___x_874_, v_e_873_, v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_norm(lean_object* v_e_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = l_Lean_Grind_Linarith_Expr_toPoly_x27(v_e_877_);
v___x_879_ = l_Lean_Grind_Linarith_Poly_norm(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul_x27(lean_object* v_p_880_, lean_object* v_k_881_){
_start:
{
if (lean_obj_tag(v_p_880_) == 0)
{
return v_p_880_;
}
else
{
lean_object* v_k_882_; lean_object* v_v_883_; lean_object* v_p_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_893_; 
v_k_882_ = lean_ctor_get(v_p_880_, 0);
v_v_883_ = lean_ctor_get(v_p_880_, 1);
v_p_884_ = lean_ctor_get(v_p_880_, 2);
v_isSharedCheck_893_ = !lean_is_exclusive(v_p_880_);
if (v_isSharedCheck_893_ == 0)
{
v___x_886_ = v_p_880_;
v_isShared_887_ = v_isSharedCheck_893_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_p_884_);
lean_inc(v_v_883_);
lean_inc(v_k_882_);
lean_dec(v_p_880_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_893_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_888_ = lean_int_mul(v_k_881_, v_k_882_);
lean_dec(v_k_882_);
v___x_889_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_884_, v_k_881_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 2, v___x_889_);
lean_ctor_set(v___x_886_, 0, v___x_888_);
v___x_891_ = v___x_886_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul_x27___boxed(lean_object* v_p_894_, lean_object* v_k_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_894_, v_k_895_);
lean_dec(v_k_895_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul(lean_object* v_p_897_, lean_object* v_k_898_){
_start:
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_900_ = lean_int_dec_eq(v_k_898_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_897_, v_k_898_);
return v___x_901_;
}
else
{
lean_object* v___x_902_; 
lean_dec(v_p_897_);
v___x_902_ = lean_box(0);
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul___boxed(lean_object* v_p_903_, lean_object* v_k_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_Grind_Linarith_Poly_mul(v_p_903_, v_k_904_);
lean_dec(v_k_904_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(lean_object* v_p_906_, lean_object* v_h__1_907_, lean_object* v_h__2_908_){
_start:
{
if (lean_obj_tag(v_p_906_) == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v_h__2_908_);
v___x_909_ = lean_box(0);
v___x_910_ = lean_apply_1(v_h__1_907_, v___x_909_);
return v___x_910_;
}
else
{
lean_object* v_k_911_; lean_object* v_v_912_; lean_object* v_p_913_; lean_object* v___x_914_; 
lean_dec(v_h__1_907_);
v_k_911_ = lean_ctor_get(v_p_906_, 0);
lean_inc(v_k_911_);
v_v_912_ = lean_ctor_get(v_p_906_, 1);
lean_inc(v_v_912_);
v_p_913_ = lean_ctor_get(v_p_906_, 2);
lean_inc(v_p_913_);
lean_dec_ref_known(v_p_906_, 3);
v___x_914_ = lean_apply_3(v_h__2_908_, v_k_911_, v_v_912_, v_p_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(lean_object* v_motive_915_, lean_object* v_p_916_, lean_object* v_h__1_917_, lean_object* v_h__2_918_){
_start:
{
if (lean_obj_tag(v_p_916_) == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_h__2_918_);
v___x_919_ = lean_box(0);
v___x_920_ = lean_apply_1(v_h__1_917_, v___x_919_);
return v___x_920_;
}
else
{
lean_object* v_k_921_; lean_object* v_v_922_; lean_object* v_p_923_; lean_object* v___x_924_; 
lean_dec(v_h__1_917_);
v_k_921_ = lean_ctor_get(v_p_916_, 0);
lean_inc(v_k_921_);
v_v_922_ = lean_ctor_get(v_p_916_, 1);
lean_inc(v_v_922_);
v_p_923_ = lean_ctor_get(v_p_916_, 2);
lean_inc(v_p_923_);
lean_dec_ref_known(v_p_916_, 3);
v___x_924_ = lean_apply_3(v_h__2_918_, v_k_921_, v_v_922_, v_p_923_);
return v___x_924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter___redArg(lean_object* v_x_925_, lean_object* v_h__1_926_, lean_object* v_h__2_927_, lean_object* v_h__3_928_, lean_object* v_h__4_929_, lean_object* v_h__5_930_, lean_object* v_h__6_931_, lean_object* v_h__7_932_){
_start:
{
switch(lean_obj_tag(v_x_925_))
{
case 0:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec(v_h__7_932_);
lean_dec(v_h__6_931_);
lean_dec(v_h__5_930_);
lean_dec(v_h__4_929_);
lean_dec(v_h__3_928_);
lean_dec(v_h__2_927_);
v___x_933_ = lean_box(0);
v___x_934_ = lean_apply_1(v_h__1_926_, v___x_933_);
return v___x_934_;
}
case 1:
{
lean_object* v_i_935_; lean_object* v___x_936_; 
lean_dec(v_h__7_932_);
lean_dec(v_h__6_931_);
lean_dec(v_h__5_930_);
lean_dec(v_h__4_929_);
lean_dec(v_h__3_928_);
lean_dec(v_h__1_926_);
v_i_935_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_i_935_);
lean_dec_ref_known(v_x_925_, 1);
v___x_936_ = lean_apply_1(v_h__2_927_, v_i_935_);
return v___x_936_;
}
case 2:
{
lean_object* v_a_937_; lean_object* v_b_938_; lean_object* v___x_939_; 
lean_dec(v_h__7_932_);
lean_dec(v_h__6_931_);
lean_dec(v_h__5_930_);
lean_dec(v_h__4_929_);
lean_dec(v_h__2_927_);
lean_dec(v_h__1_926_);
v_a_937_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_a_937_);
v_b_938_ = lean_ctor_get(v_x_925_, 1);
lean_inc(v_b_938_);
lean_dec_ref_known(v_x_925_, 2);
v___x_939_ = lean_apply_2(v_h__3_928_, v_a_937_, v_b_938_);
return v___x_939_;
}
case 3:
{
lean_object* v_a_940_; lean_object* v_b_941_; lean_object* v___x_942_; 
lean_dec(v_h__7_932_);
lean_dec(v_h__6_931_);
lean_dec(v_h__5_930_);
lean_dec(v_h__3_928_);
lean_dec(v_h__2_927_);
lean_dec(v_h__1_926_);
v_a_940_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_a_940_);
v_b_941_ = lean_ctor_get(v_x_925_, 1);
lean_inc(v_b_941_);
lean_dec_ref_known(v_x_925_, 2);
v___x_942_ = lean_apply_2(v_h__4_929_, v_a_940_, v_b_941_);
return v___x_942_;
}
case 4:
{
lean_object* v_a_943_; lean_object* v___x_944_; 
lean_dec(v_h__6_931_);
lean_dec(v_h__5_930_);
lean_dec(v_h__4_929_);
lean_dec(v_h__3_928_);
lean_dec(v_h__2_927_);
lean_dec(v_h__1_926_);
v_a_943_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v_x_925_, 1);
v___x_944_ = lean_apply_1(v_h__7_932_, v_a_943_);
return v___x_944_;
}
case 5:
{
lean_object* v_k_945_; lean_object* v_a_946_; lean_object* v___x_947_; 
lean_dec(v_h__7_932_);
lean_dec(v_h__6_931_);
lean_dec(v_h__4_929_);
lean_dec(v_h__3_928_);
lean_dec(v_h__2_927_);
lean_dec(v_h__1_926_);
v_k_945_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_k_945_);
v_a_946_ = lean_ctor_get(v_x_925_, 1);
lean_inc(v_a_946_);
lean_dec_ref_known(v_x_925_, 2);
v___x_947_ = lean_apply_2(v_h__5_930_, v_k_945_, v_a_946_);
return v___x_947_;
}
default: 
{
lean_object* v_k_948_; lean_object* v_a_949_; lean_object* v___x_950_; 
lean_dec(v_h__7_932_);
lean_dec(v_h__5_930_);
lean_dec(v_h__4_929_);
lean_dec(v_h__3_928_);
lean_dec(v_h__2_927_);
lean_dec(v_h__1_926_);
v_k_948_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_k_948_);
v_a_949_ = lean_ctor_get(v_x_925_, 1);
lean_inc(v_a_949_);
lean_dec_ref_known(v_x_925_, 2);
v___x_950_ = lean_apply_2(v_h__6_931_, v_k_948_, v_a_949_);
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter(lean_object* v_motive_951_, lean_object* v_x_952_, lean_object* v_h__1_953_, lean_object* v_h__2_954_, lean_object* v_h__3_955_, lean_object* v_h__4_956_, lean_object* v_h__5_957_, lean_object* v_h__6_958_, lean_object* v_h__7_959_){
_start:
{
switch(lean_obj_tag(v_x_952_))
{
case 0:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec(v_h__7_959_);
lean_dec(v_h__6_958_);
lean_dec(v_h__5_957_);
lean_dec(v_h__4_956_);
lean_dec(v_h__3_955_);
lean_dec(v_h__2_954_);
v___x_960_ = lean_box(0);
v___x_961_ = lean_apply_1(v_h__1_953_, v___x_960_);
return v___x_961_;
}
case 1:
{
lean_object* v_i_962_; lean_object* v___x_963_; 
lean_dec(v_h__7_959_);
lean_dec(v_h__6_958_);
lean_dec(v_h__5_957_);
lean_dec(v_h__4_956_);
lean_dec(v_h__3_955_);
lean_dec(v_h__1_953_);
v_i_962_ = lean_ctor_get(v_x_952_, 0);
lean_inc(v_i_962_);
lean_dec_ref_known(v_x_952_, 1);
v___x_963_ = lean_apply_1(v_h__2_954_, v_i_962_);
return v___x_963_;
}
case 2:
{
lean_object* v_a_964_; lean_object* v_b_965_; lean_object* v___x_966_; 
lean_dec(v_h__7_959_);
lean_dec(v_h__6_958_);
lean_dec(v_h__5_957_);
lean_dec(v_h__4_956_);
lean_dec(v_h__2_954_);
lean_dec(v_h__1_953_);
v_a_964_ = lean_ctor_get(v_x_952_, 0);
lean_inc(v_a_964_);
v_b_965_ = lean_ctor_get(v_x_952_, 1);
lean_inc(v_b_965_);
lean_dec_ref_known(v_x_952_, 2);
v___x_966_ = lean_apply_2(v_h__3_955_, v_a_964_, v_b_965_);
return v___x_966_;
}
case 3:
{
lean_object* v_a_967_; lean_object* v_b_968_; lean_object* v___x_969_; 
lean_dec(v_h__7_959_);
lean_dec(v_h__6_958_);
lean_dec(v_h__5_957_);
lean_dec(v_h__3_955_);
lean_dec(v_h__2_954_);
lean_dec(v_h__1_953_);
v_a_967_ = lean_ctor_get(v_x_952_, 0);
lean_inc(v_a_967_);
v_b_968_ = lean_ctor_get(v_x_952_, 1);
lean_inc(v_b_968_);
lean_dec_ref_known(v_x_952_, 2);
v___x_969_ = lean_apply_2(v_h__4_956_, v_a_967_, v_b_968_);
return v___x_969_;
}
case 4:
{
lean_object* v_a_970_; lean_object* v___x_971_; 
lean_dec(v_h__6_958_);
lean_dec(v_h__5_957_);
lean_dec(v_h__4_956_);
lean_dec(v_h__3_955_);
lean_dec(v_h__2_954_);
lean_dec(v_h__1_953_);
v_a_970_ = lean_ctor_get(v_x_952_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v_x_952_, 1);
v___x_971_ = lean_apply_1(v_h__7_959_, v_a_970_);
return v___x_971_;
}
case 5:
{
lean_object* v_k_972_; lean_object* v_a_973_; lean_object* v___x_974_; 
lean_dec(v_h__7_959_);
lean_dec(v_h__6_958_);
lean_dec(v_h__4_956_);
lean_dec(v_h__3_955_);
lean_dec(v_h__2_954_);
lean_dec(v_h__1_953_);
v_k_972_ = lean_ctor_get(v_x_952_, 0);
lean_inc(v_k_972_);
v_a_973_ = lean_ctor_get(v_x_952_, 1);
lean_inc(v_a_973_);
lean_dec_ref_known(v_x_952_, 2);
v___x_974_ = lean_apply_2(v_h__5_957_, v_k_972_, v_a_973_);
return v___x_974_;
}
default: 
{
lean_object* v_k_975_; lean_object* v_a_976_; lean_object* v___x_977_; 
lean_dec(v_h__7_959_);
lean_dec(v_h__5_957_);
lean_dec(v_h__4_956_);
lean_dec(v_h__3_955_);
lean_dec(v_h__2_954_);
lean_dec(v_h__1_953_);
v_k_975_ = lean_ctor_get(v_x_952_, 0);
lean_inc(v_k_975_);
v_a_976_ = lean_ctor_get(v_x_952_, 1);
lean_inc(v_a_976_);
lean_dec_ref_known(v_x_952_, 2);
v___x_977_ = lean_apply_2(v_h__6_958_, v_k_975_, v_a_976_);
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_leadCoeff(lean_object* v_p_978_){
_start:
{
if (lean_obj_tag(v_p_978_) == 1)
{
lean_object* v_k_979_; 
v_k_979_ = lean_ctor_get(v_p_978_, 0);
lean_inc(v_k_979_);
return v_k_979_;
}
else
{
lean_object* v___x_980_; 
v___x_980_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_leadCoeff___boxed(lean_object* v_p_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_981_);
lean_dec(v_p_981_);
return v_res_982_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_le__le__combine__cert(lean_object* v_p_u2081_983_, lean_object* v_p_u2082_984_, lean_object* v_p_u2083_985_){
_start:
{
lean_object* v___x_986_; lean_object* v_a_u2081_987_; lean_object* v___x_988_; lean_object* v_a_u2082_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_986_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_983_);
v_a_u2081_987_ = lean_nat_abs(v___x_986_);
lean_dec(v___x_986_);
v___x_988_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_984_);
v_a_u2082_989_ = lean_nat_abs(v___x_988_);
lean_dec(v___x_988_);
v___x_990_ = lean_nat_to_int(v_a_u2082_989_);
v___x_991_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_983_, v___x_990_);
lean_dec(v___x_990_);
v___x_992_ = lean_nat_to_int(v_a_u2081_987_);
v___x_993_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_984_, v___x_992_);
lean_dec(v___x_992_);
v___x_994_ = l_Lean_Grind_Linarith_Poly_combine(v___x_991_, v___x_993_);
v___x_995_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_985_, v___x_994_);
lean_dec(v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_le__le__combine__cert___boxed(lean_object* v_p_u2081_996_, lean_object* v_p_u2082_997_, lean_object* v_p_u2083_998_){
_start:
{
uint8_t v_res_999_; lean_object* v_r_1000_; 
v_res_999_ = l_Lean_Grind_Linarith_le__le__combine__cert(v_p_u2081_996_, v_p_u2082_997_, v_p_u2083_998_);
lean_dec(v_p_u2083_998_);
v_r_1000_ = lean_box(v_res_999_);
return v_r_1000_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_le__lt__combine__cert(lean_object* v_p_u2081_1001_, lean_object* v_p_u2082_1002_, lean_object* v_p_u2083_1003_){
_start:
{
lean_object* v___x_1004_; lean_object* v_a_u2081_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1004_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_1001_);
v_a_u2081_1005_ = lean_nat_abs(v___x_1004_);
lean_dec(v___x_1004_);
v___x_1006_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1007_ = lean_nat_to_int(v_a_u2081_1005_);
v___x_1008_ = lean_int_dec_lt(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_dec(v___x_1007_);
lean_dec(v_p_u2082_1002_);
lean_dec(v_p_u2081_1001_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; lean_object* v_a_u2082_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1009_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_1002_);
v_a_u2082_1010_ = lean_nat_abs(v___x_1009_);
lean_dec(v___x_1009_);
v___x_1011_ = lean_nat_to_int(v_a_u2082_1010_);
v___x_1012_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1001_, v___x_1011_);
lean_dec(v___x_1011_);
v___x_1013_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1002_, v___x_1007_);
lean_dec(v___x_1007_);
v___x_1014_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1012_, v___x_1013_);
v___x_1015_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1003_, v___x_1014_);
lean_dec(v___x_1014_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_le__lt__combine__cert___boxed(lean_object* v_p_u2081_1016_, lean_object* v_p_u2082_1017_, lean_object* v_p_u2083_1018_){
_start:
{
uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_res_1019_ = l_Lean_Grind_Linarith_le__lt__combine__cert(v_p_u2081_1016_, v_p_u2082_1017_, v_p_u2083_1018_);
lean_dec(v_p_u2083_1018_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_lt__lt__combine__cert(lean_object* v_p_u2081_1021_, lean_object* v_p_u2082_1022_, lean_object* v_p_u2083_1023_){
_start:
{
lean_object* v___x_1024_; lean_object* v_a_u2082_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1024_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_1022_);
v_a_u2082_1025_ = lean_nat_abs(v___x_1024_);
lean_dec(v___x_1024_);
v___x_1026_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1027_ = lean_nat_to_int(v_a_u2082_1025_);
v___x_1028_ = lean_int_dec_lt(v___x_1026_, v___x_1027_);
if (v___x_1028_ == 0)
{
lean_dec(v___x_1027_);
lean_dec(v_p_u2082_1022_);
lean_dec(v_p_u2081_1021_);
return v___x_1028_;
}
else
{
lean_object* v___x_1029_; lean_object* v_a_u2081_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1029_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_1021_);
v_a_u2081_1030_ = lean_nat_abs(v___x_1029_);
lean_dec(v___x_1029_);
v___x_1031_ = lean_nat_to_int(v_a_u2081_1030_);
v___x_1032_ = lean_int_dec_lt(v___x_1026_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_dec(v___x_1031_);
lean_dec(v___x_1027_);
lean_dec(v_p_u2082_1022_);
lean_dec(v_p_u2081_1021_);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1033_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1021_, v___x_1027_);
lean_dec(v___x_1027_);
v___x_1034_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1022_, v___x_1031_);
lean_dec(v___x_1031_);
v___x_1035_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1033_, v___x_1034_);
v___x_1036_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1023_, v___x_1035_);
lean_dec(v___x_1035_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_lt__lt__combine__cert___boxed(lean_object* v_p_u2081_1037_, lean_object* v_p_u2082_1038_, lean_object* v_p_u2083_1039_){
_start:
{
uint8_t v_res_1040_; lean_object* v_r_1041_; 
v_res_1040_ = l_Lean_Grind_Linarith_lt__lt__combine__cert(v_p_u2081_1037_, v_p_u2082_1038_, v_p_u2083_1039_);
lean_dec(v_p_u2083_1039_);
v_r_1041_ = lean_box(v_res_1040_);
return v_r_1041_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1043_ = lean_int_neg(v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_diseq__split__cert(lean_object* v_p_u2081_1044_, lean_object* v_p_u2082_1045_){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v___x_1046_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1047_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1044_, v___x_1046_);
v___x_1048_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_1045_, v___x_1047_);
lean_dec(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_diseq__split__cert___boxed(lean_object* v_p_u2081_1049_, lean_object* v_p_u2082_1050_){
_start:
{
uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_res_1051_ = l_Lean_Grind_Linarith_diseq__split__cert(v_p_u2081_1049_, v_p_u2082_1050_);
lean_dec(v_p_u2082_1050_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_norm__cert(lean_object* v_lhs_1053_, lean_object* v_rhs_1054_, lean_object* v_p_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1056_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_lhs_1053_);
lean_ctor_set(v___x_1056_, 1, v_rhs_1054_);
v___x_1057_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1056_);
v___x_1058_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1055_, v___x_1057_);
lean_dec(v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_norm__cert___boxed(lean_object* v_lhs_1059_, lean_object* v_rhs_1060_, lean_object* v_p_1061_){
_start:
{
uint8_t v_res_1062_; lean_object* v_r_1063_; 
v_res_1062_ = l_Lean_Grind_Linarith_norm__cert(v_lhs_1059_, v_rhs_1060_, v_p_1061_);
lean_dec(v_p_1061_);
v_r_1063_ = lean_box(v_res_1062_);
return v_r_1063_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__of__le__ge__cert(lean_object* v_p_u2081_1064_, lean_object* v_p_u2082_1065_){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1067_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1064_, v___x_1066_);
v___x_1068_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_1065_, v___x_1067_);
lean_dec(v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__of__le__ge__cert___boxed(lean_object* v_p_u2081_1069_, lean_object* v_p_u2082_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Lean_Grind_Linarith_eq__of__le__ge__cert(v_p_u2081_1069_, v_p_u2082_1070_);
lean_dec(v_p_u2082_1070_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1076_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v___x_1074_);
lean_ctor_set(v___x_1076_, 2, v___x_1073_);
return v___x_1076_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_zero__lt__one__cert(lean_object* v_p_1077_){
_start:
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = lean_obj_once(&l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0, &l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0_once, _init_l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0);
v___x_1079_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1077_, v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__lt__one__cert___boxed(lean_object* v_p_1080_){
_start:
{
uint8_t v_res_1081_; lean_object* v_r_1082_; 
v_res_1081_ = l_Lean_Grind_Linarith_zero__lt__one__cert(v_p_1080_);
lean_dec(v_p_1080_);
v_r_1082_ = lean_box(v_res_1081_);
return v_r_1082_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_unsigned_to_nat(0u);
v___x_1085_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1086_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v___x_1084_);
lean_ctor_set(v___x_1086_, 2, v___x_1083_);
return v___x_1086_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_zero__ne__one__cert(lean_object* v_p_1087_){
_start:
{
lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = lean_obj_once(&l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0, &l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once, _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0);
v___x_1089_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1087_, v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__ne__one__cert___boxed(lean_object* v_p_1090_){
_start:
{
uint8_t v_res_1091_; lean_object* v_r_1092_; 
v_res_1091_ = l_Lean_Grind_Linarith_zero__ne__one__cert(v_p_1090_);
lean_dec(v_p_1090_);
v_r_1092_ = lean_box(v_res_1091_);
return v_r_1092_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(lean_object* v_c_1093_, lean_object* v_p_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1095_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1096_ = lean_nat_to_int(v_c_1093_);
v___x_1097_ = lean_int_dec_lt(v___x_1095_, v___x_1096_);
lean_dec(v___x_1096_);
if (v___x_1097_ == 0)
{
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = lean_obj_once(&l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0, &l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once, _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0);
v___x_1099_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1094_, v___x_1098_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert___boxed(lean_object* v_c_1100_, lean_object* v_p_1101_){
_start:
{
uint8_t v_res_1102_; lean_object* v_r_1103_; 
v_res_1102_ = l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(v_c_1100_, v_p_1101_);
lean_dec(v_p_1101_);
v_r_1103_ = lean_box(v_res_1102_);
return v_r_1103_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__neg__cert(lean_object* v_p_u2081_1104_, lean_object* v_p_u2082_1105_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1106_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1107_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1104_, v___x_1106_);
v___x_1108_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_1105_, v___x_1107_);
lean_dec(v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__neg__cert___boxed(lean_object* v_p_u2081_1109_, lean_object* v_p_u2082_1110_){
_start:
{
uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_res_1111_ = l_Lean_Grind_Linarith_eq__neg__cert(v_p_u2081_1109_, v_p_u2082_1110_);
lean_dec(v_p_u2082_1110_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__coeff__cert(lean_object* v_p_u2081_1113_, lean_object* v_p_u2082_1114_, lean_object* v_k_1115_){
_start:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = lean_unsigned_to_nat(0u);
v___x_1117_ = lean_nat_dec_eq(v_k_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1118_ = lean_nat_to_int(v_k_1115_);
v___x_1119_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1114_, v___x_1118_);
lean_dec(v___x_1118_);
v___x_1120_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2081_1113_, v___x_1119_);
lean_dec(v___x_1119_);
return v___x_1120_;
}
else
{
uint8_t v___x_1121_; 
lean_dec(v_k_1115_);
lean_dec(v_p_u2082_1114_);
v___x_1121_ = 0;
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__coeff__cert___boxed(lean_object* v_p_u2081_1122_, lean_object* v_p_u2082_1123_, lean_object* v_k_1124_){
_start:
{
uint8_t v_res_1125_; lean_object* v_r_1126_; 
v_res_1125_ = l_Lean_Grind_Linarith_eq__coeff__cert(v_p_u2081_1122_, v_p_u2082_1123_, v_k_1124_);
lean_dec(v_p_u2081_1122_);
v_r_1126_ = lean_box(v_res_1125_);
return v_r_1126_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_coeff__cert(lean_object* v_p_u2081_1127_, lean_object* v_p_u2082_1128_, lean_object* v_k_1129_){
_start:
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = lean_nat_dec_lt(v___x_1130_, v_k_1129_);
if (v___x_1131_ == 0)
{
lean_dec(v_k_1129_);
lean_dec(v_p_u2082_1128_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1132_ = lean_nat_to_int(v_k_1129_);
v___x_1133_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1128_, v___x_1132_);
lean_dec(v___x_1132_);
v___x_1134_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2081_1127_, v___x_1133_);
lean_dec(v___x_1133_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_coeff__cert___boxed(lean_object* v_p_u2081_1135_, lean_object* v_p_u2082_1136_, lean_object* v_k_1137_){
_start:
{
uint8_t v_res_1138_; lean_object* v_r_1139_; 
v_res_1138_ = l_Lean_Grind_Linarith_coeff__cert(v_p_u2081_1135_, v_p_u2082_1136_, v_k_1137_);
lean_dec(v_p_u2081_1135_);
v_r_1139_ = lean_box(v_res_1138_);
return v_r_1139_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__diseq__subst__cert(lean_object* v_k_u2081_1140_, lean_object* v_k_u2082_1141_, lean_object* v_p_u2081_1142_, lean_object* v_p_u2082_1143_, lean_object* v_p_u2083_1144_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = lean_nat_abs(v_k_u2081_1140_);
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = lean_nat_dec_eq(v___x_1145_, v___x_1146_);
lean_dec(v___x_1145_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1148_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1142_, v_k_u2082_1141_);
v___x_1149_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1143_, v_k_u2081_1140_);
v___x_1150_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1148_, v___x_1149_);
v___x_1151_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1144_, v___x_1150_);
lean_dec(v___x_1150_);
return v___x_1151_;
}
else
{
uint8_t v___x_1152_; 
lean_dec(v_p_u2082_1143_);
lean_dec(v_p_u2081_1142_);
v___x_1152_ = 0;
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__diseq__subst__cert___boxed(lean_object* v_k_u2081_1153_, lean_object* v_k_u2082_1154_, lean_object* v_p_u2081_1155_, lean_object* v_p_u2082_1156_, lean_object* v_p_u2083_1157_){
_start:
{
uint8_t v_res_1158_; lean_object* v_r_1159_; 
v_res_1158_ = l_Lean_Grind_Linarith_eq__diseq__subst__cert(v_k_u2081_1153_, v_k_u2082_1154_, v_p_u2081_1155_, v_p_u2082_1156_, v_p_u2083_1157_);
lean_dec(v_p_u2083_1157_);
lean_dec(v_k_u2082_1154_);
lean_dec(v_k_u2081_1153_);
v_r_1159_ = lean_box(v_res_1158_);
return v_r_1159_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__diseq__subst1__cert(lean_object* v_k_1160_, lean_object* v_p_u2081_1161_, lean_object* v_p_u2082_1162_, lean_object* v_p_u2083_1163_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1164_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1161_, v_k_1160_);
v___x_1165_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1164_, v_p_u2082_1162_);
v___x_1166_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1163_, v___x_1165_);
lean_dec(v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__diseq__subst1__cert___boxed(lean_object* v_k_1167_, lean_object* v_p_u2081_1168_, lean_object* v_p_u2082_1169_, lean_object* v_p_u2083_1170_){
_start:
{
uint8_t v_res_1171_; lean_object* v_r_1172_; 
v_res_1171_ = l_Lean_Grind_Linarith_eq__diseq__subst1__cert(v_k_1167_, v_p_u2081_1168_, v_p_u2082_1169_, v_p_u2083_1170_);
lean_dec(v_p_u2083_1170_);
lean_dec(v_k_1167_);
v_r_1172_ = lean_box(v_res_1171_);
return v_r_1172_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__le__subst__cert(lean_object* v_x_1173_, lean_object* v_p_u2081_1174_, lean_object* v_p_u2082_1175_, lean_object* v_p_u2083_1176_){
_start:
{
lean_object* v_a_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_a_1177_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_1174_, v_x_1173_);
v___x_1178_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1179_ = lean_int_dec_le(v___x_1178_, v_a_1177_);
if (v___x_1179_ == 0)
{
lean_dec(v_a_1177_);
lean_dec(v_p_u2082_1175_);
lean_dec(v_p_u2081_1174_);
return v___x_1179_;
}
else
{
lean_object* v_b_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v_b_1180_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_1175_, v_x_1173_);
v___x_1181_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1175_, v_a_1177_);
lean_dec(v_a_1177_);
v___x_1182_ = lean_int_neg(v_b_1180_);
lean_dec(v_b_1180_);
v___x_1183_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1174_, v___x_1182_);
lean_dec(v___x_1182_);
v___x_1184_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1181_, v___x_1183_);
v___x_1185_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1176_, v___x_1184_);
lean_dec(v___x_1184_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__le__subst__cert___boxed(lean_object* v_x_1186_, lean_object* v_p_u2081_1187_, lean_object* v_p_u2082_1188_, lean_object* v_p_u2083_1189_){
_start:
{
uint8_t v_res_1190_; lean_object* v_r_1191_; 
v_res_1190_ = l_Lean_Grind_Linarith_eq__le__subst__cert(v_x_1186_, v_p_u2081_1187_, v_p_u2082_1188_, v_p_u2083_1189_);
lean_dec(v_p_u2083_1189_);
lean_dec(v_x_1186_);
v_r_1191_ = lean_box(v_res_1190_);
return v_r_1191_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__lt__subst__cert(lean_object* v_x_1192_, lean_object* v_p_u2081_1193_, lean_object* v_p_u2082_1194_, lean_object* v_p_u2083_1195_){
_start:
{
lean_object* v_a_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v_a_1196_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_1193_, v_x_1192_);
v___x_1197_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1198_ = lean_int_dec_lt(v___x_1197_, v_a_1196_);
if (v___x_1198_ == 0)
{
lean_dec(v_a_1196_);
lean_dec(v_p_u2082_1194_);
lean_dec(v_p_u2081_1193_);
return v___x_1198_;
}
else
{
lean_object* v_b_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v_b_1199_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_1194_, v_x_1192_);
v___x_1200_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1194_, v_a_1196_);
lean_dec(v_a_1196_);
v___x_1201_ = lean_int_neg(v_b_1199_);
lean_dec(v_b_1199_);
v___x_1202_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1193_, v___x_1201_);
lean_dec(v___x_1201_);
v___x_1203_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1200_, v___x_1202_);
v___x_1204_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1195_, v___x_1203_);
lean_dec(v___x_1203_);
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__lt__subst__cert___boxed(lean_object* v_x_1205_, lean_object* v_p_u2081_1206_, lean_object* v_p_u2082_1207_, lean_object* v_p_u2083_1208_){
_start:
{
uint8_t v_res_1209_; lean_object* v_r_1210_; 
v_res_1209_ = l_Lean_Grind_Linarith_eq__lt__subst__cert(v_x_1205_, v_p_u2081_1206_, v_p_u2082_1207_, v_p_u2083_1208_);
lean_dec(v_p_u2083_1208_);
lean_dec(v_x_1205_);
v_r_1210_ = lean_box(v_res_1209_);
return v_r_1210_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__eq__subst__cert(lean_object* v_x_1211_, lean_object* v_p_u2081_1212_, lean_object* v_p_u2082_1213_, lean_object* v_p_u2083_1214_){
_start:
{
lean_object* v_a_1215_; lean_object* v_b_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v_a_1215_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_1212_, v_x_1211_);
v_b_1216_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_1213_, v_x_1211_);
v___x_1217_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1213_, v_a_1215_);
lean_dec(v_a_1215_);
v___x_1218_ = lean_int_neg(v_b_1216_);
lean_dec(v_b_1216_);
v___x_1219_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1212_, v___x_1218_);
lean_dec(v___x_1218_);
v___x_1220_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1217_, v___x_1219_);
v___x_1221_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1214_, v___x_1220_);
lean_dec(v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__eq__subst__cert___boxed(lean_object* v_x_1222_, lean_object* v_p_u2081_1223_, lean_object* v_p_u2082_1224_, lean_object* v_p_u2083_1225_){
_start:
{
uint8_t v_res_1226_; lean_object* v_r_1227_; 
v_res_1226_ = l_Lean_Grind_Linarith_eq__eq__subst__cert(v_x_1222_, v_p_u2081_1223_, v_p_u2082_1224_, v_p_u2083_1225_);
lean_dec(v_p_u2083_1225_);
lean_dec(v_x_1222_);
v_r_1227_ = lean_box(v_res_1226_);
return v_r_1227_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_imp__eq__cert(lean_object* v_p_1228_, lean_object* v_x_1229_, lean_object* v_y_1230_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1231_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1232_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1233_ = lean_box(0);
v___x_1234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v_y_1230_);
lean_ctor_set(v___x_1234_, 2, v___x_1233_);
v___x_1235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1231_);
lean_ctor_set(v___x_1235_, 1, v_x_1229_);
lean_ctor_set(v___x_1235_, 2, v___x_1234_);
v___x_1236_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1228_, v___x_1235_);
lean_dec_ref_known(v___x_1235_, 3);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_imp__eq__cert___boxed(lean_object* v_p_1237_, lean_object* v_x_1238_, lean_object* v_y_1239_){
_start:
{
uint8_t v_res_1240_; lean_object* v_r_1241_; 
v_res_1240_ = l_Lean_Grind_Linarith_imp__eq__cert(v_p_1237_, v_x_1238_, v_y_1239_);
lean_dec(v_p_1237_);
v_r_1241_ = lean_box(v_res_1240_);
return v_r_1241_;
}
}
lean_object* runtime_initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_Field(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_AC(uint8_t builtin);
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Ordered_Linarith(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ordered_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Field(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ordered_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_Linarith_instInhabitedExpr_default = _init_l_Lean_Grind_Linarith_instInhabitedExpr_default();
lean_mark_persistent(l_Lean_Grind_Linarith_instInhabitedExpr_default);
l_Lean_Grind_Linarith_instInhabitedExpr = _init_l_Lean_Grind_Linarith_instInhabitedExpr();
lean_mark_persistent(l_Lean_Grind_Linarith_instInhabitedExpr);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Ordered_Linarith(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_Field(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_AC(uint8_t builtin);
lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_RArray(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Grind_Ordered_Order(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Repr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Ordered_Linarith(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ordered_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Field(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ordered_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Ordered_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Ordered_Linarith(builtin);
}
#ifdef __cplusplus
}
#endif
