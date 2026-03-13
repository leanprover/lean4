// Lean compiler output
// Module: Init.Grind.Ordered.Linarith
// Imports: public import Init.Grind.Ordered.Ring public import Init.Grind.Ring.Field import all Init.Data.Ord.Basic import all Init.Data.AC import Init.LawfulBEqTactics public import Init.Data.Bool public import Init.Data.RArray import Init.Data.Int.DivMod.Lemmas import Init.Data.Nat.Lemmas import Init.Grind.Ordered.Order import Init.Omega import Init.WFTactics
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
lean_dec_ref(v_t_11_);
v___x_14_ = lean_apply_1(v_k_12_, v_i_13_);
return v___x_14_;
}
case 4:
{
lean_object* v_a_15_; lean_object* v___x_16_; 
v_a_15_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_15_);
lean_dec_ref(v_t_11_);
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
lean_dec_ref(v_x_184_);
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
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 5);
lean_ctor_set(v___x_311_, 1, v___y_318_);
lean_ctor_set(v___x_311_, 0, v___y_315_);
v___x_320_ = v___x_311_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___y_315_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___y_318_);
v___x_320_ = v_reuseFailAlloc_328_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___y_316_);
v___x_322_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_309_, v___x_313_);
v___x_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_324_, 0, v___y_317_);
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
v___y_315_ = v___x_332_;
v___y_316_ = v___x_331_;
v___y_317_ = v___y_330_;
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
v___y_315_ = v___x_332_;
v___y_316_ = v___x_331_;
v___y_317_ = v___y_330_;
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
lean_object* v___x_366_; lean_object* v_toAddCommMonoid_367_; 
v___x_366_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_363_);
v_toAddCommMonoid_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc_ref(v_toAddCommMonoid_367_);
switch(lean_obj_tag(v_x_365_))
{
case 0:
{
lean_object* v_toZero_368_; 
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
lean_dec_ref(v_toAddCommMonoid_367_);
lean_dec_ref(v___x_366_);
lean_dec_ref(v_inst_363_);
v_i_369_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_i_369_);
lean_dec_ref(v_x_365_);
v___x_370_ = l_Lean_RArray_getImpl___redArg(v_ctx_364_, v_i_369_);
lean_dec(v_i_369_);
return v___x_370_;
}
case 2:
{
lean_object* v_toAdd_371_; lean_object* v_a_372_; lean_object* v_b_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec_ref(v___x_366_);
v_toAdd_371_ = lean_ctor_get(v_toAddCommMonoid_367_, 1);
lean_inc(v_toAdd_371_);
lean_dec_ref(v_toAddCommMonoid_367_);
v_a_372_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_a_372_);
v_b_373_ = lean_ctor_get(v_x_365_, 1);
lean_inc(v_b_373_);
lean_dec_ref(v_x_365_);
lean_inc_ref(v_inst_363_);
v___x_374_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_a_372_);
v___x_375_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_b_373_);
v___x_376_ = lean_apply_2(v_toAdd_371_, v___x_374_, v___x_375_);
return v___x_376_;
}
case 3:
{
lean_object* v_toAddCommGroup_377_; lean_object* v_toSub_378_; lean_object* v_a_379_; lean_object* v_b_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_toAddCommGroup_377_ = lean_ctor_get(v_inst_363_, 0);
lean_dec_ref(v_toAddCommMonoid_367_);
lean_dec_ref(v___x_366_);
v_toSub_378_ = lean_ctor_get(v_toAddCommGroup_377_, 2);
lean_inc(v_toSub_378_);
v_a_379_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_a_379_);
v_b_380_ = lean_ctor_get(v_x_365_, 1);
lean_inc(v_b_380_);
lean_dec_ref(v_x_365_);
lean_inc_ref(v_inst_363_);
v___x_381_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_a_379_);
v___x_382_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_b_380_);
v___x_383_ = lean_apply_2(v_toSub_378_, v___x_381_, v___x_382_);
return v___x_383_;
}
case 4:
{
lean_object* v_toAddCommGroup_384_; lean_object* v_toNeg_385_; lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_toAddCommGroup_384_ = lean_ctor_get(v_inst_363_, 0);
lean_dec_ref(v_toAddCommMonoid_367_);
lean_dec_ref(v___x_366_);
v_toNeg_385_ = lean_ctor_get(v_toAddCommGroup_384_, 1);
lean_inc(v_toNeg_385_);
v_a_386_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_a_386_);
lean_dec_ref(v_x_365_);
v___x_387_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_a_386_);
v___x_388_ = lean_apply_1(v_toNeg_385_, v___x_387_);
return v___x_388_;
}
case 5:
{
lean_object* v_nsmul_389_; lean_object* v_k_390_; lean_object* v_a_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec_ref(v_toAddCommMonoid_367_);
v_nsmul_389_ = lean_ctor_get(v___x_366_, 1);
lean_inc(v_nsmul_389_);
lean_dec_ref(v___x_366_);
v_k_390_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_k_390_);
v_a_391_ = lean_ctor_get(v_x_365_, 1);
lean_inc(v_a_391_);
lean_dec_ref(v_x_365_);
v___x_392_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_a_391_);
v___x_393_ = lean_apply_2(v_nsmul_389_, v_k_390_, v___x_392_);
return v___x_393_;
}
default: 
{
lean_object* v_zsmul_394_; lean_object* v_k_395_; lean_object* v_a_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec_ref(v_toAddCommMonoid_367_);
lean_dec_ref(v___x_366_);
v_zsmul_394_ = lean_ctor_get(v_inst_363_, 2);
lean_inc(v_zsmul_394_);
v_k_395_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_k_395_);
v_a_396_ = lean_ctor_get(v_x_365_, 1);
lean_inc(v_a_396_);
lean_dec_ref(v_x_365_);
v___x_397_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_363_, v_ctx_364_, v_a_396_);
v___x_398_ = lean_apply_2(v_zsmul_394_, v_k_395_, v___x_397_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___redArg___boxed(lean_object* v_inst_399_, lean_object* v_ctx_400_, lean_object* v_x_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_399_, v_ctx_400_, v_x_401_);
lean_dec_ref(v_ctx_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote(lean_object* v_00_u03b1_403_, lean_object* v_inst_404_, lean_object* v_ctx_405_, lean_object* v_x_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_404_, v_ctx_405_, v_x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___boxed(lean_object* v_00_u03b1_408_, lean_object* v_inst_409_, lean_object* v_ctx_410_, lean_object* v_x_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Grind_Linarith_Expr_denote(v_00_u03b1_408_, v_inst_409_, v_ctx_410_, v_x_411_);
lean_dec_ref(v_ctx_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorIdx(lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_413_) == 0)
{
lean_object* v___x_414_; 
v___x_414_ = lean_unsigned_to_nat(0u);
return v___x_414_;
}
else
{
lean_object* v___x_415_; 
v___x_415_ = lean_unsigned_to_nat(1u);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorIdx___boxed(lean_object* v_x_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Grind_Linarith_Poly_ctorIdx(v_x_416_);
lean_dec(v_x_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim___redArg(lean_object* v_t_418_, lean_object* v_k_419_){
_start:
{
if (lean_obj_tag(v_t_418_) == 0)
{
return v_k_419_;
}
else
{
lean_object* v_k_420_; lean_object* v_v_421_; lean_object* v_p_422_; lean_object* v___x_423_; 
v_k_420_ = lean_ctor_get(v_t_418_, 0);
lean_inc(v_k_420_);
v_v_421_ = lean_ctor_get(v_t_418_, 1);
lean_inc(v_v_421_);
v_p_422_ = lean_ctor_get(v_t_418_, 2);
lean_inc(v_p_422_);
lean_dec_ref(v_t_418_);
v___x_423_ = lean_apply_3(v_k_419_, v_k_420_, v_v_421_, v_p_422_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim(lean_object* v_motive_424_, lean_object* v_ctorIdx_425_, lean_object* v_t_426_, lean_object* v_h_427_, lean_object* v_k_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_426_, v_k_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim___boxed(lean_object* v_motive_430_, lean_object* v_ctorIdx_431_, lean_object* v_t_432_, lean_object* v_h_433_, lean_object* v_k_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Grind_Linarith_Poly_ctorElim(v_motive_430_, v_ctorIdx_431_, v_t_432_, v_h_433_, v_k_434_);
lean_dec(v_ctorIdx_431_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_nil_elim___redArg(lean_object* v_t_436_, lean_object* v_nil_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_436_, v_nil_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_nil_elim(lean_object* v_motive_439_, lean_object* v_t_440_, lean_object* v_h_441_, lean_object* v_nil_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_440_, v_nil_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_add_elim___redArg(lean_object* v_t_444_, lean_object* v_add_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_444_, v_add_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_add_elim(lean_object* v_motive_447_, lean_object* v_t_448_, lean_object* v_h_449_, lean_object* v_add_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_448_, v_add_450_);
return v___x_451_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_instBEqPoly_beq(lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
if (lean_obj_tag(v_x_452_) == 0)
{
if (lean_obj_tag(v_x_453_) == 0)
{
uint8_t v___x_454_; 
v___x_454_ = 1;
return v___x_454_;
}
else
{
uint8_t v___x_455_; 
v___x_455_ = 0;
return v___x_455_;
}
}
else
{
if (lean_obj_tag(v_x_453_) == 1)
{
lean_object* v_k_456_; lean_object* v_v_457_; lean_object* v_p_458_; lean_object* v_k_459_; lean_object* v_v_460_; lean_object* v_p_461_; uint8_t v___x_462_; 
v_k_456_ = lean_ctor_get(v_x_452_, 0);
v_v_457_ = lean_ctor_get(v_x_452_, 1);
v_p_458_ = lean_ctor_get(v_x_452_, 2);
v_k_459_ = lean_ctor_get(v_x_453_, 0);
v_v_460_ = lean_ctor_get(v_x_453_, 1);
v_p_461_ = lean_ctor_get(v_x_453_, 2);
v___x_462_ = lean_int_dec_eq(v_k_456_, v_k_459_);
if (v___x_462_ == 0)
{
return v___x_462_;
}
else
{
uint8_t v___x_463_; 
v___x_463_ = lean_nat_dec_eq(v_v_457_, v_v_460_);
if (v___x_463_ == 0)
{
return v___x_463_;
}
else
{
v_x_452_ = v_p_458_;
v_x_453_ = v_p_461_;
goto _start;
}
}
}
else
{
uint8_t v___x_465_; 
v___x_465_ = 0;
return v___x_465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instBEqPoly_beq___boxed(lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
uint8_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_x_466_, v_x_467_);
lean_dec(v_x_467_);
lean_dec(v_x_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v_h__1_474_, lean_object* v_h__2_475_, lean_object* v_h__3_476_){
_start:
{
if (lean_obj_tag(v_x_472_) == 0)
{
lean_dec(v_h__2_475_);
if (lean_obj_tag(v_x_473_) == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_h__3_476_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_apply_1(v_h__1_474_, v___x_477_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
lean_dec(v_h__1_474_);
v___x_479_ = lean_apply_4(v_h__3_476_, v_x_472_, v_x_473_, lean_box(0), lean_box(0));
return v___x_479_;
}
}
else
{
lean_dec(v_h__1_474_);
if (lean_obj_tag(v_x_473_) == 1)
{
lean_object* v_k_480_; lean_object* v_v_481_; lean_object* v_p_482_; lean_object* v_k_483_; lean_object* v_v_484_; lean_object* v_p_485_; lean_object* v___x_486_; 
lean_dec(v_h__3_476_);
v_k_480_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_k_480_);
v_v_481_ = lean_ctor_get(v_x_472_, 1);
lean_inc(v_v_481_);
v_p_482_ = lean_ctor_get(v_x_472_, 2);
lean_inc(v_p_482_);
lean_dec_ref(v_x_472_);
v_k_483_ = lean_ctor_get(v_x_473_, 0);
lean_inc(v_k_483_);
v_v_484_ = lean_ctor_get(v_x_473_, 1);
lean_inc(v_v_484_);
v_p_485_ = lean_ctor_get(v_x_473_, 2);
lean_inc(v_p_485_);
lean_dec_ref(v_x_473_);
v___x_486_ = lean_apply_6(v_h__2_475_, v_k_480_, v_v_481_, v_p_482_, v_k_483_, v_v_484_, v_p_485_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; 
lean_dec(v_h__2_475_);
v___x_487_ = lean_apply_4(v_h__3_476_, v_x_472_, v_x_473_, lean_box(0), lean_box(0));
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_488_, lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_h__1_491_, lean_object* v_h__2_492_, lean_object* v_h__3_493_){
_start:
{
if (lean_obj_tag(v_x_489_) == 0)
{
lean_dec(v_h__2_492_);
if (lean_obj_tag(v_x_490_) == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v_h__3_493_);
v___x_494_ = lean_box(0);
v___x_495_ = lean_apply_1(v_h__1_491_, v___x_494_);
return v___x_495_;
}
else
{
lean_object* v___x_496_; 
lean_dec(v_h__1_491_);
v___x_496_ = lean_apply_4(v_h__3_493_, v_x_489_, v_x_490_, lean_box(0), lean_box(0));
return v___x_496_;
}
}
else
{
lean_dec(v_h__1_491_);
if (lean_obj_tag(v_x_490_) == 1)
{
lean_object* v_k_497_; lean_object* v_v_498_; lean_object* v_p_499_; lean_object* v_k_500_; lean_object* v_v_501_; lean_object* v_p_502_; lean_object* v___x_503_; 
lean_dec(v_h__3_493_);
v_k_497_ = lean_ctor_get(v_x_489_, 0);
lean_inc(v_k_497_);
v_v_498_ = lean_ctor_get(v_x_489_, 1);
lean_inc(v_v_498_);
v_p_499_ = lean_ctor_get(v_x_489_, 2);
lean_inc(v_p_499_);
lean_dec_ref(v_x_489_);
v_k_500_ = lean_ctor_get(v_x_490_, 0);
lean_inc(v_k_500_);
v_v_501_ = lean_ctor_get(v_x_490_, 1);
lean_inc(v_v_501_);
v_p_502_ = lean_ctor_get(v_x_490_, 2);
lean_inc(v_p_502_);
lean_dec_ref(v_x_490_);
v___x_503_ = lean_apply_6(v_h__2_492_, v_k_497_, v_v_498_, v_p_499_, v_k_500_, v_v_501_, v_p_502_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; 
lean_dec(v_h__2_492_);
v___x_504_ = lean_apply_4(v_h__3_493_, v_x_489_, v_x_490_, lean_box(0), lean_box(0));
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprPoly_repr(lean_object* v_x_514_, lean_object* v_prec_515_){
_start:
{
lean_object* v___y_517_; 
if (lean_obj_tag(v_x_514_) == 0)
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(1024u);
v___x_524_ = lean_nat_dec_le(v___x_523_, v_prec_515_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
v___x_525_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_517_ = v___x_525_;
goto v___jp_516_;
}
else
{
lean_object* v___x_526_; 
v___x_526_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_517_ = v___x_526_;
goto v___jp_516_;
}
}
else
{
lean_object* v_k_527_; lean_object* v_v_528_; lean_object* v_p_529_; lean_object* v___x_530_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_549_; uint8_t v___x_559_; 
v_k_527_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_k_527_);
v_v_528_ = lean_ctor_get(v_x_514_, 1);
lean_inc(v_v_528_);
v_p_529_ = lean_ctor_get(v_x_514_, 2);
lean_inc(v_p_529_);
lean_dec_ref(v_x_514_);
v___x_530_ = lean_unsigned_to_nat(1024u);
v___x_559_ = lean_nat_dec_le(v___x_530_, v_prec_515_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_549_ = v___x_560_;
goto v___jp_548_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_549_ = v___x_561_;
goto v___jp_548_;
}
v___jp_531_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_536_, 0, v___y_532_);
lean_ctor_set(v___x_536_, 1, v___y_535_);
lean_inc(v___y_533_);
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___y_533_);
v___x_538_ = l_Nat_reprFast(v_v_528_);
v___x_539_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
v___x_540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_537_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___y_533_);
v___x_542_ = l_Lean_Grind_Linarith_instReprPoly_repr(v_p_529_, v___x_530_);
v___x_543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_544_, 0, v___y_534_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = 0;
v___x_546_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*1, v___x_545_);
v___x_547_ = l_Repr_addAppParen(v___x_546_, v_prec_515_);
return v___x_547_;
}
v___jp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_550_ = lean_box(1);
v___x_551_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprPoly_repr___closed__4));
v___x_552_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_553_ = lean_int_dec_lt(v_k_527_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = l_Int_repr(v_k_527_);
lean_dec(v_k_527_);
v___x_555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
v___y_532_ = v___x_551_;
v___y_533_ = v___x_550_;
v___y_534_ = v___y_549_;
v___y_535_ = v___x_555_;
goto v___jp_531_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = l_Int_repr(v_k_527_);
lean_dec(v_k_527_);
v___x_557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
v___x_558_ = l_Repr_addAppParen(v___x_557_, v___x_530_);
v___y_532_ = v___x_551_;
v___y_533_ = v___x_550_;
v___y_534_ = v___y_549_;
v___y_535_ = v___x_558_;
goto v___jp_531_;
}
}
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_518_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprPoly_repr___closed__1));
v___x_519_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_519_, 0, v___y_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = 0;
v___x_521_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*1, v___x_520_);
v___x_522_ = l_Repr_addAppParen(v___x_521_, v_prec_515_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprPoly_repr___boxed(lean_object* v_x_562_, lean_object* v_prec_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Grind_Linarith_instReprPoly_repr(v_x_562_, v_prec_563_);
lean_dec(v_prec_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___redArg(lean_object* v_inst_567_, lean_object* v_ctx_568_, lean_object* v_p_569_){
_start:
{
lean_object* v___x_570_; lean_object* v_toAddCommMonoid_571_; 
v___x_570_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_567_);
v_toAddCommMonoid_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc_ref(v_toAddCommMonoid_571_);
lean_dec_ref(v___x_570_);
if (lean_obj_tag(v_p_569_) == 0)
{
lean_object* v_toZero_572_; 
lean_dec_ref(v_inst_567_);
v_toZero_572_ = lean_ctor_get(v_toAddCommMonoid_571_, 0);
lean_inc(v_toZero_572_);
lean_dec_ref(v_toAddCommMonoid_571_);
return v_toZero_572_;
}
else
{
lean_object* v_toAdd_573_; lean_object* v_zsmul_574_; lean_object* v_k_575_; lean_object* v_v_576_; lean_object* v_p_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_toAdd_573_ = lean_ctor_get(v_toAddCommMonoid_571_, 1);
lean_inc(v_toAdd_573_);
lean_dec_ref(v_toAddCommMonoid_571_);
v_zsmul_574_ = lean_ctor_get(v_inst_567_, 2);
v_k_575_ = lean_ctor_get(v_p_569_, 0);
lean_inc(v_k_575_);
v_v_576_ = lean_ctor_get(v_p_569_, 1);
lean_inc(v_v_576_);
v_p_577_ = lean_ctor_get(v_p_569_, 2);
lean_inc(v_p_577_);
lean_dec_ref(v_p_569_);
v___x_578_ = l_Lean_RArray_getImpl___redArg(v_ctx_568_, v_v_576_);
lean_dec(v_v_576_);
lean_inc(v_zsmul_574_);
v___x_579_ = lean_apply_2(v_zsmul_574_, v_k_575_, v___x_578_);
v___x_580_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_567_, v_ctx_568_, v_p_577_);
v___x_581_ = lean_apply_2(v_toAdd_573_, v___x_579_, v___x_580_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___redArg___boxed(lean_object* v_inst_582_, lean_object* v_ctx_583_, lean_object* v_p_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_582_, v_ctx_583_, v_p_584_);
lean_dec_ref(v_ctx_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote(lean_object* v_00_u03b1_586_, lean_object* v_inst_587_, lean_object* v_ctx_588_, lean_object* v_p_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_587_, v_ctx_588_, v_p_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___boxed(lean_object* v_00_u03b1_591_, lean_object* v_inst_592_, lean_object* v_ctx_593_, lean_object* v_p_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Grind_Linarith_Poly_denote(v_00_u03b1_591_, v_inst_592_, v_ctx_593_, v_p_594_);
lean_dec_ref(v_ctx_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(lean_object* v_inst_596_, lean_object* v_ctx_597_, lean_object* v_r_598_, lean_object* v_p_599_){
_start:
{
lean_object* v___x_600_; lean_object* v_toAddCommMonoid_601_; 
v___x_600_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_596_);
v_toAddCommMonoid_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc_ref(v_toAddCommMonoid_601_);
lean_dec_ref(v___x_600_);
if (lean_obj_tag(v_p_599_) == 0)
{
lean_dec_ref(v_toAddCommMonoid_601_);
lean_dec_ref(v_inst_596_);
return v_r_598_;
}
else
{
lean_object* v_toAdd_602_; lean_object* v_zsmul_603_; lean_object* v_k_604_; lean_object* v_v_605_; lean_object* v_p_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_toAdd_602_ = lean_ctor_get(v_toAddCommMonoid_601_, 1);
lean_inc(v_toAdd_602_);
lean_dec_ref(v_toAddCommMonoid_601_);
v_zsmul_603_ = lean_ctor_get(v_inst_596_, 2);
v_k_604_ = lean_ctor_get(v_p_599_, 0);
lean_inc(v_k_604_);
v_v_605_ = lean_ctor_get(v_p_599_, 1);
lean_inc(v_v_605_);
v_p_606_ = lean_ctor_get(v_p_599_, 2);
lean_inc(v_p_606_);
lean_dec_ref(v_p_599_);
v___x_607_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_608_ = lean_int_dec_eq(v_k_604_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = l_Lean_RArray_getImpl___redArg(v_ctx_597_, v_v_605_);
lean_dec(v_v_605_);
lean_inc(v_zsmul_603_);
v___x_610_ = lean_apply_2(v_zsmul_603_, v_k_604_, v___x_609_);
v___x_611_ = lean_apply_2(v_toAdd_602_, v_r_598_, v___x_610_);
v_r_598_ = v___x_611_;
v_p_599_ = v_p_606_;
goto _start;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_k_604_);
v___x_613_ = l_Lean_RArray_getImpl___redArg(v_ctx_597_, v_v_605_);
lean_dec(v_v_605_);
v___x_614_ = lean_apply_2(v_toAdd_602_, v_r_598_, v___x_613_);
v_r_598_ = v___x_614_;
v_p_599_ = v_p_606_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg___boxed(lean_object* v_inst_616_, lean_object* v_ctx_617_, lean_object* v_r_618_, lean_object* v_p_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_616_, v_ctx_617_, v_r_618_, v_p_619_);
lean_dec_ref(v_ctx_617_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go(lean_object* v_00_u03b1_621_, lean_object* v_inst_622_, lean_object* v_ctx_623_, lean_object* v_r_624_, lean_object* v_p_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_622_, v_ctx_623_, v_r_624_, v_p_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___boxed(lean_object* v_00_u03b1_627_, lean_object* v_inst_628_, lean_object* v_ctx_629_, lean_object* v_r_630_, lean_object* v_p_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Grind_Linarith_Poly_denote_x27_go(v_00_u03b1_627_, v_inst_628_, v_ctx_629_, v_r_630_, v_p_631_);
lean_dec_ref(v_ctx_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___redArg(lean_object* v_inst_633_, lean_object* v_ctx_634_, lean_object* v_p_635_){
_start:
{
lean_object* v___x_636_; lean_object* v_toAddCommMonoid_637_; 
v___x_636_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_633_);
v_toAddCommMonoid_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc_ref(v_toAddCommMonoid_637_);
lean_dec_ref(v___x_636_);
if (lean_obj_tag(v_p_635_) == 0)
{
lean_object* v_toZero_638_; 
lean_dec_ref(v_inst_633_);
v_toZero_638_ = lean_ctor_get(v_toAddCommMonoid_637_, 0);
lean_inc(v_toZero_638_);
lean_dec_ref(v_toAddCommMonoid_637_);
return v_toZero_638_;
}
else
{
lean_object* v_zsmul_639_; lean_object* v_k_640_; lean_object* v_v_641_; lean_object* v_p_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
lean_dec_ref(v_toAddCommMonoid_637_);
v_zsmul_639_ = lean_ctor_get(v_inst_633_, 2);
v_k_640_ = lean_ctor_get(v_p_635_, 0);
lean_inc(v_k_640_);
v_v_641_ = lean_ctor_get(v_p_635_, 1);
lean_inc(v_v_641_);
v_p_642_ = lean_ctor_get(v_p_635_, 2);
lean_inc(v_p_642_);
lean_dec_ref(v_p_635_);
v___x_643_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_644_ = lean_int_dec_eq(v_k_640_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = l_Lean_RArray_getImpl___redArg(v_ctx_634_, v_v_641_);
lean_dec(v_v_641_);
lean_inc(v_zsmul_639_);
v___x_646_ = lean_apply_2(v_zsmul_639_, v_k_640_, v___x_645_);
v___x_647_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_633_, v_ctx_634_, v___x_646_, v_p_642_);
return v___x_647_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v_k_640_);
v___x_648_ = l_Lean_RArray_getImpl___redArg(v_ctx_634_, v_v_641_);
lean_dec(v_v_641_);
v___x_649_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_633_, v_ctx_634_, v___x_648_, v_p_642_);
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___redArg___boxed(lean_object* v_inst_650_, lean_object* v_ctx_651_, lean_object* v_p_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Grind_Linarith_Poly_denote_x27___redArg(v_inst_650_, v_ctx_651_, v_p_652_);
lean_dec_ref(v_ctx_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27(lean_object* v_00_u03b1_654_, lean_object* v_inst_655_, lean_object* v_ctx_656_, lean_object* v_p_657_){
_start:
{
lean_object* v___x_658_; lean_object* v_toAddCommMonoid_659_; 
v___x_658_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_655_);
v_toAddCommMonoid_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc_ref(v_toAddCommMonoid_659_);
lean_dec_ref(v___x_658_);
if (lean_obj_tag(v_p_657_) == 0)
{
lean_object* v_toZero_660_; 
lean_dec_ref(v_inst_655_);
v_toZero_660_ = lean_ctor_get(v_toAddCommMonoid_659_, 0);
lean_inc(v_toZero_660_);
lean_dec_ref(v_toAddCommMonoid_659_);
return v_toZero_660_;
}
else
{
lean_object* v_zsmul_661_; lean_object* v_k_662_; lean_object* v_v_663_; lean_object* v_p_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
lean_dec_ref(v_toAddCommMonoid_659_);
v_zsmul_661_ = lean_ctor_get(v_inst_655_, 2);
v_k_662_ = lean_ctor_get(v_p_657_, 0);
lean_inc(v_k_662_);
v_v_663_ = lean_ctor_get(v_p_657_, 1);
lean_inc(v_v_663_);
v_p_664_ = lean_ctor_get(v_p_657_, 2);
lean_inc(v_p_664_);
lean_dec_ref(v_p_657_);
v___x_665_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_666_ = lean_int_dec_eq(v_k_662_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = l_Lean_RArray_getImpl___redArg(v_ctx_656_, v_v_663_);
lean_dec(v_v_663_);
lean_inc(v_zsmul_661_);
v___x_668_ = lean_apply_2(v_zsmul_661_, v_k_662_, v___x_667_);
v___x_669_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_655_, v_ctx_656_, v___x_668_, v_p_664_);
return v___x_669_;
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec(v_k_662_);
v___x_670_ = l_Lean_RArray_getImpl___redArg(v_ctx_656_, v_v_663_);
lean_dec(v_v_663_);
v___x_671_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_655_, v_ctx_656_, v___x_670_, v_p_664_);
return v___x_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___boxed(lean_object* v_00_u03b1_672_, lean_object* v_inst_673_, lean_object* v_ctx_674_, lean_object* v_p_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Grind_Linarith_Poly_denote_x27(v_00_u03b1_672_, v_inst_673_, v_ctx_674_, v_p_675_);
lean_dec_ref(v_ctx_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter___redArg(lean_object* v_p_677_, lean_object* v_h__1_678_, lean_object* v_h__2_679_, lean_object* v_h__3_680_){
_start:
{
if (lean_obj_tag(v_p_677_) == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec(v_h__3_680_);
lean_dec(v_h__2_679_);
v___x_681_ = lean_box(0);
v___x_682_ = lean_apply_1(v_h__1_678_, v___x_681_);
return v___x_682_;
}
else
{
lean_object* v_k_683_; lean_object* v_v_684_; lean_object* v_p_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
lean_dec(v_h__1_678_);
v_k_683_ = lean_ctor_get(v_p_677_, 0);
lean_inc(v_k_683_);
v_v_684_ = lean_ctor_get(v_p_677_, 1);
lean_inc(v_v_684_);
v_p_685_ = lean_ctor_get(v_p_677_, 2);
lean_inc(v_p_685_);
lean_dec_ref(v_p_677_);
v___x_686_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_687_ = lean_int_dec_eq(v_k_683_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
lean_dec(v_h__2_679_);
v___x_688_ = lean_apply_4(v_h__3_680_, v_k_683_, v_v_684_, v_p_685_, lean_box(0));
return v___x_688_;
}
else
{
lean_object* v___x_689_; 
lean_dec(v_k_683_);
lean_dec(v_h__3_680_);
v___x_689_ = lean_apply_2(v_h__2_679_, v_v_684_, v_p_685_);
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter(lean_object* v_motive_690_, lean_object* v_p_691_, lean_object* v_h__1_692_, lean_object* v_h__2_693_, lean_object* v_h__3_694_){
_start:
{
if (lean_obj_tag(v_p_691_) == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec(v_h__3_694_);
lean_dec(v_h__2_693_);
v___x_695_ = lean_box(0);
v___x_696_ = lean_apply_1(v_h__1_692_, v___x_695_);
return v___x_696_;
}
else
{
lean_object* v_k_697_; lean_object* v_v_698_; lean_object* v_p_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
lean_dec(v_h__1_692_);
v_k_697_ = lean_ctor_get(v_p_691_, 0);
lean_inc(v_k_697_);
v_v_698_ = lean_ctor_get(v_p_691_, 1);
lean_inc(v_v_698_);
v_p_699_ = lean_ctor_get(v_p_691_, 2);
lean_inc(v_p_699_);
lean_dec_ref(v_p_691_);
v___x_700_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_701_ = lean_int_dec_eq(v_k_697_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
lean_dec(v_h__2_693_);
v___x_702_ = lean_apply_4(v_h__3_694_, v_k_697_, v_v_698_, v_p_699_, lean_box(0));
return v___x_702_;
}
else
{
lean_object* v___x_703_; 
lean_dec(v_k_697_);
lean_dec(v_h__3_694_);
v___x_703_ = lean_apply_2(v_h__2_693_, v_v_698_, v_p_699_);
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_coeff(lean_object* v_p_704_, lean_object* v_x_705_){
_start:
{
if (lean_obj_tag(v_p_704_) == 0)
{
lean_object* v___x_706_; 
v___x_706_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
return v___x_706_;
}
else
{
lean_object* v_k_707_; lean_object* v_v_708_; lean_object* v_p_709_; uint8_t v___x_710_; 
v_k_707_ = lean_ctor_get(v_p_704_, 0);
v_v_708_ = lean_ctor_get(v_p_704_, 1);
v_p_709_ = lean_ctor_get(v_p_704_, 2);
v___x_710_ = lean_nat_dec_eq(v_x_705_, v_v_708_);
if (v___x_710_ == 0)
{
v_p_704_ = v_p_709_;
goto _start;
}
else
{
lean_inc(v_k_707_);
return v_k_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_coeff___boxed(lean_object* v_p_712_, lean_object* v_x_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_712_, v_x_713_);
lean_dec(v_x_713_);
lean_dec(v_p_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_insert(lean_object* v_k_715_, lean_object* v_v_716_, lean_object* v_p_717_){
_start:
{
if (lean_obj_tag(v_p_717_) == 0)
{
lean_object* v___x_718_; 
v___x_718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_718_, 0, v_k_715_);
lean_ctor_set(v___x_718_, 1, v_v_716_);
lean_ctor_set(v___x_718_, 2, v_p_717_);
return v___x_718_;
}
else
{
lean_object* v_k_719_; lean_object* v_v_720_; lean_object* v_p_721_; uint8_t v___x_722_; 
v_k_719_ = lean_ctor_get(v_p_717_, 0);
v_v_720_ = lean_ctor_get(v_p_717_, 1);
v_p_721_ = lean_ctor_get(v_p_717_, 2);
v___x_722_ = l_Nat_blt(v_v_720_, v_v_716_);
if (v___x_722_ == 0)
{
lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_737_; 
lean_inc(v_p_721_);
lean_inc(v_v_720_);
lean_inc(v_k_719_);
v_isSharedCheck_737_ = !lean_is_exclusive(v_p_717_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; lean_object* v_unused_739_; lean_object* v_unused_740_; 
v_unused_738_ = lean_ctor_get(v_p_717_, 2);
lean_dec(v_unused_738_);
v_unused_739_ = lean_ctor_get(v_p_717_, 1);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_p_717_, 0);
lean_dec(v_unused_740_);
v___x_724_ = v_p_717_;
v_isShared_725_ = v_isSharedCheck_737_;
goto v_resetjp_723_;
}
else
{
lean_dec(v_p_717_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_737_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
uint8_t v___x_726_; 
v___x_726_ = lean_nat_dec_eq(v_v_716_, v_v_720_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = l_Lean_Grind_Linarith_Poly_insert(v_k_715_, v_v_716_, v_p_721_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 2, v___x_727_);
v___x_729_ = v___x_724_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_k_719_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_v_720_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
lean_dec(v_v_716_);
v___x_731_ = lean_int_add(v_k_715_, v_k_719_);
lean_dec(v_k_719_);
lean_dec(v_k_715_);
v___x_732_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_733_ = lean_int_dec_eq(v___x_731_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_735_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_731_);
v___x_735_ = v___x_724_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_v_720_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v_p_721_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
else
{
lean_dec(v___x_731_);
lean_del_object(v___x_724_);
lean_dec(v_v_720_);
return v_p_721_;
}
}
}
}
else
{
lean_object* v___x_741_; 
v___x_741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_741_, 0, v_k_715_);
lean_ctor_set(v___x_741_, 1, v_v_716_);
lean_ctor_set(v___x_741_, 2, v_p_717_);
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_norm(lean_object* v_p_742_){
_start:
{
if (lean_obj_tag(v_p_742_) == 0)
{
return v_p_742_;
}
else
{
lean_object* v_k_743_; lean_object* v_v_744_; lean_object* v_p_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_k_743_ = lean_ctor_get(v_p_742_, 0);
lean_inc(v_k_743_);
v_v_744_ = lean_ctor_get(v_p_742_, 1);
lean_inc(v_v_744_);
v_p_745_ = lean_ctor_get(v_p_742_, 2);
lean_inc(v_p_745_);
lean_dec_ref(v_p_742_);
v___x_746_ = l_Lean_Grind_Linarith_Poly_norm(v_p_745_);
v___x_747_ = l_Lean_Grind_Linarith_Poly_insert(v_k_743_, v_v_744_, v___x_746_);
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_append(lean_object* v_p_u2081_748_, lean_object* v_p_u2082_749_){
_start:
{
if (lean_obj_tag(v_p_u2081_748_) == 0)
{
lean_inc(v_p_u2082_749_);
return v_p_u2082_749_;
}
else
{
lean_object* v_k_750_; lean_object* v_v_751_; lean_object* v_p_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_760_; 
v_k_750_ = lean_ctor_get(v_p_u2081_748_, 0);
v_v_751_ = lean_ctor_get(v_p_u2081_748_, 1);
v_p_752_ = lean_ctor_get(v_p_u2081_748_, 2);
v_isSharedCheck_760_ = !lean_is_exclusive(v_p_u2081_748_);
if (v_isSharedCheck_760_ == 0)
{
v___x_754_ = v_p_u2081_748_;
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_p_752_);
lean_inc(v_v_751_);
lean_inc(v_k_750_);
lean_dec(v_p_u2081_748_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_756_ = l_Lean_Grind_Linarith_Poly_append(v_p_752_, v_p_u2082_749_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 2, v___x_756_);
v___x_758_ = v___x_754_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_k_750_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_v_751_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_append___boxed(lean_object* v_p_u2081_761_, lean_object* v_p_u2082_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Grind_Linarith_Poly_append(v_p_u2081_761_, v_p_u2082_762_);
lean_dec(v_p_u2082_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_combine(lean_object* v_p_u2081_764_, lean_object* v_p_u2082_765_){
_start:
{
if (lean_obj_tag(v_p_u2081_764_) == 0)
{
return v_p_u2082_765_;
}
else
{
if (lean_obj_tag(v_p_u2082_765_) == 0)
{
return v_p_u2081_764_;
}
else
{
lean_object* v_k_766_; lean_object* v_v_767_; lean_object* v_p_768_; lean_object* v_k_769_; lean_object* v_v_770_; lean_object* v_p_771_; uint8_t v___x_772_; 
v_k_766_ = lean_ctor_get(v_p_u2081_764_, 0);
v_v_767_ = lean_ctor_get(v_p_u2081_764_, 1);
v_p_768_ = lean_ctor_get(v_p_u2081_764_, 2);
v_k_769_ = lean_ctor_get(v_p_u2082_765_, 0);
v_v_770_ = lean_ctor_get(v_p_u2082_765_, 1);
v_p_771_ = lean_ctor_get(v_p_u2082_765_, 2);
v___x_772_ = lean_nat_dec_eq(v_v_767_, v_v_770_);
if (v___x_772_ == 0)
{
uint8_t v___x_773_; 
v___x_773_ = l_Nat_blt(v_v_770_, v_v_767_);
if (v___x_773_ == 0)
{
lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_781_; 
lean_inc(v_p_771_);
lean_inc(v_v_770_);
lean_inc(v_k_769_);
v_isSharedCheck_781_ = !lean_is_exclusive(v_p_u2082_765_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; lean_object* v_unused_783_; lean_object* v_unused_784_; 
v_unused_782_ = lean_ctor_get(v_p_u2082_765_, 2);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_p_u2082_765_, 1);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_p_u2082_765_, 0);
lean_dec(v_unused_784_);
v___x_775_ = v_p_u2082_765_;
v_isShared_776_ = v_isSharedCheck_781_;
goto v_resetjp_774_;
}
else
{
lean_dec(v_p_u2082_765_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_781_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = l_Lean_Grind_Linarith_Poly_combine(v_p_u2081_764_, v_p_771_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 2, v___x_777_);
v___x_779_ = v___x_775_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_k_769_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_v_770_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
else
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_792_; 
lean_inc(v_p_768_);
lean_inc(v_v_767_);
lean_inc(v_k_766_);
v_isSharedCheck_792_ = !lean_is_exclusive(v_p_u2081_764_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; lean_object* v_unused_794_; lean_object* v_unused_795_; 
v_unused_793_ = lean_ctor_get(v_p_u2081_764_, 2);
lean_dec(v_unused_793_);
v_unused_794_ = lean_ctor_get(v_p_u2081_764_, 1);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_p_u2081_764_, 0);
lean_dec(v_unused_795_);
v___x_786_ = v_p_u2081_764_;
v_isShared_787_ = v_isSharedCheck_792_;
goto v_resetjp_785_;
}
else
{
lean_dec(v_p_u2081_764_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_792_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = l_Lean_Grind_Linarith_Poly_combine(v_p_768_, v_p_u2082_765_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 2, v___x_788_);
v___x_790_ = v___x_786_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_k_766_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_v_767_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_807_; 
lean_inc(v_p_771_);
lean_inc(v_k_769_);
lean_inc(v_p_768_);
lean_inc(v_v_767_);
lean_inc(v_k_766_);
lean_dec_ref(v_p_u2081_764_);
v_isSharedCheck_807_ = !lean_is_exclusive(v_p_u2082_765_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; lean_object* v_unused_809_; lean_object* v_unused_810_; 
v_unused_808_ = lean_ctor_get(v_p_u2082_765_, 2);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_p_u2082_765_, 1);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_p_u2082_765_, 0);
lean_dec(v_unused_810_);
v___x_797_ = v_p_u2082_765_;
v_isShared_798_ = v_isSharedCheck_807_;
goto v_resetjp_796_;
}
else
{
lean_dec(v_p_u2082_765_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_807_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_a_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v_a_799_ = lean_int_add(v_k_766_, v_k_769_);
lean_dec(v_k_769_);
lean_dec(v_k_766_);
v___x_800_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_801_ = lean_int_dec_eq(v_a_799_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = l_Lean_Grind_Linarith_Poly_combine(v_p_768_, v_p_771_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 2, v___x_802_);
lean_ctor_set(v___x_797_, 1, v_v_767_);
lean_ctor_set(v___x_797_, 0, v_a_799_);
v___x_804_ = v___x_797_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_v_767_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
else
{
lean_dec(v_a_799_);
lean_del_object(v___x_797_);
lean_dec(v_v_767_);
v_p_u2081_764_ = v_p_768_;
v_p_u2082_765_ = v_p_771_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter___redArg(lean_object* v_p_u2081_811_, lean_object* v_p_u2082_812_, lean_object* v_h__1_813_, lean_object* v_h__2_814_, lean_object* v_h__3_815_){
_start:
{
if (lean_obj_tag(v_p_u2081_811_) == 0)
{
lean_object* v___x_816_; 
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
v___x_816_ = lean_apply_1(v_h__1_813_, v_p_u2082_812_);
return v___x_816_;
}
else
{
lean_dec(v_h__1_813_);
if (lean_obj_tag(v_p_u2082_812_) == 0)
{
lean_object* v___x_817_; 
lean_dec(v_h__3_815_);
v___x_817_ = lean_apply_2(v_h__2_814_, v_p_u2081_811_, lean_box(0));
return v___x_817_;
}
else
{
lean_object* v_k_818_; lean_object* v_v_819_; lean_object* v_p_820_; lean_object* v_k_821_; lean_object* v_v_822_; lean_object* v_p_823_; lean_object* v___x_824_; 
lean_dec(v_h__2_814_);
v_k_818_ = lean_ctor_get(v_p_u2081_811_, 0);
lean_inc(v_k_818_);
v_v_819_ = lean_ctor_get(v_p_u2081_811_, 1);
lean_inc(v_v_819_);
v_p_820_ = lean_ctor_get(v_p_u2081_811_, 2);
lean_inc(v_p_820_);
lean_dec_ref(v_p_u2081_811_);
v_k_821_ = lean_ctor_get(v_p_u2082_812_, 0);
lean_inc(v_k_821_);
v_v_822_ = lean_ctor_get(v_p_u2082_812_, 1);
lean_inc(v_v_822_);
v_p_823_ = lean_ctor_get(v_p_u2082_812_, 2);
lean_inc(v_p_823_);
lean_dec_ref(v_p_u2082_812_);
v___x_824_ = lean_apply_6(v_h__3_815_, v_k_818_, v_v_819_, v_p_820_, v_k_821_, v_v_822_, v_p_823_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter(lean_object* v_motive_825_, lean_object* v_p_u2081_826_, lean_object* v_p_u2082_827_, lean_object* v_h__1_828_, lean_object* v_h__2_829_, lean_object* v_h__3_830_){
_start:
{
if (lean_obj_tag(v_p_u2081_826_) == 0)
{
lean_object* v___x_831_; 
lean_dec(v_h__3_830_);
lean_dec(v_h__2_829_);
v___x_831_ = lean_apply_1(v_h__1_828_, v_p_u2082_827_);
return v___x_831_;
}
else
{
lean_dec(v_h__1_828_);
if (lean_obj_tag(v_p_u2082_827_) == 0)
{
lean_object* v___x_832_; 
lean_dec(v_h__3_830_);
v___x_832_ = lean_apply_2(v_h__2_829_, v_p_u2081_826_, lean_box(0));
return v___x_832_;
}
else
{
lean_object* v_k_833_; lean_object* v_v_834_; lean_object* v_p_835_; lean_object* v_k_836_; lean_object* v_v_837_; lean_object* v_p_838_; lean_object* v___x_839_; 
lean_dec(v_h__2_829_);
v_k_833_ = lean_ctor_get(v_p_u2081_826_, 0);
lean_inc(v_k_833_);
v_v_834_ = lean_ctor_get(v_p_u2081_826_, 1);
lean_inc(v_v_834_);
v_p_835_ = lean_ctor_get(v_p_u2081_826_, 2);
lean_inc(v_p_835_);
lean_dec_ref(v_p_u2081_826_);
v_k_836_ = lean_ctor_get(v_p_u2082_827_, 0);
lean_inc(v_k_836_);
v_v_837_ = lean_ctor_get(v_p_u2082_827_, 1);
lean_inc(v_v_837_);
v_p_838_ = lean_ctor_get(v_p_u2082_827_, 2);
lean_inc(v_p_838_);
lean_dec_ref(v_p_u2082_827_);
v___x_839_ = lean_apply_6(v_h__3_830_, v_k_833_, v_v_834_, v_p_835_, v_k_836_, v_v_837_, v_p_838_);
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Expr_toPoly_x27_go_spec__0(lean_object* v_a_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_nat_to_int(v_a_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPoly_x27_go(lean_object* v_coeff_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
switch(lean_obj_tag(v_a_843_))
{
case 0:
{
lean_dec(v_coeff_842_);
return v_a_844_;
}
case 1:
{
lean_object* v_i_845_; lean_object* v___x_846_; 
v_i_845_ = lean_ctor_get(v_a_843_, 0);
lean_inc(v_i_845_);
lean_dec_ref(v_a_843_);
v___x_846_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_846_, 0, v_coeff_842_);
lean_ctor_set(v___x_846_, 1, v_i_845_);
lean_ctor_set(v___x_846_, 2, v_a_844_);
return v___x_846_;
}
case 2:
{
lean_object* v_a_847_; lean_object* v_b_848_; lean_object* v___x_849_; 
v_a_847_ = lean_ctor_get(v_a_843_, 0);
lean_inc(v_a_847_);
v_b_848_ = lean_ctor_get(v_a_843_, 1);
lean_inc(v_b_848_);
lean_dec_ref(v_a_843_);
lean_inc(v_coeff_842_);
v___x_849_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v_coeff_842_, v_b_848_, v_a_844_);
v_a_843_ = v_a_847_;
v_a_844_ = v___x_849_;
goto _start;
}
case 3:
{
lean_object* v_a_851_; lean_object* v_b_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_a_851_ = lean_ctor_get(v_a_843_, 0);
lean_inc(v_a_851_);
v_b_852_ = lean_ctor_get(v_a_843_, 1);
lean_inc(v_b_852_);
lean_dec_ref(v_a_843_);
v___x_853_ = lean_int_neg(v_coeff_842_);
v___x_854_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v___x_853_, v_b_852_, v_a_844_);
v_a_843_ = v_a_851_;
v_a_844_ = v___x_854_;
goto _start;
}
case 4:
{
lean_object* v_a_856_; lean_object* v___x_857_; 
v_a_856_ = lean_ctor_get(v_a_843_, 0);
lean_inc(v_a_856_);
lean_dec_ref(v_a_843_);
v___x_857_ = lean_int_neg(v_coeff_842_);
lean_dec(v_coeff_842_);
v_coeff_842_ = v___x_857_;
v_a_843_ = v_a_856_;
goto _start;
}
case 5:
{
lean_object* v_k_859_; lean_object* v_a_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v_k_859_ = lean_ctor_get(v_a_843_, 0);
lean_inc(v_k_859_);
v_a_860_ = lean_ctor_get(v_a_843_, 1);
lean_inc(v_a_860_);
lean_dec_ref(v_a_843_);
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_nat_dec_eq(v_k_859_, v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_nat_to_int(v_k_859_);
v___x_864_ = lean_int_mul(v_coeff_842_, v___x_863_);
lean_dec(v___x_863_);
lean_dec(v_coeff_842_);
v_coeff_842_ = v___x_864_;
v_a_843_ = v_a_860_;
goto _start;
}
else
{
lean_dec(v_a_860_);
lean_dec(v_k_859_);
lean_dec(v_coeff_842_);
return v_a_844_;
}
}
default: 
{
lean_object* v_k_866_; lean_object* v_a_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_k_866_ = lean_ctor_get(v_a_843_, 0);
lean_inc(v_k_866_);
v_a_867_ = lean_ctor_get(v_a_843_, 1);
lean_inc(v_a_867_);
lean_dec_ref(v_a_843_);
v___x_868_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_869_ = lean_int_dec_eq(v_k_866_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = lean_int_mul(v_coeff_842_, v_k_866_);
lean_dec(v_k_866_);
lean_dec(v_coeff_842_);
v_coeff_842_ = v___x_870_;
v_a_843_ = v_a_867_;
goto _start;
}
else
{
lean_dec(v_a_867_);
lean_dec(v_k_866_);
lean_dec(v_coeff_842_);
return v_a_844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPoly_x27(lean_object* v_e_872_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_874_ = lean_box(0);
v___x_875_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v___x_873_, v_e_872_, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_norm(lean_object* v_e_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = l_Lean_Grind_Linarith_Expr_toPoly_x27(v_e_876_);
v___x_878_ = l_Lean_Grind_Linarith_Poly_norm(v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul_x27(lean_object* v_p_879_, lean_object* v_k_880_){
_start:
{
if (lean_obj_tag(v_p_879_) == 0)
{
return v_p_879_;
}
else
{
lean_object* v_k_881_; lean_object* v_v_882_; lean_object* v_p_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_892_; 
v_k_881_ = lean_ctor_get(v_p_879_, 0);
v_v_882_ = lean_ctor_get(v_p_879_, 1);
v_p_883_ = lean_ctor_get(v_p_879_, 2);
v_isSharedCheck_892_ = !lean_is_exclusive(v_p_879_);
if (v_isSharedCheck_892_ == 0)
{
v___x_885_ = v_p_879_;
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_p_883_);
lean_inc(v_v_882_);
lean_inc(v_k_881_);
lean_dec(v_p_879_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_887_ = lean_int_mul(v_k_880_, v_k_881_);
lean_dec(v_k_881_);
v___x_888_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_883_, v_k_880_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 2, v___x_888_);
lean_ctor_set(v___x_885_, 0, v___x_887_);
v___x_890_ = v___x_885_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_v_882_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul_x27___boxed(lean_object* v_p_893_, lean_object* v_k_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_893_, v_k_894_);
lean_dec(v_k_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul(lean_object* v_p_896_, lean_object* v_k_897_){
_start:
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_899_ = lean_int_dec_eq(v_k_897_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_896_, v_k_897_);
return v___x_900_;
}
else
{
lean_object* v___x_901_; 
lean_dec(v_p_896_);
v___x_901_ = lean_box(0);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul___boxed(lean_object* v_p_902_, lean_object* v_k_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Grind_Linarith_Poly_mul(v_p_902_, v_k_903_);
lean_dec(v_k_903_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(lean_object* v_p_905_, lean_object* v_h__1_906_, lean_object* v_h__2_907_){
_start:
{
if (lean_obj_tag(v_p_905_) == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec(v_h__2_907_);
v___x_908_ = lean_box(0);
v___x_909_ = lean_apply_1(v_h__1_906_, v___x_908_);
return v___x_909_;
}
else
{
lean_object* v_k_910_; lean_object* v_v_911_; lean_object* v_p_912_; lean_object* v___x_913_; 
lean_dec(v_h__1_906_);
v_k_910_ = lean_ctor_get(v_p_905_, 0);
lean_inc(v_k_910_);
v_v_911_ = lean_ctor_get(v_p_905_, 1);
lean_inc(v_v_911_);
v_p_912_ = lean_ctor_get(v_p_905_, 2);
lean_inc(v_p_912_);
lean_dec_ref(v_p_905_);
v___x_913_ = lean_apply_3(v_h__2_907_, v_k_910_, v_v_911_, v_p_912_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(lean_object* v_motive_914_, lean_object* v_p_915_, lean_object* v_h__1_916_, lean_object* v_h__2_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(v_p_915_, v_h__1_916_, v_h__2_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter___redArg(lean_object* v_x_919_, lean_object* v_h__1_920_, lean_object* v_h__2_921_, lean_object* v_h__3_922_, lean_object* v_h__4_923_, lean_object* v_h__5_924_, lean_object* v_h__6_925_, lean_object* v_h__7_926_){
_start:
{
switch(lean_obj_tag(v_x_919_))
{
case 0:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec(v_h__7_926_);
lean_dec(v_h__6_925_);
lean_dec(v_h__5_924_);
lean_dec(v_h__4_923_);
lean_dec(v_h__3_922_);
lean_dec(v_h__2_921_);
v___x_927_ = lean_box(0);
v___x_928_ = lean_apply_1(v_h__1_920_, v___x_927_);
return v___x_928_;
}
case 1:
{
lean_object* v_i_929_; lean_object* v___x_930_; 
lean_dec(v_h__7_926_);
lean_dec(v_h__6_925_);
lean_dec(v_h__5_924_);
lean_dec(v_h__4_923_);
lean_dec(v_h__3_922_);
lean_dec(v_h__1_920_);
v_i_929_ = lean_ctor_get(v_x_919_, 0);
lean_inc(v_i_929_);
lean_dec_ref(v_x_919_);
v___x_930_ = lean_apply_1(v_h__2_921_, v_i_929_);
return v___x_930_;
}
case 2:
{
lean_object* v_a_931_; lean_object* v_b_932_; lean_object* v___x_933_; 
lean_dec(v_h__7_926_);
lean_dec(v_h__6_925_);
lean_dec(v_h__5_924_);
lean_dec(v_h__4_923_);
lean_dec(v_h__2_921_);
lean_dec(v_h__1_920_);
v_a_931_ = lean_ctor_get(v_x_919_, 0);
lean_inc(v_a_931_);
v_b_932_ = lean_ctor_get(v_x_919_, 1);
lean_inc(v_b_932_);
lean_dec_ref(v_x_919_);
v___x_933_ = lean_apply_2(v_h__3_922_, v_a_931_, v_b_932_);
return v___x_933_;
}
case 3:
{
lean_object* v_a_934_; lean_object* v_b_935_; lean_object* v___x_936_; 
lean_dec(v_h__7_926_);
lean_dec(v_h__6_925_);
lean_dec(v_h__5_924_);
lean_dec(v_h__3_922_);
lean_dec(v_h__2_921_);
lean_dec(v_h__1_920_);
v_a_934_ = lean_ctor_get(v_x_919_, 0);
lean_inc(v_a_934_);
v_b_935_ = lean_ctor_get(v_x_919_, 1);
lean_inc(v_b_935_);
lean_dec_ref(v_x_919_);
v___x_936_ = lean_apply_2(v_h__4_923_, v_a_934_, v_b_935_);
return v___x_936_;
}
case 4:
{
lean_object* v_a_937_; lean_object* v___x_938_; 
lean_dec(v_h__6_925_);
lean_dec(v_h__5_924_);
lean_dec(v_h__4_923_);
lean_dec(v_h__3_922_);
lean_dec(v_h__2_921_);
lean_dec(v_h__1_920_);
v_a_937_ = lean_ctor_get(v_x_919_, 0);
lean_inc(v_a_937_);
lean_dec_ref(v_x_919_);
v___x_938_ = lean_apply_1(v_h__7_926_, v_a_937_);
return v___x_938_;
}
case 5:
{
lean_object* v_k_939_; lean_object* v_a_940_; lean_object* v___x_941_; 
lean_dec(v_h__7_926_);
lean_dec(v_h__6_925_);
lean_dec(v_h__4_923_);
lean_dec(v_h__3_922_);
lean_dec(v_h__2_921_);
lean_dec(v_h__1_920_);
v_k_939_ = lean_ctor_get(v_x_919_, 0);
lean_inc(v_k_939_);
v_a_940_ = lean_ctor_get(v_x_919_, 1);
lean_inc(v_a_940_);
lean_dec_ref(v_x_919_);
v___x_941_ = lean_apply_2(v_h__5_924_, v_k_939_, v_a_940_);
return v___x_941_;
}
default: 
{
lean_object* v_k_942_; lean_object* v_a_943_; lean_object* v___x_944_; 
lean_dec(v_h__7_926_);
lean_dec(v_h__5_924_);
lean_dec(v_h__4_923_);
lean_dec(v_h__3_922_);
lean_dec(v_h__2_921_);
lean_dec(v_h__1_920_);
v_k_942_ = lean_ctor_get(v_x_919_, 0);
lean_inc(v_k_942_);
v_a_943_ = lean_ctor_get(v_x_919_, 1);
lean_inc(v_a_943_);
lean_dec_ref(v_x_919_);
v___x_944_ = lean_apply_2(v_h__6_925_, v_k_942_, v_a_943_);
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter(lean_object* v_motive_945_, lean_object* v_x_946_, lean_object* v_h__1_947_, lean_object* v_h__2_948_, lean_object* v_h__3_949_, lean_object* v_h__4_950_, lean_object* v_h__5_951_, lean_object* v_h__6_952_, lean_object* v_h__7_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter___redArg(v_x_946_, v_h__1_947_, v_h__2_948_, v_h__3_949_, v_h__4_950_, v_h__5_951_, v_h__6_952_, v_h__7_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_leadCoeff(lean_object* v_p_955_){
_start:
{
if (lean_obj_tag(v_p_955_) == 1)
{
lean_object* v_k_956_; 
v_k_956_ = lean_ctor_get(v_p_955_, 0);
lean_inc(v_k_956_);
return v_k_956_;
}
else
{
lean_object* v___x_957_; 
v___x_957_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_leadCoeff___boxed(lean_object* v_p_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_958_);
lean_dec(v_p_958_);
return v_res_959_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_le__le__combine__cert(lean_object* v_p_u2081_960_, lean_object* v_p_u2082_961_, lean_object* v_p_u2083_962_){
_start:
{
lean_object* v___x_963_; lean_object* v_a_u2081_964_; lean_object* v___x_965_; lean_object* v_a_u2082_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_963_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_960_);
v_a_u2081_964_ = lean_nat_abs(v___x_963_);
lean_dec(v___x_963_);
v___x_965_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_961_);
v_a_u2082_966_ = lean_nat_abs(v___x_965_);
lean_dec(v___x_965_);
v___x_967_ = lean_nat_to_int(v_a_u2082_966_);
v___x_968_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_960_, v___x_967_);
lean_dec(v___x_967_);
v___x_969_ = lean_nat_to_int(v_a_u2081_964_);
v___x_970_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_961_, v___x_969_);
lean_dec(v___x_969_);
v___x_971_ = l_Lean_Grind_Linarith_Poly_combine(v___x_968_, v___x_970_);
v___x_972_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_962_, v___x_971_);
lean_dec(v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_le__le__combine__cert___boxed(lean_object* v_p_u2081_973_, lean_object* v_p_u2082_974_, lean_object* v_p_u2083_975_){
_start:
{
uint8_t v_res_976_; lean_object* v_r_977_; 
v_res_976_ = l_Lean_Grind_Linarith_le__le__combine__cert(v_p_u2081_973_, v_p_u2082_974_, v_p_u2083_975_);
lean_dec(v_p_u2083_975_);
v_r_977_ = lean_box(v_res_976_);
return v_r_977_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_le__lt__combine__cert(lean_object* v_p_u2081_978_, lean_object* v_p_u2082_979_, lean_object* v_p_u2083_980_){
_start:
{
lean_object* v___x_981_; lean_object* v_a_u2081_982_; lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_981_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_978_);
v_a_u2081_982_ = lean_nat_abs(v___x_981_);
lean_dec(v___x_981_);
v___x_983_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_984_ = lean_nat_to_int(v_a_u2081_982_);
v___x_985_ = lean_int_dec_lt(v___x_983_, v___x_984_);
if (v___x_985_ == 0)
{
lean_dec(v___x_984_);
lean_dec(v_p_u2082_979_);
lean_dec(v_p_u2081_978_);
return v___x_985_;
}
else
{
lean_object* v___x_986_; lean_object* v_a_u2082_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_986_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_979_);
v_a_u2082_987_ = lean_nat_abs(v___x_986_);
lean_dec(v___x_986_);
v___x_988_ = lean_nat_to_int(v_a_u2082_987_);
v___x_989_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_978_, v___x_988_);
lean_dec(v___x_988_);
v___x_990_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_979_, v___x_984_);
lean_dec(v___x_984_);
v___x_991_ = l_Lean_Grind_Linarith_Poly_combine(v___x_989_, v___x_990_);
v___x_992_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_980_, v___x_991_);
lean_dec(v___x_991_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_le__lt__combine__cert___boxed(lean_object* v_p_u2081_993_, lean_object* v_p_u2082_994_, lean_object* v_p_u2083_995_){
_start:
{
uint8_t v_res_996_; lean_object* v_r_997_; 
v_res_996_ = l_Lean_Grind_Linarith_le__lt__combine__cert(v_p_u2081_993_, v_p_u2082_994_, v_p_u2083_995_);
lean_dec(v_p_u2083_995_);
v_r_997_ = lean_box(v_res_996_);
return v_r_997_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_lt__lt__combine__cert(lean_object* v_p_u2081_998_, lean_object* v_p_u2082_999_, lean_object* v_p_u2083_1000_){
_start:
{
lean_object* v___x_1001_; lean_object* v_a_u2081_1002_; lean_object* v___x_1003_; lean_object* v_a_u2082_1004_; uint8_t v___y_1006_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1001_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_998_);
v_a_u2081_1002_ = lean_nat_abs(v___x_1001_);
lean_dec(v___x_1001_);
v___x_1003_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_999_);
v_a_u2082_1004_ = lean_nat_abs(v___x_1003_);
lean_dec(v___x_1003_);
v___x_1013_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
lean_inc(v_a_u2082_1004_);
v___x_1014_ = lean_nat_to_int(v_a_u2082_1004_);
v___x_1015_ = lean_int_dec_lt(v___x_1013_, v___x_1014_);
lean_dec(v___x_1014_);
if (v___x_1015_ == 0)
{
v___y_1006_ = v___x_1015_;
goto v___jp_1005_;
}
else
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
lean_inc(v_a_u2081_1002_);
v___x_1016_ = lean_nat_to_int(v_a_u2081_1002_);
v___x_1017_ = lean_int_dec_lt(v___x_1013_, v___x_1016_);
lean_dec(v___x_1016_);
v___y_1006_ = v___x_1017_;
goto v___jp_1005_;
}
v___jp_1005_:
{
if (v___y_1006_ == 0)
{
lean_dec(v_a_u2082_1004_);
lean_dec(v_a_u2081_1002_);
lean_dec(v_p_u2082_999_);
lean_dec(v_p_u2081_998_);
return v___y_1006_;
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1007_ = lean_nat_to_int(v_a_u2082_1004_);
v___x_1008_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_998_, v___x_1007_);
lean_dec(v___x_1007_);
v___x_1009_ = lean_nat_to_int(v_a_u2081_1002_);
v___x_1010_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_999_, v___x_1009_);
lean_dec(v___x_1009_);
v___x_1011_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1008_, v___x_1010_);
v___x_1012_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1000_, v___x_1011_);
lean_dec(v___x_1011_);
return v___x_1012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_lt__lt__combine__cert___boxed(lean_object* v_p_u2081_1018_, lean_object* v_p_u2082_1019_, lean_object* v_p_u2083_1020_){
_start:
{
uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_res_1021_ = l_Lean_Grind_Linarith_lt__lt__combine__cert(v_p_u2081_1018_, v_p_u2082_1019_, v_p_u2083_1020_);
lean_dec(v_p_u2083_1020_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1024_ = lean_int_neg(v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_diseq__split__cert(lean_object* v_p_u2081_1025_, lean_object* v_p_u2082_1026_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1027_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1028_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1025_, v___x_1027_);
v___x_1029_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_1026_, v___x_1028_);
lean_dec(v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_diseq__split__cert___boxed(lean_object* v_p_u2081_1030_, lean_object* v_p_u2082_1031_){
_start:
{
uint8_t v_res_1032_; lean_object* v_r_1033_; 
v_res_1032_ = l_Lean_Grind_Linarith_diseq__split__cert(v_p_u2081_1030_, v_p_u2082_1031_);
lean_dec(v_p_u2082_1031_);
v_r_1033_ = lean_box(v_res_1032_);
return v_r_1033_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_norm__cert(lean_object* v_lhs_1034_, lean_object* v_rhs_1035_, lean_object* v_p_1036_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1037_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1037_, 0, v_lhs_1034_);
lean_ctor_set(v___x_1037_, 1, v_rhs_1035_);
v___x_1038_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1037_);
v___x_1039_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1036_, v___x_1038_);
lean_dec(v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_norm__cert___boxed(lean_object* v_lhs_1040_, lean_object* v_rhs_1041_, lean_object* v_p_1042_){
_start:
{
uint8_t v_res_1043_; lean_object* v_r_1044_; 
v_res_1043_ = l_Lean_Grind_Linarith_norm__cert(v_lhs_1040_, v_rhs_1041_, v_p_1042_);
lean_dec(v_p_1042_);
v_r_1044_ = lean_box(v_res_1043_);
return v_r_1044_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__of__le__ge__cert(lean_object* v_p_u2081_1045_, lean_object* v_p_u2082_1046_){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1048_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1045_, v___x_1047_);
v___x_1049_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_1046_, v___x_1048_);
lean_dec(v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__of__le__ge__cert___boxed(lean_object* v_p_u2081_1050_, lean_object* v_p_u2082_1051_){
_start:
{
uint8_t v_res_1052_; lean_object* v_r_1053_; 
v_res_1052_ = l_Lean_Grind_Linarith_eq__of__le__ge__cert(v_p_u2081_1050_, v_p_u2082_1051_);
lean_dec(v_p_u2082_1051_);
v_r_1053_ = lean_box(v_res_1052_);
return v_r_1053_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___x_1055_);
lean_ctor_set(v___x_1057_, 2, v___x_1054_);
return v___x_1057_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_zero__lt__one__cert(lean_object* v_p_1058_){
_start:
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = lean_obj_once(&l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0, &l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0_once, _init_l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0);
v___x_1060_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1058_, v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__lt__one__cert___boxed(lean_object* v_p_1061_){
_start:
{
uint8_t v_res_1062_; lean_object* v_r_1063_; 
v_res_1062_ = l_Lean_Grind_Linarith_zero__lt__one__cert(v_p_1061_);
lean_dec(v_p_1061_);
v_r_1063_ = lean_box(v_res_1062_);
return v_r_1063_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1067_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_1065_);
lean_ctor_set(v___x_1067_, 2, v___x_1064_);
return v___x_1067_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_zero__ne__one__cert(lean_object* v_p_1068_){
_start:
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = lean_obj_once(&l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0, &l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once, _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0);
v___x_1070_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1068_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__ne__one__cert___boxed(lean_object* v_p_1071_){
_start:
{
uint8_t v_res_1072_; lean_object* v_r_1073_; 
v_res_1072_ = l_Lean_Grind_Linarith_zero__ne__one__cert(v_p_1071_);
lean_dec(v_p_1071_);
v_r_1073_ = lean_box(v_res_1072_);
return v_r_1073_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(lean_object* v_c_1074_, lean_object* v_p_1075_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1076_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1077_ = lean_nat_to_int(v_c_1074_);
v___x_1078_ = lean_int_dec_lt(v___x_1076_, v___x_1077_);
lean_dec(v___x_1077_);
if (v___x_1078_ == 0)
{
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = lean_obj_once(&l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0, &l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once, _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0);
v___x_1080_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1075_, v___x_1079_);
return v___x_1080_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert___boxed(lean_object* v_c_1081_, lean_object* v_p_1082_){
_start:
{
uint8_t v_res_1083_; lean_object* v_r_1084_; 
v_res_1083_ = l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(v_c_1081_, v_p_1082_);
lean_dec(v_p_1082_);
v_r_1084_ = lean_box(v_res_1083_);
return v_r_1084_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__neg__cert(lean_object* v_p_u2081_1085_, lean_object* v_p_u2082_1086_){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1087_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1088_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1085_, v___x_1087_);
v___x_1089_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_1086_, v___x_1088_);
lean_dec(v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__neg__cert___boxed(lean_object* v_p_u2081_1090_, lean_object* v_p_u2082_1091_){
_start:
{
uint8_t v_res_1092_; lean_object* v_r_1093_; 
v_res_1092_ = l_Lean_Grind_Linarith_eq__neg__cert(v_p_u2081_1090_, v_p_u2082_1091_);
lean_dec(v_p_u2082_1091_);
v_r_1093_ = lean_box(v_res_1092_);
return v_r_1093_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__coeff__cert(lean_object* v_p_u2081_1094_, lean_object* v_p_u2082_1095_, lean_object* v_k_1096_){
_start:
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = lean_nat_dec_eq(v_k_1096_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1099_ = lean_nat_to_int(v_k_1096_);
v___x_1100_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1095_, v___x_1099_);
lean_dec(v___x_1099_);
v___x_1101_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2081_1094_, v___x_1100_);
lean_dec(v___x_1100_);
return v___x_1101_;
}
else
{
uint8_t v___x_1102_; 
lean_dec(v_k_1096_);
lean_dec(v_p_u2082_1095_);
v___x_1102_ = 0;
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__coeff__cert___boxed(lean_object* v_p_u2081_1103_, lean_object* v_p_u2082_1104_, lean_object* v_k_1105_){
_start:
{
uint8_t v_res_1106_; lean_object* v_r_1107_; 
v_res_1106_ = l_Lean_Grind_Linarith_eq__coeff__cert(v_p_u2081_1103_, v_p_u2082_1104_, v_k_1105_);
lean_dec(v_p_u2081_1103_);
v_r_1107_ = lean_box(v_res_1106_);
return v_r_1107_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_coeff__cert(lean_object* v_p_u2081_1108_, lean_object* v_p_u2082_1109_, lean_object* v_k_1110_){
_start:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = lean_nat_dec_lt(v___x_1111_, v_k_1110_);
if (v___x_1112_ == 0)
{
lean_dec(v_k_1110_);
lean_dec(v_p_u2082_1109_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1113_ = lean_nat_to_int(v_k_1110_);
v___x_1114_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1109_, v___x_1113_);
lean_dec(v___x_1113_);
v___x_1115_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2081_1108_, v___x_1114_);
lean_dec(v___x_1114_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_coeff__cert___boxed(lean_object* v_p_u2081_1116_, lean_object* v_p_u2082_1117_, lean_object* v_k_1118_){
_start:
{
uint8_t v_res_1119_; lean_object* v_r_1120_; 
v_res_1119_ = l_Lean_Grind_Linarith_coeff__cert(v_p_u2081_1116_, v_p_u2082_1117_, v_k_1118_);
lean_dec(v_p_u2081_1116_);
v_r_1120_ = lean_box(v_res_1119_);
return v_r_1120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__diseq__subst__cert(lean_object* v_k_u2081_1121_, lean_object* v_k_u2082_1122_, lean_object* v_p_u2081_1123_, lean_object* v_p_u2082_1124_, lean_object* v_p_u2083_1125_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1126_ = lean_nat_abs(v_k_u2081_1121_);
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_nat_dec_eq(v___x_1126_, v___x_1127_);
lean_dec(v___x_1126_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1129_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1123_, v_k_u2082_1122_);
v___x_1130_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1124_, v_k_u2081_1121_);
v___x_1131_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1129_, v___x_1130_);
v___x_1132_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1125_, v___x_1131_);
lean_dec(v___x_1131_);
return v___x_1132_;
}
else
{
uint8_t v___x_1133_; 
lean_dec(v_p_u2082_1124_);
lean_dec(v_p_u2081_1123_);
v___x_1133_ = 0;
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__diseq__subst__cert___boxed(lean_object* v_k_u2081_1134_, lean_object* v_k_u2082_1135_, lean_object* v_p_u2081_1136_, lean_object* v_p_u2082_1137_, lean_object* v_p_u2083_1138_){
_start:
{
uint8_t v_res_1139_; lean_object* v_r_1140_; 
v_res_1139_ = l_Lean_Grind_Linarith_eq__diseq__subst__cert(v_k_u2081_1134_, v_k_u2082_1135_, v_p_u2081_1136_, v_p_u2082_1137_, v_p_u2083_1138_);
lean_dec(v_p_u2083_1138_);
lean_dec(v_k_u2082_1135_);
lean_dec(v_k_u2081_1134_);
v_r_1140_ = lean_box(v_res_1139_);
return v_r_1140_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__diseq__subst1__cert(lean_object* v_k_1141_, lean_object* v_p_u2081_1142_, lean_object* v_p_u2082_1143_, lean_object* v_p_u2083_1144_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1142_, v_k_1141_);
v___x_1146_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1145_, v_p_u2082_1143_);
v___x_1147_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1144_, v___x_1146_);
lean_dec(v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__diseq__subst1__cert___boxed(lean_object* v_k_1148_, lean_object* v_p_u2081_1149_, lean_object* v_p_u2082_1150_, lean_object* v_p_u2083_1151_){
_start:
{
uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_res_1152_ = l_Lean_Grind_Linarith_eq__diseq__subst1__cert(v_k_1148_, v_p_u2081_1149_, v_p_u2082_1150_, v_p_u2083_1151_);
lean_dec(v_p_u2083_1151_);
lean_dec(v_k_1148_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__le__subst__cert(lean_object* v_x_1154_, lean_object* v_p_u2081_1155_, lean_object* v_p_u2082_1156_, lean_object* v_p_u2083_1157_){
_start:
{
lean_object* v_a_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_a_1158_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_1155_, v_x_1154_);
v___x_1159_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1160_ = lean_int_dec_le(v___x_1159_, v_a_1158_);
if (v___x_1160_ == 0)
{
lean_dec(v_a_1158_);
lean_dec(v_p_u2082_1156_);
lean_dec(v_p_u2081_1155_);
return v___x_1160_;
}
else
{
lean_object* v_b_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v_b_1161_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_1156_, v_x_1154_);
v___x_1162_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1156_, v_a_1158_);
lean_dec(v_a_1158_);
v___x_1163_ = lean_int_neg(v_b_1161_);
lean_dec(v_b_1161_);
v___x_1164_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1155_, v___x_1163_);
lean_dec(v___x_1163_);
v___x_1165_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1162_, v___x_1164_);
v___x_1166_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1157_, v___x_1165_);
lean_dec(v___x_1165_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__le__subst__cert___boxed(lean_object* v_x_1167_, lean_object* v_p_u2081_1168_, lean_object* v_p_u2082_1169_, lean_object* v_p_u2083_1170_){
_start:
{
uint8_t v_res_1171_; lean_object* v_r_1172_; 
v_res_1171_ = l_Lean_Grind_Linarith_eq__le__subst__cert(v_x_1167_, v_p_u2081_1168_, v_p_u2082_1169_, v_p_u2083_1170_);
lean_dec(v_p_u2083_1170_);
lean_dec(v_x_1167_);
v_r_1172_ = lean_box(v_res_1171_);
return v_r_1172_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__lt__subst__cert(lean_object* v_x_1173_, lean_object* v_p_u2081_1174_, lean_object* v_p_u2082_1175_, lean_object* v_p_u2083_1176_){
_start:
{
lean_object* v_a_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_a_1177_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_1174_, v_x_1173_);
v___x_1178_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1179_ = lean_int_dec_lt(v___x_1178_, v_a_1177_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__lt__subst__cert___boxed(lean_object* v_x_1186_, lean_object* v_p_u2081_1187_, lean_object* v_p_u2082_1188_, lean_object* v_p_u2083_1189_){
_start:
{
uint8_t v_res_1190_; lean_object* v_r_1191_; 
v_res_1190_ = l_Lean_Grind_Linarith_eq__lt__subst__cert(v_x_1186_, v_p_u2081_1187_, v_p_u2082_1188_, v_p_u2083_1189_);
lean_dec(v_p_u2083_1189_);
lean_dec(v_x_1186_);
v_r_1191_ = lean_box(v_res_1190_);
return v_r_1191_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__eq__subst__cert(lean_object* v_x_1192_, lean_object* v_p_u2081_1193_, lean_object* v_p_u2082_1194_, lean_object* v_p_u2083_1195_){
_start:
{
lean_object* v_a_1196_; lean_object* v_b_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_a_1196_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_1193_, v_x_1192_);
v_b_1197_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_1194_, v_x_1192_);
v___x_1198_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1194_, v_a_1196_);
lean_dec(v_a_1196_);
v___x_1199_ = lean_int_neg(v_b_1197_);
lean_dec(v_b_1197_);
v___x_1200_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1193_, v___x_1199_);
lean_dec(v___x_1199_);
v___x_1201_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1198_, v___x_1200_);
v___x_1202_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1195_, v___x_1201_);
lean_dec(v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__eq__subst__cert___boxed(lean_object* v_x_1203_, lean_object* v_p_u2081_1204_, lean_object* v_p_u2082_1205_, lean_object* v_p_u2083_1206_){
_start:
{
uint8_t v_res_1207_; lean_object* v_r_1208_; 
v_res_1207_ = l_Lean_Grind_Linarith_eq__eq__subst__cert(v_x_1203_, v_p_u2081_1204_, v_p_u2082_1205_, v_p_u2083_1206_);
lean_dec(v_p_u2083_1206_);
lean_dec(v_x_1203_);
v_r_1208_ = lean_box(v_res_1207_);
return v_r_1208_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_imp__eq__cert(lean_object* v_p_1209_, lean_object* v_x_1210_, lean_object* v_y_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1212_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1213_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v_y_1211_);
lean_ctor_set(v___x_1215_, 2, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1212_);
lean_ctor_set(v___x_1216_, 1, v_x_1210_);
lean_ctor_set(v___x_1216_, 2, v___x_1215_);
v___x_1217_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1209_, v___x_1216_);
lean_dec_ref(v___x_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_imp__eq__cert___boxed(lean_object* v_p_1218_, lean_object* v_x_1219_, lean_object* v_y_1220_){
_start:
{
uint8_t v_res_1221_; lean_object* v_r_1222_; 
v_res_1221_ = l_Lean_Grind_Linarith_imp__eq__cert(v_p_1218_, v_x_1219_, v_y_1220_);
lean_dec(v_p_1218_);
v_r_1222_ = lean_box(v_res_1221_);
return v_r_1222_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Ordered_Linarith(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
