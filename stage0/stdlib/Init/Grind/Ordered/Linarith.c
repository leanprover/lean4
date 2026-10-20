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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Grind_IntModule_toNatModule___redArg(lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Grind_Linarith_Expr_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 0:
{
return v_k_6_;
}
case 1:
{
lean_object* v_i_7_; lean_object* v___x_8_; 
v_i_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_i_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_i_7_);
return v___x_8_;
}
case 4:
{
lean_object* v_a_9_; lean_object* v___x_10_; 
v_a_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_a_9_);
lean_dec_ref_known(v_t_5_, 1);
v___x_10_ = lean_apply_1(v_k_6_, v_a_9_);
return v___x_10_;
}
default: 
{
lean_object* v_a_11_; lean_object* v_b_12_; lean_object* v___x_13_; 
v_a_11_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_a_11_);
v_b_12_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_b_12_);
lean_dec(v_t_5_);
v___x_13_ = lean_apply_2(v_k_6_, v_a_11_, v_b_12_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, lean_object* v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_16_, v_k_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Grind_Linarith_Expr_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_22_, v_h_23_, v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_zero_elim___redArg(lean_object* v_t_26_, lean_object* v_zero_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_26_, v_zero_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_zero_elim(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_zero_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_30_, v_zero_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_var_elim___redArg(lean_object* v_t_34_, lean_object* v_var_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_34_, v_var_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_var_elim(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_var_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_38_, v_var_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_add_elim___redArg(lean_object* v_t_42_, lean_object* v_add_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_42_, v_add_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_add_elim(lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_add_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_46_, v_add_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_sub_elim___redArg(lean_object* v_t_50_, lean_object* v_sub_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_50_, v_sub_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_sub_elim(lean_object* v_motive_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_sub_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_54_, v_sub_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_neg_elim___redArg(lean_object* v_t_58_, lean_object* v_neg_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_58_, v_neg_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_neg_elim(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_neg_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_62_, v_neg_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_natMul_elim___redArg(lean_object* v_t_66_, lean_object* v_natMul_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_66_, v_natMul_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_natMul_elim(lean_object* v_motive_69_, lean_object* v_t_70_, lean_object* v_h_71_, lean_object* v_natMul_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_70_, v_natMul_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_intMul_elim___redArg(lean_object* v_t_74_, lean_object* v_intMul_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_74_, v_intMul_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_intMul_elim(lean_object* v_motive_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_intMul_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Grind_Linarith_Expr_ctorElim___redArg(v_t_78_, v_intMul_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_instInhabitedExpr_default(void){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(0);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_instInhabitedExpr(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_box(0);
return v___x_83_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_instBEqExpr_beq(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
lean_object* v_a_87_; lean_object* v_a_88_; lean_object* v_b_89_; lean_object* v_b_90_; 
switch(lean_obj_tag(v_x_84_))
{
case 0:
{
if (lean_obj_tag(v_x_85_) == 0)
{
uint8_t v___x_93_; 
v___x_93_ = 1;
return v___x_93_;
}
else
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
}
case 1:
{
if (lean_obj_tag(v_x_85_) == 1)
{
lean_object* v_i_95_; lean_object* v_i_96_; uint8_t v___x_97_; 
v_i_95_ = lean_ctor_get(v_x_84_, 0);
v_i_96_ = lean_ctor_get(v_x_85_, 0);
v___x_97_ = lean_nat_dec_eq(v_i_95_, v_i_96_);
return v___x_97_;
}
else
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
case 2:
{
if (lean_obj_tag(v_x_85_) == 2)
{
lean_object* v_a_99_; lean_object* v_b_100_; lean_object* v_a_101_; lean_object* v_b_102_; 
v_a_99_ = lean_ctor_get(v_x_84_, 0);
v_b_100_ = lean_ctor_get(v_x_84_, 1);
v_a_101_ = lean_ctor_get(v_x_85_, 0);
v_b_102_ = lean_ctor_get(v_x_85_, 1);
v_a_87_ = v_a_99_;
v_a_88_ = v_b_100_;
v_b_89_ = v_a_101_;
v_b_90_ = v_b_102_;
goto v___jp_86_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = 0;
return v___x_103_;
}
}
case 3:
{
if (lean_obj_tag(v_x_85_) == 3)
{
lean_object* v_a_104_; lean_object* v_b_105_; lean_object* v_a_106_; lean_object* v_b_107_; 
v_a_104_ = lean_ctor_get(v_x_84_, 0);
v_b_105_ = lean_ctor_get(v_x_84_, 1);
v_a_106_ = lean_ctor_get(v_x_85_, 0);
v_b_107_ = lean_ctor_get(v_x_85_, 1);
v_a_87_ = v_a_104_;
v_a_88_ = v_b_105_;
v_b_89_ = v_a_106_;
v_b_90_ = v_b_107_;
goto v___jp_86_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
}
case 4:
{
if (lean_obj_tag(v_x_85_) == 4)
{
lean_object* v_a_109_; lean_object* v_a_110_; 
v_a_109_ = lean_ctor_get(v_x_84_, 0);
v_a_110_ = lean_ctor_get(v_x_85_, 0);
v_x_84_ = v_a_109_;
v_x_85_ = v_a_110_;
goto _start;
}
else
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
case 5:
{
if (lean_obj_tag(v_x_85_) == 5)
{
lean_object* v_k_113_; lean_object* v_a_114_; lean_object* v_k_115_; lean_object* v_a_116_; uint8_t v___x_117_; 
v_k_113_ = lean_ctor_get(v_x_84_, 0);
v_a_114_ = lean_ctor_get(v_x_84_, 1);
v_k_115_ = lean_ctor_get(v_x_85_, 0);
v_a_116_ = lean_ctor_get(v_x_85_, 1);
v___x_117_ = lean_nat_dec_eq(v_k_113_, v_k_115_);
if (v___x_117_ == 0)
{
return v___x_117_;
}
else
{
v_x_84_ = v_a_114_;
v_x_85_ = v_a_116_;
goto _start;
}
}
else
{
uint8_t v___x_119_; 
v___x_119_ = 0;
return v___x_119_;
}
}
default: 
{
if (lean_obj_tag(v_x_85_) == 6)
{
lean_object* v_k_120_; lean_object* v_a_121_; lean_object* v_k_122_; lean_object* v_a_123_; uint8_t v___x_124_; 
v_k_120_ = lean_ctor_get(v_x_84_, 0);
v_a_121_ = lean_ctor_get(v_x_84_, 1);
v_k_122_ = lean_ctor_get(v_x_85_, 0);
v_a_123_ = lean_ctor_get(v_x_85_, 1);
v___x_124_ = lean_int_dec_eq(v_k_120_, v_k_122_);
if (v___x_124_ == 0)
{
return v___x_124_;
}
else
{
v_x_84_ = v_a_121_;
v_x_85_ = v_a_123_;
goto _start;
}
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 0;
return v___x_126_;
}
}
}
v___jp_86_:
{
uint8_t v___x_91_; 
v___x_91_ = l_Lean_Grind_Linarith_instBEqExpr_beq(v_a_87_, v_b_89_);
if (v___x_91_ == 0)
{
return v___x_91_;
}
else
{
v_x_84_ = v_a_88_;
v_x_85_ = v_b_90_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instBEqExpr_beq___boxed(lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Lean_Grind_Linarith_instBEqExpr_beq(v_x_127_, v_x_128_);
lean_dec(v_x_128_);
lean_dec(v_x_127_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(2u);
v___x_137_ = lean_nat_to_int(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_to_int(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_nat_to_int(v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprExpr_repr(lean_object* v_x_178_, lean_object* v_prec_179_){
_start:
{
lean_object* v___y_181_; 
switch(lean_obj_tag(v_x_178_))
{
case 0:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(1024u);
v___x_188_ = lean_nat_dec_le(v___x_187_, v_prec_179_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_181_ = v___x_189_;
goto v___jp_180_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_181_ = v___x_190_;
goto v___jp_180_;
}
}
case 1:
{
lean_object* v_i_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_211_; 
v_i_191_ = lean_ctor_get(v_x_178_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_211_ == 0)
{
v___x_193_ = v_x_178_;
v_isShared_194_ = v_isSharedCheck_211_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_i_191_);
lean_dec(v_x_178_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_211_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___y_196_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(1024u);
v___x_208_ = lean_nat_dec_le(v___x_207_, v_prec_179_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_196_ = v___x_209_;
goto v___jp_195_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_196_ = v___x_210_;
goto v___jp_195_;
}
v___jp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_197_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__6));
v___x_198_ = l_Nat_reprFast(v_i_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 3);
lean_ctor_set(v___x_193_, 0, v___x_198_);
v___x_200_ = v___x_193_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_206_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_197_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
lean_inc(v___y_196_);
v___x_202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_202_, 0, v___y_196_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = 0;
v___x_204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_204_, sizeof(void*)*1, v___x_203_);
v___x_205_ = l_Repr_addAppParen(v___x_204_, v_prec_179_);
return v___x_205_;
}
}
}
}
case 2:
{
lean_object* v_a_212_; lean_object* v_b_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_236_; 
v_a_212_ = lean_ctor_get(v_x_178_, 0);
v_b_213_ = lean_ctor_get(v_x_178_, 1);
v_isSharedCheck_236_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_236_ == 0)
{
v___x_215_ = v_x_178_;
v_isShared_216_ = v_isSharedCheck_236_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_b_213_);
lean_inc(v_a_212_);
lean_dec(v_x_178_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_236_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___y_219_; uint8_t v___x_233_; 
v___x_217_ = lean_unsigned_to_nat(1024u);
v___x_233_ = lean_nat_dec_le(v___x_217_, v_prec_179_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_219_ = v___x_234_;
goto v___jp_218_;
}
else
{
lean_object* v___x_235_; 
v___x_235_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_219_ = v___x_235_;
goto v___jp_218_;
}
v___jp_218_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_220_ = lean_box(1);
v___x_221_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__9));
v___x_222_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_212_, v___x_217_);
if (v_isShared_216_ == 0)
{
lean_ctor_set_tag(v___x_215_, 5);
lean_ctor_set(v___x_215_, 1, v___x_222_);
lean_ctor_set(v___x_215_, 0, v___x_221_);
v___x_224_ = v___x_215_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_232_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v___x_220_);
v___x_226_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_b_213_, v___x_217_);
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
lean_inc(v___y_219_);
v___x_228_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_228_, 0, v___y_219_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = 0;
v___x_230_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*1, v___x_229_);
v___x_231_ = l_Repr_addAppParen(v___x_230_, v_prec_179_);
return v___x_231_;
}
}
}
}
case 3:
{
lean_object* v_a_237_; lean_object* v_b_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_261_; 
v_a_237_ = lean_ctor_get(v_x_178_, 0);
v_b_238_ = lean_ctor_get(v_x_178_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_261_ == 0)
{
v___x_240_ = v_x_178_;
v_isShared_241_ = v_isSharedCheck_261_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_b_238_);
lean_inc(v_a_237_);
lean_dec(v_x_178_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_261_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___y_244_; uint8_t v___x_258_; 
v___x_242_ = lean_unsigned_to_nat(1024u);
v___x_258_ = lean_nat_dec_le(v___x_242_, v_prec_179_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_244_ = v___x_259_;
goto v___jp_243_;
}
else
{
lean_object* v___x_260_; 
v___x_260_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_244_ = v___x_260_;
goto v___jp_243_;
}
v___jp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_245_ = lean_box(1);
v___x_246_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__12));
v___x_247_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_237_, v___x_242_);
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 5);
lean_ctor_set(v___x_240_, 1, v___x_247_);
lean_ctor_set(v___x_240_, 0, v___x_246_);
v___x_249_ = v___x_240_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v___x_247_);
v___x_249_ = v_reuseFailAlloc_257_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_245_);
v___x_251_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_b_238_, v___x_242_);
v___x_252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_inc(v___y_244_);
v___x_253_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_253_, 0, v___y_244_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = 0;
v___x_255_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*1, v___x_254_);
v___x_256_ = l_Repr_addAppParen(v___x_255_, v_prec_179_);
return v___x_256_;
}
}
}
}
case 4:
{
lean_object* v_a_262_; lean_object* v___x_263_; lean_object* v___y_265_; uint8_t v___x_273_; 
v_a_262_ = lean_ctor_get(v_x_178_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v_x_178_, 1);
v___x_263_ = lean_unsigned_to_nat(1024u);
v___x_273_ = lean_nat_dec_le(v___x_263_, v_prec_179_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_265_ = v___x_274_;
goto v___jp_264_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_265_ = v___x_275_;
goto v___jp_264_;
}
v___jp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_266_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__15));
v___x_267_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_262_, v___x_263_);
v___x_268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
lean_inc(v___y_265_);
v___x_269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_269_, 0, v___y_265_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = 0;
v___x_271_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*1, v___x_270_);
v___x_272_ = l_Repr_addAppParen(v___x_271_, v_prec_179_);
return v___x_272_;
}
}
case 5:
{
lean_object* v_k_276_; lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_301_; 
v_k_276_ = lean_ctor_get(v_x_178_, 0);
v_a_277_ = lean_ctor_get(v_x_178_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_301_ == 0)
{
v___x_279_ = v_x_178_;
v_isShared_280_ = v_isSharedCheck_301_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_inc(v_k_276_);
lean_dec(v_x_178_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_301_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___y_283_; uint8_t v___x_298_; 
v___x_281_ = lean_unsigned_to_nat(1024u);
v___x_298_ = lean_nat_dec_le(v___x_281_, v_prec_179_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_283_ = v___x_299_;
goto v___jp_282_;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_283_ = v___x_300_;
goto v___jp_282_;
}
v___jp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_284_ = lean_box(1);
v___x_285_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__18));
v___x_286_ = l_Nat_reprFast(v_k_276_);
v___x_287_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 1, v___x_287_);
lean_ctor_set(v___x_279_, 0, v___x_285_);
v___x_289_ = v___x_279_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_287_);
v___x_289_ = v_reuseFailAlloc_297_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_284_);
v___x_291_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_277_, v___x_281_);
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
lean_inc(v___y_283_);
v___x_293_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_293_, 0, v___y_283_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = 0;
v___x_295_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set_uint8(v___x_295_, sizeof(void*)*1, v___x_294_);
v___x_296_ = l_Repr_addAppParen(v___x_295_, v_prec_179_);
return v___x_296_;
}
}
}
}
default: 
{
lean_object* v_k_302_; lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_337_; 
v_k_302_ = lean_ctor_get(v_x_178_, 0);
v_a_303_ = lean_ctor_get(v_x_178_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_337_ == 0)
{
v___x_305_ = v_x_178_;
v_isShared_306_ = v_isSharedCheck_337_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_inc(v_k_302_);
lean_dec(v_x_178_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_337_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_324_; uint8_t v___x_334_; 
v___x_307_ = lean_unsigned_to_nat(1024u);
v___x_334_ = lean_nat_dec_le(v___x_307_, v_prec_179_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
v___x_335_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_324_ = v___x_335_;
goto v___jp_323_;
}
else
{
lean_object* v___x_336_; 
v___x_336_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_324_ = v___x_336_;
goto v___jp_323_;
}
v___jp_308_:
{
lean_object* v___x_314_; 
lean_inc(v___y_309_);
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 5);
lean_ctor_set(v___x_305_, 1, v___y_312_);
lean_ctor_set(v___x_305_, 0, v___y_309_);
v___x_314_ = v___x_305_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___y_309_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v___y_312_);
v___x_314_ = v_reuseFailAlloc_322_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
lean_inc(v___y_311_);
v___x_315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___y_311_);
v___x_316_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_303_, v___x_307_);
v___x_317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
lean_inc(v___y_310_);
v___x_318_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_318_, 0, v___y_310_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = 0;
v___x_320_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set_uint8(v___x_320_, sizeof(void*)*1, v___x_319_);
v___x_321_ = l_Repr_addAppParen(v___x_320_, v_prec_179_);
return v___x_321_;
}
}
v___jp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_325_ = lean_box(1);
v___x_326_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__21));
v___x_327_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_328_ = lean_int_dec_lt(v_k_302_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = l_Int_repr(v_k_302_);
lean_dec(v_k_302_);
v___x_330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
v___y_309_ = v___x_326_;
v___y_310_ = v___y_324_;
v___y_311_ = v___x_325_;
v___y_312_ = v___x_330_;
goto v___jp_308_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = l_Int_repr(v_k_302_);
lean_dec(v_k_302_);
v___x_332_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
v___x_333_ = l_Repr_addAppParen(v___x_332_, v___x_307_);
v___y_309_ = v___x_326_;
v___y_310_ = v___y_324_;
v___y_311_ = v___x_325_;
v___y_312_ = v___x_333_;
goto v___jp_308_;
}
}
}
}
}
v___jp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_182_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__1));
lean_inc(v___y_181_);
v___x_183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_183_, 0, v___y_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = 0;
v___x_185_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set_uint8(v___x_185_, sizeof(void*)*1, v___x_184_);
v___x_186_ = l_Repr_addAppParen(v___x_185_, v_prec_179_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___boxed(lean_object* v_x_338_, lean_object* v_prec_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_x_338_, v_prec_339_);
lean_dec(v_prec_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote___redArg(lean_object* v_ctx_343_, lean_object* v_v_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_RArray_getImpl___redArg(v_ctx_343_, v_v_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote___redArg___boxed(lean_object* v_ctx_346_, lean_object* v_v_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Grind_Linarith_Var_denote___redArg(v_ctx_346_, v_v_347_);
lean_dec(v_v_347_);
lean_dec_ref(v_ctx_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote(lean_object* v_00_u03b1_349_, lean_object* v_ctx_350_, lean_object* v_v_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_RArray_getImpl___redArg(v_ctx_350_, v_v_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote___boxed(lean_object* v_00_u03b1_353_, lean_object* v_ctx_354_, lean_object* v_v_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Grind_Linarith_Var_denote(v_00_u03b1_353_, v_ctx_354_, v_v_355_);
lean_dec(v_v_355_);
lean_dec_ref(v_ctx_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___redArg(lean_object* v_inst_357_, lean_object* v_ctx_358_, lean_object* v_x_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_357_);
switch(lean_obj_tag(v_x_359_))
{
case 0:
{
lean_object* v_toAddCommMonoid_361_; lean_object* v_toZero_362_; 
v_toAddCommMonoid_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc_ref(v_toAddCommMonoid_361_);
lean_dec_ref(v___x_360_);
lean_dec_ref(v_inst_357_);
v_toZero_362_ = lean_ctor_get(v_toAddCommMonoid_361_, 0);
lean_inc(v_toZero_362_);
lean_dec_ref(v_toAddCommMonoid_361_);
return v_toZero_362_;
}
case 1:
{
lean_object* v_i_363_; lean_object* v___x_364_; 
lean_dec_ref(v___x_360_);
lean_dec_ref(v_inst_357_);
v_i_363_ = lean_ctor_get(v_x_359_, 0);
lean_inc(v_i_363_);
lean_dec_ref_known(v_x_359_, 1);
v___x_364_ = l_Lean_RArray_getImpl___redArg(v_ctx_358_, v_i_363_);
lean_dec(v_i_363_);
return v___x_364_;
}
case 2:
{
lean_object* v_toAddCommMonoid_365_; lean_object* v_toAdd_366_; lean_object* v_a_367_; lean_object* v_b_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_toAddCommMonoid_365_ = lean_ctor_get(v___x_360_, 0);
lean_inc_ref(v_toAddCommMonoid_365_);
lean_dec_ref(v___x_360_);
v_toAdd_366_ = lean_ctor_get(v_toAddCommMonoid_365_, 1);
lean_inc(v_toAdd_366_);
lean_dec_ref(v_toAddCommMonoid_365_);
v_a_367_ = lean_ctor_get(v_x_359_, 0);
lean_inc(v_a_367_);
v_b_368_ = lean_ctor_get(v_x_359_, 1);
lean_inc(v_b_368_);
lean_dec_ref_known(v_x_359_, 2);
lean_inc_ref(v_inst_357_);
v___x_369_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_357_, v_ctx_358_, v_a_367_);
v___x_370_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_357_, v_ctx_358_, v_b_368_);
v___x_371_ = lean_apply_2(v_toAdd_366_, v___x_369_, v___x_370_);
return v___x_371_;
}
case 3:
{
lean_object* v_toAddCommGroup_372_; lean_object* v_toSub_373_; lean_object* v_a_374_; lean_object* v_b_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_toAddCommGroup_372_ = lean_ctor_get(v_inst_357_, 0);
lean_dec_ref(v___x_360_);
v_toSub_373_ = lean_ctor_get(v_toAddCommGroup_372_, 2);
lean_inc(v_toSub_373_);
v_a_374_ = lean_ctor_get(v_x_359_, 0);
lean_inc(v_a_374_);
v_b_375_ = lean_ctor_get(v_x_359_, 1);
lean_inc(v_b_375_);
lean_dec_ref_known(v_x_359_, 2);
lean_inc_ref(v_inst_357_);
v___x_376_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_357_, v_ctx_358_, v_a_374_);
v___x_377_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_357_, v_ctx_358_, v_b_375_);
v___x_378_ = lean_apply_2(v_toSub_373_, v___x_376_, v___x_377_);
return v___x_378_;
}
case 4:
{
lean_object* v_toAddCommGroup_379_; lean_object* v_toNeg_380_; lean_object* v_a_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_toAddCommGroup_379_ = lean_ctor_get(v_inst_357_, 0);
lean_dec_ref(v___x_360_);
v_toNeg_380_ = lean_ctor_get(v_toAddCommGroup_379_, 1);
lean_inc(v_toNeg_380_);
v_a_381_ = lean_ctor_get(v_x_359_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v_x_359_, 1);
v___x_382_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_357_, v_ctx_358_, v_a_381_);
v___x_383_ = lean_apply_1(v_toNeg_380_, v___x_382_);
return v___x_383_;
}
case 5:
{
lean_object* v_nsmul_384_; lean_object* v_k_385_; lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_nsmul_384_ = lean_ctor_get(v___x_360_, 1);
lean_inc(v_nsmul_384_);
lean_dec_ref(v___x_360_);
v_k_385_ = lean_ctor_get(v_x_359_, 0);
lean_inc(v_k_385_);
v_a_386_ = lean_ctor_get(v_x_359_, 1);
lean_inc(v_a_386_);
lean_dec_ref_known(v_x_359_, 2);
v___x_387_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_357_, v_ctx_358_, v_a_386_);
v___x_388_ = lean_apply_2(v_nsmul_384_, v_k_385_, v___x_387_);
return v___x_388_;
}
default: 
{
lean_object* v_zsmul_389_; lean_object* v_k_390_; lean_object* v_a_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec_ref(v___x_360_);
v_zsmul_389_ = lean_ctor_get(v_inst_357_, 2);
lean_inc(v_zsmul_389_);
v_k_390_ = lean_ctor_get(v_x_359_, 0);
lean_inc(v_k_390_);
v_a_391_ = lean_ctor_get(v_x_359_, 1);
lean_inc(v_a_391_);
lean_dec_ref_known(v_x_359_, 2);
v___x_392_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_357_, v_ctx_358_, v_a_391_);
v___x_393_ = lean_apply_2(v_zsmul_389_, v_k_390_, v___x_392_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___redArg___boxed(lean_object* v_inst_394_, lean_object* v_ctx_395_, lean_object* v_x_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_394_, v_ctx_395_, v_x_396_);
lean_dec_ref(v_ctx_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote(lean_object* v_00_u03b1_398_, lean_object* v_inst_399_, lean_object* v_ctx_400_, lean_object* v_x_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_399_, v_ctx_400_, v_x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___boxed(lean_object* v_00_u03b1_403_, lean_object* v_inst_404_, lean_object* v_ctx_405_, lean_object* v_x_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Grind_Linarith_Expr_denote(v_00_u03b1_403_, v_inst_404_, v_ctx_405_, v_x_406_);
lean_dec_ref(v_ctx_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorIdx___impl(lean_object* v_x_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = lean_obj_tag_nat(v_x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorIdx___impl___boxed(lean_object* v_x_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Grind_Linarith_Poly_ctorIdx___impl(v_x_410_);
lean_dec(v_x_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim___redArg(lean_object* v_t_412_, lean_object* v_k_413_){
_start:
{
if (lean_obj_tag(v_t_412_) == 0)
{
return v_k_413_;
}
else
{
lean_object* v_k_414_; lean_object* v_v_415_; lean_object* v_p_416_; lean_object* v___x_417_; 
v_k_414_ = lean_ctor_get(v_t_412_, 0);
lean_inc(v_k_414_);
v_v_415_ = lean_ctor_get(v_t_412_, 1);
lean_inc(v_v_415_);
v_p_416_ = lean_ctor_get(v_t_412_, 2);
lean_inc(v_p_416_);
lean_dec_ref_known(v_t_412_, 3);
v___x_417_ = lean_apply_3(v_k_413_, v_k_414_, v_v_415_, v_p_416_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim(lean_object* v_motive_418_, lean_object* v_ctorIdx_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_k_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_420_, v_k_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim___boxed(lean_object* v_motive_424_, lean_object* v_ctorIdx_425_, lean_object* v_t_426_, lean_object* v_h_427_, lean_object* v_k_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Grind_Linarith_Poly_ctorElim(v_motive_424_, v_ctorIdx_425_, v_t_426_, v_h_427_, v_k_428_);
lean_dec(v_ctorIdx_425_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_nil_elim___redArg(lean_object* v_t_430_, lean_object* v_nil_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_430_, v_nil_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_nil_elim(lean_object* v_motive_433_, lean_object* v_t_434_, lean_object* v_h_435_, lean_object* v_nil_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_434_, v_nil_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_add_elim___redArg(lean_object* v_t_438_, lean_object* v_add_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_438_, v_add_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_add_elim(lean_object* v_motive_441_, lean_object* v_t_442_, lean_object* v_h_443_, lean_object* v_add_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_442_, v_add_444_);
return v___x_445_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_instBEqPoly_beq(lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_446_) == 0)
{
if (lean_obj_tag(v_x_447_) == 0)
{
uint8_t v___x_448_; 
v___x_448_ = 1;
return v___x_448_;
}
else
{
uint8_t v___x_449_; 
v___x_449_ = 0;
return v___x_449_;
}
}
else
{
if (lean_obj_tag(v_x_447_) == 1)
{
lean_object* v_k_450_; lean_object* v_v_451_; lean_object* v_p_452_; lean_object* v_k_453_; lean_object* v_v_454_; lean_object* v_p_455_; uint8_t v___x_456_; 
v_k_450_ = lean_ctor_get(v_x_446_, 0);
v_v_451_ = lean_ctor_get(v_x_446_, 1);
v_p_452_ = lean_ctor_get(v_x_446_, 2);
v_k_453_ = lean_ctor_get(v_x_447_, 0);
v_v_454_ = lean_ctor_get(v_x_447_, 1);
v_p_455_ = lean_ctor_get(v_x_447_, 2);
v___x_456_ = lean_int_dec_eq(v_k_450_, v_k_453_);
if (v___x_456_ == 0)
{
return v___x_456_;
}
else
{
uint8_t v___x_457_; 
v___x_457_ = lean_nat_dec_eq(v_v_451_, v_v_454_);
if (v___x_457_ == 0)
{
return v___x_457_;
}
else
{
v_x_446_ = v_p_452_;
v_x_447_ = v_p_455_;
goto _start;
}
}
}
else
{
uint8_t v___x_459_; 
v___x_459_ = 0;
return v___x_459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instBEqPoly_beq___boxed(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_x_460_, v_x_461_);
lean_dec(v_x_461_);
lean_dec(v_x_460_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_466_, lean_object* v_x_467_, lean_object* v_h__1_468_, lean_object* v_h__2_469_, lean_object* v_h__3_470_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_dec(v_h__2_469_);
if (lean_obj_tag(v_x_467_) == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec(v_h__3_470_);
v___x_471_ = lean_box(0);
v___x_472_ = lean_apply_1(v_h__1_468_, v___x_471_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; 
lean_dec(v_h__1_468_);
v___x_473_ = lean_apply_4(v_h__3_470_, v_x_466_, v_x_467_, lean_box(0), lean_box(0));
return v___x_473_;
}
}
else
{
lean_dec(v_h__1_468_);
if (lean_obj_tag(v_x_467_) == 1)
{
lean_object* v_k_474_; lean_object* v_v_475_; lean_object* v_p_476_; lean_object* v_k_477_; lean_object* v_v_478_; lean_object* v_p_479_; lean_object* v___x_480_; 
lean_dec(v_h__3_470_);
v_k_474_ = lean_ctor_get(v_x_466_, 0);
lean_inc(v_k_474_);
v_v_475_ = lean_ctor_get(v_x_466_, 1);
lean_inc(v_v_475_);
v_p_476_ = lean_ctor_get(v_x_466_, 2);
lean_inc(v_p_476_);
lean_dec_ref_known(v_x_466_, 3);
v_k_477_ = lean_ctor_get(v_x_467_, 0);
lean_inc(v_k_477_);
v_v_478_ = lean_ctor_get(v_x_467_, 1);
lean_inc(v_v_478_);
v_p_479_ = lean_ctor_get(v_x_467_, 2);
lean_inc(v_p_479_);
lean_dec_ref_known(v_x_467_, 3);
v___x_480_ = lean_apply_6(v_h__2_469_, v_k_474_, v_v_475_, v_p_476_, v_k_477_, v_v_478_, v_p_479_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; 
lean_dec(v_h__2_469_);
v___x_481_ = lean_apply_4(v_h__3_470_, v_x_466_, v_x_467_, lean_box(0), lean_box(0));
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_h__1_485_, lean_object* v_h__2_486_, lean_object* v_h__3_487_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
lean_dec(v_h__2_486_);
if (lean_obj_tag(v_x_484_) == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec(v_h__3_487_);
v___x_488_ = lean_box(0);
v___x_489_ = lean_apply_1(v_h__1_485_, v___x_488_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; 
lean_dec(v_h__1_485_);
v___x_490_ = lean_apply_4(v_h__3_487_, v_x_483_, v_x_484_, lean_box(0), lean_box(0));
return v___x_490_;
}
}
else
{
lean_dec(v_h__1_485_);
if (lean_obj_tag(v_x_484_) == 1)
{
lean_object* v_k_491_; lean_object* v_v_492_; lean_object* v_p_493_; lean_object* v_k_494_; lean_object* v_v_495_; lean_object* v_p_496_; lean_object* v___x_497_; 
lean_dec(v_h__3_487_);
v_k_491_ = lean_ctor_get(v_x_483_, 0);
lean_inc(v_k_491_);
v_v_492_ = lean_ctor_get(v_x_483_, 1);
lean_inc(v_v_492_);
v_p_493_ = lean_ctor_get(v_x_483_, 2);
lean_inc(v_p_493_);
lean_dec_ref_known(v_x_483_, 3);
v_k_494_ = lean_ctor_get(v_x_484_, 0);
lean_inc(v_k_494_);
v_v_495_ = lean_ctor_get(v_x_484_, 1);
lean_inc(v_v_495_);
v_p_496_ = lean_ctor_get(v_x_484_, 2);
lean_inc(v_p_496_);
lean_dec_ref_known(v_x_484_, 3);
v___x_497_ = lean_apply_6(v_h__2_486_, v_k_491_, v_v_492_, v_p_493_, v_k_494_, v_v_495_, v_p_496_);
return v___x_497_;
}
else
{
lean_object* v___x_498_; 
lean_dec(v_h__2_486_);
v___x_498_ = lean_apply_4(v_h__3_487_, v_x_483_, v_x_484_, lean_box(0), lean_box(0));
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprPoly_repr(lean_object* v_x_508_, lean_object* v_prec_509_){
_start:
{
lean_object* v___y_511_; 
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(1024u);
v___x_518_ = lean_nat_dec_le(v___x_517_, v_prec_509_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
v___x_519_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_511_ = v___x_519_;
goto v___jp_510_;
}
else
{
lean_object* v___x_520_; 
v___x_520_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_511_ = v___x_520_;
goto v___jp_510_;
}
}
else
{
lean_object* v_k_521_; lean_object* v_v_522_; lean_object* v_p_523_; lean_object* v___x_524_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_543_; uint8_t v___x_553_; 
v_k_521_ = lean_ctor_get(v_x_508_, 0);
lean_inc(v_k_521_);
v_v_522_ = lean_ctor_get(v_x_508_, 1);
lean_inc(v_v_522_);
v_p_523_ = lean_ctor_get(v_x_508_, 2);
lean_inc(v_p_523_);
lean_dec_ref_known(v_x_508_, 3);
v___x_524_ = lean_unsigned_to_nat(1024u);
v___x_553_ = lean_nat_dec_le(v___x_524_, v_prec_509_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
v___x_554_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_543_ = v___x_554_;
goto v___jp_542_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_543_ = v___x_555_;
goto v___jp_542_;
}
v___jp_525_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
lean_inc(v___y_526_);
v___x_530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_530_, 0, v___y_526_);
lean_ctor_set(v___x_530_, 1, v___y_529_);
lean_inc_n(v___y_528_, 2);
v___x_531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___y_528_);
v___x_532_ = l_Nat_reprFast(v_v_522_);
v___x_533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
v___x_534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_531_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___y_528_);
v___x_536_ = l_Lean_Grind_Linarith_instReprPoly_repr(v_p_523_, v___x_524_);
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
lean_inc(v___y_527_);
v___x_538_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_538_, 0, v___y_527_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = 0;
v___x_540_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*1, v___x_539_);
v___x_541_ = l_Repr_addAppParen(v___x_540_, v_prec_509_);
return v___x_541_;
}
v___jp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_544_ = lean_box(1);
v___x_545_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprPoly_repr___closed__4));
v___x_546_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_547_ = lean_int_dec_lt(v_k_521_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = l_Int_repr(v_k_521_);
lean_dec(v_k_521_);
v___x_549_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
v___y_526_ = v___x_545_;
v___y_527_ = v___y_543_;
v___y_528_ = v___x_544_;
v___y_529_ = v___x_549_;
goto v___jp_525_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = l_Int_repr(v_k_521_);
lean_dec(v_k_521_);
v___x_551_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
v___x_552_ = l_Repr_addAppParen(v___x_551_, v___x_524_);
v___y_526_ = v___x_545_;
v___y_527_ = v___y_543_;
v___y_528_ = v___x_544_;
v___y_529_ = v___x_552_;
goto v___jp_525_;
}
}
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_512_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprPoly_repr___closed__1));
lean_inc(v___y_511_);
v___x_513_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_513_, 0, v___y_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = 0;
v___x_515_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*1, v___x_514_);
v___x_516_ = l_Repr_addAppParen(v___x_515_, v_prec_509_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprPoly_repr___boxed(lean_object* v_x_556_, lean_object* v_prec_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Grind_Linarith_instReprPoly_repr(v_x_556_, v_prec_557_);
lean_dec(v_prec_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___redArg(lean_object* v_inst_561_, lean_object* v_ctx_562_, lean_object* v_p_563_){
_start:
{
lean_object* v___x_564_; lean_object* v_toAddCommMonoid_565_; 
v___x_564_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_561_);
v_toAddCommMonoid_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc_ref(v_toAddCommMonoid_565_);
lean_dec_ref(v___x_564_);
if (lean_obj_tag(v_p_563_) == 0)
{
lean_object* v_toZero_566_; 
lean_dec_ref(v_inst_561_);
v_toZero_566_ = lean_ctor_get(v_toAddCommMonoid_565_, 0);
lean_inc(v_toZero_566_);
lean_dec_ref(v_toAddCommMonoid_565_);
return v_toZero_566_;
}
else
{
lean_object* v_toAdd_567_; lean_object* v_zsmul_568_; lean_object* v_k_569_; lean_object* v_v_570_; lean_object* v_p_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_toAdd_567_ = lean_ctor_get(v_toAddCommMonoid_565_, 1);
lean_inc(v_toAdd_567_);
lean_dec_ref(v_toAddCommMonoid_565_);
v_zsmul_568_ = lean_ctor_get(v_inst_561_, 2);
v_k_569_ = lean_ctor_get(v_p_563_, 0);
lean_inc(v_k_569_);
v_v_570_ = lean_ctor_get(v_p_563_, 1);
lean_inc(v_v_570_);
v_p_571_ = lean_ctor_get(v_p_563_, 2);
lean_inc(v_p_571_);
lean_dec_ref_known(v_p_563_, 3);
v___x_572_ = l_Lean_RArray_getImpl___redArg(v_ctx_562_, v_v_570_);
lean_dec(v_v_570_);
lean_inc(v_zsmul_568_);
v___x_573_ = lean_apply_2(v_zsmul_568_, v_k_569_, v___x_572_);
v___x_574_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_561_, v_ctx_562_, v_p_571_);
v___x_575_ = lean_apply_2(v_toAdd_567_, v___x_573_, v___x_574_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___redArg___boxed(lean_object* v_inst_576_, lean_object* v_ctx_577_, lean_object* v_p_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_576_, v_ctx_577_, v_p_578_);
lean_dec_ref(v_ctx_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote(lean_object* v_00_u03b1_580_, lean_object* v_inst_581_, lean_object* v_ctx_582_, lean_object* v_p_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_581_, v_ctx_582_, v_p_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___boxed(lean_object* v_00_u03b1_585_, lean_object* v_inst_586_, lean_object* v_ctx_587_, lean_object* v_p_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Grind_Linarith_Poly_denote(v_00_u03b1_585_, v_inst_586_, v_ctx_587_, v_p_588_);
lean_dec_ref(v_ctx_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(lean_object* v_inst_590_, lean_object* v_ctx_591_, lean_object* v_r_592_, lean_object* v_p_593_){
_start:
{
lean_object* v___x_594_; lean_object* v_toAddCommMonoid_595_; 
v___x_594_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_590_);
v_toAddCommMonoid_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc_ref(v_toAddCommMonoid_595_);
lean_dec_ref(v___x_594_);
if (lean_obj_tag(v_p_593_) == 0)
{
lean_dec_ref(v_toAddCommMonoid_595_);
lean_dec_ref(v_inst_590_);
return v_r_592_;
}
else
{
lean_object* v_toAdd_596_; lean_object* v_zsmul_597_; lean_object* v_k_598_; lean_object* v_v_599_; lean_object* v_p_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_toAdd_596_ = lean_ctor_get(v_toAddCommMonoid_595_, 1);
lean_inc(v_toAdd_596_);
lean_dec_ref(v_toAddCommMonoid_595_);
v_zsmul_597_ = lean_ctor_get(v_inst_590_, 2);
v_k_598_ = lean_ctor_get(v_p_593_, 0);
lean_inc(v_k_598_);
v_v_599_ = lean_ctor_get(v_p_593_, 1);
lean_inc(v_v_599_);
v_p_600_ = lean_ctor_get(v_p_593_, 2);
lean_inc(v_p_600_);
lean_dec_ref_known(v_p_593_, 3);
v___x_601_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_602_ = lean_int_dec_eq(v_k_598_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = l_Lean_RArray_getImpl___redArg(v_ctx_591_, v_v_599_);
lean_dec(v_v_599_);
lean_inc(v_zsmul_597_);
v___x_604_ = lean_apply_2(v_zsmul_597_, v_k_598_, v___x_603_);
v___x_605_ = lean_apply_2(v_toAdd_596_, v_r_592_, v___x_604_);
v_r_592_ = v___x_605_;
v_p_593_ = v_p_600_;
goto _start;
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v_k_598_);
v___x_607_ = l_Lean_RArray_getImpl___redArg(v_ctx_591_, v_v_599_);
lean_dec(v_v_599_);
v___x_608_ = lean_apply_2(v_toAdd_596_, v_r_592_, v___x_607_);
v_r_592_ = v___x_608_;
v_p_593_ = v_p_600_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg___boxed(lean_object* v_inst_610_, lean_object* v_ctx_611_, lean_object* v_r_612_, lean_object* v_p_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_610_, v_ctx_611_, v_r_612_, v_p_613_);
lean_dec_ref(v_ctx_611_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go(lean_object* v_00_u03b1_615_, lean_object* v_inst_616_, lean_object* v_ctx_617_, lean_object* v_r_618_, lean_object* v_p_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_616_, v_ctx_617_, v_r_618_, v_p_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___boxed(lean_object* v_00_u03b1_621_, lean_object* v_inst_622_, lean_object* v_ctx_623_, lean_object* v_r_624_, lean_object* v_p_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Grind_Linarith_Poly_denote_x27_go(v_00_u03b1_621_, v_inst_622_, v_ctx_623_, v_r_624_, v_p_625_);
lean_dec_ref(v_ctx_623_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___redArg(lean_object* v_inst_627_, lean_object* v_ctx_628_, lean_object* v_p_629_){
_start:
{
lean_object* v___x_630_; lean_object* v_toAddCommMonoid_631_; 
v___x_630_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_627_);
v_toAddCommMonoid_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc_ref(v_toAddCommMonoid_631_);
lean_dec_ref(v___x_630_);
if (lean_obj_tag(v_p_629_) == 0)
{
lean_object* v_toZero_632_; 
lean_dec_ref(v_inst_627_);
v_toZero_632_ = lean_ctor_get(v_toAddCommMonoid_631_, 0);
lean_inc(v_toZero_632_);
lean_dec_ref(v_toAddCommMonoid_631_);
return v_toZero_632_;
}
else
{
lean_object* v_zsmul_633_; lean_object* v_k_634_; lean_object* v_v_635_; lean_object* v_p_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
lean_dec_ref(v_toAddCommMonoid_631_);
v_zsmul_633_ = lean_ctor_get(v_inst_627_, 2);
v_k_634_ = lean_ctor_get(v_p_629_, 0);
lean_inc(v_k_634_);
v_v_635_ = lean_ctor_get(v_p_629_, 1);
lean_inc(v_v_635_);
v_p_636_ = lean_ctor_get(v_p_629_, 2);
lean_inc(v_p_636_);
lean_dec_ref_known(v_p_629_, 3);
v___x_637_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_638_ = lean_int_dec_eq(v_k_634_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = l_Lean_RArray_getImpl___redArg(v_ctx_628_, v_v_635_);
lean_dec(v_v_635_);
lean_inc(v_zsmul_633_);
v___x_640_ = lean_apply_2(v_zsmul_633_, v_k_634_, v___x_639_);
v___x_641_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_627_, v_ctx_628_, v___x_640_, v_p_636_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec(v_k_634_);
v___x_642_ = l_Lean_RArray_getImpl___redArg(v_ctx_628_, v_v_635_);
lean_dec(v_v_635_);
v___x_643_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_627_, v_ctx_628_, v___x_642_, v_p_636_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___redArg___boxed(lean_object* v_inst_644_, lean_object* v_ctx_645_, lean_object* v_p_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Grind_Linarith_Poly_denote_x27___redArg(v_inst_644_, v_ctx_645_, v_p_646_);
lean_dec_ref(v_ctx_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27(lean_object* v_00_u03b1_648_, lean_object* v_inst_649_, lean_object* v_ctx_650_, lean_object* v_p_651_){
_start:
{
lean_object* v___x_652_; lean_object* v_toAddCommMonoid_653_; 
v___x_652_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_649_);
v_toAddCommMonoid_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc_ref(v_toAddCommMonoid_653_);
lean_dec_ref(v___x_652_);
if (lean_obj_tag(v_p_651_) == 0)
{
lean_object* v_toZero_654_; 
lean_dec_ref(v_inst_649_);
v_toZero_654_ = lean_ctor_get(v_toAddCommMonoid_653_, 0);
lean_inc(v_toZero_654_);
lean_dec_ref(v_toAddCommMonoid_653_);
return v_toZero_654_;
}
else
{
lean_object* v_zsmul_655_; lean_object* v_k_656_; lean_object* v_v_657_; lean_object* v_p_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
lean_dec_ref(v_toAddCommMonoid_653_);
v_zsmul_655_ = lean_ctor_get(v_inst_649_, 2);
v_k_656_ = lean_ctor_get(v_p_651_, 0);
lean_inc(v_k_656_);
v_v_657_ = lean_ctor_get(v_p_651_, 1);
lean_inc(v_v_657_);
v_p_658_ = lean_ctor_get(v_p_651_, 2);
lean_inc(v_p_658_);
lean_dec_ref_known(v_p_651_, 3);
v___x_659_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_660_ = lean_int_dec_eq(v_k_656_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = l_Lean_RArray_getImpl___redArg(v_ctx_650_, v_v_657_);
lean_dec(v_v_657_);
lean_inc(v_zsmul_655_);
v___x_662_ = lean_apply_2(v_zsmul_655_, v_k_656_, v___x_661_);
v___x_663_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_649_, v_ctx_650_, v___x_662_, v_p_658_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec(v_k_656_);
v___x_664_ = l_Lean_RArray_getImpl___redArg(v_ctx_650_, v_v_657_);
lean_dec(v_v_657_);
v___x_665_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_649_, v_ctx_650_, v___x_664_, v_p_658_);
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___boxed(lean_object* v_00_u03b1_666_, lean_object* v_inst_667_, lean_object* v_ctx_668_, lean_object* v_p_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Grind_Linarith_Poly_denote_x27(v_00_u03b1_666_, v_inst_667_, v_ctx_668_, v_p_669_);
lean_dec_ref(v_ctx_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter___redArg(lean_object* v_p_671_, lean_object* v_h__1_672_, lean_object* v_h__2_673_, lean_object* v_h__3_674_){
_start:
{
if (lean_obj_tag(v_p_671_) == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v_h__3_674_);
lean_dec(v_h__2_673_);
v___x_675_ = lean_box(0);
v___x_676_ = lean_apply_1(v_h__1_672_, v___x_675_);
return v___x_676_;
}
else
{
lean_object* v_k_677_; lean_object* v_v_678_; lean_object* v_p_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
lean_dec(v_h__1_672_);
v_k_677_ = lean_ctor_get(v_p_671_, 0);
lean_inc(v_k_677_);
v_v_678_ = lean_ctor_get(v_p_671_, 1);
lean_inc(v_v_678_);
v_p_679_ = lean_ctor_get(v_p_671_, 2);
lean_inc(v_p_679_);
lean_dec_ref_known(v_p_671_, 3);
v___x_680_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_681_ = lean_int_dec_eq(v_k_677_, v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
lean_dec(v_h__2_673_);
v___x_682_ = lean_apply_4(v_h__3_674_, v_k_677_, v_v_678_, v_p_679_, lean_box(0));
return v___x_682_;
}
else
{
lean_object* v___x_683_; 
lean_dec(v_k_677_);
lean_dec(v_h__3_674_);
v___x_683_ = lean_apply_2(v_h__2_673_, v_v_678_, v_p_679_);
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter(lean_object* v_motive_684_, lean_object* v_p_685_, lean_object* v_h__1_686_, lean_object* v_h__2_687_, lean_object* v_h__3_688_){
_start:
{
if (lean_obj_tag(v_p_685_) == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec(v_h__3_688_);
lean_dec(v_h__2_687_);
v___x_689_ = lean_box(0);
v___x_690_ = lean_apply_1(v_h__1_686_, v___x_689_);
return v___x_690_;
}
else
{
lean_object* v_k_691_; lean_object* v_v_692_; lean_object* v_p_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
lean_dec(v_h__1_686_);
v_k_691_ = lean_ctor_get(v_p_685_, 0);
lean_inc(v_k_691_);
v_v_692_ = lean_ctor_get(v_p_685_, 1);
lean_inc(v_v_692_);
v_p_693_ = lean_ctor_get(v_p_685_, 2);
lean_inc(v_p_693_);
lean_dec_ref_known(v_p_685_, 3);
v___x_694_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_695_ = lean_int_dec_eq(v_k_691_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
lean_dec(v_h__2_687_);
v___x_696_ = lean_apply_4(v_h__3_688_, v_k_691_, v_v_692_, v_p_693_, lean_box(0));
return v___x_696_;
}
else
{
lean_object* v___x_697_; 
lean_dec(v_k_691_);
lean_dec(v_h__3_688_);
v___x_697_ = lean_apply_2(v_h__2_687_, v_v_692_, v_p_693_);
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_coeff(lean_object* v_p_698_, lean_object* v_x_699_){
_start:
{
if (lean_obj_tag(v_p_698_) == 0)
{
lean_object* v___x_700_; 
v___x_700_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
return v___x_700_;
}
else
{
lean_object* v_k_701_; lean_object* v_v_702_; lean_object* v_p_703_; uint8_t v___x_704_; 
v_k_701_ = lean_ctor_get(v_p_698_, 0);
v_v_702_ = lean_ctor_get(v_p_698_, 1);
v_p_703_ = lean_ctor_get(v_p_698_, 2);
v___x_704_ = lean_nat_dec_eq(v_x_699_, v_v_702_);
if (v___x_704_ == 0)
{
v_p_698_ = v_p_703_;
goto _start;
}
else
{
lean_inc(v_k_701_);
return v_k_701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_coeff___boxed(lean_object* v_p_706_, lean_object* v_x_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_706_, v_x_707_);
lean_dec(v_x_707_);
lean_dec(v_p_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_insert(lean_object* v_k_709_, lean_object* v_v_710_, lean_object* v_p_711_){
_start:
{
if (lean_obj_tag(v_p_711_) == 0)
{
lean_object* v___x_712_; 
v___x_712_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_712_, 0, v_k_709_);
lean_ctor_set(v___x_712_, 1, v_v_710_);
lean_ctor_set(v___x_712_, 2, v_p_711_);
return v___x_712_;
}
else
{
lean_object* v_k_713_; lean_object* v_v_714_; lean_object* v_p_715_; uint8_t v___x_716_; 
v_k_713_ = lean_ctor_get(v_p_711_, 0);
v_v_714_ = lean_ctor_get(v_p_711_, 1);
v_p_715_ = lean_ctor_get(v_p_711_, 2);
v___x_716_ = l_Nat_blt(v_v_714_, v_v_710_);
if (v___x_716_ == 0)
{
lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_731_; 
lean_inc(v_p_715_);
lean_inc(v_v_714_);
lean_inc(v_k_713_);
v_isSharedCheck_731_ = !lean_is_exclusive(v_p_711_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; lean_object* v_unused_733_; lean_object* v_unused_734_; 
v_unused_732_ = lean_ctor_get(v_p_711_, 2);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_p_711_, 1);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_p_711_, 0);
lean_dec(v_unused_734_);
v___x_718_ = v_p_711_;
v_isShared_719_ = v_isSharedCheck_731_;
goto v_resetjp_717_;
}
else
{
lean_dec(v_p_711_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_731_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
uint8_t v___x_720_; 
v___x_720_ = lean_nat_dec_eq(v_v_710_, v_v_714_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_721_ = l_Lean_Grind_Linarith_Poly_insert(v_k_709_, v_v_710_, v_p_715_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 2, v___x_721_);
v___x_723_ = v___x_718_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_k_713_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_v_714_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
lean_dec(v_v_710_);
v___x_725_ = lean_int_add(v_k_709_, v_k_713_);
lean_dec(v_k_713_);
lean_dec(v_k_709_);
v___x_726_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_727_ = lean_int_dec_eq(v___x_725_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_729_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_725_);
v___x_729_ = v___x_718_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_v_714_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_p_715_);
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
lean_dec(v___x_725_);
lean_del_object(v___x_718_);
lean_dec(v_v_714_);
return v_p_715_;
}
}
}
}
else
{
lean_object* v___x_735_; 
v___x_735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_735_, 0, v_k_709_);
lean_ctor_set(v___x_735_, 1, v_v_710_);
lean_ctor_set(v___x_735_, 2, v_p_711_);
return v___x_735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_norm(lean_object* v_p_736_){
_start:
{
if (lean_obj_tag(v_p_736_) == 0)
{
return v_p_736_;
}
else
{
lean_object* v_k_737_; lean_object* v_v_738_; lean_object* v_p_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_k_737_ = lean_ctor_get(v_p_736_, 0);
lean_inc(v_k_737_);
v_v_738_ = lean_ctor_get(v_p_736_, 1);
lean_inc(v_v_738_);
v_p_739_ = lean_ctor_get(v_p_736_, 2);
lean_inc(v_p_739_);
lean_dec_ref_known(v_p_736_, 3);
v___x_740_ = l_Lean_Grind_Linarith_Poly_norm(v_p_739_);
v___x_741_ = l_Lean_Grind_Linarith_Poly_insert(v_k_737_, v_v_738_, v___x_740_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_append(lean_object* v_p_u2081_742_, lean_object* v_p_u2082_743_){
_start:
{
if (lean_obj_tag(v_p_u2081_742_) == 0)
{
lean_inc(v_p_u2082_743_);
return v_p_u2082_743_;
}
else
{
lean_object* v_k_744_; lean_object* v_v_745_; lean_object* v_p_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
v_k_744_ = lean_ctor_get(v_p_u2081_742_, 0);
v_v_745_ = lean_ctor_get(v_p_u2081_742_, 1);
v_p_746_ = lean_ctor_get(v_p_u2081_742_, 2);
v_isSharedCheck_754_ = !lean_is_exclusive(v_p_u2081_742_);
if (v_isSharedCheck_754_ == 0)
{
v___x_748_ = v_p_u2081_742_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_p_746_);
lean_inc(v_v_745_);
lean_inc(v_k_744_);
lean_dec(v_p_u2081_742_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = l_Lean_Grind_Linarith_Poly_append(v_p_746_, v_p_u2082_743_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 2, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_k_744_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_v_745_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_append___boxed(lean_object* v_p_u2081_755_, lean_object* v_p_u2082_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Grind_Linarith_Poly_append(v_p_u2081_755_, v_p_u2082_756_);
lean_dec(v_p_u2082_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_combine(lean_object* v_p_u2081_758_, lean_object* v_p_u2082_759_){
_start:
{
if (lean_obj_tag(v_p_u2081_758_) == 0)
{
return v_p_u2082_759_;
}
else
{
if (lean_obj_tag(v_p_u2082_759_) == 0)
{
return v_p_u2081_758_;
}
else
{
lean_object* v_k_760_; lean_object* v_v_761_; lean_object* v_p_762_; lean_object* v_k_763_; lean_object* v_v_764_; lean_object* v_p_765_; uint8_t v___x_766_; 
v_k_760_ = lean_ctor_get(v_p_u2081_758_, 0);
v_v_761_ = lean_ctor_get(v_p_u2081_758_, 1);
v_p_762_ = lean_ctor_get(v_p_u2081_758_, 2);
v_k_763_ = lean_ctor_get(v_p_u2082_759_, 0);
v_v_764_ = lean_ctor_get(v_p_u2082_759_, 1);
v_p_765_ = lean_ctor_get(v_p_u2082_759_, 2);
v___x_766_ = lean_nat_dec_eq(v_v_761_, v_v_764_);
if (v___x_766_ == 0)
{
uint8_t v___x_767_; 
v___x_767_ = l_Nat_blt(v_v_764_, v_v_761_);
if (v___x_767_ == 0)
{
lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_775_; 
lean_inc(v_p_765_);
lean_inc(v_v_764_);
lean_inc(v_k_763_);
v_isSharedCheck_775_ = !lean_is_exclusive(v_p_u2082_759_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; lean_object* v_unused_777_; lean_object* v_unused_778_; 
v_unused_776_ = lean_ctor_get(v_p_u2082_759_, 2);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_p_u2082_759_, 1);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_p_u2082_759_, 0);
lean_dec(v_unused_778_);
v___x_769_ = v_p_u2082_759_;
v_isShared_770_ = v_isSharedCheck_775_;
goto v_resetjp_768_;
}
else
{
lean_dec(v_p_u2082_759_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_775_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_771_ = l_Lean_Grind_Linarith_Poly_combine(v_p_u2081_758_, v_p_765_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 2, v___x_771_);
v___x_773_ = v___x_769_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_k_763_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_v_764_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
else
{
lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_786_; 
lean_inc(v_p_762_);
lean_inc(v_v_761_);
lean_inc(v_k_760_);
v_isSharedCheck_786_ = !lean_is_exclusive(v_p_u2081_758_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; lean_object* v_unused_788_; lean_object* v_unused_789_; 
v_unused_787_ = lean_ctor_get(v_p_u2081_758_, 2);
lean_dec(v_unused_787_);
v_unused_788_ = lean_ctor_get(v_p_u2081_758_, 1);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_p_u2081_758_, 0);
lean_dec(v_unused_789_);
v___x_780_ = v_p_u2081_758_;
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
else
{
lean_dec(v_p_u2081_758_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = l_Lean_Grind_Linarith_Poly_combine(v_p_762_, v_p_u2082_759_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 2, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_k_760_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_v_761_);
lean_ctor_set(v_reuseFailAlloc_785_, 2, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_801_; 
lean_inc(v_p_765_);
lean_inc(v_k_763_);
lean_inc(v_p_762_);
lean_inc(v_v_761_);
lean_inc(v_k_760_);
lean_dec_ref_known(v_p_u2081_758_, 3);
v_isSharedCheck_801_ = !lean_is_exclusive(v_p_u2082_759_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; lean_object* v_unused_803_; lean_object* v_unused_804_; 
v_unused_802_ = lean_ctor_get(v_p_u2082_759_, 2);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_p_u2082_759_, 1);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_p_u2082_759_, 0);
lean_dec(v_unused_804_);
v___x_791_ = v_p_u2082_759_;
v_isShared_792_ = v_isSharedCheck_801_;
goto v_resetjp_790_;
}
else
{
lean_dec(v_p_u2082_759_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_801_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_a_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_a_793_ = lean_int_add(v_k_760_, v_k_763_);
lean_dec(v_k_763_);
lean_dec(v_k_760_);
v___x_794_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_795_ = lean_int_dec_eq(v_a_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = l_Lean_Grind_Linarith_Poly_combine(v_p_762_, v_p_765_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 2, v___x_796_);
lean_ctor_set(v___x_791_, 1, v_v_761_);
lean_ctor_set(v___x_791_, 0, v_a_793_);
v___x_798_ = v___x_791_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_v_761_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
else
{
lean_dec(v_a_793_);
lean_del_object(v___x_791_);
lean_dec(v_v_761_);
v_p_u2081_758_ = v_p_762_;
v_p_u2082_759_ = v_p_765_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter___redArg(lean_object* v_p_u2081_805_, lean_object* v_p_u2082_806_, lean_object* v_h__1_807_, lean_object* v_h__2_808_, lean_object* v_h__3_809_){
_start:
{
if (lean_obj_tag(v_p_u2081_805_) == 0)
{
lean_object* v___x_810_; 
lean_dec(v_h__3_809_);
lean_dec(v_h__2_808_);
v___x_810_ = lean_apply_1(v_h__1_807_, v_p_u2082_806_);
return v___x_810_;
}
else
{
lean_dec(v_h__1_807_);
if (lean_obj_tag(v_p_u2082_806_) == 0)
{
lean_object* v___x_811_; 
lean_dec(v_h__3_809_);
v___x_811_ = lean_apply_2(v_h__2_808_, v_p_u2081_805_, lean_box(0));
return v___x_811_;
}
else
{
lean_object* v_k_812_; lean_object* v_v_813_; lean_object* v_p_814_; lean_object* v_k_815_; lean_object* v_v_816_; lean_object* v_p_817_; lean_object* v___x_818_; 
lean_dec(v_h__2_808_);
v_k_812_ = lean_ctor_get(v_p_u2081_805_, 0);
lean_inc(v_k_812_);
v_v_813_ = lean_ctor_get(v_p_u2081_805_, 1);
lean_inc(v_v_813_);
v_p_814_ = lean_ctor_get(v_p_u2081_805_, 2);
lean_inc(v_p_814_);
lean_dec_ref_known(v_p_u2081_805_, 3);
v_k_815_ = lean_ctor_get(v_p_u2082_806_, 0);
lean_inc(v_k_815_);
v_v_816_ = lean_ctor_get(v_p_u2082_806_, 1);
lean_inc(v_v_816_);
v_p_817_ = lean_ctor_get(v_p_u2082_806_, 2);
lean_inc(v_p_817_);
lean_dec_ref_known(v_p_u2082_806_, 3);
v___x_818_ = lean_apply_6(v_h__3_809_, v_k_812_, v_v_813_, v_p_814_, v_k_815_, v_v_816_, v_p_817_);
return v___x_818_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter(lean_object* v_motive_819_, lean_object* v_p_u2081_820_, lean_object* v_p_u2082_821_, lean_object* v_h__1_822_, lean_object* v_h__2_823_, lean_object* v_h__3_824_){
_start:
{
if (lean_obj_tag(v_p_u2081_820_) == 0)
{
lean_object* v___x_825_; 
lean_dec(v_h__3_824_);
lean_dec(v_h__2_823_);
v___x_825_ = lean_apply_1(v_h__1_822_, v_p_u2082_821_);
return v___x_825_;
}
else
{
lean_dec(v_h__1_822_);
if (lean_obj_tag(v_p_u2082_821_) == 0)
{
lean_object* v___x_826_; 
lean_dec(v_h__3_824_);
v___x_826_ = lean_apply_2(v_h__2_823_, v_p_u2081_820_, lean_box(0));
return v___x_826_;
}
else
{
lean_object* v_k_827_; lean_object* v_v_828_; lean_object* v_p_829_; lean_object* v_k_830_; lean_object* v_v_831_; lean_object* v_p_832_; lean_object* v___x_833_; 
lean_dec(v_h__2_823_);
v_k_827_ = lean_ctor_get(v_p_u2081_820_, 0);
lean_inc(v_k_827_);
v_v_828_ = lean_ctor_get(v_p_u2081_820_, 1);
lean_inc(v_v_828_);
v_p_829_ = lean_ctor_get(v_p_u2081_820_, 2);
lean_inc(v_p_829_);
lean_dec_ref_known(v_p_u2081_820_, 3);
v_k_830_ = lean_ctor_get(v_p_u2082_821_, 0);
lean_inc(v_k_830_);
v_v_831_ = lean_ctor_get(v_p_u2082_821_, 1);
lean_inc(v_v_831_);
v_p_832_ = lean_ctor_get(v_p_u2082_821_, 2);
lean_inc(v_p_832_);
lean_dec_ref_known(v_p_u2082_821_, 3);
v___x_833_ = lean_apply_6(v_h__3_824_, v_k_827_, v_v_828_, v_p_829_, v_k_830_, v_v_831_, v_p_832_);
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Expr_toPoly_x27_go_spec__0(lean_object* v_a_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = lean_nat_to_int(v_a_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPoly_x27_go(lean_object* v_coeff_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
switch(lean_obj_tag(v_a_837_))
{
case 0:
{
lean_dec(v_coeff_836_);
return v_a_838_;
}
case 1:
{
lean_object* v_i_839_; lean_object* v___x_840_; 
v_i_839_ = lean_ctor_get(v_a_837_, 0);
lean_inc(v_i_839_);
lean_dec_ref_known(v_a_837_, 1);
v___x_840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_840_, 0, v_coeff_836_);
lean_ctor_set(v___x_840_, 1, v_i_839_);
lean_ctor_set(v___x_840_, 2, v_a_838_);
return v___x_840_;
}
case 2:
{
lean_object* v_a_841_; lean_object* v_b_842_; lean_object* v___x_843_; 
v_a_841_ = lean_ctor_get(v_a_837_, 0);
lean_inc(v_a_841_);
v_b_842_ = lean_ctor_get(v_a_837_, 1);
lean_inc(v_b_842_);
lean_dec_ref_known(v_a_837_, 2);
lean_inc(v_coeff_836_);
v___x_843_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v_coeff_836_, v_b_842_, v_a_838_);
v_a_837_ = v_a_841_;
v_a_838_ = v___x_843_;
goto _start;
}
case 3:
{
lean_object* v_a_845_; lean_object* v_b_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_a_845_ = lean_ctor_get(v_a_837_, 0);
lean_inc(v_a_845_);
v_b_846_ = lean_ctor_get(v_a_837_, 1);
lean_inc(v_b_846_);
lean_dec_ref_known(v_a_837_, 2);
v___x_847_ = lean_int_neg(v_coeff_836_);
v___x_848_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v___x_847_, v_b_846_, v_a_838_);
v_a_837_ = v_a_845_;
v_a_838_ = v___x_848_;
goto _start;
}
case 4:
{
lean_object* v_a_850_; lean_object* v___x_851_; 
v_a_850_ = lean_ctor_get(v_a_837_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v_a_837_, 1);
v___x_851_ = lean_int_neg(v_coeff_836_);
lean_dec(v_coeff_836_);
v_coeff_836_ = v___x_851_;
v_a_837_ = v_a_850_;
goto _start;
}
case 5:
{
lean_object* v_k_853_; lean_object* v_a_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_k_853_ = lean_ctor_get(v_a_837_, 0);
lean_inc(v_k_853_);
v_a_854_ = lean_ctor_get(v_a_837_, 1);
lean_inc(v_a_854_);
lean_dec_ref_known(v_a_837_, 2);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_nat_dec_eq(v_k_853_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_nat_to_int(v_k_853_);
v___x_858_ = lean_int_mul(v_coeff_836_, v___x_857_);
lean_dec(v___x_857_);
lean_dec(v_coeff_836_);
v_coeff_836_ = v___x_858_;
v_a_837_ = v_a_854_;
goto _start;
}
else
{
lean_dec(v_a_854_);
lean_dec(v_k_853_);
lean_dec(v_coeff_836_);
return v_a_838_;
}
}
default: 
{
lean_object* v_k_860_; lean_object* v_a_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_k_860_ = lean_ctor_get(v_a_837_, 0);
lean_inc(v_k_860_);
v_a_861_ = lean_ctor_get(v_a_837_, 1);
lean_inc(v_a_861_);
lean_dec_ref_known(v_a_837_, 2);
v___x_862_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_863_ = lean_int_dec_eq(v_k_860_, v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; 
v___x_864_ = lean_int_mul(v_coeff_836_, v_k_860_);
lean_dec(v_k_860_);
lean_dec(v_coeff_836_);
v_coeff_836_ = v___x_864_;
v_a_837_ = v_a_861_;
goto _start;
}
else
{
lean_dec(v_a_861_);
lean_dec(v_k_860_);
lean_dec(v_coeff_836_);
return v_a_838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPoly_x27(lean_object* v_e_866_){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_868_ = lean_box(0);
v___x_869_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v___x_867_, v_e_866_, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_norm(lean_object* v_e_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = l_Lean_Grind_Linarith_Expr_toPoly_x27(v_e_870_);
v___x_872_ = l_Lean_Grind_Linarith_Poly_norm(v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul_x27(lean_object* v_p_873_, lean_object* v_k_874_){
_start:
{
if (lean_obj_tag(v_p_873_) == 0)
{
return v_p_873_;
}
else
{
lean_object* v_k_875_; lean_object* v_v_876_; lean_object* v_p_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_886_; 
v_k_875_ = lean_ctor_get(v_p_873_, 0);
v_v_876_ = lean_ctor_get(v_p_873_, 1);
v_p_877_ = lean_ctor_get(v_p_873_, 2);
v_isSharedCheck_886_ = !lean_is_exclusive(v_p_873_);
if (v_isSharedCheck_886_ == 0)
{
v___x_879_ = v_p_873_;
v_isShared_880_ = v_isSharedCheck_886_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_p_877_);
lean_inc(v_v_876_);
lean_inc(v_k_875_);
lean_dec(v_p_873_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_886_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_881_ = lean_int_mul(v_k_874_, v_k_875_);
lean_dec(v_k_875_);
v___x_882_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_877_, v_k_874_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 2, v___x_882_);
lean_ctor_set(v___x_879_, 0, v___x_881_);
v___x_884_ = v___x_879_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_v_876_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul_x27___boxed(lean_object* v_p_887_, lean_object* v_k_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_887_, v_k_888_);
lean_dec(v_k_888_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul(lean_object* v_p_890_, lean_object* v_k_891_){
_start:
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_893_ = lean_int_dec_eq(v_k_891_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_890_, v_k_891_);
return v___x_894_;
}
else
{
lean_object* v___x_895_; 
lean_dec(v_p_890_);
v___x_895_ = lean_box(0);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul___boxed(lean_object* v_p_896_, lean_object* v_k_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Grind_Linarith_Poly_mul(v_p_896_, v_k_897_);
lean_dec(v_k_897_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(lean_object* v_p_899_, lean_object* v_h__1_900_, lean_object* v_h__2_901_){
_start:
{
if (lean_obj_tag(v_p_899_) == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; 
lean_dec(v_h__2_901_);
v___x_902_ = lean_box(0);
v___x_903_ = lean_apply_1(v_h__1_900_, v___x_902_);
return v___x_903_;
}
else
{
lean_object* v_k_904_; lean_object* v_v_905_; lean_object* v_p_906_; lean_object* v___x_907_; 
lean_dec(v_h__1_900_);
v_k_904_ = lean_ctor_get(v_p_899_, 0);
lean_inc(v_k_904_);
v_v_905_ = lean_ctor_get(v_p_899_, 1);
lean_inc(v_v_905_);
v_p_906_ = lean_ctor_get(v_p_899_, 2);
lean_inc(v_p_906_);
lean_dec_ref_known(v_p_899_, 3);
v___x_907_ = lean_apply_3(v_h__2_901_, v_k_904_, v_v_905_, v_p_906_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(lean_object* v_motive_908_, lean_object* v_p_909_, lean_object* v_h__1_910_, lean_object* v_h__2_911_){
_start:
{
if (lean_obj_tag(v_p_909_) == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec(v_h__2_911_);
v___x_912_ = lean_box(0);
v___x_913_ = lean_apply_1(v_h__1_910_, v___x_912_);
return v___x_913_;
}
else
{
lean_object* v_k_914_; lean_object* v_v_915_; lean_object* v_p_916_; lean_object* v___x_917_; 
lean_dec(v_h__1_910_);
v_k_914_ = lean_ctor_get(v_p_909_, 0);
lean_inc(v_k_914_);
v_v_915_ = lean_ctor_get(v_p_909_, 1);
lean_inc(v_v_915_);
v_p_916_ = lean_ctor_get(v_p_909_, 2);
lean_inc(v_p_916_);
lean_dec_ref_known(v_p_909_, 3);
v___x_917_ = lean_apply_3(v_h__2_911_, v_k_914_, v_v_915_, v_p_916_);
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter___redArg(lean_object* v_x_918_, lean_object* v_h__1_919_, lean_object* v_h__2_920_, lean_object* v_h__3_921_, lean_object* v_h__4_922_, lean_object* v_h__5_923_, lean_object* v_h__6_924_, lean_object* v_h__7_925_){
_start:
{
switch(lean_obj_tag(v_x_918_))
{
case 0:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v_h__7_925_);
lean_dec(v_h__6_924_);
lean_dec(v_h__5_923_);
lean_dec(v_h__4_922_);
lean_dec(v_h__3_921_);
lean_dec(v_h__2_920_);
v___x_926_ = lean_box(0);
v___x_927_ = lean_apply_1(v_h__1_919_, v___x_926_);
return v___x_927_;
}
case 1:
{
lean_object* v_i_928_; lean_object* v___x_929_; 
lean_dec(v_h__7_925_);
lean_dec(v_h__6_924_);
lean_dec(v_h__5_923_);
lean_dec(v_h__4_922_);
lean_dec(v_h__3_921_);
lean_dec(v_h__1_919_);
v_i_928_ = lean_ctor_get(v_x_918_, 0);
lean_inc(v_i_928_);
lean_dec_ref_known(v_x_918_, 1);
v___x_929_ = lean_apply_1(v_h__2_920_, v_i_928_);
return v___x_929_;
}
case 2:
{
lean_object* v_a_930_; lean_object* v_b_931_; lean_object* v___x_932_; 
lean_dec(v_h__7_925_);
lean_dec(v_h__6_924_);
lean_dec(v_h__5_923_);
lean_dec(v_h__4_922_);
lean_dec(v_h__2_920_);
lean_dec(v_h__1_919_);
v_a_930_ = lean_ctor_get(v_x_918_, 0);
lean_inc(v_a_930_);
v_b_931_ = lean_ctor_get(v_x_918_, 1);
lean_inc(v_b_931_);
lean_dec_ref_known(v_x_918_, 2);
v___x_932_ = lean_apply_2(v_h__3_921_, v_a_930_, v_b_931_);
return v___x_932_;
}
case 3:
{
lean_object* v_a_933_; lean_object* v_b_934_; lean_object* v___x_935_; 
lean_dec(v_h__7_925_);
lean_dec(v_h__6_924_);
lean_dec(v_h__5_923_);
lean_dec(v_h__3_921_);
lean_dec(v_h__2_920_);
lean_dec(v_h__1_919_);
v_a_933_ = lean_ctor_get(v_x_918_, 0);
lean_inc(v_a_933_);
v_b_934_ = lean_ctor_get(v_x_918_, 1);
lean_inc(v_b_934_);
lean_dec_ref_known(v_x_918_, 2);
v___x_935_ = lean_apply_2(v_h__4_922_, v_a_933_, v_b_934_);
return v___x_935_;
}
case 4:
{
lean_object* v_a_936_; lean_object* v___x_937_; 
lean_dec(v_h__6_924_);
lean_dec(v_h__5_923_);
lean_dec(v_h__4_922_);
lean_dec(v_h__3_921_);
lean_dec(v_h__2_920_);
lean_dec(v_h__1_919_);
v_a_936_ = lean_ctor_get(v_x_918_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v_x_918_, 1);
v___x_937_ = lean_apply_1(v_h__7_925_, v_a_936_);
return v___x_937_;
}
case 5:
{
lean_object* v_k_938_; lean_object* v_a_939_; lean_object* v___x_940_; 
lean_dec(v_h__7_925_);
lean_dec(v_h__6_924_);
lean_dec(v_h__4_922_);
lean_dec(v_h__3_921_);
lean_dec(v_h__2_920_);
lean_dec(v_h__1_919_);
v_k_938_ = lean_ctor_get(v_x_918_, 0);
lean_inc(v_k_938_);
v_a_939_ = lean_ctor_get(v_x_918_, 1);
lean_inc(v_a_939_);
lean_dec_ref_known(v_x_918_, 2);
v___x_940_ = lean_apply_2(v_h__5_923_, v_k_938_, v_a_939_);
return v___x_940_;
}
default: 
{
lean_object* v_k_941_; lean_object* v_a_942_; lean_object* v___x_943_; 
lean_dec(v_h__7_925_);
lean_dec(v_h__5_923_);
lean_dec(v_h__4_922_);
lean_dec(v_h__3_921_);
lean_dec(v_h__2_920_);
lean_dec(v_h__1_919_);
v_k_941_ = lean_ctor_get(v_x_918_, 0);
lean_inc(v_k_941_);
v_a_942_ = lean_ctor_get(v_x_918_, 1);
lean_inc(v_a_942_);
lean_dec_ref_known(v_x_918_, 2);
v___x_943_ = lean_apply_2(v_h__6_924_, v_k_941_, v_a_942_);
return v___x_943_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter(lean_object* v_motive_944_, lean_object* v_x_945_, lean_object* v_h__1_946_, lean_object* v_h__2_947_, lean_object* v_h__3_948_, lean_object* v_h__4_949_, lean_object* v_h__5_950_, lean_object* v_h__6_951_, lean_object* v_h__7_952_){
_start:
{
switch(lean_obj_tag(v_x_945_))
{
case 0:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec(v_h__7_952_);
lean_dec(v_h__6_951_);
lean_dec(v_h__5_950_);
lean_dec(v_h__4_949_);
lean_dec(v_h__3_948_);
lean_dec(v_h__2_947_);
v___x_953_ = lean_box(0);
v___x_954_ = lean_apply_1(v_h__1_946_, v___x_953_);
return v___x_954_;
}
case 1:
{
lean_object* v_i_955_; lean_object* v___x_956_; 
lean_dec(v_h__7_952_);
lean_dec(v_h__6_951_);
lean_dec(v_h__5_950_);
lean_dec(v_h__4_949_);
lean_dec(v_h__3_948_);
lean_dec(v_h__1_946_);
v_i_955_ = lean_ctor_get(v_x_945_, 0);
lean_inc(v_i_955_);
lean_dec_ref_known(v_x_945_, 1);
v___x_956_ = lean_apply_1(v_h__2_947_, v_i_955_);
return v___x_956_;
}
case 2:
{
lean_object* v_a_957_; lean_object* v_b_958_; lean_object* v___x_959_; 
lean_dec(v_h__7_952_);
lean_dec(v_h__6_951_);
lean_dec(v_h__5_950_);
lean_dec(v_h__4_949_);
lean_dec(v_h__2_947_);
lean_dec(v_h__1_946_);
v_a_957_ = lean_ctor_get(v_x_945_, 0);
lean_inc(v_a_957_);
v_b_958_ = lean_ctor_get(v_x_945_, 1);
lean_inc(v_b_958_);
lean_dec_ref_known(v_x_945_, 2);
v___x_959_ = lean_apply_2(v_h__3_948_, v_a_957_, v_b_958_);
return v___x_959_;
}
case 3:
{
lean_object* v_a_960_; lean_object* v_b_961_; lean_object* v___x_962_; 
lean_dec(v_h__7_952_);
lean_dec(v_h__6_951_);
lean_dec(v_h__5_950_);
lean_dec(v_h__3_948_);
lean_dec(v_h__2_947_);
lean_dec(v_h__1_946_);
v_a_960_ = lean_ctor_get(v_x_945_, 0);
lean_inc(v_a_960_);
v_b_961_ = lean_ctor_get(v_x_945_, 1);
lean_inc(v_b_961_);
lean_dec_ref_known(v_x_945_, 2);
v___x_962_ = lean_apply_2(v_h__4_949_, v_a_960_, v_b_961_);
return v___x_962_;
}
case 4:
{
lean_object* v_a_963_; lean_object* v___x_964_; 
lean_dec(v_h__6_951_);
lean_dec(v_h__5_950_);
lean_dec(v_h__4_949_);
lean_dec(v_h__3_948_);
lean_dec(v_h__2_947_);
lean_dec(v_h__1_946_);
v_a_963_ = lean_ctor_get(v_x_945_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v_x_945_, 1);
v___x_964_ = lean_apply_1(v_h__7_952_, v_a_963_);
return v___x_964_;
}
case 5:
{
lean_object* v_k_965_; lean_object* v_a_966_; lean_object* v___x_967_; 
lean_dec(v_h__7_952_);
lean_dec(v_h__6_951_);
lean_dec(v_h__4_949_);
lean_dec(v_h__3_948_);
lean_dec(v_h__2_947_);
lean_dec(v_h__1_946_);
v_k_965_ = lean_ctor_get(v_x_945_, 0);
lean_inc(v_k_965_);
v_a_966_ = lean_ctor_get(v_x_945_, 1);
lean_inc(v_a_966_);
lean_dec_ref_known(v_x_945_, 2);
v___x_967_ = lean_apply_2(v_h__5_950_, v_k_965_, v_a_966_);
return v___x_967_;
}
default: 
{
lean_object* v_k_968_; lean_object* v_a_969_; lean_object* v___x_970_; 
lean_dec(v_h__7_952_);
lean_dec(v_h__5_950_);
lean_dec(v_h__4_949_);
lean_dec(v_h__3_948_);
lean_dec(v_h__2_947_);
lean_dec(v_h__1_946_);
v_k_968_ = lean_ctor_get(v_x_945_, 0);
lean_inc(v_k_968_);
v_a_969_ = lean_ctor_get(v_x_945_, 1);
lean_inc(v_a_969_);
lean_dec_ref_known(v_x_945_, 2);
v___x_970_ = lean_apply_2(v_h__6_951_, v_k_968_, v_a_969_);
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_leadCoeff(lean_object* v_p_971_){
_start:
{
if (lean_obj_tag(v_p_971_) == 1)
{
lean_object* v_k_972_; 
v_k_972_ = lean_ctor_get(v_p_971_, 0);
lean_inc(v_k_972_);
return v_k_972_;
}
else
{
lean_object* v___x_973_; 
v___x_973_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_leadCoeff___boxed(lean_object* v_p_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_974_);
lean_dec(v_p_974_);
return v_res_975_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_le__le__combine__cert(lean_object* v_p_u2081_976_, lean_object* v_p_u2082_977_, lean_object* v_p_u2083_978_){
_start:
{
lean_object* v___x_979_; lean_object* v_a_u2081_980_; lean_object* v___x_981_; lean_object* v_a_u2082_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_979_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_976_);
v_a_u2081_980_ = lean_nat_abs(v___x_979_);
lean_dec(v___x_979_);
v___x_981_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_977_);
v_a_u2082_982_ = lean_nat_abs(v___x_981_);
lean_dec(v___x_981_);
v___x_983_ = lean_nat_to_int(v_a_u2082_982_);
v___x_984_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_976_, v___x_983_);
lean_dec(v___x_983_);
v___x_985_ = lean_nat_to_int(v_a_u2081_980_);
v___x_986_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_977_, v___x_985_);
lean_dec(v___x_985_);
v___x_987_ = l_Lean_Grind_Linarith_Poly_combine(v___x_984_, v___x_986_);
v___x_988_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_978_, v___x_987_);
lean_dec(v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_le__le__combine__cert___boxed(lean_object* v_p_u2081_989_, lean_object* v_p_u2082_990_, lean_object* v_p_u2083_991_){
_start:
{
uint8_t v_res_992_; lean_object* v_r_993_; 
v_res_992_ = l_Lean_Grind_Linarith_le__le__combine__cert(v_p_u2081_989_, v_p_u2082_990_, v_p_u2083_991_);
lean_dec(v_p_u2083_991_);
v_r_993_ = lean_box(v_res_992_);
return v_r_993_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_le__lt__combine__cert(lean_object* v_p_u2081_994_, lean_object* v_p_u2082_995_, lean_object* v_p_u2083_996_){
_start:
{
lean_object* v___x_997_; lean_object* v_a_u2081_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_997_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_994_);
v_a_u2081_998_ = lean_nat_abs(v___x_997_);
lean_dec(v___x_997_);
v___x_999_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1000_ = lean_nat_to_int(v_a_u2081_998_);
v___x_1001_ = lean_int_dec_lt(v___x_999_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_dec(v___x_1000_);
lean_dec(v_p_u2082_995_);
lean_dec(v_p_u2081_994_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; lean_object* v_a_u2082_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1002_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_995_);
v_a_u2082_1003_ = lean_nat_abs(v___x_1002_);
lean_dec(v___x_1002_);
v___x_1004_ = lean_nat_to_int(v_a_u2082_1003_);
v___x_1005_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_994_, v___x_1004_);
lean_dec(v___x_1004_);
v___x_1006_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_995_, v___x_1000_);
lean_dec(v___x_1000_);
v___x_1007_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1005_, v___x_1006_);
v___x_1008_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_996_, v___x_1007_);
lean_dec(v___x_1007_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_le__lt__combine__cert___boxed(lean_object* v_p_u2081_1009_, lean_object* v_p_u2082_1010_, lean_object* v_p_u2083_1011_){
_start:
{
uint8_t v_res_1012_; lean_object* v_r_1013_; 
v_res_1012_ = l_Lean_Grind_Linarith_le__lt__combine__cert(v_p_u2081_1009_, v_p_u2082_1010_, v_p_u2083_1011_);
lean_dec(v_p_u2083_1011_);
v_r_1013_ = lean_box(v_res_1012_);
return v_r_1013_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_lt__lt__combine__cert(lean_object* v_p_u2081_1014_, lean_object* v_p_u2082_1015_, lean_object* v_p_u2083_1016_){
_start:
{
lean_object* v___x_1017_; lean_object* v_a_u2082_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1017_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_1015_);
v_a_u2082_1018_ = lean_nat_abs(v___x_1017_);
lean_dec(v___x_1017_);
v___x_1019_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1020_ = lean_nat_to_int(v_a_u2082_1018_);
v___x_1021_ = lean_int_dec_lt(v___x_1019_, v___x_1020_);
if (v___x_1021_ == 0)
{
lean_dec(v___x_1020_);
lean_dec(v_p_u2082_1015_);
lean_dec(v_p_u2081_1014_);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; lean_object* v_a_u2081_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1022_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_1014_);
v_a_u2081_1023_ = lean_nat_abs(v___x_1022_);
lean_dec(v___x_1022_);
v___x_1024_ = lean_nat_to_int(v_a_u2081_1023_);
v___x_1025_ = lean_int_dec_lt(v___x_1019_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_dec(v___x_1024_);
lean_dec(v___x_1020_);
lean_dec(v_p_u2082_1015_);
lean_dec(v_p_u2081_1014_);
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1026_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1014_, v___x_1020_);
lean_dec(v___x_1020_);
v___x_1027_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1015_, v___x_1024_);
lean_dec(v___x_1024_);
v___x_1028_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1026_, v___x_1027_);
v___x_1029_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1016_, v___x_1028_);
lean_dec(v___x_1028_);
return v___x_1029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_lt__lt__combine__cert___boxed(lean_object* v_p_u2081_1030_, lean_object* v_p_u2082_1031_, lean_object* v_p_u2083_1032_){
_start:
{
uint8_t v_res_1033_; lean_object* v_r_1034_; 
v_res_1033_ = l_Lean_Grind_Linarith_lt__lt__combine__cert(v_p_u2081_1030_, v_p_u2082_1031_, v_p_u2083_1032_);
lean_dec(v_p_u2083_1032_);
v_r_1034_ = lean_box(v_res_1033_);
return v_r_1034_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1036_ = lean_int_neg(v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_diseq__split__cert(lean_object* v_p_u2081_1037_, lean_object* v_p_u2082_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1039_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1040_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1037_, v___x_1039_);
v___x_1041_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_1038_, v___x_1040_);
lean_dec(v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_diseq__split__cert___boxed(lean_object* v_p_u2081_1042_, lean_object* v_p_u2082_1043_){
_start:
{
uint8_t v_res_1044_; lean_object* v_r_1045_; 
v_res_1044_ = l_Lean_Grind_Linarith_diseq__split__cert(v_p_u2081_1042_, v_p_u2082_1043_);
lean_dec(v_p_u2082_1043_);
v_r_1045_ = lean_box(v_res_1044_);
return v_r_1045_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_norm__cert(lean_object* v_lhs_1046_, lean_object* v_rhs_1047_, lean_object* v_p_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1049_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_lhs_1046_);
lean_ctor_set(v___x_1049_, 1, v_rhs_1047_);
v___x_1050_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1049_);
v___x_1051_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1048_, v___x_1050_);
lean_dec(v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_norm__cert___boxed(lean_object* v_lhs_1052_, lean_object* v_rhs_1053_, lean_object* v_p_1054_){
_start:
{
uint8_t v_res_1055_; lean_object* v_r_1056_; 
v_res_1055_ = l_Lean_Grind_Linarith_norm__cert(v_lhs_1052_, v_rhs_1053_, v_p_1054_);
lean_dec(v_p_1054_);
v_r_1056_ = lean_box(v_res_1055_);
return v_r_1056_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__of__le__ge__cert(lean_object* v_p_u2081_1057_, lean_object* v_p_u2082_1058_){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1059_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1060_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1057_, v___x_1059_);
v___x_1061_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_1058_, v___x_1060_);
lean_dec(v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__of__le__ge__cert___boxed(lean_object* v_p_u2081_1062_, lean_object* v_p_u2082_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l_Lean_Grind_Linarith_eq__of__le__ge__cert(v_p_u2081_1062_, v_p_u2082_1063_);
lean_dec(v_p_u2082_1063_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1069_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1067_);
lean_ctor_set(v___x_1069_, 2, v___x_1066_);
return v___x_1069_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_zero__lt__one__cert(lean_object* v_p_1070_){
_start:
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = lean_obj_once(&l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0, &l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0_once, _init_l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0);
v___x_1072_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1070_, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__lt__one__cert___boxed(lean_object* v_p_1073_){
_start:
{
uint8_t v_res_1074_; lean_object* v_r_1075_; 
v_res_1074_ = l_Lean_Grind_Linarith_zero__lt__one__cert(v_p_1073_);
lean_dec(v_p_1073_);
v_r_1075_ = lean_box(v_res_1074_);
return v_r_1075_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1079_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___x_1077_);
lean_ctor_set(v___x_1079_, 2, v___x_1076_);
return v___x_1079_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_zero__ne__one__cert(lean_object* v_p_1080_){
_start:
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = lean_obj_once(&l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0, &l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once, _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0);
v___x_1082_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1080_, v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__ne__one__cert___boxed(lean_object* v_p_1083_){
_start:
{
uint8_t v_res_1084_; lean_object* v_r_1085_; 
v_res_1084_ = l_Lean_Grind_Linarith_zero__ne__one__cert(v_p_1083_);
lean_dec(v_p_1083_);
v_r_1085_ = lean_box(v_res_1084_);
return v_r_1085_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(lean_object* v_c_1086_, lean_object* v_p_1087_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1088_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1089_ = lean_nat_to_int(v_c_1086_);
v___x_1090_ = lean_int_dec_lt(v___x_1088_, v___x_1089_);
lean_dec(v___x_1089_);
if (v___x_1090_ == 0)
{
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = lean_obj_once(&l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0, &l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once, _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0);
v___x_1092_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1087_, v___x_1091_);
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert___boxed(lean_object* v_c_1093_, lean_object* v_p_1094_){
_start:
{
uint8_t v_res_1095_; lean_object* v_r_1096_; 
v_res_1095_ = l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(v_c_1093_, v_p_1094_);
lean_dec(v_p_1094_);
v_r_1096_ = lean_box(v_res_1095_);
return v_r_1096_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__neg__cert(lean_object* v_p_u2081_1097_, lean_object* v_p_u2082_1098_){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1099_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1100_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1097_, v___x_1099_);
v___x_1101_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_1098_, v___x_1100_);
lean_dec(v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__neg__cert___boxed(lean_object* v_p_u2081_1102_, lean_object* v_p_u2082_1103_){
_start:
{
uint8_t v_res_1104_; lean_object* v_r_1105_; 
v_res_1104_ = l_Lean_Grind_Linarith_eq__neg__cert(v_p_u2081_1102_, v_p_u2082_1103_);
lean_dec(v_p_u2082_1103_);
v_r_1105_ = lean_box(v_res_1104_);
return v_r_1105_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__coeff__cert(lean_object* v_p_u2081_1106_, lean_object* v_p_u2082_1107_, lean_object* v_k_1108_){
_start:
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = lean_nat_dec_eq(v_k_1108_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1111_ = lean_nat_to_int(v_k_1108_);
v___x_1112_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1107_, v___x_1111_);
lean_dec(v___x_1111_);
v___x_1113_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2081_1106_, v___x_1112_);
lean_dec(v___x_1112_);
return v___x_1113_;
}
else
{
uint8_t v___x_1114_; 
lean_dec(v_k_1108_);
lean_dec(v_p_u2082_1107_);
v___x_1114_ = 0;
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__coeff__cert___boxed(lean_object* v_p_u2081_1115_, lean_object* v_p_u2082_1116_, lean_object* v_k_1117_){
_start:
{
uint8_t v_res_1118_; lean_object* v_r_1119_; 
v_res_1118_ = l_Lean_Grind_Linarith_eq__coeff__cert(v_p_u2081_1115_, v_p_u2082_1116_, v_k_1117_);
lean_dec(v_p_u2081_1115_);
v_r_1119_ = lean_box(v_res_1118_);
return v_r_1119_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_coeff__cert(lean_object* v_p_u2081_1120_, lean_object* v_p_u2082_1121_, lean_object* v_k_1122_){
_start:
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_nat_dec_lt(v___x_1123_, v_k_1122_);
if (v___x_1124_ == 0)
{
lean_dec(v_k_1122_);
lean_dec(v_p_u2082_1121_);
return v___x_1124_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1125_ = lean_nat_to_int(v_k_1122_);
v___x_1126_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1121_, v___x_1125_);
lean_dec(v___x_1125_);
v___x_1127_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2081_1120_, v___x_1126_);
lean_dec(v___x_1126_);
return v___x_1127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_coeff__cert___boxed(lean_object* v_p_u2081_1128_, lean_object* v_p_u2082_1129_, lean_object* v_k_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_Lean_Grind_Linarith_coeff__cert(v_p_u2081_1128_, v_p_u2082_1129_, v_k_1130_);
lean_dec(v_p_u2081_1128_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__diseq__subst__cert(lean_object* v_k_u2081_1133_, lean_object* v_k_u2082_1134_, lean_object* v_p_u2081_1135_, lean_object* v_p_u2082_1136_, lean_object* v_p_u2083_1137_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1138_ = lean_nat_abs(v_k_u2081_1133_);
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = lean_nat_dec_eq(v___x_1138_, v___x_1139_);
lean_dec(v___x_1138_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1141_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1135_, v_k_u2082_1134_);
v___x_1142_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1136_, v_k_u2081_1133_);
v___x_1143_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1141_, v___x_1142_);
v___x_1144_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1137_, v___x_1143_);
lean_dec(v___x_1143_);
return v___x_1144_;
}
else
{
uint8_t v___x_1145_; 
lean_dec(v_p_u2082_1136_);
lean_dec(v_p_u2081_1135_);
v___x_1145_ = 0;
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__diseq__subst__cert___boxed(lean_object* v_k_u2081_1146_, lean_object* v_k_u2082_1147_, lean_object* v_p_u2081_1148_, lean_object* v_p_u2082_1149_, lean_object* v_p_u2083_1150_){
_start:
{
uint8_t v_res_1151_; lean_object* v_r_1152_; 
v_res_1151_ = l_Lean_Grind_Linarith_eq__diseq__subst__cert(v_k_u2081_1146_, v_k_u2082_1147_, v_p_u2081_1148_, v_p_u2082_1149_, v_p_u2083_1150_);
lean_dec(v_p_u2083_1150_);
lean_dec(v_k_u2082_1147_);
lean_dec(v_k_u2081_1146_);
v_r_1152_ = lean_box(v_res_1151_);
return v_r_1152_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__diseq__subst1__cert(lean_object* v_k_1153_, lean_object* v_p_u2081_1154_, lean_object* v_p_u2082_1155_, lean_object* v_p_u2083_1156_){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1157_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1154_, v_k_1153_);
v___x_1158_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1157_, v_p_u2082_1155_);
v___x_1159_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1156_, v___x_1158_);
lean_dec(v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__diseq__subst1__cert___boxed(lean_object* v_k_1160_, lean_object* v_p_u2081_1161_, lean_object* v_p_u2082_1162_, lean_object* v_p_u2083_1163_){
_start:
{
uint8_t v_res_1164_; lean_object* v_r_1165_; 
v_res_1164_ = l_Lean_Grind_Linarith_eq__diseq__subst1__cert(v_k_1160_, v_p_u2081_1161_, v_p_u2082_1162_, v_p_u2083_1163_);
lean_dec(v_p_u2083_1163_);
lean_dec(v_k_1160_);
v_r_1165_ = lean_box(v_res_1164_);
return v_r_1165_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__le__subst__cert(lean_object* v_x_1166_, lean_object* v_p_u2081_1167_, lean_object* v_p_u2082_1168_, lean_object* v_p_u2083_1169_){
_start:
{
lean_object* v_a_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_a_1170_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_1167_, v_x_1166_);
v___x_1171_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1172_ = lean_int_dec_le(v___x_1171_, v_a_1170_);
if (v___x_1172_ == 0)
{
lean_dec(v_a_1170_);
lean_dec(v_p_u2082_1168_);
lean_dec(v_p_u2081_1167_);
return v___x_1172_;
}
else
{
lean_object* v_b_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_b_1173_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_1168_, v_x_1166_);
v___x_1174_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1168_, v_a_1170_);
lean_dec(v_a_1170_);
v___x_1175_ = lean_int_neg(v_b_1173_);
lean_dec(v_b_1173_);
v___x_1176_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1167_, v___x_1175_);
lean_dec(v___x_1175_);
v___x_1177_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1174_, v___x_1176_);
v___x_1178_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1169_, v___x_1177_);
lean_dec(v___x_1177_);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__le__subst__cert___boxed(lean_object* v_x_1179_, lean_object* v_p_u2081_1180_, lean_object* v_p_u2082_1181_, lean_object* v_p_u2083_1182_){
_start:
{
uint8_t v_res_1183_; lean_object* v_r_1184_; 
v_res_1183_ = l_Lean_Grind_Linarith_eq__le__subst__cert(v_x_1179_, v_p_u2081_1180_, v_p_u2082_1181_, v_p_u2083_1182_);
lean_dec(v_p_u2083_1182_);
lean_dec(v_x_1179_);
v_r_1184_ = lean_box(v_res_1183_);
return v_r_1184_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__lt__subst__cert(lean_object* v_x_1185_, lean_object* v_p_u2081_1186_, lean_object* v_p_u2082_1187_, lean_object* v_p_u2083_1188_){
_start:
{
lean_object* v_a_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v_a_1189_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_1186_, v_x_1185_);
v___x_1190_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1191_ = lean_int_dec_lt(v___x_1190_, v_a_1189_);
if (v___x_1191_ == 0)
{
lean_dec(v_a_1189_);
lean_dec(v_p_u2082_1187_);
lean_dec(v_p_u2081_1186_);
return v___x_1191_;
}
else
{
lean_object* v_b_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v_b_1192_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_1187_, v_x_1185_);
v___x_1193_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1187_, v_a_1189_);
lean_dec(v_a_1189_);
v___x_1194_ = lean_int_neg(v_b_1192_);
lean_dec(v_b_1192_);
v___x_1195_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1186_, v___x_1194_);
lean_dec(v___x_1194_);
v___x_1196_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1193_, v___x_1195_);
v___x_1197_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1188_, v___x_1196_);
lean_dec(v___x_1196_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__lt__subst__cert___boxed(lean_object* v_x_1198_, lean_object* v_p_u2081_1199_, lean_object* v_p_u2082_1200_, lean_object* v_p_u2083_1201_){
_start:
{
uint8_t v_res_1202_; lean_object* v_r_1203_; 
v_res_1202_ = l_Lean_Grind_Linarith_eq__lt__subst__cert(v_x_1198_, v_p_u2081_1199_, v_p_u2082_1200_, v_p_u2083_1201_);
lean_dec(v_p_u2083_1201_);
lean_dec(v_x_1198_);
v_r_1203_ = lean_box(v_res_1202_);
return v_r_1203_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__eq__subst__cert(lean_object* v_x_1204_, lean_object* v_p_u2081_1205_, lean_object* v_p_u2082_1206_, lean_object* v_p_u2083_1207_){
_start:
{
lean_object* v_a_1208_; lean_object* v_b_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v_a_1208_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_1205_, v_x_1204_);
v_b_1209_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_1206_, v_x_1204_);
v___x_1210_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1206_, v_a_1208_);
lean_dec(v_a_1208_);
v___x_1211_ = lean_int_neg(v_b_1209_);
lean_dec(v_b_1209_);
v___x_1212_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1205_, v___x_1211_);
lean_dec(v___x_1211_);
v___x_1213_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1210_, v___x_1212_);
v___x_1214_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1207_, v___x_1213_);
lean_dec(v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__eq__subst__cert___boxed(lean_object* v_x_1215_, lean_object* v_p_u2081_1216_, lean_object* v_p_u2082_1217_, lean_object* v_p_u2083_1218_){
_start:
{
uint8_t v_res_1219_; lean_object* v_r_1220_; 
v_res_1219_ = l_Lean_Grind_Linarith_eq__eq__subst__cert(v_x_1215_, v_p_u2081_1216_, v_p_u2082_1217_, v_p_u2083_1218_);
lean_dec(v_p_u2083_1218_);
lean_dec(v_x_1215_);
v_r_1220_ = lean_box(v_res_1219_);
return v_r_1220_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_imp__eq__cert(lean_object* v_p_1221_, lean_object* v_x_1222_, lean_object* v_y_1223_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1224_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1225_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v_y_1223_);
lean_ctor_set(v___x_1227_, 2, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1224_);
lean_ctor_set(v___x_1228_, 1, v_x_1222_);
lean_ctor_set(v___x_1228_, 2, v___x_1227_);
v___x_1229_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1221_, v___x_1228_);
lean_dec_ref_known(v___x_1228_, 3);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_imp__eq__cert___boxed(lean_object* v_p_1230_, lean_object* v_x_1231_, lean_object* v_y_1232_){
_start:
{
uint8_t v_res_1233_; lean_object* v_r_1234_; 
v_res_1233_ = l_Lean_Grind_Linarith_imp__eq__cert(v_p_1230_, v_x_1231_, v_y_1232_);
lean_dec(v_p_1230_);
v_r_1234_ = lean_box(v_res_1233_);
return v_r_1234_;
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
