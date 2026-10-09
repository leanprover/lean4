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
uint8_t l_Lean_Grind_Linarith_instBEqExpr_beq(lean_object* v_x_84_, lean_object* v_x_85_){
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
LEAN_EXPORT void l_Lean_Grind_Linarith_instBEqExpr_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_84_ = stack[0].m_obj;
lean_object* v_x_85_ = stack[1].m_obj;
uint8_t v_res_127_;
v_res_127_ = l_Lean_Grind_Linarith_instBEqExpr_beq(v_x_84_, v_x_85_);
stack->m_num = v_res_127_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instBEqExpr_beq___boxed(lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_Grind_Linarith_instBEqExpr_beq(v_x_128_, v_x_129_);
lean_dec(v_x_129_);
lean_dec(v_x_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(2u);
v___x_138_ = lean_nat_to_int(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = lean_nat_to_int(v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = lean_nat_to_int(v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprExpr_repr(lean_object* v_x_179_, lean_object* v_prec_180_){
_start:
{
lean_object* v___y_182_; 
switch(lean_obj_tag(v_x_179_))
{
case 0:
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(1024u);
v___x_189_ = lean_nat_dec_le(v___x_188_, v_prec_180_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_182_ = v___x_190_;
goto v___jp_181_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_182_ = v___x_191_;
goto v___jp_181_;
}
}
case 1:
{
lean_object* v_i_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_212_; 
v_i_192_ = lean_ctor_get(v_x_179_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_212_ == 0)
{
v___x_194_ = v_x_179_;
v_isShared_195_ = v_isSharedCheck_212_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_i_192_);
lean_dec(v_x_179_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_212_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___y_197_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(1024u);
v___x_209_ = lean_nat_dec_le(v___x_208_, v_prec_180_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
v___x_210_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_197_ = v___x_210_;
goto v___jp_196_;
}
else
{
lean_object* v___x_211_; 
v___x_211_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_197_ = v___x_211_;
goto v___jp_196_;
}
v___jp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_198_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__6));
v___x_199_ = l_Nat_reprFast(v_i_192_);
if (v_isShared_195_ == 0)
{
lean_ctor_set_tag(v___x_194_, 3);
lean_ctor_set(v___x_194_, 0, v___x_199_);
v___x_201_ = v___x_194_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_207_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_198_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
lean_inc(v___y_197_);
v___x_203_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_203_, 0, v___y_197_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = 0;
v___x_205_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*1, v___x_204_);
v___x_206_ = l_Repr_addAppParen(v___x_205_, v_prec_180_);
return v___x_206_;
}
}
}
}
case 2:
{
lean_object* v_a_213_; lean_object* v_b_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_237_; 
v_a_213_ = lean_ctor_get(v_x_179_, 0);
v_b_214_ = lean_ctor_get(v_x_179_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_237_ == 0)
{
v___x_216_ = v_x_179_;
v_isShared_217_ = v_isSharedCheck_237_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_b_214_);
lean_inc(v_a_213_);
lean_dec(v_x_179_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_237_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___y_220_; uint8_t v___x_234_; 
v___x_218_ = lean_unsigned_to_nat(1024u);
v___x_234_ = lean_nat_dec_le(v___x_218_, v_prec_180_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
v___x_235_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_220_ = v___x_235_;
goto v___jp_219_;
}
else
{
lean_object* v___x_236_; 
v___x_236_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_220_ = v___x_236_;
goto v___jp_219_;
}
v___jp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_221_ = lean_box(1);
v___x_222_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__9));
v___x_223_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_213_, v___x_218_);
if (v_isShared_217_ == 0)
{
lean_ctor_set_tag(v___x_216_, 5);
lean_ctor_set(v___x_216_, 1, v___x_223_);
lean_ctor_set(v___x_216_, 0, v___x_222_);
v___x_225_ = v___x_216_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v___x_223_);
v___x_225_ = v_reuseFailAlloc_233_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_221_);
v___x_227_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_b_214_, v___x_218_);
v___x_228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
lean_inc(v___y_220_);
v___x_229_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_229_, 0, v___y_220_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = 0;
v___x_231_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*1, v___x_230_);
v___x_232_ = l_Repr_addAppParen(v___x_231_, v_prec_180_);
return v___x_232_;
}
}
}
}
case 3:
{
lean_object* v_a_238_; lean_object* v_b_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_262_; 
v_a_238_ = lean_ctor_get(v_x_179_, 0);
v_b_239_ = lean_ctor_get(v_x_179_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_262_ == 0)
{
v___x_241_ = v_x_179_;
v_isShared_242_ = v_isSharedCheck_262_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_b_239_);
lean_inc(v_a_238_);
lean_dec(v_x_179_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_262_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___y_245_; uint8_t v___x_259_; 
v___x_243_ = lean_unsigned_to_nat(1024u);
v___x_259_ = lean_nat_dec_le(v___x_243_, v_prec_180_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
v___x_260_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_245_ = v___x_260_;
goto v___jp_244_;
}
else
{
lean_object* v___x_261_; 
v___x_261_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_245_ = v___x_261_;
goto v___jp_244_;
}
v___jp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_246_ = lean_box(1);
v___x_247_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__12));
v___x_248_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_238_, v___x_243_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 5);
lean_ctor_set(v___x_241_, 1, v___x_248_);
lean_ctor_set(v___x_241_, 0, v___x_247_);
v___x_250_ = v___x_241_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v___x_248_);
v___x_250_ = v_reuseFailAlloc_258_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_246_);
v___x_252_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_b_239_, v___x_243_);
v___x_253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
lean_inc(v___y_245_);
v___x_254_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_254_, 0, v___y_245_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = 0;
v___x_256_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set_uint8(v___x_256_, sizeof(void*)*1, v___x_255_);
v___x_257_ = l_Repr_addAppParen(v___x_256_, v_prec_180_);
return v___x_257_;
}
}
}
}
case 4:
{
lean_object* v_a_263_; lean_object* v___x_264_; lean_object* v___y_266_; uint8_t v___x_274_; 
v_a_263_ = lean_ctor_get(v_x_179_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v_x_179_, 1);
v___x_264_ = lean_unsigned_to_nat(1024u);
v___x_274_ = lean_nat_dec_le(v___x_264_, v_prec_180_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
v___x_275_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_266_ = v___x_275_;
goto v___jp_265_;
}
else
{
lean_object* v___x_276_; 
v___x_276_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_266_ = v___x_276_;
goto v___jp_265_;
}
v___jp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_267_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__15));
v___x_268_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_263_, v___x_264_);
v___x_269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
lean_inc(v___y_266_);
v___x_270_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_270_, 0, v___y_266_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = 0;
v___x_272_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*1, v___x_271_);
v___x_273_ = l_Repr_addAppParen(v___x_272_, v_prec_180_);
return v___x_273_;
}
}
case 5:
{
lean_object* v_k_277_; lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_302_; 
v_k_277_ = lean_ctor_get(v_x_179_, 0);
v_a_278_ = lean_ctor_get(v_x_179_, 1);
v_isSharedCheck_302_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_302_ == 0)
{
v___x_280_ = v_x_179_;
v_isShared_281_ = v_isSharedCheck_302_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_inc(v_k_277_);
lean_dec(v_x_179_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_302_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___y_284_; uint8_t v___x_299_; 
v___x_282_ = lean_unsigned_to_nat(1024u);
v___x_299_ = lean_nat_dec_le(v___x_282_, v_prec_180_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
v___x_300_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_284_ = v___x_300_;
goto v___jp_283_;
}
else
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_284_ = v___x_301_;
goto v___jp_283_;
}
v___jp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_285_ = lean_box(1);
v___x_286_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__18));
v___x_287_ = l_Nat_reprFast(v_k_277_);
v___x_288_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v___x_288_);
lean_ctor_set(v___x_280_, 0, v___x_286_);
v___x_290_ = v___x_280_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___x_288_);
v___x_290_ = v_reuseFailAlloc_298_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_285_);
v___x_292_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_278_, v___x_282_);
v___x_293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
lean_inc(v___y_284_);
v___x_294_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_294_, 0, v___y_284_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = 0;
v___x_296_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*1, v___x_295_);
v___x_297_ = l_Repr_addAppParen(v___x_296_, v_prec_180_);
return v___x_297_;
}
}
}
}
default: 
{
lean_object* v_k_303_; lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_338_; 
v_k_303_ = lean_ctor_get(v_x_179_, 0);
v_a_304_ = lean_ctor_get(v_x_179_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_338_ == 0)
{
v___x_306_ = v_x_179_;
v_isShared_307_ = v_isSharedCheck_338_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_inc(v_k_303_);
lean_dec(v_x_179_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_338_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_325_; uint8_t v___x_335_; 
v___x_308_ = lean_unsigned_to_nat(1024u);
v___x_335_ = lean_nat_dec_le(v___x_308_, v_prec_180_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
v___x_336_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_325_ = v___x_336_;
goto v___jp_324_;
}
else
{
lean_object* v___x_337_; 
v___x_337_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_325_ = v___x_337_;
goto v___jp_324_;
}
v___jp_309_:
{
lean_object* v___x_315_; 
lean_inc(v___y_310_);
if (v_isShared_307_ == 0)
{
lean_ctor_set_tag(v___x_306_, 5);
lean_ctor_set(v___x_306_, 1, v___y_313_);
lean_ctor_set(v___x_306_, 0, v___y_310_);
v___x_315_ = v___x_306_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___y_310_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___y_313_);
v___x_315_ = v_reuseFailAlloc_323_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_inc(v___y_312_);
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___y_312_);
v___x_317_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_a_304_, v___x_308_);
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
lean_inc(v___y_311_);
v___x_319_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_319_, 0, v___y_311_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = 0;
v___x_321_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*1, v___x_320_);
v___x_322_ = l_Repr_addAppParen(v___x_321_, v_prec_180_);
return v___x_322_;
}
}
v___jp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_326_ = lean_box(1);
v___x_327_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__21));
v___x_328_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_329_ = lean_int_dec_lt(v_k_303_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = l_Int_repr(v_k_303_);
lean_dec(v_k_303_);
v___x_331_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
v___y_310_ = v___x_327_;
v___y_311_ = v___y_325_;
v___y_312_ = v___x_326_;
v___y_313_ = v___x_331_;
goto v___jp_309_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = l_Int_repr(v_k_303_);
lean_dec(v_k_303_);
v___x_333_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
v___x_334_ = l_Repr_addAppParen(v___x_333_, v___x_308_);
v___y_310_ = v___x_327_;
v___y_311_ = v___y_325_;
v___y_312_ = v___x_326_;
v___y_313_ = v___x_334_;
goto v___jp_309_;
}
}
}
}
}
v___jp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_183_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprExpr_repr___closed__1));
lean_inc(v___y_182_);
v___x_184_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_184_, 0, v___y_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = 0;
v___x_186_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*1, v___x_185_);
v___x_187_ = l_Repr_addAppParen(v___x_186_, v_prec_180_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprExpr_repr___boxed(lean_object* v_x_339_, lean_object* v_prec_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Grind_Linarith_instReprExpr_repr(v_x_339_, v_prec_340_);
lean_dec(v_prec_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote___redArg(lean_object* v_ctx_344_, lean_object* v_v_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_RArray_getImpl___redArg(v_ctx_344_, v_v_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote___redArg___boxed(lean_object* v_ctx_347_, lean_object* v_v_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Grind_Linarith_Var_denote___redArg(v_ctx_347_, v_v_348_);
lean_dec(v_v_348_);
lean_dec_ref(v_ctx_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote(lean_object* v_00_u03b1_350_, lean_object* v_ctx_351_, lean_object* v_v_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_RArray_getImpl___redArg(v_ctx_351_, v_v_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Var_denote___boxed(lean_object* v_00_u03b1_354_, lean_object* v_ctx_355_, lean_object* v_v_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Grind_Linarith_Var_denote(v_00_u03b1_354_, v_ctx_355_, v_v_356_);
lean_dec(v_v_356_);
lean_dec_ref(v_ctx_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___redArg(lean_object* v_inst_358_, lean_object* v_ctx_359_, lean_object* v_x_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_358_);
switch(lean_obj_tag(v_x_360_))
{
case 0:
{
lean_object* v_toAddCommMonoid_362_; lean_object* v_toZero_363_; 
v_toAddCommMonoid_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_toAddCommMonoid_362_);
lean_dec_ref(v___x_361_);
lean_dec_ref(v_inst_358_);
v_toZero_363_ = lean_ctor_get(v_toAddCommMonoid_362_, 0);
lean_inc(v_toZero_363_);
lean_dec_ref(v_toAddCommMonoid_362_);
return v_toZero_363_;
}
case 1:
{
lean_object* v_i_364_; lean_object* v___x_365_; 
lean_dec_ref(v___x_361_);
lean_dec_ref(v_inst_358_);
v_i_364_ = lean_ctor_get(v_x_360_, 0);
lean_inc(v_i_364_);
lean_dec_ref_known(v_x_360_, 1);
v___x_365_ = l_Lean_RArray_getImpl___redArg(v_ctx_359_, v_i_364_);
lean_dec(v_i_364_);
return v___x_365_;
}
case 2:
{
lean_object* v_toAddCommMonoid_366_; lean_object* v_toAdd_367_; lean_object* v_a_368_; lean_object* v_b_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_toAddCommMonoid_366_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_toAddCommMonoid_366_);
lean_dec_ref(v___x_361_);
v_toAdd_367_ = lean_ctor_get(v_toAddCommMonoid_366_, 1);
lean_inc(v_toAdd_367_);
lean_dec_ref(v_toAddCommMonoid_366_);
v_a_368_ = lean_ctor_get(v_x_360_, 0);
lean_inc(v_a_368_);
v_b_369_ = lean_ctor_get(v_x_360_, 1);
lean_inc(v_b_369_);
lean_dec_ref_known(v_x_360_, 2);
lean_inc_ref(v_inst_358_);
v___x_370_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_358_, v_ctx_359_, v_a_368_);
v___x_371_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_358_, v_ctx_359_, v_b_369_);
v___x_372_ = lean_apply_2(v_toAdd_367_, v___x_370_, v___x_371_);
return v___x_372_;
}
case 3:
{
lean_object* v_toAddCommGroup_373_; lean_object* v_toSub_374_; lean_object* v_a_375_; lean_object* v_b_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_toAddCommGroup_373_ = lean_ctor_get(v_inst_358_, 0);
lean_dec_ref(v___x_361_);
v_toSub_374_ = lean_ctor_get(v_toAddCommGroup_373_, 2);
lean_inc(v_toSub_374_);
v_a_375_ = lean_ctor_get(v_x_360_, 0);
lean_inc(v_a_375_);
v_b_376_ = lean_ctor_get(v_x_360_, 1);
lean_inc(v_b_376_);
lean_dec_ref_known(v_x_360_, 2);
lean_inc_ref(v_inst_358_);
v___x_377_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_358_, v_ctx_359_, v_a_375_);
v___x_378_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_358_, v_ctx_359_, v_b_376_);
v___x_379_ = lean_apply_2(v_toSub_374_, v___x_377_, v___x_378_);
return v___x_379_;
}
case 4:
{
lean_object* v_toAddCommGroup_380_; lean_object* v_toNeg_381_; lean_object* v_a_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_toAddCommGroup_380_ = lean_ctor_get(v_inst_358_, 0);
lean_dec_ref(v___x_361_);
v_toNeg_381_ = lean_ctor_get(v_toAddCommGroup_380_, 1);
lean_inc(v_toNeg_381_);
v_a_382_ = lean_ctor_get(v_x_360_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v_x_360_, 1);
v___x_383_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_358_, v_ctx_359_, v_a_382_);
v___x_384_ = lean_apply_1(v_toNeg_381_, v___x_383_);
return v___x_384_;
}
case 5:
{
lean_object* v_nsmul_385_; lean_object* v_k_386_; lean_object* v_a_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_nsmul_385_ = lean_ctor_get(v___x_361_, 1);
lean_inc(v_nsmul_385_);
lean_dec_ref(v___x_361_);
v_k_386_ = lean_ctor_get(v_x_360_, 0);
lean_inc(v_k_386_);
v_a_387_ = lean_ctor_get(v_x_360_, 1);
lean_inc(v_a_387_);
lean_dec_ref_known(v_x_360_, 2);
v___x_388_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_358_, v_ctx_359_, v_a_387_);
v___x_389_ = lean_apply_2(v_nsmul_385_, v_k_386_, v___x_388_);
return v___x_389_;
}
default: 
{
lean_object* v_zsmul_390_; lean_object* v_k_391_; lean_object* v_a_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec_ref(v___x_361_);
v_zsmul_390_ = lean_ctor_get(v_inst_358_, 2);
lean_inc(v_zsmul_390_);
v_k_391_ = lean_ctor_get(v_x_360_, 0);
lean_inc(v_k_391_);
v_a_392_ = lean_ctor_get(v_x_360_, 1);
lean_inc(v_a_392_);
lean_dec_ref_known(v_x_360_, 2);
v___x_393_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_358_, v_ctx_359_, v_a_392_);
v___x_394_ = lean_apply_2(v_zsmul_390_, v_k_391_, v___x_393_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___redArg___boxed(lean_object* v_inst_395_, lean_object* v_ctx_396_, lean_object* v_x_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_395_, v_ctx_396_, v_x_397_);
lean_dec_ref(v_ctx_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote(lean_object* v_00_u03b1_399_, lean_object* v_inst_400_, lean_object* v_ctx_401_, lean_object* v_x_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Grind_Linarith_Expr_denote___redArg(v_inst_400_, v_ctx_401_, v_x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denote___boxed(lean_object* v_00_u03b1_404_, lean_object* v_inst_405_, lean_object* v_ctx_406_, lean_object* v_x_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Grind_Linarith_Expr_denote(v_00_u03b1_404_, v_inst_405_, v_ctx_406_, v_x_407_);
lean_dec_ref(v_ctx_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorIdx___impl(lean_object* v_x_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_obj_tag_nat(v_x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorIdx___impl___boxed(lean_object* v_x_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Grind_Linarith_Poly_ctorIdx___impl(v_x_411_);
lean_dec(v_x_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim___redArg(lean_object* v_t_413_, lean_object* v_k_414_){
_start:
{
if (lean_obj_tag(v_t_413_) == 0)
{
return v_k_414_;
}
else
{
lean_object* v_k_415_; lean_object* v_v_416_; lean_object* v_p_417_; lean_object* v___x_418_; 
v_k_415_ = lean_ctor_get(v_t_413_, 0);
lean_inc(v_k_415_);
v_v_416_ = lean_ctor_get(v_t_413_, 1);
lean_inc(v_v_416_);
v_p_417_ = lean_ctor_get(v_t_413_, 2);
lean_inc(v_p_417_);
lean_dec_ref_known(v_t_413_, 3);
v___x_418_ = lean_apply_3(v_k_414_, v_k_415_, v_v_416_, v_p_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim(lean_object* v_motive_419_, lean_object* v_ctorIdx_420_, lean_object* v_t_421_, lean_object* v_h_422_, lean_object* v_k_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_421_, v_k_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_ctorElim___boxed(lean_object* v_motive_425_, lean_object* v_ctorIdx_426_, lean_object* v_t_427_, lean_object* v_h_428_, lean_object* v_k_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Grind_Linarith_Poly_ctorElim(v_motive_425_, v_ctorIdx_426_, v_t_427_, v_h_428_, v_k_429_);
lean_dec(v_ctorIdx_426_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_nil_elim___redArg(lean_object* v_t_431_, lean_object* v_nil_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_431_, v_nil_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_nil_elim(lean_object* v_motive_434_, lean_object* v_t_435_, lean_object* v_h_436_, lean_object* v_nil_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_435_, v_nil_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_add_elim___redArg(lean_object* v_t_439_, lean_object* v_add_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_439_, v_add_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_add_elim(lean_object* v_motive_442_, lean_object* v_t_443_, lean_object* v_h_444_, lean_object* v_add_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Grind_Linarith_Poly_ctorElim___redArg(v_t_443_, v_add_445_);
return v___x_446_;
}
}
uint8_t l_Lean_Grind_Linarith_instBEqPoly_beq(lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
if (lean_obj_tag(v_x_448_) == 0)
{
uint8_t v___x_449_; 
v___x_449_ = 1;
return v___x_449_;
}
else
{
uint8_t v___x_450_; 
v___x_450_ = 0;
return v___x_450_;
}
}
else
{
if (lean_obj_tag(v_x_448_) == 1)
{
lean_object* v_k_451_; lean_object* v_v_452_; lean_object* v_p_453_; lean_object* v_k_454_; lean_object* v_v_455_; lean_object* v_p_456_; uint8_t v___x_457_; 
v_k_451_ = lean_ctor_get(v_x_447_, 0);
v_v_452_ = lean_ctor_get(v_x_447_, 1);
v_p_453_ = lean_ctor_get(v_x_447_, 2);
v_k_454_ = lean_ctor_get(v_x_448_, 0);
v_v_455_ = lean_ctor_get(v_x_448_, 1);
v_p_456_ = lean_ctor_get(v_x_448_, 2);
v___x_457_ = lean_int_dec_eq(v_k_451_, v_k_454_);
if (v___x_457_ == 0)
{
return v___x_457_;
}
else
{
uint8_t v___x_458_; 
v___x_458_ = lean_nat_dec_eq(v_v_452_, v_v_455_);
if (v___x_458_ == 0)
{
return v___x_458_;
}
else
{
v_x_447_ = v_p_453_;
v_x_448_ = v_p_456_;
goto _start;
}
}
}
else
{
uint8_t v___x_460_; 
v___x_460_ = 0;
return v___x_460_;
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_instBEqPoly_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_447_ = stack[0].m_obj;
lean_object* v_x_448_ = stack[1].m_obj;
uint8_t v_res_461_;
v_res_461_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_x_447_, v_x_448_);
stack->m_num = v_res_461_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instBEqPoly_beq___boxed(lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_x_462_, v_x_463_);
lean_dec(v_x_463_);
lean_dec(v_x_462_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_468_, lean_object* v_x_469_, lean_object* v_h__1_470_, lean_object* v_h__2_471_, lean_object* v_h__3_472_){
_start:
{
if (lean_obj_tag(v_x_468_) == 0)
{
lean_dec(v_h__2_471_);
if (lean_obj_tag(v_x_469_) == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v_h__3_472_);
v___x_473_ = lean_box(0);
v___x_474_ = lean_apply_1(v_h__1_470_, v___x_473_);
return v___x_474_;
}
else
{
lean_object* v___x_475_; 
lean_dec(v_h__1_470_);
v___x_475_ = lean_apply_4(v_h__3_472_, v_x_468_, v_x_469_, lean_box(0), lean_box(0));
return v___x_475_;
}
}
else
{
lean_dec(v_h__1_470_);
if (lean_obj_tag(v_x_469_) == 1)
{
lean_object* v_k_476_; lean_object* v_v_477_; lean_object* v_p_478_; lean_object* v_k_479_; lean_object* v_v_480_; lean_object* v_p_481_; lean_object* v___x_482_; 
lean_dec(v_h__3_472_);
v_k_476_ = lean_ctor_get(v_x_468_, 0);
lean_inc(v_k_476_);
v_v_477_ = lean_ctor_get(v_x_468_, 1);
lean_inc(v_v_477_);
v_p_478_ = lean_ctor_get(v_x_468_, 2);
lean_inc(v_p_478_);
lean_dec_ref_known(v_x_468_, 3);
v_k_479_ = lean_ctor_get(v_x_469_, 0);
lean_inc(v_k_479_);
v_v_480_ = lean_ctor_get(v_x_469_, 1);
lean_inc(v_v_480_);
v_p_481_ = lean_ctor_get(v_x_469_, 2);
lean_inc(v_p_481_);
lean_dec_ref_known(v_x_469_, 3);
v___x_482_ = lean_apply_6(v_h__2_471_, v_k_476_, v_v_477_, v_p_478_, v_k_479_, v_v_480_, v_p_481_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; 
lean_dec(v_h__2_471_);
v___x_483_ = lean_apply_4(v_h__3_472_, v_x_468_, v_x_469_, lean_box(0), lean_box(0));
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_484_, lean_object* v_x_485_, lean_object* v_x_486_, lean_object* v_h__1_487_, lean_object* v_h__2_488_, lean_object* v_h__3_489_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
lean_dec(v_h__2_488_);
if (lean_obj_tag(v_x_486_) == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v_h__3_489_);
v___x_490_ = lean_box(0);
v___x_491_ = lean_apply_1(v_h__1_487_, v___x_490_);
return v___x_491_;
}
else
{
lean_object* v___x_492_; 
lean_dec(v_h__1_487_);
v___x_492_ = lean_apply_4(v_h__3_489_, v_x_485_, v_x_486_, lean_box(0), lean_box(0));
return v___x_492_;
}
}
else
{
lean_dec(v_h__1_487_);
if (lean_obj_tag(v_x_486_) == 1)
{
lean_object* v_k_493_; lean_object* v_v_494_; lean_object* v_p_495_; lean_object* v_k_496_; lean_object* v_v_497_; lean_object* v_p_498_; lean_object* v___x_499_; 
lean_dec(v_h__3_489_);
v_k_493_ = lean_ctor_get(v_x_485_, 0);
lean_inc(v_k_493_);
v_v_494_ = lean_ctor_get(v_x_485_, 1);
lean_inc(v_v_494_);
v_p_495_ = lean_ctor_get(v_x_485_, 2);
lean_inc(v_p_495_);
lean_dec_ref_known(v_x_485_, 3);
v_k_496_ = lean_ctor_get(v_x_486_, 0);
lean_inc(v_k_496_);
v_v_497_ = lean_ctor_get(v_x_486_, 1);
lean_inc(v_v_497_);
v_p_498_ = lean_ctor_get(v_x_486_, 2);
lean_inc(v_p_498_);
lean_dec_ref_known(v_x_486_, 3);
v___x_499_ = lean_apply_6(v_h__2_488_, v_k_493_, v_v_494_, v_p_495_, v_k_496_, v_v_497_, v_p_498_);
return v___x_499_;
}
else
{
lean_object* v___x_500_; 
lean_dec(v_h__2_488_);
v___x_500_ = lean_apply_4(v_h__3_489_, v_x_485_, v_x_486_, lean_box(0), lean_box(0));
return v___x_500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprPoly_repr(lean_object* v_x_510_, lean_object* v_prec_511_){
_start:
{
lean_object* v___y_513_; 
if (lean_obj_tag(v_x_510_) == 0)
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(1024u);
v___x_520_ = lean_nat_dec_le(v___x_519_, v_prec_511_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
v___x_521_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_513_ = v___x_521_;
goto v___jp_512_;
}
else
{
lean_object* v___x_522_; 
v___x_522_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_513_ = v___x_522_;
goto v___jp_512_;
}
}
else
{
lean_object* v_k_523_; lean_object* v_v_524_; lean_object* v_p_525_; lean_object* v___x_526_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_545_; uint8_t v___x_555_; 
v_k_523_ = lean_ctor_get(v_x_510_, 0);
lean_inc(v_k_523_);
v_v_524_ = lean_ctor_get(v_x_510_, 1);
lean_inc(v_v_524_);
v_p_525_ = lean_ctor_get(v_x_510_, 2);
lean_inc(v_p_525_);
lean_dec_ref_known(v_x_510_, 3);
v___x_526_ = lean_unsigned_to_nat(1024u);
v___x_555_ = lean_nat_dec_le(v___x_526_, v_prec_511_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__2, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__2_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__2);
v___y_545_ = v___x_556_;
goto v___jp_544_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___y_545_ = v___x_557_;
goto v___jp_544_;
}
v___jp_527_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_inc(v___y_528_);
v___x_532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_532_, 0, v___y_528_);
lean_ctor_set(v___x_532_, 1, v___y_531_);
lean_inc_n(v___y_530_, 2);
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___y_530_);
v___x_534_ = l_Nat_reprFast(v_v_524_);
v___x_535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
v___x_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_533_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___y_530_);
v___x_538_ = l_Lean_Grind_Linarith_instReprPoly_repr(v_p_525_, v___x_526_);
v___x_539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
lean_inc(v___y_529_);
v___x_540_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_540_, 0, v___y_529_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = 0;
v___x_542_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_541_);
v___x_543_ = l_Repr_addAppParen(v___x_542_, v_prec_511_);
return v___x_543_;
}
v___jp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_546_ = lean_box(1);
v___x_547_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprPoly_repr___closed__4));
v___x_548_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_549_ = lean_int_dec_lt(v_k_523_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = l_Int_repr(v_k_523_);
lean_dec(v_k_523_);
v___x_551_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
v___y_528_ = v___x_547_;
v___y_529_ = v___y_545_;
v___y_530_ = v___x_546_;
v___y_531_ = v___x_551_;
goto v___jp_527_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_552_ = l_Int_repr(v_k_523_);
lean_dec(v_k_523_);
v___x_553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
v___x_554_ = l_Repr_addAppParen(v___x_553_, v___x_526_);
v___y_528_ = v___x_547_;
v___y_529_ = v___y_545_;
v___y_530_ = v___x_546_;
v___y_531_ = v___x_554_;
goto v___jp_527_;
}
}
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_514_ = ((lean_object*)(l_Lean_Grind_Linarith_instReprPoly_repr___closed__1));
lean_inc(v___y_513_);
v___x_515_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_515_, 0, v___y_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = 0;
v___x_517_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*1, v___x_516_);
v___x_518_ = l_Repr_addAppParen(v___x_517_, v_prec_511_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_instReprPoly_repr___boxed(lean_object* v_x_558_, lean_object* v_prec_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Grind_Linarith_instReprPoly_repr(v_x_558_, v_prec_559_);
lean_dec(v_prec_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___redArg(lean_object* v_inst_563_, lean_object* v_ctx_564_, lean_object* v_p_565_){
_start:
{
lean_object* v___x_566_; lean_object* v_toAddCommMonoid_567_; 
v___x_566_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_563_);
v_toAddCommMonoid_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc_ref(v_toAddCommMonoid_567_);
lean_dec_ref(v___x_566_);
if (lean_obj_tag(v_p_565_) == 0)
{
lean_object* v_toZero_568_; 
lean_dec_ref(v_inst_563_);
v_toZero_568_ = lean_ctor_get(v_toAddCommMonoid_567_, 0);
lean_inc(v_toZero_568_);
lean_dec_ref(v_toAddCommMonoid_567_);
return v_toZero_568_;
}
else
{
lean_object* v_toAdd_569_; lean_object* v_zsmul_570_; lean_object* v_k_571_; lean_object* v_v_572_; lean_object* v_p_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_toAdd_569_ = lean_ctor_get(v_toAddCommMonoid_567_, 1);
lean_inc(v_toAdd_569_);
lean_dec_ref(v_toAddCommMonoid_567_);
v_zsmul_570_ = lean_ctor_get(v_inst_563_, 2);
v_k_571_ = lean_ctor_get(v_p_565_, 0);
lean_inc(v_k_571_);
v_v_572_ = lean_ctor_get(v_p_565_, 1);
lean_inc(v_v_572_);
v_p_573_ = lean_ctor_get(v_p_565_, 2);
lean_inc(v_p_573_);
lean_dec_ref_known(v_p_565_, 3);
v___x_574_ = l_Lean_RArray_getImpl___redArg(v_ctx_564_, v_v_572_);
lean_dec(v_v_572_);
lean_inc(v_zsmul_570_);
v___x_575_ = lean_apply_2(v_zsmul_570_, v_k_571_, v___x_574_);
v___x_576_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_563_, v_ctx_564_, v_p_573_);
v___x_577_ = lean_apply_2(v_toAdd_569_, v___x_575_, v___x_576_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___redArg___boxed(lean_object* v_inst_578_, lean_object* v_ctx_579_, lean_object* v_p_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_578_, v_ctx_579_, v_p_580_);
lean_dec_ref(v_ctx_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote(lean_object* v_00_u03b1_582_, lean_object* v_inst_583_, lean_object* v_ctx_584_, lean_object* v_p_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Grind_Linarith_Poly_denote___redArg(v_inst_583_, v_ctx_584_, v_p_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote___boxed(lean_object* v_00_u03b1_587_, lean_object* v_inst_588_, lean_object* v_ctx_589_, lean_object* v_p_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Grind_Linarith_Poly_denote(v_00_u03b1_587_, v_inst_588_, v_ctx_589_, v_p_590_);
lean_dec_ref(v_ctx_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(lean_object* v_inst_592_, lean_object* v_ctx_593_, lean_object* v_r_594_, lean_object* v_p_595_){
_start:
{
lean_object* v___x_596_; lean_object* v_toAddCommMonoid_597_; 
v___x_596_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_592_);
v_toAddCommMonoid_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc_ref(v_toAddCommMonoid_597_);
lean_dec_ref(v___x_596_);
if (lean_obj_tag(v_p_595_) == 0)
{
lean_dec_ref(v_toAddCommMonoid_597_);
lean_dec_ref(v_inst_592_);
return v_r_594_;
}
else
{
lean_object* v_toAdd_598_; lean_object* v_zsmul_599_; lean_object* v_k_600_; lean_object* v_v_601_; lean_object* v_p_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_toAdd_598_ = lean_ctor_get(v_toAddCommMonoid_597_, 1);
lean_inc(v_toAdd_598_);
lean_dec_ref(v_toAddCommMonoid_597_);
v_zsmul_599_ = lean_ctor_get(v_inst_592_, 2);
v_k_600_ = lean_ctor_get(v_p_595_, 0);
lean_inc(v_k_600_);
v_v_601_ = lean_ctor_get(v_p_595_, 1);
lean_inc(v_v_601_);
v_p_602_ = lean_ctor_get(v_p_595_, 2);
lean_inc(v_p_602_);
lean_dec_ref_known(v_p_595_, 3);
v___x_603_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_604_ = lean_int_dec_eq(v_k_600_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = l_Lean_RArray_getImpl___redArg(v_ctx_593_, v_v_601_);
lean_dec(v_v_601_);
lean_inc(v_zsmul_599_);
v___x_606_ = lean_apply_2(v_zsmul_599_, v_k_600_, v___x_605_);
v___x_607_ = lean_apply_2(v_toAdd_598_, v_r_594_, v___x_606_);
v_r_594_ = v___x_607_;
v_p_595_ = v_p_602_;
goto _start;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v_k_600_);
v___x_609_ = l_Lean_RArray_getImpl___redArg(v_ctx_593_, v_v_601_);
lean_dec(v_v_601_);
v___x_610_ = lean_apply_2(v_toAdd_598_, v_r_594_, v___x_609_);
v_r_594_ = v___x_610_;
v_p_595_ = v_p_602_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg___boxed(lean_object* v_inst_612_, lean_object* v_ctx_613_, lean_object* v_r_614_, lean_object* v_p_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_612_, v_ctx_613_, v_r_614_, v_p_615_);
lean_dec_ref(v_ctx_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go(lean_object* v_00_u03b1_617_, lean_object* v_inst_618_, lean_object* v_ctx_619_, lean_object* v_r_620_, lean_object* v_p_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_618_, v_ctx_619_, v_r_620_, v_p_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27_go___boxed(lean_object* v_00_u03b1_623_, lean_object* v_inst_624_, lean_object* v_ctx_625_, lean_object* v_r_626_, lean_object* v_p_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Grind_Linarith_Poly_denote_x27_go(v_00_u03b1_623_, v_inst_624_, v_ctx_625_, v_r_626_, v_p_627_);
lean_dec_ref(v_ctx_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___redArg(lean_object* v_inst_629_, lean_object* v_ctx_630_, lean_object* v_p_631_){
_start:
{
lean_object* v___x_632_; lean_object* v_toAddCommMonoid_633_; 
v___x_632_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_629_);
v_toAddCommMonoid_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc_ref(v_toAddCommMonoid_633_);
lean_dec_ref(v___x_632_);
if (lean_obj_tag(v_p_631_) == 0)
{
lean_object* v_toZero_634_; 
lean_dec_ref(v_inst_629_);
v_toZero_634_ = lean_ctor_get(v_toAddCommMonoid_633_, 0);
lean_inc(v_toZero_634_);
lean_dec_ref(v_toAddCommMonoid_633_);
return v_toZero_634_;
}
else
{
lean_object* v_zsmul_635_; lean_object* v_k_636_; lean_object* v_v_637_; lean_object* v_p_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
lean_dec_ref(v_toAddCommMonoid_633_);
v_zsmul_635_ = lean_ctor_get(v_inst_629_, 2);
v_k_636_ = lean_ctor_get(v_p_631_, 0);
lean_inc(v_k_636_);
v_v_637_ = lean_ctor_get(v_p_631_, 1);
lean_inc(v_v_637_);
v_p_638_ = lean_ctor_get(v_p_631_, 2);
lean_inc(v_p_638_);
lean_dec_ref_known(v_p_631_, 3);
v___x_639_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_640_ = lean_int_dec_eq(v_k_636_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = l_Lean_RArray_getImpl___redArg(v_ctx_630_, v_v_637_);
lean_dec(v_v_637_);
lean_inc(v_zsmul_635_);
v___x_642_ = lean_apply_2(v_zsmul_635_, v_k_636_, v___x_641_);
v___x_643_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_629_, v_ctx_630_, v___x_642_, v_p_638_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v_k_636_);
v___x_644_ = l_Lean_RArray_getImpl___redArg(v_ctx_630_, v_v_637_);
lean_dec(v_v_637_);
v___x_645_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_629_, v_ctx_630_, v___x_644_, v_p_638_);
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___redArg___boxed(lean_object* v_inst_646_, lean_object* v_ctx_647_, lean_object* v_p_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_Grind_Linarith_Poly_denote_x27___redArg(v_inst_646_, v_ctx_647_, v_p_648_);
lean_dec_ref(v_ctx_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27(lean_object* v_00_u03b1_650_, lean_object* v_inst_651_, lean_object* v_ctx_652_, lean_object* v_p_653_){
_start:
{
lean_object* v___x_654_; lean_object* v_toAddCommMonoid_655_; 
v___x_654_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_inst_651_);
v_toAddCommMonoid_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc_ref(v_toAddCommMonoid_655_);
lean_dec_ref(v___x_654_);
if (lean_obj_tag(v_p_653_) == 0)
{
lean_object* v_toZero_656_; 
lean_dec_ref(v_inst_651_);
v_toZero_656_ = lean_ctor_get(v_toAddCommMonoid_655_, 0);
lean_inc(v_toZero_656_);
lean_dec_ref(v_toAddCommMonoid_655_);
return v_toZero_656_;
}
else
{
lean_object* v_zsmul_657_; lean_object* v_k_658_; lean_object* v_v_659_; lean_object* v_p_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
lean_dec_ref(v_toAddCommMonoid_655_);
v_zsmul_657_ = lean_ctor_get(v_inst_651_, 2);
v_k_658_ = lean_ctor_get(v_p_653_, 0);
lean_inc(v_k_658_);
v_v_659_ = lean_ctor_get(v_p_653_, 1);
lean_inc(v_v_659_);
v_p_660_ = lean_ctor_get(v_p_653_, 2);
lean_inc(v_p_660_);
lean_dec_ref_known(v_p_653_, 3);
v___x_661_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_662_ = lean_int_dec_eq(v_k_658_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = l_Lean_RArray_getImpl___redArg(v_ctx_652_, v_v_659_);
lean_dec(v_v_659_);
lean_inc(v_zsmul_657_);
v___x_664_ = lean_apply_2(v_zsmul_657_, v_k_658_, v___x_663_);
v___x_665_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_651_, v_ctx_652_, v___x_664_, v_p_660_);
return v___x_665_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec(v_k_658_);
v___x_666_ = l_Lean_RArray_getImpl___redArg(v_ctx_652_, v_v_659_);
lean_dec(v_v_659_);
v___x_667_ = l_Lean_Grind_Linarith_Poly_denote_x27_go___redArg(v_inst_651_, v_ctx_652_, v___x_666_, v_p_660_);
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denote_x27___boxed(lean_object* v_00_u03b1_668_, lean_object* v_inst_669_, lean_object* v_ctx_670_, lean_object* v_p_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Grind_Linarith_Poly_denote_x27(v_00_u03b1_668_, v_inst_669_, v_ctx_670_, v_p_671_);
lean_dec_ref(v_ctx_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter___redArg(lean_object* v_p_673_, lean_object* v_h__1_674_, lean_object* v_h__2_675_, lean_object* v_h__3_676_){
_start:
{
if (lean_obj_tag(v_p_673_) == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec(v_h__3_676_);
lean_dec(v_h__2_675_);
v___x_677_ = lean_box(0);
v___x_678_ = lean_apply_1(v_h__1_674_, v___x_677_);
return v___x_678_;
}
else
{
lean_object* v_k_679_; lean_object* v_v_680_; lean_object* v_p_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
lean_dec(v_h__1_674_);
v_k_679_ = lean_ctor_get(v_p_673_, 0);
lean_inc(v_k_679_);
v_v_680_ = lean_ctor_get(v_p_673_, 1);
lean_inc(v_v_680_);
v_p_681_ = lean_ctor_get(v_p_673_, 2);
lean_inc(v_p_681_);
lean_dec_ref_known(v_p_673_, 3);
v___x_682_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_683_ = lean_int_dec_eq(v_k_679_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_dec(v_h__2_675_);
v___x_684_ = lean_apply_4(v_h__3_676_, v_k_679_, v_v_680_, v_p_681_, lean_box(0));
return v___x_684_;
}
else
{
lean_object* v___x_685_; 
lean_dec(v_k_679_);
lean_dec(v_h__3_676_);
v___x_685_ = lean_apply_2(v_h__2_675_, v_v_680_, v_p_681_);
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_x27_go_match__1_splitter(lean_object* v_motive_686_, lean_object* v_p_687_, lean_object* v_h__1_688_, lean_object* v_h__2_689_, lean_object* v_h__3_690_){
_start:
{
if (lean_obj_tag(v_p_687_) == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v_h__3_690_);
lean_dec(v_h__2_689_);
v___x_691_ = lean_box(0);
v___x_692_ = lean_apply_1(v_h__1_688_, v___x_691_);
return v___x_692_;
}
else
{
lean_object* v_k_693_; lean_object* v_v_694_; lean_object* v_p_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
lean_dec(v_h__1_688_);
v_k_693_ = lean_ctor_get(v_p_687_, 0);
lean_inc(v_k_693_);
v_v_694_ = lean_ctor_get(v_p_687_, 1);
lean_inc(v_v_694_);
v_p_695_ = lean_ctor_get(v_p_687_, 2);
lean_inc(v_p_695_);
lean_dec_ref_known(v_p_687_, 3);
v___x_696_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_697_ = lean_int_dec_eq(v_k_693_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
lean_dec(v_h__2_689_);
v___x_698_ = lean_apply_4(v_h__3_690_, v_k_693_, v_v_694_, v_p_695_, lean_box(0));
return v___x_698_;
}
else
{
lean_object* v___x_699_; 
lean_dec(v_k_693_);
lean_dec(v_h__3_690_);
v___x_699_ = lean_apply_2(v_h__2_689_, v_v_694_, v_p_695_);
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_coeff(lean_object* v_p_700_, lean_object* v_x_701_){
_start:
{
if (lean_obj_tag(v_p_700_) == 0)
{
lean_object* v___x_702_; 
v___x_702_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
return v___x_702_;
}
else
{
lean_object* v_k_703_; lean_object* v_v_704_; lean_object* v_p_705_; uint8_t v___x_706_; 
v_k_703_ = lean_ctor_get(v_p_700_, 0);
v_v_704_ = lean_ctor_get(v_p_700_, 1);
v_p_705_ = lean_ctor_get(v_p_700_, 2);
v___x_706_ = lean_nat_dec_eq(v_x_701_, v_v_704_);
if (v___x_706_ == 0)
{
v_p_700_ = v_p_705_;
goto _start;
}
else
{
lean_inc(v_k_703_);
return v_k_703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_coeff___boxed(lean_object* v_p_708_, lean_object* v_x_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_708_, v_x_709_);
lean_dec(v_x_709_);
lean_dec(v_p_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_insert(lean_object* v_k_711_, lean_object* v_v_712_, lean_object* v_p_713_){
_start:
{
if (lean_obj_tag(v_p_713_) == 0)
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_714_, 0, v_k_711_);
lean_ctor_set(v___x_714_, 1, v_v_712_);
lean_ctor_set(v___x_714_, 2, v_p_713_);
return v___x_714_;
}
else
{
lean_object* v_k_715_; lean_object* v_v_716_; lean_object* v_p_717_; uint8_t v___x_718_; 
v_k_715_ = lean_ctor_get(v_p_713_, 0);
v_v_716_ = lean_ctor_get(v_p_713_, 1);
v_p_717_ = lean_ctor_get(v_p_713_, 2);
v___x_718_ = l_Nat_blt(v_v_716_, v_v_712_);
if (v___x_718_ == 0)
{
lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_733_; 
lean_inc(v_p_717_);
lean_inc(v_v_716_);
lean_inc(v_k_715_);
v_isSharedCheck_733_ = !lean_is_exclusive(v_p_713_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_734_ = lean_ctor_get(v_p_713_, 2);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_p_713_, 1);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_p_713_, 0);
lean_dec(v_unused_736_);
v___x_720_ = v_p_713_;
v_isShared_721_ = v_isSharedCheck_733_;
goto v_resetjp_719_;
}
else
{
lean_dec(v_p_713_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_733_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
uint8_t v___x_722_; 
v___x_722_ = lean_nat_dec_eq(v_v_712_, v_v_716_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = l_Lean_Grind_Linarith_Poly_insert(v_k_711_, v_v_712_, v_p_717_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 2, v___x_723_);
v___x_725_ = v___x_720_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_k_715_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_v_716_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
lean_dec(v_v_712_);
v___x_727_ = lean_int_add(v_k_711_, v_k_715_);
lean_dec(v_k_715_);
lean_dec(v_k_711_);
v___x_728_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_729_ = lean_int_dec_eq(v___x_727_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_731_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_727_);
v___x_731_ = v___x_720_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_v_716_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_p_717_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
else
{
lean_dec(v___x_727_);
lean_del_object(v___x_720_);
lean_dec(v_v_716_);
return v_p_717_;
}
}
}
}
else
{
lean_object* v___x_737_; 
v___x_737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_737_, 0, v_k_711_);
lean_ctor_set(v___x_737_, 1, v_v_712_);
lean_ctor_set(v___x_737_, 2, v_p_713_);
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_norm(lean_object* v_p_738_){
_start:
{
if (lean_obj_tag(v_p_738_) == 0)
{
return v_p_738_;
}
else
{
lean_object* v_k_739_; lean_object* v_v_740_; lean_object* v_p_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_k_739_ = lean_ctor_get(v_p_738_, 0);
lean_inc(v_k_739_);
v_v_740_ = lean_ctor_get(v_p_738_, 1);
lean_inc(v_v_740_);
v_p_741_ = lean_ctor_get(v_p_738_, 2);
lean_inc(v_p_741_);
lean_dec_ref_known(v_p_738_, 3);
v___x_742_ = l_Lean_Grind_Linarith_Poly_norm(v_p_741_);
v___x_743_ = l_Lean_Grind_Linarith_Poly_insert(v_k_739_, v_v_740_, v___x_742_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_append(lean_object* v_p_u2081_744_, lean_object* v_p_u2082_745_){
_start:
{
if (lean_obj_tag(v_p_u2081_744_) == 0)
{
lean_inc(v_p_u2082_745_);
return v_p_u2082_745_;
}
else
{
lean_object* v_k_746_; lean_object* v_v_747_; lean_object* v_p_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_756_; 
v_k_746_ = lean_ctor_get(v_p_u2081_744_, 0);
v_v_747_ = lean_ctor_get(v_p_u2081_744_, 1);
v_p_748_ = lean_ctor_get(v_p_u2081_744_, 2);
v_isSharedCheck_756_ = !lean_is_exclusive(v_p_u2081_744_);
if (v_isSharedCheck_756_ == 0)
{
v___x_750_ = v_p_u2081_744_;
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_p_748_);
lean_inc(v_v_747_);
lean_inc(v_k_746_);
lean_dec(v_p_u2081_744_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_752_ = l_Lean_Grind_Linarith_Poly_append(v_p_748_, v_p_u2082_745_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 2, v___x_752_);
v___x_754_ = v___x_750_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_k_746_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_v_747_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_append___boxed(lean_object* v_p_u2081_757_, lean_object* v_p_u2082_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Grind_Linarith_Poly_append(v_p_u2081_757_, v_p_u2082_758_);
lean_dec(v_p_u2082_758_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_combine(lean_object* v_p_u2081_760_, lean_object* v_p_u2082_761_){
_start:
{
if (lean_obj_tag(v_p_u2081_760_) == 0)
{
return v_p_u2082_761_;
}
else
{
if (lean_obj_tag(v_p_u2082_761_) == 0)
{
return v_p_u2081_760_;
}
else
{
lean_object* v_k_762_; lean_object* v_v_763_; lean_object* v_p_764_; lean_object* v_k_765_; lean_object* v_v_766_; lean_object* v_p_767_; uint8_t v___x_768_; 
v_k_762_ = lean_ctor_get(v_p_u2081_760_, 0);
v_v_763_ = lean_ctor_get(v_p_u2081_760_, 1);
v_p_764_ = lean_ctor_get(v_p_u2081_760_, 2);
v_k_765_ = lean_ctor_get(v_p_u2082_761_, 0);
v_v_766_ = lean_ctor_get(v_p_u2082_761_, 1);
v_p_767_ = lean_ctor_get(v_p_u2082_761_, 2);
v___x_768_ = lean_nat_dec_eq(v_v_763_, v_v_766_);
if (v___x_768_ == 0)
{
uint8_t v___x_769_; 
v___x_769_ = l_Nat_blt(v_v_766_, v_v_763_);
if (v___x_769_ == 0)
{
lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_777_; 
lean_inc(v_p_767_);
lean_inc(v_v_766_);
lean_inc(v_k_765_);
v_isSharedCheck_777_ = !lean_is_exclusive(v_p_u2082_761_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; lean_object* v_unused_779_; lean_object* v_unused_780_; 
v_unused_778_ = lean_ctor_get(v_p_u2082_761_, 2);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_p_u2082_761_, 1);
lean_dec(v_unused_779_);
v_unused_780_ = lean_ctor_get(v_p_u2082_761_, 0);
lean_dec(v_unused_780_);
v___x_771_ = v_p_u2082_761_;
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
else
{
lean_dec(v_p_u2082_761_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = l_Lean_Grind_Linarith_Poly_combine(v_p_u2081_760_, v_p_767_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 2, v___x_773_);
v___x_775_ = v___x_771_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_k_765_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_v_766_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
else
{
lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
lean_inc(v_p_764_);
lean_inc(v_v_763_);
lean_inc(v_k_762_);
v_isSharedCheck_788_ = !lean_is_exclusive(v_p_u2081_760_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; lean_object* v_unused_790_; lean_object* v_unused_791_; 
v_unused_789_ = lean_ctor_get(v_p_u2081_760_, 2);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v_p_u2081_760_, 1);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v_p_u2081_760_, 0);
lean_dec(v_unused_791_);
v___x_782_ = v_p_u2081_760_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_dec(v_p_u2081_760_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = l_Lean_Grind_Linarith_Poly_combine(v_p_764_, v_p_u2082_761_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 2, v___x_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_k_762_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_v_763_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_803_; 
lean_inc(v_p_767_);
lean_inc(v_k_765_);
lean_inc(v_p_764_);
lean_inc(v_v_763_);
lean_inc(v_k_762_);
lean_dec_ref_known(v_p_u2081_760_, 3);
v_isSharedCheck_803_ = !lean_is_exclusive(v_p_u2082_761_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; lean_object* v_unused_805_; lean_object* v_unused_806_; 
v_unused_804_ = lean_ctor_get(v_p_u2082_761_, 2);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_p_u2082_761_, 1);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_p_u2082_761_, 0);
lean_dec(v_unused_806_);
v___x_793_ = v_p_u2082_761_;
v_isShared_794_ = v_isSharedCheck_803_;
goto v_resetjp_792_;
}
else
{
lean_dec(v_p_u2082_761_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_803_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_a_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_a_795_ = lean_int_add(v_k_762_, v_k_765_);
lean_dec(v_k_765_);
lean_dec(v_k_762_);
v___x_796_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_797_ = lean_int_dec_eq(v_a_795_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = l_Lean_Grind_Linarith_Poly_combine(v_p_764_, v_p_767_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 2, v___x_798_);
lean_ctor_set(v___x_793_, 1, v_v_763_);
lean_ctor_set(v___x_793_, 0, v_a_795_);
v___x_800_ = v___x_793_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_v_763_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
else
{
lean_dec(v_a_795_);
lean_del_object(v___x_793_);
lean_dec(v_v_763_);
v_p_u2081_760_ = v_p_764_;
v_p_u2082_761_ = v_p_767_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter___redArg(lean_object* v_p_u2081_807_, lean_object* v_p_u2082_808_, lean_object* v_h__1_809_, lean_object* v_h__2_810_, lean_object* v_h__3_811_){
_start:
{
if (lean_obj_tag(v_p_u2081_807_) == 0)
{
lean_object* v___x_812_; 
lean_dec(v_h__3_811_);
lean_dec(v_h__2_810_);
v___x_812_ = lean_apply_1(v_h__1_809_, v_p_u2082_808_);
return v___x_812_;
}
else
{
lean_dec(v_h__1_809_);
if (lean_obj_tag(v_p_u2082_808_) == 0)
{
lean_object* v___x_813_; 
lean_dec(v_h__3_811_);
v___x_813_ = lean_apply_2(v_h__2_810_, v_p_u2081_807_, lean_box(0));
return v___x_813_;
}
else
{
lean_object* v_k_814_; lean_object* v_v_815_; lean_object* v_p_816_; lean_object* v_k_817_; lean_object* v_v_818_; lean_object* v_p_819_; lean_object* v___x_820_; 
lean_dec(v_h__2_810_);
v_k_814_ = lean_ctor_get(v_p_u2081_807_, 0);
lean_inc(v_k_814_);
v_v_815_ = lean_ctor_get(v_p_u2081_807_, 1);
lean_inc(v_v_815_);
v_p_816_ = lean_ctor_get(v_p_u2081_807_, 2);
lean_inc(v_p_816_);
lean_dec_ref_known(v_p_u2081_807_, 3);
v_k_817_ = lean_ctor_get(v_p_u2082_808_, 0);
lean_inc(v_k_817_);
v_v_818_ = lean_ctor_get(v_p_u2082_808_, 1);
lean_inc(v_v_818_);
v_p_819_ = lean_ctor_get(v_p_u2082_808_, 2);
lean_inc(v_p_819_);
lean_dec_ref_known(v_p_u2082_808_, 3);
v___x_820_ = lean_apply_6(v_h__3_811_, v_k_814_, v_v_815_, v_p_816_, v_k_817_, v_v_818_, v_p_819_);
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter(lean_object* v_motive_821_, lean_object* v_p_u2081_822_, lean_object* v_p_u2082_823_, lean_object* v_h__1_824_, lean_object* v_h__2_825_, lean_object* v_h__3_826_){
_start:
{
if (lean_obj_tag(v_p_u2081_822_) == 0)
{
lean_object* v___x_827_; 
lean_dec(v_h__3_826_);
lean_dec(v_h__2_825_);
v___x_827_ = lean_apply_1(v_h__1_824_, v_p_u2082_823_);
return v___x_827_;
}
else
{
lean_dec(v_h__1_824_);
if (lean_obj_tag(v_p_u2082_823_) == 0)
{
lean_object* v___x_828_; 
lean_dec(v_h__3_826_);
v___x_828_ = lean_apply_2(v_h__2_825_, v_p_u2081_822_, lean_box(0));
return v___x_828_;
}
else
{
lean_object* v_k_829_; lean_object* v_v_830_; lean_object* v_p_831_; lean_object* v_k_832_; lean_object* v_v_833_; lean_object* v_p_834_; lean_object* v___x_835_; 
lean_dec(v_h__2_825_);
v_k_829_ = lean_ctor_get(v_p_u2081_822_, 0);
lean_inc(v_k_829_);
v_v_830_ = lean_ctor_get(v_p_u2081_822_, 1);
lean_inc(v_v_830_);
v_p_831_ = lean_ctor_get(v_p_u2081_822_, 2);
lean_inc(v_p_831_);
lean_dec_ref_known(v_p_u2081_822_, 3);
v_k_832_ = lean_ctor_get(v_p_u2082_823_, 0);
lean_inc(v_k_832_);
v_v_833_ = lean_ctor_get(v_p_u2082_823_, 1);
lean_inc(v_v_833_);
v_p_834_ = lean_ctor_get(v_p_u2082_823_, 2);
lean_inc(v_p_834_);
lean_dec_ref_known(v_p_u2082_823_, 3);
v___x_835_ = lean_apply_6(v_h__3_826_, v_k_829_, v_v_830_, v_p_831_, v_k_832_, v_v_833_, v_p_834_);
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Expr_toPoly_x27_go_spec__0(lean_object* v_a_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = lean_nat_to_int(v_a_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPoly_x27_go(lean_object* v_coeff_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
switch(lean_obj_tag(v_a_839_))
{
case 0:
{
lean_dec(v_coeff_838_);
return v_a_840_;
}
case 1:
{
lean_object* v_i_841_; lean_object* v___x_842_; 
v_i_841_ = lean_ctor_get(v_a_839_, 0);
lean_inc(v_i_841_);
lean_dec_ref_known(v_a_839_, 1);
v___x_842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_842_, 0, v_coeff_838_);
lean_ctor_set(v___x_842_, 1, v_i_841_);
lean_ctor_set(v___x_842_, 2, v_a_840_);
return v___x_842_;
}
case 2:
{
lean_object* v_a_843_; lean_object* v_b_844_; lean_object* v___x_845_; 
v_a_843_ = lean_ctor_get(v_a_839_, 0);
lean_inc(v_a_843_);
v_b_844_ = lean_ctor_get(v_a_839_, 1);
lean_inc(v_b_844_);
lean_dec_ref_known(v_a_839_, 2);
lean_inc(v_coeff_838_);
v___x_845_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v_coeff_838_, v_b_844_, v_a_840_);
v_a_839_ = v_a_843_;
v_a_840_ = v___x_845_;
goto _start;
}
case 3:
{
lean_object* v_a_847_; lean_object* v_b_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_a_847_ = lean_ctor_get(v_a_839_, 0);
lean_inc(v_a_847_);
v_b_848_ = lean_ctor_get(v_a_839_, 1);
lean_inc(v_b_848_);
lean_dec_ref_known(v_a_839_, 2);
v___x_849_ = lean_int_neg(v_coeff_838_);
v___x_850_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v___x_849_, v_b_848_, v_a_840_);
v_a_839_ = v_a_847_;
v_a_840_ = v___x_850_;
goto _start;
}
case 4:
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_ctor_get(v_a_839_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v_a_839_, 1);
v___x_853_ = lean_int_neg(v_coeff_838_);
lean_dec(v_coeff_838_);
v_coeff_838_ = v___x_853_;
v_a_839_ = v_a_852_;
goto _start;
}
case 5:
{
lean_object* v_k_855_; lean_object* v_a_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_k_855_ = lean_ctor_get(v_a_839_, 0);
lean_inc(v_k_855_);
v_a_856_ = lean_ctor_get(v_a_839_, 1);
lean_inc(v_a_856_);
lean_dec_ref_known(v_a_839_, 2);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_nat_dec_eq(v_k_855_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_nat_to_int(v_k_855_);
v___x_860_ = lean_int_mul(v_coeff_838_, v___x_859_);
lean_dec(v___x_859_);
lean_dec(v_coeff_838_);
v_coeff_838_ = v___x_860_;
v_a_839_ = v_a_856_;
goto _start;
}
else
{
lean_dec(v_a_856_);
lean_dec(v_k_855_);
lean_dec(v_coeff_838_);
return v_a_840_;
}
}
default: 
{
lean_object* v_k_862_; lean_object* v_a_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v_k_862_ = lean_ctor_get(v_a_839_, 0);
lean_inc(v_k_862_);
v_a_863_ = lean_ctor_get(v_a_839_, 1);
lean_inc(v_a_863_);
lean_dec_ref_known(v_a_839_, 2);
v___x_864_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_865_ = lean_int_dec_eq(v_k_862_, v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; 
v___x_866_ = lean_int_mul(v_coeff_838_, v_k_862_);
lean_dec(v_k_862_);
lean_dec(v_coeff_838_);
v_coeff_838_ = v___x_866_;
v_a_839_ = v_a_863_;
goto _start;
}
else
{
lean_dec(v_a_863_);
lean_dec(v_k_862_);
lean_dec(v_coeff_838_);
return v_a_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPoly_x27(lean_object* v_e_868_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_870_ = lean_box(0);
v___x_871_ = l_Lean_Grind_Linarith_Expr_toPoly_x27_go(v___x_869_, v_e_868_, v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_norm(lean_object* v_e_872_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = l_Lean_Grind_Linarith_Expr_toPoly_x27(v_e_872_);
v___x_874_ = l_Lean_Grind_Linarith_Poly_norm(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul_x27(lean_object* v_p_875_, lean_object* v_k_876_){
_start:
{
if (lean_obj_tag(v_p_875_) == 0)
{
return v_p_875_;
}
else
{
lean_object* v_k_877_; lean_object* v_v_878_; lean_object* v_p_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_888_; 
v_k_877_ = lean_ctor_get(v_p_875_, 0);
v_v_878_ = lean_ctor_get(v_p_875_, 1);
v_p_879_ = lean_ctor_get(v_p_875_, 2);
v_isSharedCheck_888_ = !lean_is_exclusive(v_p_875_);
if (v_isSharedCheck_888_ == 0)
{
v___x_881_ = v_p_875_;
v_isShared_882_ = v_isSharedCheck_888_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_p_879_);
lean_inc(v_v_878_);
lean_inc(v_k_877_);
lean_dec(v_p_875_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_888_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_883_ = lean_int_mul(v_k_876_, v_k_877_);
lean_dec(v_k_877_);
v___x_884_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_879_, v_k_876_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 2, v___x_884_);
lean_ctor_set(v___x_881_, 0, v___x_883_);
v___x_886_ = v___x_881_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul_x27___boxed(lean_object* v_p_889_, lean_object* v_k_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_889_, v_k_890_);
lean_dec(v_k_890_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul(lean_object* v_p_892_, lean_object* v_k_893_){
_start:
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_895_ = lean_int_dec_eq(v_k_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_Grind_Linarith_Poly_mul_x27(v_p_892_, v_k_893_);
return v___x_896_;
}
else
{
lean_object* v___x_897_; 
lean_dec(v_p_892_);
v___x_897_ = lean_box(0);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_mul___boxed(lean_object* v_p_898_, lean_object* v_k_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Grind_Linarith_Poly_mul(v_p_898_, v_k_899_);
lean_dec(v_k_899_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(lean_object* v_p_901_, lean_object* v_h__1_902_, lean_object* v_h__2_903_){
_start:
{
if (lean_obj_tag(v_p_901_) == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; 
lean_dec(v_h__2_903_);
v___x_904_ = lean_box(0);
v___x_905_ = lean_apply_1(v_h__1_902_, v___x_904_);
return v___x_905_;
}
else
{
lean_object* v_k_906_; lean_object* v_v_907_; lean_object* v_p_908_; lean_object* v___x_909_; 
lean_dec(v_h__1_902_);
v_k_906_ = lean_ctor_get(v_p_901_, 0);
lean_inc(v_k_906_);
v_v_907_ = lean_ctor_get(v_p_901_, 1);
lean_inc(v_v_907_);
v_p_908_ = lean_ctor_get(v_p_901_, 2);
lean_inc(v_p_908_);
lean_dec_ref_known(v_p_901_, 3);
v___x_909_ = lean_apply_3(v_h__2_903_, v_k_906_, v_v_907_, v_p_908_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(lean_object* v_motive_910_, lean_object* v_p_911_, lean_object* v_h__1_912_, lean_object* v_h__2_913_){
_start:
{
if (lean_obj_tag(v_p_911_) == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec(v_h__2_913_);
v___x_914_ = lean_box(0);
v___x_915_ = lean_apply_1(v_h__1_912_, v___x_914_);
return v___x_915_;
}
else
{
lean_object* v_k_916_; lean_object* v_v_917_; lean_object* v_p_918_; lean_object* v___x_919_; 
lean_dec(v_h__1_912_);
v_k_916_ = lean_ctor_get(v_p_911_, 0);
lean_inc(v_k_916_);
v_v_917_ = lean_ctor_get(v_p_911_, 1);
lean_inc(v_v_917_);
v_p_918_ = lean_ctor_get(v_p_911_, 2);
lean_inc(v_p_918_);
lean_dec_ref_known(v_p_911_, 3);
v___x_919_ = lean_apply_3(v_h__2_913_, v_k_916_, v_v_917_, v_p_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter___redArg(lean_object* v_x_920_, lean_object* v_h__1_921_, lean_object* v_h__2_922_, lean_object* v_h__3_923_, lean_object* v_h__4_924_, lean_object* v_h__5_925_, lean_object* v_h__6_926_, lean_object* v_h__7_927_){
_start:
{
switch(lean_obj_tag(v_x_920_))
{
case 0:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
v___x_928_ = lean_box(0);
v___x_929_ = lean_apply_1(v_h__1_921_, v___x_928_);
return v___x_929_;
}
case 1:
{
lean_object* v_i_930_; lean_object* v___x_931_; 
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__1_921_);
v_i_930_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_i_930_);
lean_dec_ref_known(v_x_920_, 1);
v___x_931_ = lean_apply_1(v_h__2_922_, v_i_930_);
return v___x_931_;
}
case 2:
{
lean_object* v_a_932_; lean_object* v_b_933_; lean_object* v___x_934_; 
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_a_932_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_a_932_);
v_b_933_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_b_933_);
lean_dec_ref_known(v_x_920_, 2);
v___x_934_ = lean_apply_2(v_h__3_923_, v_a_932_, v_b_933_);
return v___x_934_;
}
case 3:
{
lean_object* v_a_935_; lean_object* v_b_936_; lean_object* v___x_937_; 
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_a_935_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_a_935_);
v_b_936_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_b_936_);
lean_dec_ref_known(v_x_920_, 2);
v___x_937_ = lean_apply_2(v_h__4_924_, v_a_935_, v_b_936_);
return v___x_937_;
}
case 4:
{
lean_object* v_a_938_; lean_object* v___x_939_; 
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_a_938_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v_x_920_, 1);
v___x_939_ = lean_apply_1(v_h__7_927_, v_a_938_);
return v___x_939_;
}
case 5:
{
lean_object* v_k_940_; lean_object* v_a_941_; lean_object* v___x_942_; 
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_k_940_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_k_940_);
v_a_941_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_a_941_);
lean_dec_ref_known(v_x_920_, 2);
v___x_942_ = lean_apply_2(v_h__5_925_, v_k_940_, v_a_941_);
return v___x_942_;
}
default: 
{
lean_object* v_k_943_; lean_object* v_a_944_; lean_object* v___x_945_; 
lean_dec(v_h__7_927_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_k_943_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_k_943_);
v_a_944_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_a_944_);
lean_dec_ref_known(v_x_920_, 2);
v___x_945_ = lean_apply_2(v_h__6_926_, v_k_943_, v_a_944_);
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ordered_Linarith_0__Lean_Grind_Linarith_Expr_denote_match__1_splitter(lean_object* v_motive_946_, lean_object* v_x_947_, lean_object* v_h__1_948_, lean_object* v_h__2_949_, lean_object* v_h__3_950_, lean_object* v_h__4_951_, lean_object* v_h__5_952_, lean_object* v_h__6_953_, lean_object* v_h__7_954_){
_start:
{
switch(lean_obj_tag(v_x_947_))
{
case 0:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec(v_h__7_954_);
lean_dec(v_h__6_953_);
lean_dec(v_h__5_952_);
lean_dec(v_h__4_951_);
lean_dec(v_h__3_950_);
lean_dec(v_h__2_949_);
v___x_955_ = lean_box(0);
v___x_956_ = lean_apply_1(v_h__1_948_, v___x_955_);
return v___x_956_;
}
case 1:
{
lean_object* v_i_957_; lean_object* v___x_958_; 
lean_dec(v_h__7_954_);
lean_dec(v_h__6_953_);
lean_dec(v_h__5_952_);
lean_dec(v_h__4_951_);
lean_dec(v_h__3_950_);
lean_dec(v_h__1_948_);
v_i_957_ = lean_ctor_get(v_x_947_, 0);
lean_inc(v_i_957_);
lean_dec_ref_known(v_x_947_, 1);
v___x_958_ = lean_apply_1(v_h__2_949_, v_i_957_);
return v___x_958_;
}
case 2:
{
lean_object* v_a_959_; lean_object* v_b_960_; lean_object* v___x_961_; 
lean_dec(v_h__7_954_);
lean_dec(v_h__6_953_);
lean_dec(v_h__5_952_);
lean_dec(v_h__4_951_);
lean_dec(v_h__2_949_);
lean_dec(v_h__1_948_);
v_a_959_ = lean_ctor_get(v_x_947_, 0);
lean_inc(v_a_959_);
v_b_960_ = lean_ctor_get(v_x_947_, 1);
lean_inc(v_b_960_);
lean_dec_ref_known(v_x_947_, 2);
v___x_961_ = lean_apply_2(v_h__3_950_, v_a_959_, v_b_960_);
return v___x_961_;
}
case 3:
{
lean_object* v_a_962_; lean_object* v_b_963_; lean_object* v___x_964_; 
lean_dec(v_h__7_954_);
lean_dec(v_h__6_953_);
lean_dec(v_h__5_952_);
lean_dec(v_h__3_950_);
lean_dec(v_h__2_949_);
lean_dec(v_h__1_948_);
v_a_962_ = lean_ctor_get(v_x_947_, 0);
lean_inc(v_a_962_);
v_b_963_ = lean_ctor_get(v_x_947_, 1);
lean_inc(v_b_963_);
lean_dec_ref_known(v_x_947_, 2);
v___x_964_ = lean_apply_2(v_h__4_951_, v_a_962_, v_b_963_);
return v___x_964_;
}
case 4:
{
lean_object* v_a_965_; lean_object* v___x_966_; 
lean_dec(v_h__6_953_);
lean_dec(v_h__5_952_);
lean_dec(v_h__4_951_);
lean_dec(v_h__3_950_);
lean_dec(v_h__2_949_);
lean_dec(v_h__1_948_);
v_a_965_ = lean_ctor_get(v_x_947_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v_x_947_, 1);
v___x_966_ = lean_apply_1(v_h__7_954_, v_a_965_);
return v___x_966_;
}
case 5:
{
lean_object* v_k_967_; lean_object* v_a_968_; lean_object* v___x_969_; 
lean_dec(v_h__7_954_);
lean_dec(v_h__6_953_);
lean_dec(v_h__4_951_);
lean_dec(v_h__3_950_);
lean_dec(v_h__2_949_);
lean_dec(v_h__1_948_);
v_k_967_ = lean_ctor_get(v_x_947_, 0);
lean_inc(v_k_967_);
v_a_968_ = lean_ctor_get(v_x_947_, 1);
lean_inc(v_a_968_);
lean_dec_ref_known(v_x_947_, 2);
v___x_969_ = lean_apply_2(v_h__5_952_, v_k_967_, v_a_968_);
return v___x_969_;
}
default: 
{
lean_object* v_k_970_; lean_object* v_a_971_; lean_object* v___x_972_; 
lean_dec(v_h__7_954_);
lean_dec(v_h__5_952_);
lean_dec(v_h__4_951_);
lean_dec(v_h__3_950_);
lean_dec(v_h__2_949_);
lean_dec(v_h__1_948_);
v_k_970_ = lean_ctor_get(v_x_947_, 0);
lean_inc(v_k_970_);
v_a_971_ = lean_ctor_get(v_x_947_, 1);
lean_inc(v_a_971_);
lean_dec_ref_known(v_x_947_, 2);
v___x_972_ = lean_apply_2(v_h__6_953_, v_k_970_, v_a_971_);
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_leadCoeff(lean_object* v_p_973_){
_start:
{
if (lean_obj_tag(v_p_973_) == 1)
{
lean_object* v_k_974_; 
v_k_974_ = lean_ctor_get(v_p_973_, 0);
lean_inc(v_k_974_);
return v_k_974_;
}
else
{
lean_object* v___x_975_; 
v___x_975_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_leadCoeff___boxed(lean_object* v_p_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_976_);
lean_dec(v_p_976_);
return v_res_977_;
}
}
uint8_t l_Lean_Grind_Linarith_le__le__combine__cert(lean_object* v_p_u2081_978_, lean_object* v_p_u2082_979_, lean_object* v_p_u2083_980_){
_start:
{
lean_object* v___x_981_; lean_object* v_a_u2081_982_; lean_object* v___x_983_; lean_object* v_a_u2082_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_981_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_978_);
v_a_u2081_982_ = lean_nat_abs(v___x_981_);
lean_dec(v___x_981_);
v___x_983_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_979_);
v_a_u2082_984_ = lean_nat_abs(v___x_983_);
lean_dec(v___x_983_);
v___x_985_ = lean_nat_to_int(v_a_u2082_984_);
v___x_986_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_978_, v___x_985_);
lean_dec(v___x_985_);
v___x_987_ = lean_nat_to_int(v_a_u2081_982_);
v___x_988_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_979_, v___x_987_);
lean_dec(v___x_987_);
v___x_989_ = l_Lean_Grind_Linarith_Poly_combine(v___x_986_, v___x_988_);
v___x_990_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_980_, v___x_989_);
lean_dec(v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_le__le__combine__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_978_ = stack[0].m_obj;
lean_object* v_p_u2082_979_ = stack[1].m_obj;
lean_object* v_p_u2083_980_ = stack[2].m_obj;
uint8_t v_res_991_;
v_res_991_ = l_Lean_Grind_Linarith_le__le__combine__cert(v_p_u2081_978_, v_p_u2082_979_, v_p_u2083_980_);
stack->m_num = v_res_991_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_le__le__combine__cert___boxed(lean_object* v_p_u2081_992_, lean_object* v_p_u2082_993_, lean_object* v_p_u2083_994_){
_start:
{
uint8_t v_res_995_; lean_object* v_r_996_; 
v_res_995_ = l_Lean_Grind_Linarith_le__le__combine__cert(v_p_u2081_992_, v_p_u2082_993_, v_p_u2083_994_);
lean_dec(v_p_u2083_994_);
v_r_996_ = lean_box(v_res_995_);
return v_r_996_;
}
}
uint8_t l_Lean_Grind_Linarith_le__lt__combine__cert(lean_object* v_p_u2081_997_, lean_object* v_p_u2082_998_, lean_object* v_p_u2083_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v_a_u2081_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1000_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_997_);
v_a_u2081_1001_ = lean_nat_abs(v___x_1000_);
lean_dec(v___x_1000_);
v___x_1002_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1003_ = lean_nat_to_int(v_a_u2081_1001_);
v___x_1004_ = lean_int_dec_lt(v___x_1002_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_dec(v___x_1003_);
lean_dec(v_p_u2082_998_);
lean_dec(v_p_u2081_997_);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; lean_object* v_a_u2082_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1005_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_998_);
v_a_u2082_1006_ = lean_nat_abs(v___x_1005_);
lean_dec(v___x_1005_);
v___x_1007_ = lean_nat_to_int(v_a_u2082_1006_);
v___x_1008_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_997_, v___x_1007_);
lean_dec(v___x_1007_);
v___x_1009_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_998_, v___x_1003_);
lean_dec(v___x_1003_);
v___x_1010_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1008_, v___x_1009_);
v___x_1011_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_999_, v___x_1010_);
lean_dec(v___x_1010_);
return v___x_1011_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_le__lt__combine__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_997_ = stack[0].m_obj;
lean_object* v_p_u2082_998_ = stack[1].m_obj;
lean_object* v_p_u2083_999_ = stack[2].m_obj;
uint8_t v_res_1012_;
v_res_1012_ = l_Lean_Grind_Linarith_le__lt__combine__cert(v_p_u2081_997_, v_p_u2082_998_, v_p_u2083_999_);
stack->m_num = v_res_1012_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_le__lt__combine__cert___boxed(lean_object* v_p_u2081_1013_, lean_object* v_p_u2082_1014_, lean_object* v_p_u2083_1015_){
_start:
{
uint8_t v_res_1016_; lean_object* v_r_1017_; 
v_res_1016_ = l_Lean_Grind_Linarith_le__lt__combine__cert(v_p_u2081_1013_, v_p_u2082_1014_, v_p_u2083_1015_);
lean_dec(v_p_u2083_1015_);
v_r_1017_ = lean_box(v_res_1016_);
return v_r_1017_;
}
}
uint8_t l_Lean_Grind_Linarith_lt__lt__combine__cert(lean_object* v_p_u2081_1018_, lean_object* v_p_u2082_1019_, lean_object* v_p_u2083_1020_){
_start:
{
lean_object* v___x_1021_; lean_object* v_a_u2082_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1021_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2082_1019_);
v_a_u2082_1022_ = lean_nat_abs(v___x_1021_);
lean_dec(v___x_1021_);
v___x_1023_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1024_ = lean_nat_to_int(v_a_u2082_1022_);
v___x_1025_ = lean_int_dec_lt(v___x_1023_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_dec(v___x_1024_);
lean_dec(v_p_u2082_1019_);
lean_dec(v_p_u2081_1018_);
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; lean_object* v_a_u2081_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1026_ = l_Lean_Grind_Linarith_Poly_leadCoeff(v_p_u2081_1018_);
v_a_u2081_1027_ = lean_nat_abs(v___x_1026_);
lean_dec(v___x_1026_);
v___x_1028_ = lean_nat_to_int(v_a_u2081_1027_);
v___x_1029_ = lean_int_dec_lt(v___x_1023_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_dec(v___x_1028_);
lean_dec(v___x_1024_);
lean_dec(v_p_u2082_1019_);
lean_dec(v_p_u2081_1018_);
return v___x_1029_;
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1030_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1018_, v___x_1024_);
lean_dec(v___x_1024_);
v___x_1031_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1019_, v___x_1028_);
lean_dec(v___x_1028_);
v___x_1032_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1030_, v___x_1031_);
v___x_1033_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1020_, v___x_1032_);
lean_dec(v___x_1032_);
return v___x_1033_;
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_lt__lt__combine__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_1018_ = stack[0].m_obj;
lean_object* v_p_u2082_1019_ = stack[1].m_obj;
lean_object* v_p_u2083_1020_ = stack[2].m_obj;
uint8_t v_res_1034_;
v_res_1034_ = l_Lean_Grind_Linarith_lt__lt__combine__cert(v_p_u2081_1018_, v_p_u2082_1019_, v_p_u2083_1020_);
stack->m_num = v_res_1034_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_lt__lt__combine__cert___boxed(lean_object* v_p_u2081_1035_, lean_object* v_p_u2082_1036_, lean_object* v_p_u2083_1037_){
_start:
{
uint8_t v_res_1038_; lean_object* v_r_1039_; 
v_res_1038_ = l_Lean_Grind_Linarith_lt__lt__combine__cert(v_p_u2081_1035_, v_p_u2082_1036_, v_p_u2083_1037_);
lean_dec(v_p_u2083_1037_);
v_r_1039_ = lean_box(v_res_1038_);
return v_r_1039_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1041_ = lean_int_neg(v___x_1040_);
return v___x_1041_;
}
}
uint8_t l_Lean_Grind_Linarith_diseq__split__cert(lean_object* v_p_u2081_1042_, lean_object* v_p_u2082_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1044_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1045_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1042_, v___x_1044_);
v___x_1046_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_1043_, v___x_1045_);
lean_dec(v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_diseq__split__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_1042_ = stack[0].m_obj;
lean_object* v_p_u2082_1043_ = stack[1].m_obj;
uint8_t v_res_1047_;
v_res_1047_ = l_Lean_Grind_Linarith_diseq__split__cert(v_p_u2081_1042_, v_p_u2082_1043_);
stack->m_num = v_res_1047_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_diseq__split__cert___boxed(lean_object* v_p_u2081_1048_, lean_object* v_p_u2082_1049_){
_start:
{
uint8_t v_res_1050_; lean_object* v_r_1051_; 
v_res_1050_ = l_Lean_Grind_Linarith_diseq__split__cert(v_p_u2081_1048_, v_p_u2082_1049_);
lean_dec(v_p_u2082_1049_);
v_r_1051_ = lean_box(v_res_1050_);
return v_r_1051_;
}
}
uint8_t l_Lean_Grind_Linarith_norm__cert(lean_object* v_lhs_1052_, lean_object* v_rhs_1053_, lean_object* v_p_1054_){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1055_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_lhs_1052_);
lean_ctor_set(v___x_1055_, 1, v_rhs_1053_);
v___x_1056_ = l_Lean_Grind_Linarith_Expr_norm(v___x_1055_);
v___x_1057_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1054_, v___x_1056_);
lean_dec(v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_norm__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1052_ = stack[0].m_obj;
lean_object* v_rhs_1053_ = stack[1].m_obj;
lean_object* v_p_1054_ = stack[2].m_obj;
uint8_t v_res_1058_;
v_res_1058_ = l_Lean_Grind_Linarith_norm__cert(v_lhs_1052_, v_rhs_1053_, v_p_1054_);
stack->m_num = v_res_1058_;
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
uint8_t l_Lean_Grind_Linarith_eq__of__le__ge__cert(lean_object* v_p_u2081_1064_, lean_object* v_p_u2082_1065_){
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
LEAN_EXPORT void l_Lean_Grind_Linarith_eq__of__le__ge__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_1064_ = stack[0].m_obj;
lean_object* v_p_u2082_1065_ = stack[1].m_obj;
uint8_t v_res_1069_;
v_res_1069_ = l_Lean_Grind_Linarith_eq__of__le__ge__cert(v_p_u2081_1064_, v_p_u2082_1065_);
stack->m_num = v_res_1069_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__of__le__ge__cert___boxed(lean_object* v_p_u2081_1070_, lean_object* v_p_u2082_1071_){
_start:
{
uint8_t v_res_1072_; lean_object* v_r_1073_; 
v_res_1072_ = l_Lean_Grind_Linarith_eq__of__le__ge__cert(v_p_u2081_1070_, v_p_u2082_1071_);
lean_dec(v_p_u2082_1071_);
v_r_1073_ = lean_box(v_res_1072_);
return v_r_1073_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1077_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_1075_);
lean_ctor_set(v___x_1077_, 2, v___x_1074_);
return v___x_1077_;
}
}
uint8_t l_Lean_Grind_Linarith_zero__lt__one__cert(lean_object* v_p_1078_){
_start:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = lean_obj_once(&l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0, &l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0_once, _init_l_Lean_Grind_Linarith_zero__lt__one__cert___closed__0);
v___x_1080_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1078_, v___x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_zero__lt__one__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1078_ = stack[0].m_obj;
uint8_t v_res_1081_;
v_res_1081_ = l_Lean_Grind_Linarith_zero__lt__one__cert(v_p_1078_);
stack->m_num = v_res_1081_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__lt__one__cert___boxed(lean_object* v_p_1082_){
_start:
{
uint8_t v_res_1083_; lean_object* v_r_1084_; 
v_res_1083_ = l_Lean_Grind_Linarith_zero__lt__one__cert(v_p_1082_);
lean_dec(v_p_1082_);
v_r_1084_ = lean_box(v_res_1083_);
return v_r_1084_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1088_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v___x_1086_);
lean_ctor_set(v___x_1088_, 2, v___x_1085_);
return v___x_1088_;
}
}
uint8_t l_Lean_Grind_Linarith_zero__ne__one__cert(lean_object* v_p_1089_){
_start:
{
lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = lean_obj_once(&l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0, &l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once, _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0);
v___x_1091_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1089_, v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_zero__ne__one__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1089_ = stack[0].m_obj;
uint8_t v_res_1092_;
v_res_1092_ = l_Lean_Grind_Linarith_zero__ne__one__cert(v_p_1089_);
stack->m_num = v_res_1092_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__ne__one__cert___boxed(lean_object* v_p_1093_){
_start:
{
uint8_t v_res_1094_; lean_object* v_r_1095_; 
v_res_1094_ = l_Lean_Grind_Linarith_zero__ne__one__cert(v_p_1093_);
lean_dec(v_p_1093_);
v_r_1095_ = lean_box(v_res_1094_);
return v_r_1095_;
}
}
uint8_t l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(lean_object* v_c_1096_, lean_object* v_p_1097_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1098_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1099_ = lean_nat_to_int(v_c_1096_);
v___x_1100_ = lean_int_dec_lt(v___x_1098_, v___x_1099_);
lean_dec(v___x_1099_);
if (v___x_1100_ == 0)
{
return v___x_1100_;
}
else
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = lean_obj_once(&l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0, &l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0_once, _init_l_Lean_Grind_Linarith_zero__ne__one__cert___closed__0);
v___x_1102_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1097_, v___x_1101_);
return v___x_1102_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1096_ = stack[0].m_obj;
lean_object* v_p_1097_ = stack[1].m_obj;
uint8_t v_res_1103_;
v_res_1103_ = l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(v_c_1096_, v_p_1097_);
stack->m_num = v_res_1103_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert___boxed(lean_object* v_c_1104_, lean_object* v_p_1105_){
_start:
{
uint8_t v_res_1106_; lean_object* v_r_1107_; 
v_res_1106_ = l_Lean_Grind_Linarith_zero__ne__one__of__charC__cert(v_c_1104_, v_p_1105_);
lean_dec(v_p_1105_);
v_r_1107_ = lean_box(v_res_1106_);
return v_r_1107_;
}
}
uint8_t l_Lean_Grind_Linarith_eq__neg__cert(lean_object* v_p_u2081_1108_, lean_object* v_p_u2082_1109_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1110_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1111_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1108_, v___x_1110_);
v___x_1112_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2082_1109_, v___x_1111_);
lean_dec(v___x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_eq__neg__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_1108_ = stack[0].m_obj;
lean_object* v_p_u2082_1109_ = stack[1].m_obj;
uint8_t v_res_1113_;
v_res_1113_ = l_Lean_Grind_Linarith_eq__neg__cert(v_p_u2081_1108_, v_p_u2082_1109_);
stack->m_num = v_res_1113_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__neg__cert___boxed(lean_object* v_p_u2081_1114_, lean_object* v_p_u2082_1115_){
_start:
{
uint8_t v_res_1116_; lean_object* v_r_1117_; 
v_res_1116_ = l_Lean_Grind_Linarith_eq__neg__cert(v_p_u2081_1114_, v_p_u2082_1115_);
lean_dec(v_p_u2082_1115_);
v_r_1117_ = lean_box(v_res_1116_);
return v_r_1117_;
}
}
uint8_t l_Lean_Grind_Linarith_eq__coeff__cert(lean_object* v_p_u2081_1118_, lean_object* v_p_u2082_1119_, lean_object* v_k_1120_){
_start:
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1122_ = lean_nat_dec_eq(v_k_1120_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1123_ = lean_nat_to_int(v_k_1120_);
v___x_1124_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1119_, v___x_1123_);
lean_dec(v___x_1123_);
v___x_1125_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2081_1118_, v___x_1124_);
lean_dec(v___x_1124_);
return v___x_1125_;
}
else
{
uint8_t v___x_1126_; 
lean_dec(v_k_1120_);
lean_dec(v_p_u2082_1119_);
v___x_1126_ = 0;
return v___x_1126_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_eq__coeff__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_1118_ = stack[0].m_obj;
lean_object* v_p_u2082_1119_ = stack[1].m_obj;
lean_object* v_k_1120_ = stack[2].m_obj;
uint8_t v_res_1127_;
v_res_1127_ = l_Lean_Grind_Linarith_eq__coeff__cert(v_p_u2081_1118_, v_p_u2082_1119_, v_k_1120_);
stack->m_num = v_res_1127_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__coeff__cert___boxed(lean_object* v_p_u2081_1128_, lean_object* v_p_u2082_1129_, lean_object* v_k_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_Lean_Grind_Linarith_eq__coeff__cert(v_p_u2081_1128_, v_p_u2082_1129_, v_k_1130_);
lean_dec(v_p_u2081_1128_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
uint8_t l_Lean_Grind_Linarith_coeff__cert(lean_object* v_p_u2081_1133_, lean_object* v_p_u2082_1134_, lean_object* v_k_1135_){
_start:
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = lean_nat_dec_lt(v___x_1136_, v_k_1135_);
if (v___x_1137_ == 0)
{
lean_dec(v_k_1135_);
lean_dec(v_p_u2082_1134_);
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1138_ = lean_nat_to_int(v_k_1135_);
v___x_1139_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1134_, v___x_1138_);
lean_dec(v___x_1138_);
v___x_1140_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2081_1133_, v___x_1139_);
lean_dec(v___x_1139_);
return v___x_1140_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_coeff__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_1133_ = stack[0].m_obj;
lean_object* v_p_u2082_1134_ = stack[1].m_obj;
lean_object* v_k_1135_ = stack[2].m_obj;
uint8_t v_res_1141_;
v_res_1141_ = l_Lean_Grind_Linarith_coeff__cert(v_p_u2081_1133_, v_p_u2082_1134_, v_k_1135_);
stack->m_num = v_res_1141_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_coeff__cert___boxed(lean_object* v_p_u2081_1142_, lean_object* v_p_u2082_1143_, lean_object* v_k_1144_){
_start:
{
uint8_t v_res_1145_; lean_object* v_r_1146_; 
v_res_1145_ = l_Lean_Grind_Linarith_coeff__cert(v_p_u2081_1142_, v_p_u2082_1143_, v_k_1144_);
lean_dec(v_p_u2081_1142_);
v_r_1146_ = lean_box(v_res_1145_);
return v_r_1146_;
}
}
uint8_t l_Lean_Grind_Linarith_eq__diseq__subst__cert(lean_object* v_k_u2081_1147_, lean_object* v_k_u2082_1148_, lean_object* v_p_u2081_1149_, lean_object* v_p_u2082_1150_, lean_object* v_p_u2083_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1152_ = lean_nat_abs(v_k_u2081_1147_);
v___x_1153_ = lean_unsigned_to_nat(0u);
v___x_1154_ = lean_nat_dec_eq(v___x_1152_, v___x_1153_);
lean_dec(v___x_1152_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1155_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1149_, v_k_u2082_1148_);
v___x_1156_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1150_, v_k_u2081_1147_);
v___x_1157_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1155_, v___x_1156_);
v___x_1158_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1151_, v___x_1157_);
lean_dec(v___x_1157_);
return v___x_1158_;
}
else
{
uint8_t v___x_1159_; 
lean_dec(v_p_u2082_1150_);
lean_dec(v_p_u2081_1149_);
v___x_1159_ = 0;
return v___x_1159_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_eq__diseq__subst__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_u2081_1147_ = stack[0].m_obj;
lean_object* v_k_u2082_1148_ = stack[1].m_obj;
lean_object* v_p_u2081_1149_ = stack[2].m_obj;
lean_object* v_p_u2082_1150_ = stack[3].m_obj;
lean_object* v_p_u2083_1151_ = stack[4].m_obj;
uint8_t v_res_1160_;
v_res_1160_ = l_Lean_Grind_Linarith_eq__diseq__subst__cert(v_k_u2081_1147_, v_k_u2082_1148_, v_p_u2081_1149_, v_p_u2082_1150_, v_p_u2083_1151_);
stack->m_num = v_res_1160_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__diseq__subst__cert___boxed(lean_object* v_k_u2081_1161_, lean_object* v_k_u2082_1162_, lean_object* v_p_u2081_1163_, lean_object* v_p_u2082_1164_, lean_object* v_p_u2083_1165_){
_start:
{
uint8_t v_res_1166_; lean_object* v_r_1167_; 
v_res_1166_ = l_Lean_Grind_Linarith_eq__diseq__subst__cert(v_k_u2081_1161_, v_k_u2082_1162_, v_p_u2081_1163_, v_p_u2082_1164_, v_p_u2083_1165_);
lean_dec(v_p_u2083_1165_);
lean_dec(v_k_u2082_1162_);
lean_dec(v_k_u2081_1161_);
v_r_1167_ = lean_box(v_res_1166_);
return v_r_1167_;
}
}
uint8_t l_Lean_Grind_Linarith_eq__diseq__subst1__cert(lean_object* v_k_1168_, lean_object* v_p_u2081_1169_, lean_object* v_p_u2082_1170_, lean_object* v_p_u2083_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1172_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1169_, v_k_1168_);
v___x_1173_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1172_, v_p_u2082_1170_);
v___x_1174_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1171_, v___x_1173_);
lean_dec(v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_eq__diseq__subst1__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1168_ = stack[0].m_obj;
lean_object* v_p_u2081_1169_ = stack[1].m_obj;
lean_object* v_p_u2082_1170_ = stack[2].m_obj;
lean_object* v_p_u2083_1171_ = stack[3].m_obj;
uint8_t v_res_1175_;
v_res_1175_ = l_Lean_Grind_Linarith_eq__diseq__subst1__cert(v_k_1168_, v_p_u2081_1169_, v_p_u2082_1170_, v_p_u2083_1171_);
stack->m_num = v_res_1175_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__diseq__subst1__cert___boxed(lean_object* v_k_1176_, lean_object* v_p_u2081_1177_, lean_object* v_p_u2082_1178_, lean_object* v_p_u2083_1179_){
_start:
{
uint8_t v_res_1180_; lean_object* v_r_1181_; 
v_res_1180_ = l_Lean_Grind_Linarith_eq__diseq__subst1__cert(v_k_1176_, v_p_u2081_1177_, v_p_u2082_1178_, v_p_u2083_1179_);
lean_dec(v_p_u2083_1179_);
lean_dec(v_k_1176_);
v_r_1181_ = lean_box(v_res_1180_);
return v_r_1181_;
}
}
uint8_t l_Lean_Grind_Linarith_eq__le__subst__cert(lean_object* v_x_1182_, lean_object* v_p_u2081_1183_, lean_object* v_p_u2082_1184_, lean_object* v_p_u2083_1185_){
_start:
{
lean_object* v_a_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v_a_1186_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_1183_, v_x_1182_);
v___x_1187_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1188_ = lean_int_dec_le(v___x_1187_, v_a_1186_);
if (v___x_1188_ == 0)
{
lean_dec(v_a_1186_);
lean_dec(v_p_u2082_1184_);
lean_dec(v_p_u2081_1183_);
return v___x_1188_;
}
else
{
lean_object* v_b_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v_b_1189_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_1184_, v_x_1182_);
v___x_1190_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1184_, v_a_1186_);
lean_dec(v_a_1186_);
v___x_1191_ = lean_int_neg(v_b_1189_);
lean_dec(v_b_1189_);
v___x_1192_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1183_, v___x_1191_);
lean_dec(v___x_1191_);
v___x_1193_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1190_, v___x_1192_);
v___x_1194_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1185_, v___x_1193_);
lean_dec(v___x_1193_);
return v___x_1194_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_eq__le__subst__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1182_ = stack[0].m_obj;
lean_object* v_p_u2081_1183_ = stack[1].m_obj;
lean_object* v_p_u2082_1184_ = stack[2].m_obj;
lean_object* v_p_u2083_1185_ = stack[3].m_obj;
uint8_t v_res_1195_;
v_res_1195_ = l_Lean_Grind_Linarith_eq__le__subst__cert(v_x_1182_, v_p_u2081_1183_, v_p_u2082_1184_, v_p_u2083_1185_);
stack->m_num = v_res_1195_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__le__subst__cert___boxed(lean_object* v_x_1196_, lean_object* v_p_u2081_1197_, lean_object* v_p_u2082_1198_, lean_object* v_p_u2083_1199_){
_start:
{
uint8_t v_res_1200_; lean_object* v_r_1201_; 
v_res_1200_ = l_Lean_Grind_Linarith_eq__le__subst__cert(v_x_1196_, v_p_u2081_1197_, v_p_u2082_1198_, v_p_u2083_1199_);
lean_dec(v_p_u2083_1199_);
lean_dec(v_x_1196_);
v_r_1201_ = lean_box(v_res_1200_);
return v_r_1201_;
}
}
uint8_t l_Lean_Grind_Linarith_eq__lt__subst__cert(lean_object* v_x_1202_, lean_object* v_p_u2081_1203_, lean_object* v_p_u2082_1204_, lean_object* v_p_u2083_1205_){
_start:
{
lean_object* v_a_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v_a_1206_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_1203_, v_x_1202_);
v___x_1207_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__22, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__22_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__22);
v___x_1208_ = lean_int_dec_lt(v___x_1207_, v_a_1206_);
if (v___x_1208_ == 0)
{
lean_dec(v_a_1206_);
lean_dec(v_p_u2082_1204_);
lean_dec(v_p_u2081_1203_);
return v___x_1208_;
}
else
{
lean_object* v_b_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v_b_1209_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_1204_, v_x_1202_);
v___x_1210_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1204_, v_a_1206_);
lean_dec(v_a_1206_);
v___x_1211_ = lean_int_neg(v_b_1209_);
lean_dec(v_b_1209_);
v___x_1212_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1203_, v___x_1211_);
lean_dec(v___x_1211_);
v___x_1213_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1210_, v___x_1212_);
v___x_1214_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1205_, v___x_1213_);
lean_dec(v___x_1213_);
return v___x_1214_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_eq__lt__subst__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1202_ = stack[0].m_obj;
lean_object* v_p_u2081_1203_ = stack[1].m_obj;
lean_object* v_p_u2082_1204_ = stack[2].m_obj;
lean_object* v_p_u2083_1205_ = stack[3].m_obj;
uint8_t v_res_1215_;
v_res_1215_ = l_Lean_Grind_Linarith_eq__lt__subst__cert(v_x_1202_, v_p_u2081_1203_, v_p_u2082_1204_, v_p_u2083_1205_);
stack->m_num = v_res_1215_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__lt__subst__cert___boxed(lean_object* v_x_1216_, lean_object* v_p_u2081_1217_, lean_object* v_p_u2082_1218_, lean_object* v_p_u2083_1219_){
_start:
{
uint8_t v_res_1220_; lean_object* v_r_1221_; 
v_res_1220_ = l_Lean_Grind_Linarith_eq__lt__subst__cert(v_x_1216_, v_p_u2081_1217_, v_p_u2082_1218_, v_p_u2083_1219_);
lean_dec(v_p_u2083_1219_);
lean_dec(v_x_1216_);
v_r_1221_ = lean_box(v_res_1220_);
return v_r_1221_;
}
}
uint8_t l_Lean_Grind_Linarith_eq__eq__subst__cert(lean_object* v_x_1222_, lean_object* v_p_u2081_1223_, lean_object* v_p_u2082_1224_, lean_object* v_p_u2083_1225_){
_start:
{
lean_object* v_a_1226_; lean_object* v_b_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_a_1226_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2081_1223_, v_x_1222_);
v_b_1227_ = l_Lean_Grind_Linarith_Poly_coeff(v_p_u2082_1224_, v_x_1222_);
v___x_1228_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2082_1224_, v_a_1226_);
lean_dec(v_a_1226_);
v___x_1229_ = lean_int_neg(v_b_1227_);
lean_dec(v_b_1227_);
v___x_1230_ = l_Lean_Grind_Linarith_Poly_mul(v_p_u2081_1223_, v___x_1229_);
lean_dec(v___x_1229_);
v___x_1231_ = l_Lean_Grind_Linarith_Poly_combine(v___x_1228_, v___x_1230_);
v___x_1232_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_u2083_1225_, v___x_1231_);
lean_dec(v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_eq__eq__subst__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1222_ = stack[0].m_obj;
lean_object* v_p_u2081_1223_ = stack[1].m_obj;
lean_object* v_p_u2082_1224_ = stack[2].m_obj;
lean_object* v_p_u2083_1225_ = stack[3].m_obj;
uint8_t v_res_1233_;
v_res_1233_ = l_Lean_Grind_Linarith_eq__eq__subst__cert(v_x_1222_, v_p_u2081_1223_, v_p_u2082_1224_, v_p_u2083_1225_);
stack->m_num = v_res_1233_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__eq__subst__cert___boxed(lean_object* v_x_1234_, lean_object* v_p_u2081_1235_, lean_object* v_p_u2082_1236_, lean_object* v_p_u2083_1237_){
_start:
{
uint8_t v_res_1238_; lean_object* v_r_1239_; 
v_res_1238_ = l_Lean_Grind_Linarith_eq__eq__subst__cert(v_x_1234_, v_p_u2081_1235_, v_p_u2082_1236_, v_p_u2083_1237_);
lean_dec(v_p_u2083_1237_);
lean_dec(v_x_1234_);
v_r_1239_ = lean_box(v_res_1238_);
return v_r_1239_;
}
}
uint8_t l_Lean_Grind_Linarith_imp__eq__cert(lean_object* v_p_1240_, lean_object* v_x_1241_, lean_object* v_y_1242_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1243_ = lean_obj_once(&l_Lean_Grind_Linarith_instReprExpr_repr___closed__3, &l_Lean_Grind_Linarith_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_Linarith_instReprExpr_repr___closed__3);
v___x_1244_ = lean_obj_once(&l_Lean_Grind_Linarith_diseq__split__cert___closed__0, &l_Lean_Grind_Linarith_diseq__split__cert___closed__0_once, _init_l_Lean_Grind_Linarith_diseq__split__cert___closed__0);
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v_y_1242_);
lean_ctor_set(v___x_1246_, 2, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1243_);
lean_ctor_set(v___x_1247_, 1, v_x_1241_);
lean_ctor_set(v___x_1247_, 2, v___x_1246_);
v___x_1248_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v_p_1240_, v___x_1247_);
lean_dec_ref_known(v___x_1247_, 3);
return v___x_1248_;
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_imp__eq__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1240_ = stack[0].m_obj;
lean_object* v_x_1241_ = stack[1].m_obj;
lean_object* v_y_1242_ = stack[2].m_obj;
uint8_t v_res_1249_;
v_res_1249_ = l_Lean_Grind_Linarith_imp__eq__cert(v_p_1240_, v_x_1241_, v_y_1242_);
stack->m_num = v_res_1249_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_imp__eq__cert___boxed(lean_object* v_p_1250_, lean_object* v_x_1251_, lean_object* v_y_1252_){
_start:
{
uint8_t v_res_1253_; lean_object* v_r_1254_; 
v_res_1253_ = l_Lean_Grind_Linarith_imp__eq__cert(v_p_1250_, v_x_1251_, v_y_1252_);
lean_dec(v_p_1250_);
v_r_1254_ = lean_box(v_res_1253_);
return v_r_1254_;
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
