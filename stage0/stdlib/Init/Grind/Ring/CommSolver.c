// Lean compiler output
// Module: Init.Grind.Ring.CommSolver
// Imports: public import Init.Data.Ord.Basic public import Init.Grind.Ring.Field public import Init.Grind.Ordered.Ring public import Init.GrindInstances.Ring.Int import all Init.Data.Ord.Basic import Init.LawfulBEqTactics public import Init.Classical public import Init.Data.Bool public import Init.Data.Int.DivMod.Lemmas public import Init.Data.RArray public import Init.Ext import Init.Data.Hashable import Init.Data.Int.LemmasAux import Init.Data.Nat.Linear import Init.Grind.Ordered.Order import Init.Omega import Init.WFTactics import Init.Data.Int.Repr
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Nat_blt(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_toIntModule___redArg(lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
uint8_t l_Int_decidableDvd(lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_natCast_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_natCast_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_intCast_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_intCast_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_neg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_neg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_sub_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_sub_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_mul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_mul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_pow_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_pow_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0;
static lean_once_cell_t l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedExpr_default;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedExpr;
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqExpr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqExpr_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instBEqExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instBEqExpr_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instBEqExpr___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instBEqExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instBEqExpr = (const lean_object*)&l_Lean_Grind_CommRing_instBEqExpr___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashableExpr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableExpr_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instHashableExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instHashableExpr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instHashableExpr___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instHashableExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instHashableExpr = (const lean_object*)&l_Lean_Grind_CommRing_instHashableExpr___closed__0_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.CommRing.Expr.num"};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__0_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__0_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__1 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__1_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__2 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__2_value;
static lean_once_cell_t l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__3;
static lean_once_cell_t l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__4;
static const lean_string_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Grind.CommRing.Expr.natCast"};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__5 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__5_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__5_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__6 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__6_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__7 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__7_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Grind.CommRing.Expr.intCast"};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__8 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__8_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__8_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__9 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__9_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__10 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__10_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.CommRing.Expr.var"};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__11 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__11_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__11_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__12 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__12_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__13 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__13_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.CommRing.Expr.neg"};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__14 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__14_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__14_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__15 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__15_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__16 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__16_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.CommRing.Expr.add"};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__17 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__17_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__17_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__18 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__18_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__18_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__19 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__19_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.CommRing.Expr.sub"};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__20 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__20_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__20_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__21 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__21_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__21_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__22 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__22_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.CommRing.Expr.mul"};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__23 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__23_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__23_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__24 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__24_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__24_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__25 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__25_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.CommRing.Expr.pow"};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__26 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__26_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__26_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__27 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__27_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprExpr_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__27_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___closed__28 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr_repr___closed__28_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprExpr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instReprExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instReprExpr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instReprExpr___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instReprExpr = (const lean_object*)&l_Lean_Grind_CommRing_instReprExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPower_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPower_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instBEqPower___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instBEqPower_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instBEqPower___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instBEqPower___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instBEqPower = (const lean_object*)&l_Lean_Grind_CommRing_instBEqPower___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_instReprPower_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7;
static const lean_string_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13;
static lean_once_cell_t l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instReprPower___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instReprPower_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instReprPower___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instReprPower = (const lean_object*)&l_Lean_Grind_CommRing_instReprPower___closed__0_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instInhabitedPower_default = (const lean_object*)&l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instInhabitedPower = (const lean_object*)&l_Lean_Grind_CommRing_instInhabitedPower_default___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePower_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePower_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instHashablePower___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instHashablePower_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instHashablePower___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instHashablePower___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instHashablePower = (const lean_object*)&l_Lean_Grind_CommRing_instHashablePower___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_varLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_varLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqMon_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqMon_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instBEqMon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instBEqMon_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instBEqMon___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instBEqMon___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instBEqMon = (const lean_object*)&l_Lean_Grind_CommRing_instBEqMon___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_CommRing_instReprMon_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.CommRing.Mon.unit"};
static const lean_object* l_Lean_Grind_CommRing_instReprMon_repr___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instReprMon_repr___closed__0_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprMon_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprMon_repr___closed__0_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprMon_repr___closed__1 = (const lean_object*)&l_Lean_Grind_CommRing_instReprMon_repr___closed__1_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprMon_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.CommRing.Mon.mult"};
static const lean_object* l_Lean_Grind_CommRing_instReprMon_repr___closed__2 = (const lean_object*)&l_Lean_Grind_CommRing_instReprMon_repr___closed__2_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprMon_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprMon_repr___closed__2_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprMon_repr___closed__3 = (const lean_object*)&l_Lean_Grind_CommRing_instReprMon_repr___closed__3_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprMon_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprMon_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_instReprMon_repr___closed__4 = (const lean_object*)&l_Lean_Grind_CommRing_instReprMon_repr___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instReprMon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instReprMon_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instReprMon___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instReprMon___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instReprMon = (const lean_object*)&l_Lean_Grind_CommRing_instReprMon___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedMon_default;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedMon;
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashableMon_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableMon_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instHashableMon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instHashableMon_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instHashableMon___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instHashableMon___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instHashableMon = (const lean_object*)&l_Lean_Grind_CommRing_instHashableMon___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ofVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow__nc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_hugeFuel;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul__nc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Var_revlex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_revlex___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_powerRevlex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_powerRevlex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_revlex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_revlex___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexWF(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexWF___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexFuel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexFuel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlex___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_grevlex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPoly_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPoly_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instBEqPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instBEqPoly_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instBEqPoly___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instBEqPoly___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instBEqPoly = (const lean_object*)&l_Lean_Grind_CommRing_instBEqPoly___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_CommRing_instReprPoly_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.CommRing.Poly.num"};
static const lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPoly_repr___closed__0_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPoly_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPoly_repr___closed__0_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___closed__1 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPoly_repr___closed__1_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPoly_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPoly_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___closed__2 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPoly_repr___closed__2_value;
static const lean_string_object l_Lean_Grind_CommRing_instReprPoly_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Grind.CommRing.Poly.add"};
static const lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___closed__3 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPoly_repr___closed__3_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPoly_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPoly_repr___closed__3_value)}};
static const lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___closed__4 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPoly_repr___closed__4_value;
static const lean_ctor_object l_Lean_Grind_CommRing_instReprPoly_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_instReprPoly_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___closed__5 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPoly_repr___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instReprPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instReprPoly_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instReprPoly___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instReprPoly___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instReprPoly = (const lean_object*)&l_Lean_Grind_CommRing_instReprPoly___closed__0_value;
static lean_once_cell_t l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedPoly_default;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instInhabitedPoly;
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePoly_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePoly_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_CommRing_instHashablePoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_CommRing_instHashablePoly_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_CommRing_instHashablePoly___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_instHashablePoly___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_CommRing_instHashablePoly = (const lean_object*)&l_Lean_Grind_CommRing_instHashablePoly___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_isSorted(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isSorted___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_concat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Poly_pow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Poly_pow___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Expr_toPoly___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly__nc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_normEq0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__gcd__cert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__gcd__cert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorIdx(lean_object* v_x_1_){
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
case 6:
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
case 7:
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(7u);
return v___x_9_;
}
default: 
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(8u);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorIdx___boxed(lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Grind_CommRing_Expr_ctorIdx(v_x_11_);
lean_dec_ref(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim___redArg(lean_object* v_t_13_, lean_object* v_k_14_){
_start:
{
switch(lean_obj_tag(v_t_13_))
{
case 4:
{
lean_object* v_a_15_; lean_object* v___x_16_; 
v_a_15_ = lean_ctor_get(v_t_13_, 0);
lean_inc_ref(v_a_15_);
lean_dec_ref(v_t_13_);
v___x_16_ = lean_apply_1(v_k_14_, v_a_15_);
return v___x_16_;
}
case 5:
{
lean_object* v_a_17_; lean_object* v_b_18_; lean_object* v___x_19_; 
v_a_17_ = lean_ctor_get(v_t_13_, 0);
lean_inc_ref(v_a_17_);
v_b_18_ = lean_ctor_get(v_t_13_, 1);
lean_inc_ref(v_b_18_);
lean_dec_ref(v_t_13_);
v___x_19_ = lean_apply_2(v_k_14_, v_a_17_, v_b_18_);
return v___x_19_;
}
case 6:
{
lean_object* v_a_20_; lean_object* v_b_21_; lean_object* v___x_22_; 
v_a_20_ = lean_ctor_get(v_t_13_, 0);
lean_inc_ref(v_a_20_);
v_b_21_ = lean_ctor_get(v_t_13_, 1);
lean_inc_ref(v_b_21_);
lean_dec_ref(v_t_13_);
v___x_22_ = lean_apply_2(v_k_14_, v_a_20_, v_b_21_);
return v___x_22_;
}
case 7:
{
lean_object* v_a_23_; lean_object* v_b_24_; lean_object* v___x_25_; 
v_a_23_ = lean_ctor_get(v_t_13_, 0);
lean_inc_ref(v_a_23_);
v_b_24_ = lean_ctor_get(v_t_13_, 1);
lean_inc_ref(v_b_24_);
lean_dec_ref(v_t_13_);
v___x_25_ = lean_apply_2(v_k_14_, v_a_23_, v_b_24_);
return v___x_25_;
}
case 8:
{
lean_object* v_a_26_; lean_object* v_k_27_; lean_object* v___x_28_; 
v_a_26_ = lean_ctor_get(v_t_13_, 0);
lean_inc_ref(v_a_26_);
v_k_27_ = lean_ctor_get(v_t_13_, 1);
lean_inc(v_k_27_);
lean_dec_ref(v_t_13_);
v___x_28_ = lean_apply_2(v_k_14_, v_a_26_, v_k_27_);
return v___x_28_;
}
default: 
{
lean_object* v_k_29_; lean_object* v___x_30_; 
v_k_29_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_k_29_);
lean_dec_ref(v_t_13_);
v___x_30_ = lean_apply_1(v_k_14_, v_k_29_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim(lean_object* v_motive_31_, lean_object* v_ctorIdx_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_k_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_33_, v_k_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim___boxed(lean_object* v_motive_37_, lean_object* v_ctorIdx_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_k_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Grind_CommRing_Expr_ctorElim(v_motive_37_, v_ctorIdx_38_, v_t_39_, v_h_40_, v_k_41_);
lean_dec(v_ctorIdx_38_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_num_elim___redArg(lean_object* v_t_43_, lean_object* v_num_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_43_, v_num_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_num_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_num_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_47_, v_num_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_natCast_elim___redArg(lean_object* v_t_51_, lean_object* v_natCast_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_51_, v_natCast_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_natCast_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_natCast_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_55_, v_natCast_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_intCast_elim___redArg(lean_object* v_t_59_, lean_object* v_intCast_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_59_, v_intCast_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_intCast_elim(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_intCast_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_63_, v_intCast_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_var_elim___redArg(lean_object* v_t_67_, lean_object* v_var_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_67_, v_var_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_var_elim(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_var_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_71_, v_var_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_neg_elim___redArg(lean_object* v_t_75_, lean_object* v_neg_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_75_, v_neg_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_neg_elim(lean_object* v_motive_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_neg_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_79_, v_neg_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_add_elim___redArg(lean_object* v_t_83_, lean_object* v_add_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_83_, v_add_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_add_elim(lean_object* v_motive_86_, lean_object* v_t_87_, lean_object* v_h_88_, lean_object* v_add_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_87_, v_add_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_sub_elim___redArg(lean_object* v_t_91_, lean_object* v_sub_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_91_, v_sub_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_sub_elim(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_sub_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_95_, v_sub_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_mul_elim___redArg(lean_object* v_t_99_, lean_object* v_mul_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_99_, v_mul_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_mul_elim(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_mul_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_103_, v_mul_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_pow_elim___redArg(lean_object* v_t_107_, lean_object* v_pow_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_107_, v_pow_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_pow_elim(lean_object* v_motive_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_pow_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_111_, v_pow_113_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_nat_to_int(v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedExpr_default(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedExpr(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Grind_CommRing_instInhabitedExpr_default;
return v___x_120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqExpr_beq(lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
lean_object* v_a_124_; lean_object* v_a_125_; lean_object* v_b_126_; lean_object* v_b_127_; 
switch(lean_obj_tag(v_x_121_))
{
case 0:
{
if (lean_obj_tag(v_x_122_) == 0)
{
lean_object* v_k_130_; lean_object* v_k_131_; uint8_t v___x_132_; 
v_k_130_ = lean_ctor_get(v_x_121_, 0);
v_k_131_ = lean_ctor_get(v_x_122_, 0);
v___x_132_ = lean_int_dec_eq(v_k_130_, v_k_131_);
return v___x_132_;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
}
case 1:
{
if (lean_obj_tag(v_x_122_) == 1)
{
lean_object* v_k_134_; lean_object* v_k_135_; uint8_t v___x_136_; 
v_k_134_ = lean_ctor_get(v_x_121_, 0);
v_k_135_ = lean_ctor_get(v_x_122_, 0);
v___x_136_ = lean_nat_dec_eq(v_k_134_, v_k_135_);
return v___x_136_;
}
else
{
uint8_t v___x_137_; 
v___x_137_ = 0;
return v___x_137_;
}
}
case 2:
{
if (lean_obj_tag(v_x_122_) == 2)
{
lean_object* v_k_138_; lean_object* v_k_139_; uint8_t v___x_140_; 
v_k_138_ = lean_ctor_get(v_x_121_, 0);
v_k_139_ = lean_ctor_get(v_x_122_, 0);
v___x_140_ = lean_int_dec_eq(v_k_138_, v_k_139_);
return v___x_140_;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = 0;
return v___x_141_;
}
}
case 3:
{
if (lean_obj_tag(v_x_122_) == 3)
{
lean_object* v_i_142_; lean_object* v_i_143_; uint8_t v___x_144_; 
v_i_142_ = lean_ctor_get(v_x_121_, 0);
v_i_143_ = lean_ctor_get(v_x_122_, 0);
v___x_144_ = lean_nat_dec_eq(v_i_142_, v_i_143_);
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
case 4:
{
if (lean_obj_tag(v_x_122_) == 4)
{
lean_object* v_a_146_; lean_object* v_a_147_; 
v_a_146_ = lean_ctor_get(v_x_121_, 0);
v_a_147_ = lean_ctor_get(v_x_122_, 0);
v_x_121_ = v_a_146_;
v_x_122_ = v_a_147_;
goto _start;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
}
case 5:
{
if (lean_obj_tag(v_x_122_) == 5)
{
lean_object* v_a_150_; lean_object* v_b_151_; lean_object* v_a_152_; lean_object* v_b_153_; 
v_a_150_ = lean_ctor_get(v_x_121_, 0);
v_b_151_ = lean_ctor_get(v_x_121_, 1);
v_a_152_ = lean_ctor_get(v_x_122_, 0);
v_b_153_ = lean_ctor_get(v_x_122_, 1);
v_a_124_ = v_a_150_;
v_a_125_ = v_b_151_;
v_b_126_ = v_a_152_;
v_b_127_ = v_b_153_;
goto v___jp_123_;
}
else
{
uint8_t v___x_154_; 
v___x_154_ = 0;
return v___x_154_;
}
}
case 6:
{
if (lean_obj_tag(v_x_122_) == 6)
{
lean_object* v_a_155_; lean_object* v_b_156_; lean_object* v_a_157_; lean_object* v_b_158_; 
v_a_155_ = lean_ctor_get(v_x_121_, 0);
v_b_156_ = lean_ctor_get(v_x_121_, 1);
v_a_157_ = lean_ctor_get(v_x_122_, 0);
v_b_158_ = lean_ctor_get(v_x_122_, 1);
v_a_124_ = v_a_155_;
v_a_125_ = v_b_156_;
v_b_126_ = v_a_157_;
v_b_127_ = v_b_158_;
goto v___jp_123_;
}
else
{
uint8_t v___x_159_; 
v___x_159_ = 0;
return v___x_159_;
}
}
case 7:
{
if (lean_obj_tag(v_x_122_) == 7)
{
lean_object* v_a_160_; lean_object* v_b_161_; lean_object* v_a_162_; lean_object* v_b_163_; 
v_a_160_ = lean_ctor_get(v_x_121_, 0);
v_b_161_ = lean_ctor_get(v_x_121_, 1);
v_a_162_ = lean_ctor_get(v_x_122_, 0);
v_b_163_ = lean_ctor_get(v_x_122_, 1);
v_a_124_ = v_a_160_;
v_a_125_ = v_b_161_;
v_b_126_ = v_a_162_;
v_b_127_ = v_b_163_;
goto v___jp_123_;
}
else
{
uint8_t v___x_164_; 
v___x_164_ = 0;
return v___x_164_;
}
}
default: 
{
if (lean_obj_tag(v_x_122_) == 8)
{
lean_object* v_a_165_; lean_object* v_k_166_; lean_object* v_a_167_; lean_object* v_k_168_; uint8_t v___x_169_; 
v_a_165_ = lean_ctor_get(v_x_121_, 0);
v_k_166_ = lean_ctor_get(v_x_121_, 1);
v_a_167_ = lean_ctor_get(v_x_122_, 0);
v_k_168_ = lean_ctor_get(v_x_122_, 1);
v___x_169_ = l_Lean_Grind_CommRing_instBEqExpr_beq(v_a_165_, v_a_167_);
if (v___x_169_ == 0)
{
return v___x_169_;
}
else
{
uint8_t v___x_170_; 
v___x_170_ = lean_nat_dec_eq(v_k_166_, v_k_168_);
return v___x_170_;
}
}
else
{
uint8_t v___x_171_; 
v___x_171_ = 0;
return v___x_171_;
}
}
}
v___jp_123_:
{
uint8_t v___x_128_; 
v___x_128_ = l_Lean_Grind_CommRing_instBEqExpr_beq(v_a_124_, v_b_126_);
if (v___x_128_ == 0)
{
return v___x_128_;
}
else
{
v_x_121_ = v_a_125_;
v_x_122_ = v_b_127_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqExpr_beq___boxed(lean_object* v_x_172_, lean_object* v_x_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Lean_Grind_CommRing_instBEqExpr_beq(v_x_172_, v_x_173_);
lean_dec_ref(v_x_173_);
lean_dec_ref(v_x_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashableExpr_hash(lean_object* v_x_178_){
_start:
{
switch(lean_obj_tag(v_x_178_))
{
case 0:
{
lean_object* v_k_179_; uint64_t v___x_180_; lean_object* v_intZero_181_; uint8_t v_isNeg_182_; 
v_k_179_ = lean_ctor_get(v_x_178_, 0);
v___x_180_ = 0ULL;
v_intZero_181_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_182_ = lean_int_dec_lt(v_k_179_, v_intZero_181_);
if (v_isNeg_182_ == 0)
{
lean_object* v_a_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; 
v_a_183_ = lean_nat_abs(v_k_179_);
v___x_184_ = lean_unsigned_to_nat(2u);
v___x_185_ = lean_nat_mul(v___x_184_, v_a_183_);
lean_dec(v_a_183_);
v___x_186_ = lean_uint64_of_nat(v___x_185_);
lean_dec(v___x_185_);
v___x_187_ = lean_uint64_mix_hash(v___x_180_, v___x_186_);
return v___x_187_;
}
else
{
lean_object* v_abs_188_; lean_object* v_one_189_; lean_object* v_a_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint64_t v___x_194_; uint64_t v___x_195_; 
v_abs_188_ = lean_nat_abs(v_k_179_);
v_one_189_ = lean_unsigned_to_nat(1u);
v_a_190_ = lean_nat_sub(v_abs_188_, v_one_189_);
lean_dec(v_abs_188_);
v___x_191_ = lean_unsigned_to_nat(2u);
v___x_192_ = lean_nat_mul(v___x_191_, v_a_190_);
lean_dec(v_a_190_);
v___x_193_ = lean_nat_add(v___x_192_, v_one_189_);
lean_dec(v___x_192_);
v___x_194_ = lean_uint64_of_nat(v___x_193_);
lean_dec(v___x_193_);
v___x_195_ = lean_uint64_mix_hash(v___x_180_, v___x_194_);
return v___x_195_;
}
}
case 1:
{
lean_object* v_k_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; 
v_k_196_ = lean_ctor_get(v_x_178_, 0);
v___x_197_ = 1ULL;
v___x_198_ = lean_uint64_of_nat(v_k_196_);
v___x_199_ = lean_uint64_mix_hash(v___x_197_, v___x_198_);
return v___x_199_;
}
case 2:
{
lean_object* v_k_200_; uint64_t v___x_201_; lean_object* v_intZero_202_; uint8_t v_isNeg_203_; 
v_k_200_ = lean_ctor_get(v_x_178_, 0);
v___x_201_ = 2ULL;
v_intZero_202_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_203_ = lean_int_dec_lt(v_k_200_, v_intZero_202_);
if (v_isNeg_203_ == 0)
{
lean_object* v_a_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint64_t v___x_207_; uint64_t v___x_208_; 
v_a_204_ = lean_nat_abs(v_k_200_);
v___x_205_ = lean_unsigned_to_nat(2u);
v___x_206_ = lean_nat_mul(v___x_205_, v_a_204_);
lean_dec(v_a_204_);
v___x_207_ = lean_uint64_of_nat(v___x_206_);
lean_dec(v___x_206_);
v___x_208_ = lean_uint64_mix_hash(v___x_201_, v___x_207_);
return v___x_208_;
}
else
{
lean_object* v_abs_209_; lean_object* v_one_210_; lean_object* v_a_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint64_t v___x_215_; uint64_t v___x_216_; 
v_abs_209_ = lean_nat_abs(v_k_200_);
v_one_210_ = lean_unsigned_to_nat(1u);
v_a_211_ = lean_nat_sub(v_abs_209_, v_one_210_);
lean_dec(v_abs_209_);
v___x_212_ = lean_unsigned_to_nat(2u);
v___x_213_ = lean_nat_mul(v___x_212_, v_a_211_);
lean_dec(v_a_211_);
v___x_214_ = lean_nat_add(v___x_213_, v_one_210_);
lean_dec(v___x_213_);
v___x_215_ = lean_uint64_of_nat(v___x_214_);
lean_dec(v___x_214_);
v___x_216_ = lean_uint64_mix_hash(v___x_201_, v___x_215_);
return v___x_216_;
}
}
case 3:
{
lean_object* v_i_217_; uint64_t v___x_218_; uint64_t v___x_219_; uint64_t v___x_220_; 
v_i_217_ = lean_ctor_get(v_x_178_, 0);
v___x_218_ = 3ULL;
v___x_219_ = lean_uint64_of_nat(v_i_217_);
v___x_220_ = lean_uint64_mix_hash(v___x_218_, v___x_219_);
return v___x_220_;
}
case 4:
{
lean_object* v_a_221_; uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v___x_224_; 
v_a_221_ = lean_ctor_get(v_x_178_, 0);
v___x_222_ = 4ULL;
v___x_223_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_221_);
v___x_224_ = lean_uint64_mix_hash(v___x_222_, v___x_223_);
return v___x_224_;
}
case 5:
{
lean_object* v_a_225_; lean_object* v_b_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v___x_231_; 
v_a_225_ = lean_ctor_get(v_x_178_, 0);
v_b_226_ = lean_ctor_get(v_x_178_, 1);
v___x_227_ = 5ULL;
v___x_228_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_225_);
v___x_229_ = lean_uint64_mix_hash(v___x_227_, v___x_228_);
v___x_230_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_226_);
v___x_231_ = lean_uint64_mix_hash(v___x_229_, v___x_230_);
return v___x_231_;
}
case 6:
{
lean_object* v_a_232_; lean_object* v_b_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; 
v_a_232_ = lean_ctor_get(v_x_178_, 0);
v_b_233_ = lean_ctor_get(v_x_178_, 1);
v___x_234_ = 6ULL;
v___x_235_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_232_);
v___x_236_ = lean_uint64_mix_hash(v___x_234_, v___x_235_);
v___x_237_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_233_);
v___x_238_ = lean_uint64_mix_hash(v___x_236_, v___x_237_);
return v___x_238_;
}
case 7:
{
lean_object* v_a_239_; lean_object* v_b_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; 
v_a_239_ = lean_ctor_get(v_x_178_, 0);
v_b_240_ = lean_ctor_get(v_x_178_, 1);
v___x_241_ = 7ULL;
v___x_242_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_239_);
v___x_243_ = lean_uint64_mix_hash(v___x_241_, v___x_242_);
v___x_244_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_240_);
v___x_245_ = lean_uint64_mix_hash(v___x_243_, v___x_244_);
return v___x_245_;
}
default: 
{
lean_object* v_a_246_; lean_object* v_k_247_; uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v___x_252_; 
v_a_246_ = lean_ctor_get(v_x_178_, 0);
v_k_247_ = lean_ctor_get(v_x_178_, 1);
v___x_248_ = 8ULL;
v___x_249_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_246_);
v___x_250_ = lean_uint64_mix_hash(v___x_248_, v___x_249_);
v___x_251_ = lean_uint64_of_nat(v_k_247_);
v___x_252_ = lean_uint64_mix_hash(v___x_250_, v___x_251_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableExpr_hash___boxed(lean_object* v_x_253_){
_start:
{
uint64_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_x_253_);
lean_dec_ref(v_x_253_);
v_r_255_ = lean_box_uint64(v_res_254_);
return v_r_255_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(2u);
v___x_265_ = lean_nat_to_int(v___x_264_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = lean_nat_to_int(v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprExpr_repr(lean_object* v_x_316_, lean_object* v_prec_317_){
_start:
{
lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; 
switch(lean_obj_tag(v_x_316_))
{
case 0:
{
lean_object* v_k_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_359_; 
v_k_336_ = lean_ctor_get(v_x_316_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_359_ == 0)
{
v___x_338_ = v_x_316_;
v_isShared_339_ = v_isSharedCheck_359_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_k_336_);
lean_dec(v_x_316_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_359_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___y_341_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = lean_unsigned_to_nat(1024u);
v___x_356_ = lean_nat_dec_le(v___x_355_, v_prec_317_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_341_ = v___x_357_;
goto v___jp_340_;
}
else
{
lean_object* v___x_358_; 
v___x_358_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_341_ = v___x_358_;
goto v___jp_340_;
}
v___jp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_342_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__2));
v___x_343_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_344_ = lean_int_dec_lt(v_k_336_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_345_ = l_Int_repr(v_k_336_);
lean_dec(v_k_336_);
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 3);
lean_ctor_set(v___x_338_, 0, v___x_345_);
v___x_347_ = v___x_338_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
v___y_328_ = v___y_341_;
v___y_329_ = v___x_342_;
v___y_330_ = v___x_347_;
goto v___jp_327_;
}
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_349_ = lean_unsigned_to_nat(1024u);
v___x_350_ = l_Int_repr(v_k_336_);
lean_dec(v_k_336_);
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 3);
lean_ctor_set(v___x_338_, 0, v___x_350_);
v___x_352_ = v___x_338_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_354_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; 
v___x_353_ = l_Repr_addAppParen(v___x_352_, v___x_349_);
v___y_328_ = v___y_341_;
v___y_329_ = v___x_342_;
v___y_330_ = v___x_353_;
goto v___jp_327_;
}
}
}
}
}
case 1:
{
lean_object* v_k_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_380_; 
v_k_360_ = lean_ctor_get(v_x_316_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_380_ == 0)
{
v___x_362_ = v_x_316_;
v_isShared_363_ = v_isSharedCheck_380_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_k_360_);
lean_dec(v_x_316_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_380_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___y_365_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = lean_unsigned_to_nat(1024u);
v___x_377_ = lean_nat_dec_le(v___x_376_, v_prec_317_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
v___x_378_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_365_ = v___x_378_;
goto v___jp_364_;
}
else
{
lean_object* v___x_379_; 
v___x_379_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_365_ = v___x_379_;
goto v___jp_364_;
}
v___jp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_366_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__7));
v___x_367_ = l_Nat_reprFast(v_k_360_);
if (v_isShared_363_ == 0)
{
lean_ctor_set_tag(v___x_362_, 3);
lean_ctor_set(v___x_362_, 0, v___x_367_);
v___x_369_ = v___x_362_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_375_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_366_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_371_, 0, v___y_365_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = 0;
v___x_373_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set_uint8(v___x_373_, sizeof(void*)*1, v___x_372_);
v___x_374_ = l_Repr_addAppParen(v___x_373_, v_prec_317_);
return v___x_374_;
}
}
}
}
case 2:
{
lean_object* v_k_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_404_; 
v_k_381_ = lean_ctor_get(v_x_316_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_404_ == 0)
{
v___x_383_ = v_x_316_;
v_isShared_384_ = v_isSharedCheck_404_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_k_381_);
lean_dec(v_x_316_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_404_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___y_386_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = lean_unsigned_to_nat(1024u);
v___x_401_ = lean_nat_dec_le(v___x_400_, v_prec_317_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
v___x_402_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_386_ = v___x_402_;
goto v___jp_385_;
}
else
{
lean_object* v___x_403_; 
v___x_403_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_386_ = v___x_403_;
goto v___jp_385_;
}
v___jp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_387_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__10));
v___x_388_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_389_ = lean_int_dec_lt(v_k_381_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = l_Int_repr(v_k_381_);
lean_dec(v_k_381_);
if (v_isShared_384_ == 0)
{
lean_ctor_set_tag(v___x_383_, 3);
lean_ctor_set(v___x_383_, 0, v___x_390_);
v___x_392_ = v___x_383_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
v___y_319_ = v___y_386_;
v___y_320_ = v___x_387_;
v___y_321_ = v___x_392_;
goto v___jp_318_;
}
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_394_ = lean_unsigned_to_nat(1024u);
v___x_395_ = l_Int_repr(v_k_381_);
lean_dec(v_k_381_);
if (v_isShared_384_ == 0)
{
lean_ctor_set_tag(v___x_383_, 3);
lean_ctor_set(v___x_383_, 0, v___x_395_);
v___x_397_ = v___x_383_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_399_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; 
v___x_398_ = l_Repr_addAppParen(v___x_397_, v___x_394_);
v___y_319_ = v___y_386_;
v___y_320_ = v___x_387_;
v___y_321_ = v___x_398_;
goto v___jp_318_;
}
}
}
}
}
case 3:
{
lean_object* v_i_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_425_; 
v_i_405_ = lean_ctor_get(v_x_316_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_425_ == 0)
{
v___x_407_ = v_x_316_;
v_isShared_408_ = v_isSharedCheck_425_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_i_405_);
lean_dec(v_x_316_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_425_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___y_410_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(1024u);
v___x_422_ = lean_nat_dec_le(v___x_421_, v_prec_317_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_410_ = v___x_423_;
goto v___jp_409_;
}
else
{
lean_object* v___x_424_; 
v___x_424_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_410_ = v___x_424_;
goto v___jp_409_;
}
v___jp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_411_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__13));
v___x_412_ = l_Nat_reprFast(v_i_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_412_);
v___x_414_ = v___x_407_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_420_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_411_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_416_, 0, v___y_410_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = 0;
v___x_418_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*1, v___x_417_);
v___x_419_ = l_Repr_addAppParen(v___x_418_, v_prec_317_);
return v___x_419_;
}
}
}
}
case 4:
{
lean_object* v_a_426_; lean_object* v___x_427_; lean_object* v___y_429_; uint8_t v___x_437_; 
v_a_426_ = lean_ctor_get(v_x_316_, 0);
lean_inc_ref(v_a_426_);
lean_dec_ref(v_x_316_);
v___x_427_ = lean_unsigned_to_nat(1024u);
v___x_437_ = lean_nat_dec_le(v___x_427_, v_prec_317_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
v___x_438_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_429_ = v___x_438_;
goto v___jp_428_;
}
else
{
lean_object* v___x_439_; 
v___x_439_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_429_ = v___x_439_;
goto v___jp_428_;
}
v___jp_428_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_430_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__16));
v___x_431_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_426_, v___x_427_);
v___x_432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_433_, 0, v___y_429_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = 0;
v___x_435_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set_uint8(v___x_435_, sizeof(void*)*1, v___x_434_);
v___x_436_ = l_Repr_addAppParen(v___x_435_, v_prec_317_);
return v___x_436_;
}
}
case 5:
{
lean_object* v_a_440_; lean_object* v_b_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_464_; 
v_a_440_ = lean_ctor_get(v_x_316_, 0);
v_b_441_ = lean_ctor_get(v_x_316_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_464_ == 0)
{
v___x_443_ = v_x_316_;
v_isShared_444_ = v_isSharedCheck_464_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_b_441_);
lean_inc(v_a_440_);
lean_dec(v_x_316_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_464_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___y_447_; uint8_t v___x_461_; 
v___x_445_ = lean_unsigned_to_nat(1024u);
v___x_461_ = lean_nat_dec_le(v___x_445_, v_prec_317_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
v___x_462_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_447_ = v___x_462_;
goto v___jp_446_;
}
else
{
lean_object* v___x_463_; 
v___x_463_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_447_ = v___x_463_;
goto v___jp_446_;
}
v___jp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_448_ = lean_box(1);
v___x_449_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__19));
v___x_450_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_440_, v___x_445_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v___x_450_);
lean_ctor_set(v___x_443_, 0, v___x_449_);
v___x_452_ = v___x_443_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_450_);
v___x_452_ = v_reuseFailAlloc_460_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_448_);
v___x_454_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_441_, v___x_445_);
v___x_455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_456_, 0, v___y_447_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = 0;
v___x_458_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1, v___x_457_);
v___x_459_ = l_Repr_addAppParen(v___x_458_, v_prec_317_);
return v___x_459_;
}
}
}
}
case 6:
{
lean_object* v_a_465_; lean_object* v_b_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_489_; 
v_a_465_ = lean_ctor_get(v_x_316_, 0);
v_b_466_ = lean_ctor_get(v_x_316_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_489_ == 0)
{
v___x_468_ = v_x_316_;
v_isShared_469_ = v_isSharedCheck_489_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_b_466_);
lean_inc(v_a_465_);
lean_dec(v_x_316_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_489_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___y_472_; uint8_t v___x_486_; 
v___x_470_ = lean_unsigned_to_nat(1024u);
v___x_486_ = lean_nat_dec_le(v___x_470_, v_prec_317_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
v___x_487_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_472_ = v___x_487_;
goto v___jp_471_;
}
else
{
lean_object* v___x_488_; 
v___x_488_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_472_ = v___x_488_;
goto v___jp_471_;
}
v___jp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_473_ = lean_box(1);
v___x_474_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__22));
v___x_475_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_465_, v___x_470_);
if (v_isShared_469_ == 0)
{
lean_ctor_set_tag(v___x_468_, 5);
lean_ctor_set(v___x_468_, 1, v___x_475_);
lean_ctor_set(v___x_468_, 0, v___x_474_);
v___x_477_ = v___x_468_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_475_);
v___x_477_ = v_reuseFailAlloc_485_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___x_473_);
v___x_479_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_466_, v___x_470_);
v___x_480_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_481_, 0, v___y_472_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = 0;
v___x_483_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set_uint8(v___x_483_, sizeof(void*)*1, v___x_482_);
v___x_484_ = l_Repr_addAppParen(v___x_483_, v_prec_317_);
return v___x_484_;
}
}
}
}
case 7:
{
lean_object* v_a_490_; lean_object* v_b_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_514_; 
v_a_490_ = lean_ctor_get(v_x_316_, 0);
v_b_491_ = lean_ctor_get(v_x_316_, 1);
v_isSharedCheck_514_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_514_ == 0)
{
v___x_493_ = v_x_316_;
v_isShared_494_ = v_isSharedCheck_514_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_b_491_);
lean_inc(v_a_490_);
lean_dec(v_x_316_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_514_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___y_497_; uint8_t v___x_511_; 
v___x_495_ = lean_unsigned_to_nat(1024u);
v___x_511_ = lean_nat_dec_le(v___x_495_, v_prec_317_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; 
v___x_512_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_497_ = v___x_512_;
goto v___jp_496_;
}
else
{
lean_object* v___x_513_; 
v___x_513_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_497_ = v___x_513_;
goto v___jp_496_;
}
v___jp_496_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_498_ = lean_box(1);
v___x_499_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__25));
v___x_500_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_490_, v___x_495_);
if (v_isShared_494_ == 0)
{
lean_ctor_set_tag(v___x_493_, 5);
lean_ctor_set(v___x_493_, 1, v___x_500_);
lean_ctor_set(v___x_493_, 0, v___x_499_);
v___x_502_ = v___x_493_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_510_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v___x_498_);
v___x_504_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_491_, v___x_495_);
v___x_505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_503_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_506_, 0, v___y_497_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = 0;
v___x_508_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*1, v___x_507_);
v___x_509_ = l_Repr_addAppParen(v___x_508_, v_prec_317_);
return v___x_509_;
}
}
}
}
default: 
{
lean_object* v_a_515_; lean_object* v_k_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_540_; 
v_a_515_ = lean_ctor_get(v_x_316_, 0);
v_k_516_ = lean_ctor_get(v_x_316_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_540_ == 0)
{
v___x_518_ = v_x_316_;
v_isShared_519_ = v_isSharedCheck_540_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_k_516_);
lean_inc(v_a_515_);
lean_dec(v_x_316_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_540_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___y_522_; uint8_t v___x_537_; 
v___x_520_ = lean_unsigned_to_nat(1024u);
v___x_537_ = lean_nat_dec_le(v___x_520_, v_prec_317_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
v___x_538_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_522_ = v___x_538_;
goto v___jp_521_;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_522_ = v___x_539_;
goto v___jp_521_;
}
v___jp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_523_ = lean_box(1);
v___x_524_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__28));
v___x_525_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_515_, v___x_520_);
if (v_isShared_519_ == 0)
{
lean_ctor_set_tag(v___x_518_, 5);
lean_ctor_set(v___x_518_, 1, v___x_525_);
lean_ctor_set(v___x_518_, 0, v___x_524_);
v___x_527_ = v___x_518_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_525_);
v___x_527_ = v_reuseFailAlloc_536_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___x_523_);
v___x_529_ = l_Nat_reprFast(v_k_516_);
v___x_530_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
v___x_531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_528_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_532_, 0, v___y_522_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = 0;
v___x_534_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*1, v___x_533_);
v___x_535_ = l_Repr_addAppParen(v___x_534_, v_prec_317_);
return v___x_535_;
}
}
}
}
}
v___jp_318_:
{
lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_322_, 0, v___y_320_);
lean_ctor_set(v___x_322_, 1, v___y_321_);
v___x_323_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_323_, 0, v___y_319_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = 0;
v___x_325_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set_uint8(v___x_325_, sizeof(void*)*1, v___x_324_);
v___x_326_ = l_Repr_addAppParen(v___x_325_, v_prec_317_);
return v___x_326_;
}
v___jp_327_:
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_331_, 0, v___y_329_);
lean_ctor_set(v___x_331_, 1, v___y_330_);
v___x_332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_332_, 0, v___y_328_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = 0;
v___x_334_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*1, v___x_333_);
v___x_335_ = l_Repr_addAppParen(v___x_334_, v_prec_317_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___boxed(lean_object* v_x_541_, lean_object* v_prec_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_x_541_, v_prec_542_);
lean_dec(v_prec_542_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___redArg(lean_object* v_ctx_546_, lean_object* v_v_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_RArray_getImpl___redArg(v_ctx_546_, v_v_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___redArg___boxed(lean_object* v_ctx_549_, lean_object* v_v_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Grind_CommRing_Var_denote___redArg(v_ctx_549_, v_v_550_);
lean_dec(v_v_550_);
lean_dec_ref(v_ctx_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote(lean_object* v_00_u03b1_552_, lean_object* v_ctx_553_, lean_object* v_v_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_RArray_getImpl___redArg(v_ctx_553_, v_v_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___boxed(lean_object* v_00_u03b1_556_, lean_object* v_ctx_557_, lean_object* v_v_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Grind_CommRing_Var_denote(v_00_u03b1_556_, v_ctx_557_, v_v_558_);
lean_dec(v_v_558_);
lean_dec_ref(v_ctx_557_);
return v_res_559_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPower_beq(lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
lean_object* v_x_562_; lean_object* v_k_563_; lean_object* v_x_564_; lean_object* v_k_565_; uint8_t v___x_566_; 
v_x_562_ = lean_ctor_get(v_x_560_, 0);
v_k_563_ = lean_ctor_get(v_x_560_, 1);
v_x_564_ = lean_ctor_get(v_x_561_, 0);
v_k_565_ = lean_ctor_get(v_x_561_, 1);
v___x_566_ = lean_nat_dec_eq(v_x_562_, v_x_564_);
if (v___x_566_ == 0)
{
return v___x_566_;
}
else
{
uint8_t v___x_567_; 
v___x_567_ = lean_nat_dec_eq(v_k_563_, v_k_565_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPower_beq___boxed(lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
uint8_t v_res_570_; lean_object* v_r_571_; 
v_res_570_ = l_Lean_Grind_CommRing_instBEqPower_beq(v_x_568_, v_x_569_);
lean_dec_ref(v_x_569_);
lean_dec_ref(v_x_568_);
v_r_571_ = lean_box(v_res_570_);
return v_r_571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___redArg(lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_h__1_576_){
_start:
{
lean_object* v_x_577_; lean_object* v_k_578_; lean_object* v_x_579_; lean_object* v_k_580_; lean_object* v___x_581_; 
v_x_577_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_x_577_);
v_k_578_ = lean_ctor_get(v_x_574_, 1);
lean_inc(v_k_578_);
lean_dec_ref(v_x_574_);
v_x_579_ = lean_ctor_get(v_x_575_, 0);
lean_inc(v_x_579_);
v_k_580_ = lean_ctor_get(v_x_575_, 1);
lean_inc(v_k_580_);
lean_dec_ref(v_x_575_);
v___x_581_ = lean_apply_4(v_h__1_576_, v_x_577_, v_k_578_, v_x_579_, v_k_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter(lean_object* v_motive_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_h__1_585_, lean_object* v_h__2_586_){
_start:
{
lean_object* v_x_587_; lean_object* v_k_588_; lean_object* v_x_589_; lean_object* v_k_590_; lean_object* v___x_591_; 
v_x_587_ = lean_ctor_get(v_x_583_, 0);
lean_inc(v_x_587_);
v_k_588_ = lean_ctor_get(v_x_583_, 1);
lean_inc(v_k_588_);
lean_dec_ref(v_x_583_);
v_x_589_ = lean_ctor_get(v_x_584_, 0);
lean_inc(v_x_589_);
v_k_590_ = lean_ctor_get(v_x_584_, 1);
lean_inc(v_k_590_);
lean_dec_ref(v_x_584_);
v___x_591_ = lean_apply_4(v_h__1_585_, v_x_587_, v_k_588_, v_x_589_, v_k_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___boxed(lean_object* v_motive_592_, lean_object* v_x_593_, lean_object* v_x_594_, lean_object* v_h__1_595_, lean_object* v_h__2_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter(v_motive_592_, v_x_593_, v_x_594_, v_h__1_595_, v_h__2_596_);
lean_dec(v_h__2_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_instReprPower_repr_spec__0(lean_object* v_a_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_nat_to_int(v_a_598_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(5u);
v___x_614_ = lean_nat_to_int(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0));
v___x_623_ = lean_string_length(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13, &l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13_once, _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13);
v___x_625_ = lean_nat_to_int(v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg(lean_object* v_x_630_){
_start:
{
lean_object* v_x_631_; lean_object* v_k_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_666_; 
v_x_631_ = lean_ctor_get(v_x_630_, 0);
v_k_632_ = lean_ctor_get(v_x_630_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_630_);
if (v_isSharedCheck_666_ == 0)
{
v___x_634_ = v_x_630_;
v_isShared_635_ = v_isSharedCheck_666_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_k_632_);
lean_inc(v_x_631_);
lean_dec(v_x_630_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_666_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_636_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5));
v___x_637_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6));
v___x_638_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7, &l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7_once, _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7);
v___x_639_ = l_Nat_reprFast(v_x_631_);
v___x_640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 4);
lean_ctor_set(v___x_634_, 1, v___x_640_);
lean_ctor_set(v___x_634_, 0, v___x_638_);
v___x_642_ = v___x_634_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_640_);
v___x_642_ = v_reuseFailAlloc_665_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_643_ = 0;
v___x_644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set_uint8(v___x_644_, sizeof(void*)*1, v___x_643_);
v___x_645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_637_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9));
v___x_647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_box(1);
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11));
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_636_);
v___x_653_ = l_Nat_reprFast(v_k_632_);
v___x_654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
v___x_655_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_638_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*1, v___x_643_);
v___x_657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_652_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14, &l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14_once, _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14);
v___x_659_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15));
v___x_660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___x_657_);
v___x_661_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16));
v___x_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_658_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*1, v___x_643_);
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr(lean_object* v_x_667_, lean_object* v_prec_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg(v_x_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___boxed(lean_object* v_x_670_, lean_object* v_prec_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Grind_CommRing_instReprPower_repr(v_x_670_, v_prec_671_);
lean_dec(v_prec_671_);
return v_res_672_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePower_hash(lean_object* v_x_679_){
_start:
{
lean_object* v_x_680_; lean_object* v_k_681_; uint64_t v___x_682_; uint64_t v___x_683_; uint64_t v___x_684_; uint64_t v___x_685_; uint64_t v___x_686_; 
v_x_680_ = lean_ctor_get(v_x_679_, 0);
v_k_681_ = lean_ctor_get(v_x_679_, 1);
v___x_682_ = 0ULL;
v___x_683_ = lean_uint64_of_nat(v_x_680_);
v___x_684_ = lean_uint64_mix_hash(v___x_682_, v___x_683_);
v___x_685_ = lean_uint64_of_nat(v_k_681_);
v___x_686_ = lean_uint64_mix_hash(v___x_684_, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePower_hash___boxed(lean_object* v_x_687_){
_start:
{
uint64_t v_res_688_; lean_object* v_r_689_; 
v_res_688_ = l_Lean_Grind_CommRing_instHashablePower_hash(v_x_687_);
lean_dec_ref(v_x_687_);
v_r_689_ = lean_box_uint64(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_varLt(lean_object* v_p_u2081_692_, lean_object* v_p_u2082_693_){
_start:
{
lean_object* v_x_694_; lean_object* v_x_695_; uint8_t v___x_696_; 
v_x_694_ = lean_ctor_get(v_p_u2081_692_, 0);
v_x_695_ = lean_ctor_get(v_p_u2082_693_, 0);
v___x_696_ = l_Nat_blt(v_x_694_, v_x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_varLt___boxed(lean_object* v_p_u2081_697_, lean_object* v_p_u2082_698_){
_start:
{
uint8_t v_res_699_; lean_object* v_r_700_; 
v_res_699_ = l_Lean_Grind_CommRing_Power_varLt(v_p_u2081_697_, v_p_u2082_698_);
lean_dec_ref(v_p_u2082_698_);
lean_dec_ref(v_p_u2081_697_);
v_r_700_ = lean_box(v_res_699_);
return v_r_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg(lean_object* v_inst_701_, lean_object* v_ctx_702_, lean_object* v_x_703_){
_start:
{
lean_object* v_ofNat_704_; lean_object* v_npow_705_; lean_object* v_x_706_; lean_object* v_k_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_ofNat_704_ = lean_ctor_get(v_inst_701_, 3);
lean_inc(v_ofNat_704_);
v_npow_705_ = lean_ctor_get(v_inst_701_, 5);
lean_inc(v_npow_705_);
lean_dec_ref(v_inst_701_);
v_x_706_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_x_706_);
v_k_707_ = lean_ctor_get(v_x_703_, 1);
lean_inc(v_k_707_);
lean_dec_ref(v_x_703_);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_nat_dec_eq(v_k_707_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; uint8_t v___x_711_; 
lean_dec(v_ofNat_704_);
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = lean_nat_dec_eq(v_k_707_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = l_Lean_RArray_getImpl___redArg(v_ctx_702_, v_x_706_);
lean_dec(v_x_706_);
v___x_713_ = lean_apply_2(v_npow_705_, v___x_712_, v_k_707_);
return v___x_713_;
}
else
{
lean_object* v___x_714_; 
lean_dec(v_k_707_);
lean_dec(v_npow_705_);
v___x_714_ = l_Lean_RArray_getImpl___redArg(v_ctx_702_, v_x_706_);
lean_dec(v_x_706_);
return v___x_714_;
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec(v_k_707_);
lean_dec(v_x_706_);
lean_dec(v_npow_705_);
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_716_ = lean_apply_1(v_ofNat_704_, v___x_715_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg___boxed(lean_object* v_inst_717_, lean_object* v_ctx_718_, lean_object* v_x_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Grind_CommRing_Power_denote___redArg(v_inst_717_, v_ctx_718_, v_x_719_);
lean_dec_ref(v_ctx_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote(lean_object* v_00_u03b1_721_, lean_object* v_inst_722_, lean_object* v_ctx_723_, lean_object* v_x_724_){
_start:
{
lean_object* v_ofNat_725_; lean_object* v_npow_726_; lean_object* v_x_727_; lean_object* v_k_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_ofNat_725_ = lean_ctor_get(v_inst_722_, 3);
lean_inc(v_ofNat_725_);
v_npow_726_ = lean_ctor_get(v_inst_722_, 5);
lean_inc(v_npow_726_);
lean_dec_ref(v_inst_722_);
v_x_727_ = lean_ctor_get(v_x_724_, 0);
lean_inc(v_x_727_);
v_k_728_ = lean_ctor_get(v_x_724_, 1);
lean_inc(v_k_728_);
lean_dec_ref(v_x_724_);
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = lean_nat_dec_eq(v_k_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; uint8_t v___x_732_; 
lean_dec(v_ofNat_725_);
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = lean_nat_dec_eq(v_k_728_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = l_Lean_RArray_getImpl___redArg(v_ctx_723_, v_x_727_);
lean_dec(v_x_727_);
v___x_734_ = lean_apply_2(v_npow_726_, v___x_733_, v_k_728_);
return v___x_734_;
}
else
{
lean_object* v___x_735_; 
lean_dec(v_k_728_);
lean_dec(v_npow_726_);
v___x_735_ = l_Lean_RArray_getImpl___redArg(v_ctx_723_, v_x_727_);
lean_dec(v_x_727_);
return v___x_735_;
}
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec(v_k_728_);
lean_dec(v_x_727_);
lean_dec(v_npow_726_);
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_apply_1(v_ofNat_725_, v___x_736_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___boxed(lean_object* v_00_u03b1_738_, lean_object* v_inst_739_, lean_object* v_ctx_740_, lean_object* v_x_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Grind_CommRing_Power_denote(v_00_u03b1_738_, v_inst_739_, v_ctx_740_, v_x_741_);
lean_dec_ref(v_ctx_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx(lean_object* v_x_743_){
_start:
{
if (lean_obj_tag(v_x_743_) == 0)
{
lean_object* v___x_744_; 
v___x_744_ = lean_unsigned_to_nat(0u);
return v___x_744_;
}
else
{
lean_object* v___x_745_; 
v___x_745_ = lean_unsigned_to_nat(1u);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx___boxed(lean_object* v_x_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Grind_CommRing_Mon_ctorIdx(v_x_746_);
lean_dec(v_x_746_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___redArg(lean_object* v_t_748_, lean_object* v_k_749_){
_start:
{
if (lean_obj_tag(v_t_748_) == 0)
{
return v_k_749_;
}
else
{
lean_object* v_p_750_; lean_object* v_m_751_; lean_object* v___x_752_; 
v_p_750_ = lean_ctor_get(v_t_748_, 0);
lean_inc_ref(v_p_750_);
v_m_751_ = lean_ctor_get(v_t_748_, 1);
lean_inc(v_m_751_);
lean_dec_ref(v_t_748_);
v___x_752_ = lean_apply_2(v_k_749_, v_p_750_, v_m_751_);
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim(lean_object* v_motive_753_, lean_object* v_ctorIdx_754_, lean_object* v_t_755_, lean_object* v_h_756_, lean_object* v_k_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_755_, v_k_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___boxed(lean_object* v_motive_759_, lean_object* v_ctorIdx_760_, lean_object* v_t_761_, lean_object* v_h_762_, lean_object* v_k_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Grind_CommRing_Mon_ctorElim(v_motive_759_, v_ctorIdx_760_, v_t_761_, v_h_762_, v_k_763_);
lean_dec(v_ctorIdx_760_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim___redArg(lean_object* v_t_765_, lean_object* v_unit_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_765_, v_unit_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim(lean_object* v_motive_768_, lean_object* v_t_769_, lean_object* v_h_770_, lean_object* v_unit_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_769_, v_unit_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim___redArg(lean_object* v_t_773_, lean_object* v_mult_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_773_, v_mult_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim(lean_object* v_motive_776_, lean_object* v_t_777_, lean_object* v_h_778_, lean_object* v_mult_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_777_, v_mult_779_);
return v___x_780_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqMon_beq(lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
if (lean_obj_tag(v_x_781_) == 0)
{
if (lean_obj_tag(v_x_782_) == 0)
{
uint8_t v___x_783_; 
v___x_783_ = 1;
return v___x_783_;
}
else
{
uint8_t v___x_784_; 
v___x_784_ = 0;
return v___x_784_;
}
}
else
{
if (lean_obj_tag(v_x_782_) == 1)
{
lean_object* v_p_785_; lean_object* v_m_786_; lean_object* v_p_787_; lean_object* v_m_788_; uint8_t v___x_789_; 
v_p_785_ = lean_ctor_get(v_x_781_, 0);
v_m_786_ = lean_ctor_get(v_x_781_, 1);
v_p_787_ = lean_ctor_get(v_x_782_, 0);
v_m_788_ = lean_ctor_get(v_x_782_, 1);
v___x_789_ = l_Lean_Grind_CommRing_instBEqPower_beq(v_p_785_, v_p_787_);
if (v___x_789_ == 0)
{
return v___x_789_;
}
else
{
v_x_781_ = v_m_786_;
v_x_782_ = v_m_788_;
goto _start;
}
}
else
{
uint8_t v___x_791_; 
v___x_791_ = 0;
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqMon_beq___boxed(lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
uint8_t v_res_794_; lean_object* v_r_795_; 
v_res_794_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_x_792_, v_x_793_);
lean_dec(v_x_793_);
lean_dec(v_x_792_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter___redArg(lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_h__1_800_, lean_object* v_h__2_801_, lean_object* v_h__3_802_){
_start:
{
if (lean_obj_tag(v_x_798_) == 0)
{
lean_dec(v_h__2_801_);
if (lean_obj_tag(v_x_799_) == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v_h__3_802_);
v___x_803_ = lean_box(0);
v___x_804_ = lean_apply_1(v_h__1_800_, v___x_803_);
return v___x_804_;
}
else
{
lean_object* v___x_805_; 
lean_dec(v_h__1_800_);
v___x_805_ = lean_apply_4(v_h__3_802_, v_x_798_, v_x_799_, lean_box(0), lean_box(0));
return v___x_805_;
}
}
else
{
lean_dec(v_h__1_800_);
if (lean_obj_tag(v_x_799_) == 1)
{
lean_object* v_p_806_; lean_object* v_m_807_; lean_object* v_p_808_; lean_object* v_m_809_; lean_object* v___x_810_; 
lean_dec(v_h__3_802_);
v_p_806_ = lean_ctor_get(v_x_798_, 0);
lean_inc_ref(v_p_806_);
v_m_807_ = lean_ctor_get(v_x_798_, 1);
lean_inc(v_m_807_);
lean_dec_ref(v_x_798_);
v_p_808_ = lean_ctor_get(v_x_799_, 0);
lean_inc_ref(v_p_808_);
v_m_809_ = lean_ctor_get(v_x_799_, 1);
lean_inc(v_m_809_);
lean_dec_ref(v_x_799_);
v___x_810_ = lean_apply_4(v_h__2_801_, v_p_806_, v_m_807_, v_p_808_, v_m_809_);
return v___x_810_;
}
else
{
lean_object* v___x_811_; 
lean_dec(v_h__2_801_);
v___x_811_ = lean_apply_4(v_h__3_802_, v_x_798_, v_x_799_, lean_box(0), lean_box(0));
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter(lean_object* v_motive_812_, lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_h__1_815_, lean_object* v_h__2_816_, lean_object* v_h__3_817_){
_start:
{
if (lean_obj_tag(v_x_813_) == 0)
{
lean_dec(v_h__2_816_);
if (lean_obj_tag(v_x_814_) == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec(v_h__3_817_);
v___x_818_ = lean_box(0);
v___x_819_ = lean_apply_1(v_h__1_815_, v___x_818_);
return v___x_819_;
}
else
{
lean_object* v___x_820_; 
lean_dec(v_h__1_815_);
v___x_820_ = lean_apply_4(v_h__3_817_, v_x_813_, v_x_814_, lean_box(0), lean_box(0));
return v___x_820_;
}
}
else
{
lean_dec(v_h__1_815_);
if (lean_obj_tag(v_x_814_) == 1)
{
lean_object* v_p_821_; lean_object* v_m_822_; lean_object* v_p_823_; lean_object* v_m_824_; lean_object* v___x_825_; 
lean_dec(v_h__3_817_);
v_p_821_ = lean_ctor_get(v_x_813_, 0);
lean_inc_ref(v_p_821_);
v_m_822_ = lean_ctor_get(v_x_813_, 1);
lean_inc(v_m_822_);
lean_dec_ref(v_x_813_);
v_p_823_ = lean_ctor_get(v_x_814_, 0);
lean_inc_ref(v_p_823_);
v_m_824_ = lean_ctor_get(v_x_814_, 1);
lean_inc(v_m_824_);
lean_dec_ref(v_x_814_);
v___x_825_ = lean_apply_4(v_h__2_816_, v_p_821_, v_m_822_, v_p_823_, v_m_824_);
return v___x_825_;
}
else
{
lean_object* v___x_826_; 
lean_dec(v_h__2_816_);
v___x_826_ = lean_apply_4(v_h__3_817_, v_x_813_, v_x_814_, lean_box(0), lean_box(0));
return v___x_826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr(lean_object* v_x_836_, lean_object* v_prec_837_){
_start:
{
lean_object* v___y_839_; 
if (lean_obj_tag(v_x_836_) == 0)
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = lean_unsigned_to_nat(1024u);
v___x_846_ = lean_nat_dec_le(v___x_845_, v_prec_837_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
v___x_847_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_839_ = v___x_847_;
goto v___jp_838_;
}
else
{
lean_object* v___x_848_; 
v___x_848_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_839_ = v___x_848_;
goto v___jp_838_;
}
}
else
{
lean_object* v_p_849_; lean_object* v_m_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_873_; 
v_p_849_ = lean_ctor_get(v_x_836_, 0);
v_m_850_ = lean_ctor_get(v_x_836_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_x_836_);
if (v_isSharedCheck_873_ == 0)
{
v___x_852_ = v_x_836_;
v_isShared_853_ = v_isSharedCheck_873_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_m_850_);
lean_inc(v_p_849_);
lean_dec(v_x_836_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_873_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___y_856_; uint8_t v___x_870_; 
v___x_854_ = lean_unsigned_to_nat(1024u);
v___x_870_ = lean_nat_dec_le(v___x_854_, v_prec_837_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
v___x_871_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_856_ = v___x_871_;
goto v___jp_855_;
}
else
{
lean_object* v___x_872_; 
v___x_872_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_856_ = v___x_872_;
goto v___jp_855_;
}
v___jp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_857_ = lean_box(1);
v___x_858_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprMon_repr___closed__4));
v___x_859_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg(v_p_849_);
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 5);
lean_ctor_set(v___x_852_, 1, v___x_859_);
lean_ctor_set(v___x_852_, 0, v___x_858_);
v___x_861_ = v___x_852_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_869_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v___x_857_);
v___x_863_ = l_Lean_Grind_CommRing_instReprMon_repr(v_m_850_, v___x_854_);
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_865_, 0, v___y_856_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = 0;
v___x_867_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*1, v___x_866_);
v___x_868_ = l_Repr_addAppParen(v___x_867_, v_prec_837_);
return v___x_868_;
}
}
}
}
v___jp_838_:
{
lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_840_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprMon_repr___closed__1));
v___x_841_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_841_, 0, v___y_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = 0;
v___x_843_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_843_, 0, v___x_841_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*1, v___x_842_);
v___x_844_ = l_Repr_addAppParen(v___x_843_, v_prec_837_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr___boxed(lean_object* v_x_874_, lean_object* v_prec_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Grind_CommRing_instReprMon_repr(v_x_874_, v_prec_875_);
lean_dec(v_prec_875_);
return v_res_876_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedMon_default(void){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = lean_box(0);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedMon(void){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = lean_box(0);
return v___x_880_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashableMon_hash(lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
uint64_t v___x_882_; 
v___x_882_ = 0ULL;
return v___x_882_;
}
else
{
lean_object* v_p_883_; lean_object* v_m_884_; uint64_t v___x_885_; uint64_t v___x_886_; uint64_t v___x_887_; uint64_t v___x_888_; uint64_t v___x_889_; 
v_p_883_ = lean_ctor_get(v_x_881_, 0);
v_m_884_ = lean_ctor_get(v_x_881_, 1);
v___x_885_ = 1ULL;
v___x_886_ = l_Lean_Grind_CommRing_instHashablePower_hash(v_p_883_);
v___x_887_ = lean_uint64_mix_hash(v___x_885_, v___x_886_);
v___x_888_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_m_884_);
v___x_889_ = lean_uint64_mix_hash(v___x_887_, v___x_888_);
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableMon_hash___boxed(lean_object* v_x_890_){
_start:
{
uint64_t v_res_891_; lean_object* v_r_892_; 
v_res_891_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_x_890_);
lean_dec(v_x_890_);
v_r_892_ = lean_box_uint64(v_res_891_);
return v_r_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg(lean_object* v_inst_895_, lean_object* v_ctx_896_, lean_object* v_x_897_){
_start:
{
if (lean_obj_tag(v_x_897_) == 0)
{
lean_object* v_ofNat_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_ofNat_898_ = lean_ctor_get(v_inst_895_, 3);
lean_inc(v_ofNat_898_);
lean_dec_ref(v_inst_895_);
v___x_899_ = lean_unsigned_to_nat(1u);
v___x_900_ = lean_apply_1(v_ofNat_898_, v___x_899_);
return v___x_900_;
}
else
{
lean_object* v_toMul_901_; lean_object* v_ofNat_902_; lean_object* v_npow_903_; lean_object* v_p_904_; lean_object* v_m_905_; lean_object* v___y_907_; lean_object* v_x_910_; lean_object* v_k_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v_toMul_901_ = lean_ctor_get(v_inst_895_, 1);
lean_inc(v_toMul_901_);
v_ofNat_902_ = lean_ctor_get(v_inst_895_, 3);
v_npow_903_ = lean_ctor_get(v_inst_895_, 5);
v_p_904_ = lean_ctor_get(v_x_897_, 0);
lean_inc_ref(v_p_904_);
v_m_905_ = lean_ctor_get(v_x_897_, 1);
lean_inc(v_m_905_);
lean_dec_ref(v_x_897_);
v_x_910_ = lean_ctor_get(v_p_904_, 0);
lean_inc(v_x_910_);
v_k_911_ = lean_ctor_get(v_p_904_, 1);
lean_inc(v_k_911_);
lean_dec_ref(v_p_904_);
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = lean_nat_dec_eq(v_k_911_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_nat_dec_eq(v_k_911_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = l_Lean_RArray_getImpl___redArg(v_ctx_896_, v_x_910_);
lean_dec(v_x_910_);
lean_inc(v_npow_903_);
v___x_917_ = lean_apply_2(v_npow_903_, v___x_916_, v_k_911_);
v___y_907_ = v___x_917_;
goto v___jp_906_;
}
else
{
lean_object* v___x_918_; 
lean_dec(v_k_911_);
v___x_918_ = l_Lean_RArray_getImpl___redArg(v_ctx_896_, v_x_910_);
lean_dec(v_x_910_);
v___y_907_ = v___x_918_;
goto v___jp_906_;
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_k_911_);
lean_dec(v_x_910_);
v___x_919_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_902_);
v___x_920_ = lean_apply_1(v_ofNat_902_, v___x_919_);
v___y_907_ = v___x_920_;
goto v___jp_906_;
}
v___jp_906_:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_895_, v_ctx_896_, v_m_905_);
v___x_909_ = lean_apply_2(v_toMul_901_, v___y_907_, v___x_908_);
return v___x_909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg___boxed(lean_object* v_inst_921_, lean_object* v_ctx_922_, lean_object* v_x_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_921_, v_ctx_922_, v_x_923_);
lean_dec_ref(v_ctx_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote(lean_object* v_00_u03b1_925_, lean_object* v_inst_926_, lean_object* v_ctx_927_, lean_object* v_x_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_926_, v_ctx_927_, v_x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___boxed(lean_object* v_00_u03b1_930_, lean_object* v_inst_931_, lean_object* v_ctx_932_, lean_object* v_x_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_Grind_CommRing_Mon_denote(v_00_u03b1_930_, v_inst_931_, v_ctx_932_, v_x_933_);
lean_dec_ref(v_ctx_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(lean_object* v_inst_935_, lean_object* v_ctx_936_, lean_object* v_m_937_, lean_object* v_acc_938_){
_start:
{
if (lean_obj_tag(v_m_937_) == 0)
{
lean_dec_ref(v_inst_935_);
return v_acc_938_;
}
else
{
lean_object* v_toMul_939_; lean_object* v_ofNat_940_; lean_object* v_npow_941_; lean_object* v_p_942_; lean_object* v_m_943_; lean_object* v___y_945_; lean_object* v_x_948_; lean_object* v_k_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_toMul_939_ = lean_ctor_get(v_inst_935_, 1);
v_ofNat_940_ = lean_ctor_get(v_inst_935_, 3);
v_npow_941_ = lean_ctor_get(v_inst_935_, 5);
v_p_942_ = lean_ctor_get(v_m_937_, 0);
lean_inc_ref(v_p_942_);
v_m_943_ = lean_ctor_get(v_m_937_, 1);
lean_inc(v_m_943_);
lean_dec_ref(v_m_937_);
v_x_948_ = lean_ctor_get(v_p_942_, 0);
lean_inc(v_x_948_);
v_k_949_ = lean_ctor_get(v_p_942_, 1);
lean_inc(v_k_949_);
lean_dec_ref(v_p_942_);
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_nat_dec_eq(v_k_949_, v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = lean_nat_dec_eq(v_k_949_, v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = l_Lean_RArray_getImpl___redArg(v_ctx_936_, v_x_948_);
lean_dec(v_x_948_);
lean_inc(v_npow_941_);
v___x_955_ = lean_apply_2(v_npow_941_, v___x_954_, v_k_949_);
v___y_945_ = v___x_955_;
goto v___jp_944_;
}
else
{
lean_object* v___x_956_; 
lean_dec(v_k_949_);
v___x_956_ = l_Lean_RArray_getImpl___redArg(v_ctx_936_, v_x_948_);
lean_dec(v_x_948_);
v___y_945_ = v___x_956_;
goto v___jp_944_;
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_k_949_);
lean_dec(v_x_948_);
v___x_957_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_940_);
v___x_958_ = lean_apply_1(v_ofNat_940_, v___x_957_);
v___y_945_ = v___x_958_;
goto v___jp_944_;
}
v___jp_944_:
{
lean_object* v___x_946_; 
lean_inc(v_toMul_939_);
v___x_946_ = lean_apply_2(v_toMul_939_, v_acc_938_, v___y_945_);
v_m_937_ = v_m_943_;
v_acc_938_ = v___x_946_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg___boxed(lean_object* v_inst_959_, lean_object* v_ctx_960_, lean_object* v_m_961_, lean_object* v_acc_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_959_, v_ctx_960_, v_m_961_, v_acc_962_);
lean_dec_ref(v_ctx_960_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go(lean_object* v_00_u03b1_964_, lean_object* v_inst_965_, lean_object* v_ctx_966_, lean_object* v_m_967_, lean_object* v_acc_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_965_, v_ctx_966_, v_m_967_, v_acc_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___boxed(lean_object* v_00_u03b1_970_, lean_object* v_inst_971_, lean_object* v_ctx_972_, lean_object* v_m_973_, lean_object* v_acc_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Grind_CommRing_Mon_denote_x27_go(v_00_u03b1_970_, v_inst_971_, v_ctx_972_, v_m_973_, v_acc_974_);
lean_dec_ref(v_ctx_972_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg(lean_object* v_inst_976_, lean_object* v_ctx_977_, lean_object* v_m_978_){
_start:
{
if (lean_obj_tag(v_m_978_) == 0)
{
lean_object* v_ofNat_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_ofNat_979_ = lean_ctor_get(v_inst_976_, 3);
lean_inc(v_ofNat_979_);
lean_dec_ref(v_inst_976_);
v___x_980_ = lean_unsigned_to_nat(1u);
v___x_981_ = lean_apply_1(v_ofNat_979_, v___x_980_);
return v___x_981_;
}
else
{
lean_object* v_p_982_; lean_object* v_m_983_; lean_object* v_ofNat_984_; lean_object* v_npow_985_; lean_object* v_x_986_; lean_object* v_k_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v_p_982_ = lean_ctor_get(v_m_978_, 0);
lean_inc_ref(v_p_982_);
v_m_983_ = lean_ctor_get(v_m_978_, 1);
lean_inc(v_m_983_);
lean_dec_ref(v_m_978_);
v_ofNat_984_ = lean_ctor_get(v_inst_976_, 3);
v_npow_985_ = lean_ctor_get(v_inst_976_, 5);
v_x_986_ = lean_ctor_get(v_p_982_, 0);
lean_inc(v_x_986_);
v_k_987_ = lean_ctor_get(v_p_982_, 1);
lean_inc(v_k_987_);
lean_dec_ref(v_p_982_);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_nat_dec_eq(v_k_987_, v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_dec_eq(v_k_987_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = l_Lean_RArray_getImpl___redArg(v_ctx_977_, v_x_986_);
lean_dec(v_x_986_);
lean_inc(v_npow_985_);
v___x_993_ = lean_apply_2(v_npow_985_, v___x_992_, v_k_987_);
v___x_994_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_976_, v_ctx_977_, v_m_983_, v___x_993_);
return v___x_994_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec(v_k_987_);
v___x_995_ = l_Lean_RArray_getImpl___redArg(v_ctx_977_, v_x_986_);
lean_dec(v_x_986_);
v___x_996_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_976_, v_ctx_977_, v_m_983_, v___x_995_);
return v___x_996_;
}
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec(v_k_987_);
lean_dec(v_x_986_);
v___x_997_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_984_);
v___x_998_ = lean_apply_1(v_ofNat_984_, v___x_997_);
v___x_999_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_976_, v_ctx_977_, v_m_983_, v___x_998_);
return v___x_999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg___boxed(lean_object* v_inst_1000_, lean_object* v_ctx_1001_, lean_object* v_m_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_Grind_CommRing_Mon_denote_x27___redArg(v_inst_1000_, v_ctx_1001_, v_m_1002_);
lean_dec_ref(v_ctx_1001_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27(lean_object* v_00_u03b1_1004_, lean_object* v_inst_1005_, lean_object* v_ctx_1006_, lean_object* v_m_1007_){
_start:
{
if (lean_obj_tag(v_m_1007_) == 0)
{
lean_object* v_ofNat_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_ofNat_1008_ = lean_ctor_get(v_inst_1005_, 3);
lean_inc(v_ofNat_1008_);
lean_dec_ref(v_inst_1005_);
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_apply_1(v_ofNat_1008_, v___x_1009_);
return v___x_1010_;
}
else
{
lean_object* v_p_1011_; lean_object* v_m_1012_; lean_object* v_ofNat_1013_; lean_object* v_npow_1014_; lean_object* v_x_1015_; lean_object* v_k_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_p_1011_ = lean_ctor_get(v_m_1007_, 0);
lean_inc_ref(v_p_1011_);
v_m_1012_ = lean_ctor_get(v_m_1007_, 1);
lean_inc(v_m_1012_);
lean_dec_ref(v_m_1007_);
v_ofNat_1013_ = lean_ctor_get(v_inst_1005_, 3);
v_npow_1014_ = lean_ctor_get(v_inst_1005_, 5);
v_x_1015_ = lean_ctor_get(v_p_1011_, 0);
lean_inc(v_x_1015_);
v_k_1016_ = lean_ctor_get(v_p_1011_, 1);
lean_inc(v_k_1016_);
lean_dec_ref(v_p_1011_);
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = lean_nat_dec_eq(v_k_1016_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_nat_dec_eq(v_k_1016_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = l_Lean_RArray_getImpl___redArg(v_ctx_1006_, v_x_1015_);
lean_dec(v_x_1015_);
lean_inc(v_npow_1014_);
v___x_1022_ = lean_apply_2(v_npow_1014_, v___x_1021_, v_k_1016_);
v___x_1023_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_1005_, v_ctx_1006_, v_m_1012_, v___x_1022_);
return v___x_1023_;
}
else
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_dec(v_k_1016_);
v___x_1024_ = l_Lean_RArray_getImpl___redArg(v_ctx_1006_, v_x_1015_);
lean_dec(v_x_1015_);
v___x_1025_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_1005_, v_ctx_1006_, v_m_1012_, v___x_1024_);
return v___x_1025_;
}
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec(v_k_1016_);
lean_dec(v_x_1015_);
v___x_1026_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_1013_);
v___x_1027_ = lean_apply_1(v_ofNat_1013_, v___x_1026_);
v___x_1028_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_1005_, v_ctx_1006_, v_m_1012_, v___x_1027_);
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___boxed(lean_object* v_00_u03b1_1029_, lean_object* v_inst_1030_, lean_object* v_ctx_1031_, lean_object* v_m_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Grind_CommRing_Mon_denote_x27(v_00_u03b1_1029_, v_inst_1030_, v_ctx_1031_, v_m_1032_);
lean_dec_ref(v_ctx_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ofVar(lean_object* v_x_1034_){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v_x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_box(0);
v___x_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat(lean_object* v_m_u2081_1039_, lean_object* v_m_u2082_1040_){
_start:
{
if (lean_obj_tag(v_m_u2081_1039_) == 0)
{
lean_inc(v_m_u2082_1040_);
return v_m_u2082_1040_;
}
else
{
lean_object* v_p_1041_; lean_object* v_m_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1050_; 
v_p_1041_ = lean_ctor_get(v_m_u2081_1039_, 0);
v_m_1042_ = lean_ctor_get(v_m_u2081_1039_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_m_u2081_1039_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1044_ = v_m_u2081_1039_;
v_isShared_1045_ = v_isSharedCheck_1050_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_m_1042_);
lean_inc(v_p_1041_);
lean_dec(v_m_u2081_1039_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1050_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = l_Lean_Grind_CommRing_Mon_concat(v_m_1042_, v_m_u2082_1040_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 1, v___x_1046_);
v___x_1048_ = v___x_1044_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_p_1041_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat___boxed(lean_object* v_m_u2081_1051_, lean_object* v_m_u2082_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_1051_, v_m_u2082_1052_);
lean_dec(v_m_u2082_1052_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow(lean_object* v_pw_1054_, lean_object* v_m_1055_){
_start:
{
if (lean_obj_tag(v_m_1055_) == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_pw_1054_);
lean_ctor_set(v___x_1056_, 1, v_m_1055_);
return v___x_1056_;
}
else
{
lean_object* v_p_1057_; lean_object* v_m_1058_; uint8_t v___x_1059_; 
v_p_1057_ = lean_ctor_get(v_m_1055_, 0);
lean_inc_ref(v_p_1057_);
v_m_1058_ = lean_ctor_get(v_m_1055_, 1);
v___x_1059_ = l_Lean_Grind_CommRing_Power_varLt(v_pw_1054_, v_p_1057_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1083_; 
lean_inc(v_m_1058_);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_m_1055_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; lean_object* v_unused_1085_; 
v_unused_1084_ = lean_ctor_get(v_m_1055_, 1);
lean_dec(v_unused_1084_);
v_unused_1085_ = lean_ctor_get(v_m_1055_, 0);
lean_dec(v_unused_1085_);
v___x_1061_ = v_m_1055_;
v_isShared_1062_ = v_isSharedCheck_1083_;
goto v_resetjp_1060_;
}
else
{
lean_dec(v_m_1055_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1083_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
uint8_t v___x_1063_; 
v___x_1063_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1057_, v_pw_1054_);
if (v___x_1063_ == 0)
{
lean_object* v_x_1064_; lean_object* v_k_1065_; lean_object* v_k_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1077_; 
v_x_1064_ = lean_ctor_get(v_pw_1054_, 0);
lean_inc(v_x_1064_);
v_k_1065_ = lean_ctor_get(v_pw_1054_, 1);
lean_inc(v_k_1065_);
lean_dec_ref(v_pw_1054_);
v_k_1066_ = lean_ctor_get(v_p_1057_, 1);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_p_1057_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v_p_1057_, 0);
lean_dec(v_unused_1078_);
v___x_1068_ = v_p_1057_;
v_isShared_1069_ = v_isSharedCheck_1077_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_k_1066_);
lean_dec(v_p_1057_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1077_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1070_ = lean_nat_add(v_k_1065_, v_k_1066_);
lean_dec(v_k_1066_);
lean_dec(v_k_1065_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 1, v___x_1070_);
lean_ctor_set(v___x_1068_, 0, v_x_1064_);
v___x_1072_ = v___x_1068_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_x_1064_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1074_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1072_);
v___x_1074_ = v___x_1061_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_m_1058_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = l_Lean_Grind_CommRing_Mon_mulPow(v_pw_1054_, v_m_1058_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v___x_1079_);
v___x_1081_ = v___x_1061_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_p_1057_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
else
{
lean_object* v___x_1086_; 
lean_dec_ref(v_p_1057_);
v___x_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_pw_1054_);
lean_ctor_set(v___x_1086_, 1, v_m_1055_);
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow__nc(lean_object* v_pw_1087_, lean_object* v_m_1088_){
_start:
{
if (lean_obj_tag(v_m_1088_) == 0)
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1089_, 0, v_pw_1087_);
lean_ctor_set(v___x_1089_, 1, v_m_1088_);
return v___x_1089_;
}
else
{
lean_object* v_p_1090_; lean_object* v_m_1091_; lean_object* v_x_1092_; lean_object* v_k_1093_; lean_object* v_x_1094_; lean_object* v_k_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1114_; 
v_p_1090_ = lean_ctor_get(v_m_1088_, 0);
lean_inc_ref(v_p_1090_);
v_m_1091_ = lean_ctor_get(v_m_1088_, 1);
v_x_1092_ = lean_ctor_get(v_pw_1087_, 0);
v_k_1093_ = lean_ctor_get(v_pw_1087_, 1);
v_x_1094_ = lean_ctor_get(v_p_1090_, 0);
v_k_1095_ = lean_ctor_get(v_p_1090_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_p_1090_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1097_ = v_p_1090_;
v_isShared_1098_ = v_isSharedCheck_1114_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_k_1095_);
lean_inc(v_x_1094_);
lean_dec(v_p_1090_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1114_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
uint8_t v___x_1099_; 
v___x_1099_ = lean_nat_dec_eq(v_x_1092_, v_x_1094_);
lean_dec(v_x_1094_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
lean_del_object(v___x_1097_);
lean_dec(v_k_1095_);
v___x_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1100_, 0, v_pw_1087_);
lean_ctor_set(v___x_1100_, 1, v_m_1088_);
return v___x_1100_;
}
else
{
lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1111_; 
lean_inc(v_k_1093_);
lean_inc(v_x_1092_);
lean_inc(v_m_1091_);
lean_dec_ref(v_pw_1087_);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_m_1088_);
if (v_isSharedCheck_1111_ == 0)
{
lean_object* v_unused_1112_; lean_object* v_unused_1113_; 
v_unused_1112_ = lean_ctor_get(v_m_1088_, 1);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v_m_1088_, 0);
lean_dec(v_unused_1113_);
v___x_1102_ = v_m_1088_;
v_isShared_1103_ = v_isSharedCheck_1111_;
goto v_resetjp_1101_;
}
else
{
lean_dec(v_m_1088_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1111_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1104_ = lean_nat_add(v_k_1093_, v_k_1095_);
lean_dec(v_k_1095_);
lean_dec(v_k_1093_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 1, v___x_1104_);
lean_ctor_set(v___x_1097_, 0, v_x_1092_);
v___x_1106_ = v___x_1097_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_x_1092_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1108_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1106_);
v___x_1108_ = v___x_1102_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_m_1091_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length(lean_object* v_x_1115_){
_start:
{
if (lean_obj_tag(v_x_1115_) == 0)
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_unsigned_to_nat(0u);
return v___x_1116_;
}
else
{
lean_object* v_m_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_m_1117_ = lean_ctor_get(v_x_1115_, 1);
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = l_Lean_Grind_CommRing_Mon_length(v_m_1117_);
v___x_1120_ = lean_nat_add(v___x_1118_, v___x_1119_);
lean_dec(v___x_1119_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length___boxed(lean_object* v_x_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Grind_CommRing_Mon_length(v_x_1121_);
lean_dec(v_x_1121_);
return v_res_1122_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_hugeFuel(void){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_unsigned_to_nat(1000000u);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go(lean_object* v_fuel_1124_, lean_object* v_m_u2081_1125_, lean_object* v_m_u2082_1126_){
_start:
{
lean_object* v_zero_1127_; uint8_t v_isZero_1128_; 
v_zero_1127_ = lean_unsigned_to_nat(0u);
v_isZero_1128_ = lean_nat_dec_eq(v_fuel_1124_, v_zero_1127_);
if (v_isZero_1128_ == 1)
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_1125_, v_m_u2082_1126_);
lean_dec(v_m_u2082_1126_);
return v___x_1129_;
}
else
{
if (lean_obj_tag(v_m_u2082_1126_) == 0)
{
return v_m_u2081_1125_;
}
else
{
if (lean_obj_tag(v_m_u2081_1125_) == 0)
{
return v_m_u2082_1126_;
}
else
{
lean_object* v_p_1130_; lean_object* v_m_1131_; lean_object* v_p_1132_; lean_object* v_m_1133_; lean_object* v_one_1134_; lean_object* v_n_1135_; uint8_t v___x_1136_; 
v_p_1130_ = lean_ctor_get(v_m_u2082_1126_, 0);
lean_inc_ref(v_p_1130_);
v_m_1131_ = lean_ctor_get(v_m_u2082_1126_, 1);
v_p_1132_ = lean_ctor_get(v_m_u2081_1125_, 0);
v_m_1133_ = lean_ctor_get(v_m_u2081_1125_, 1);
v_one_1134_ = lean_unsigned_to_nat(1u);
v_n_1135_ = lean_nat_sub(v_fuel_1124_, v_one_1134_);
v___x_1136_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1132_, v_p_1130_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1167_; 
lean_inc(v_m_1131_);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_m_u2082_1126_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; lean_object* v_unused_1169_; 
v_unused_1168_ = lean_ctor_get(v_m_u2082_1126_, 1);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_m_u2082_1126_, 0);
lean_dec(v_unused_1169_);
v___x_1138_ = v_m_u2082_1126_;
v_isShared_1139_ = v_isSharedCheck_1167_;
goto v_resetjp_1137_;
}
else
{
lean_dec(v_m_u2082_1126_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1167_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
uint8_t v___x_1140_; 
v___x_1140_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1130_, v_p_1132_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1160_; 
lean_inc(v_m_1133_);
lean_inc_ref(v_p_1132_);
lean_del_object(v___x_1138_);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_m_u2081_1125_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; lean_object* v_unused_1162_; 
v_unused_1161_ = lean_ctor_get(v_m_u2081_1125_, 1);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v_m_u2081_1125_, 0);
lean_dec(v_unused_1162_);
v___x_1142_ = v_m_u2081_1125_;
v_isShared_1143_ = v_isSharedCheck_1160_;
goto v_resetjp_1141_;
}
else
{
lean_dec(v_m_u2081_1125_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1160_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_x_1144_; lean_object* v_k_1145_; lean_object* v_k_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1158_; 
v_x_1144_ = lean_ctor_get(v_p_1132_, 0);
lean_inc(v_x_1144_);
v_k_1145_ = lean_ctor_get(v_p_1132_, 1);
lean_inc(v_k_1145_);
lean_dec_ref(v_p_1132_);
v_k_1146_ = lean_ctor_get(v_p_1130_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_p_1130_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v_p_1130_, 0);
lean_dec(v_unused_1159_);
v___x_1148_ = v_p_1130_;
v_isShared_1149_ = v_isSharedCheck_1158_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_k_1146_);
lean_dec(v_p_1130_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1158_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = lean_nat_add(v_k_1145_, v_k_1146_);
lean_dec(v_k_1146_);
lean_dec(v_k_1145_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v___x_1150_);
lean_ctor_set(v___x_1148_, 0, v_x_1144_);
v___x_1152_ = v___x_1148_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_x_1144_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1135_, v_m_1133_, v_m_1131_);
lean_dec(v_n_1135_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1153_);
lean_ctor_set(v___x_1142_, 0, v___x_1152_);
v___x_1155_ = v___x_1142_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1163_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1135_, v_m_u2081_1125_, v_m_1131_);
lean_dec(v_n_1135_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1163_);
v___x_1165_ = v___x_1138_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_p_1130_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
else
{
lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1177_; 
lean_inc(v_m_1133_);
lean_inc_ref(v_p_1132_);
lean_dec_ref(v_p_1130_);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_m_u2081_1125_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; lean_object* v_unused_1179_; 
v_unused_1178_ = lean_ctor_get(v_m_u2081_1125_, 1);
lean_dec(v_unused_1178_);
v_unused_1179_ = lean_ctor_get(v_m_u2081_1125_, 0);
lean_dec(v_unused_1179_);
v___x_1171_ = v_m_u2081_1125_;
v_isShared_1172_ = v_isSharedCheck_1177_;
goto v_resetjp_1170_;
}
else
{
lean_dec(v_m_u2081_1125_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1177_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1173_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1135_, v_m_1133_, v_m_u2082_1126_);
lean_dec(v_n_1135_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 1, v___x_1173_);
v___x_1175_ = v___x_1171_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_p_1132_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go___boxed(lean_object* v_fuel_1180_, lean_object* v_m_u2081_1181_, lean_object* v_m_u2082_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Grind_CommRing_Mon_mul_go(v_fuel_1180_, v_m_u2081_1181_, v_m_u2082_1182_);
lean_dec(v_fuel_1180_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul(lean_object* v_m_u2081_1184_, lean_object* v_m_u2082_1185_){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_unsigned_to_nat(1000000u);
v___x_1187_ = l_Lean_Grind_CommRing_Mon_mul_go(v___x_1186_, v_m_u2081_1184_, v_m_u2082_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object* v_fuel_1188_, lean_object* v_h__1_1189_, lean_object* v_h__2_1190_){
_start:
{
lean_object* v_zero_1191_; uint8_t v_isZero_1192_; 
v_zero_1191_ = lean_unsigned_to_nat(0u);
v_isZero_1192_ = lean_nat_dec_eq(v_fuel_1188_, v_zero_1191_);
if (v_isZero_1192_ == 1)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec(v_h__2_1190_);
v___x_1193_ = lean_box(0);
v___x_1194_ = lean_apply_1(v_h__1_1189_, v___x_1193_);
return v___x_1194_;
}
else
{
lean_object* v_one_1195_; lean_object* v_n_1196_; lean_object* v___x_1197_; 
lean_dec(v_h__1_1189_);
v_one_1195_ = lean_unsigned_to_nat(1u);
v_n_1196_ = lean_nat_sub(v_fuel_1188_, v_one_1195_);
v___x_1197_ = lean_apply_1(v_h__2_1190_, v_n_1196_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object* v_fuel_1198_, lean_object* v_h__1_1199_, lean_object* v_h__2_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(v_fuel_1198_, v_h__1_1199_, v_h__2_1200_);
lean_dec(v_fuel_1198_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object* v_motive_1202_, lean_object* v_fuel_1203_, lean_object* v_h__1_1204_, lean_object* v_h__2_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(v_fuel_1203_, v_h__1_1204_, v_h__2_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object* v_motive_1207_, lean_object* v_fuel_1208_, lean_object* v_h__1_1209_, lean_object* v_h__2_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(v_motive_1207_, v_fuel_1208_, v_h__1_1209_, v_h__2_1210_);
lean_dec(v_fuel_1208_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter___redArg(lean_object* v_m_u2081_1212_, lean_object* v_m_u2082_1213_, lean_object* v_h__1_1214_, lean_object* v_h__2_1215_, lean_object* v_h__3_1216_){
_start:
{
if (lean_obj_tag(v_m_u2082_1213_) == 0)
{
lean_object* v___x_1217_; 
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
v___x_1217_ = lean_apply_1(v_h__1_1214_, v_m_u2081_1212_);
return v___x_1217_;
}
else
{
lean_dec(v_h__1_1214_);
if (lean_obj_tag(v_m_u2081_1212_) == 0)
{
lean_object* v___x_1218_; 
lean_dec(v_h__3_1216_);
v___x_1218_ = lean_apply_2(v_h__2_1215_, v_m_u2082_1213_, lean_box(0));
return v___x_1218_;
}
else
{
lean_object* v_p_1219_; lean_object* v_m_1220_; lean_object* v_p_1221_; lean_object* v_m_1222_; lean_object* v___x_1223_; 
lean_dec(v_h__2_1215_);
v_p_1219_ = lean_ctor_get(v_m_u2082_1213_, 0);
lean_inc_ref(v_p_1219_);
v_m_1220_ = lean_ctor_get(v_m_u2082_1213_, 1);
lean_inc(v_m_1220_);
lean_dec_ref(v_m_u2082_1213_);
v_p_1221_ = lean_ctor_get(v_m_u2081_1212_, 0);
lean_inc_ref(v_p_1221_);
v_m_1222_ = lean_ctor_get(v_m_u2081_1212_, 1);
lean_inc(v_m_1222_);
lean_dec_ref(v_m_u2081_1212_);
v___x_1223_ = lean_apply_4(v_h__3_1216_, v_p_1221_, v_m_1222_, v_p_1219_, v_m_1220_);
return v___x_1223_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter(lean_object* v_motive_1224_, lean_object* v_m_u2081_1225_, lean_object* v_m_u2082_1226_, lean_object* v_h__1_1227_, lean_object* v_h__2_1228_, lean_object* v_h__3_1229_){
_start:
{
if (lean_obj_tag(v_m_u2082_1226_) == 0)
{
lean_object* v___x_1230_; 
lean_dec(v_h__3_1229_);
lean_dec(v_h__2_1228_);
v___x_1230_ = lean_apply_1(v_h__1_1227_, v_m_u2081_1225_);
return v___x_1230_;
}
else
{
lean_dec(v_h__1_1227_);
if (lean_obj_tag(v_m_u2081_1225_) == 0)
{
lean_object* v___x_1231_; 
lean_dec(v_h__3_1229_);
v___x_1231_ = lean_apply_2(v_h__2_1228_, v_m_u2082_1226_, lean_box(0));
return v___x_1231_;
}
else
{
lean_object* v_p_1232_; lean_object* v_m_1233_; lean_object* v_p_1234_; lean_object* v_m_1235_; lean_object* v___x_1236_; 
lean_dec(v_h__2_1228_);
v_p_1232_ = lean_ctor_get(v_m_u2082_1226_, 0);
lean_inc_ref(v_p_1232_);
v_m_1233_ = lean_ctor_get(v_m_u2082_1226_, 1);
lean_inc(v_m_1233_);
lean_dec_ref(v_m_u2082_1226_);
v_p_1234_ = lean_ctor_get(v_m_u2081_1225_, 0);
lean_inc_ref(v_p_1234_);
v_m_1235_ = lean_ctor_get(v_m_u2081_1225_, 1);
lean_inc(v_m_1235_);
lean_dec_ref(v_m_u2081_1225_);
v___x_1236_ = lean_apply_4(v_h__3_1229_, v_p_1234_, v_m_1235_, v_p_1232_, v_m_1233_);
return v___x_1236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul__nc(lean_object* v_m_u2081_1237_, lean_object* v_m_u2082_1238_){
_start:
{
if (lean_obj_tag(v_m_u2081_1237_) == 0)
{
return v_m_u2082_1238_;
}
else
{
lean_object* v_m_1239_; 
v_m_1239_ = lean_ctor_get(v_m_u2081_1237_, 1);
if (lean_obj_tag(v_m_1239_) == 0)
{
lean_object* v_p_1240_; lean_object* v___x_1241_; 
v_p_1240_ = lean_ctor_get(v_m_u2081_1237_, 0);
lean_inc_ref(v_p_1240_);
lean_dec_ref(v_m_u2081_1237_);
v___x_1241_ = l_Lean_Grind_CommRing_Mon_mulPow__nc(v_p_1240_, v_m_u2082_1238_);
return v___x_1241_;
}
else
{
lean_object* v_p_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1250_; 
lean_inc(v_m_1239_);
v_p_1242_ = lean_ctor_get(v_m_u2081_1237_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_m_u2081_1237_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v_m_u2081_1237_, 1);
lean_dec(v_unused_1251_);
v___x_1244_ = v_m_u2081_1237_;
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_p_1242_);
lean_dec(v_m_u2081_1237_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_1239_, v_m_u2082_1238_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1246_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_p_1242_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_unsigned_to_nat(0u);
return v___x_1253_;
}
else
{
lean_object* v_p_1254_; lean_object* v_m_1255_; lean_object* v_k_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_p_1254_ = lean_ctor_get(v_x_1252_, 0);
v_m_1255_ = lean_ctor_get(v_x_1252_, 1);
v_k_1256_ = lean_ctor_get(v_p_1254_, 1);
v___x_1257_ = l_Lean_Grind_CommRing_Mon_degree(v_m_1255_);
v___x_1258_ = lean_nat_add(v_k_1256_, v___x_1257_);
lean_dec(v___x_1257_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree___boxed(lean_object* v_x_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Grind_CommRing_Mon_degree(v_x_1259_);
lean_dec(v_x_1259_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object* v_x_1261_, lean_object* v_h__1_1262_, lean_object* v_h__2_1263_){
_start:
{
if (lean_obj_tag(v_x_1261_) == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec(v_h__2_1263_);
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_apply_1(v_h__1_1262_, v___x_1264_);
return v___x_1265_;
}
else
{
lean_object* v_p_1266_; lean_object* v_m_1267_; lean_object* v___x_1268_; 
lean_dec(v_h__1_1262_);
v_p_1266_ = lean_ctor_get(v_x_1261_, 0);
lean_inc_ref(v_p_1266_);
v_m_1267_ = lean_ctor_get(v_x_1261_, 1);
lean_inc(v_m_1267_);
lean_dec_ref(v_x_1261_);
v___x_1268_ = lean_apply_2(v_h__2_1263_, v_p_1266_, v_m_1267_);
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object* v_motive_1269_, lean_object* v_x_1270_, lean_object* v_h__1_1271_, lean_object* v_h__2_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(v_x_1270_, v_h__1_1271_, v_h__2_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Var_revlex(lean_object* v_x_1274_, lean_object* v_y_1275_){
_start:
{
uint8_t v___x_1276_; 
v___x_1276_ = l_Nat_blt(v_x_1274_, v_y_1275_);
if (v___x_1276_ == 0)
{
uint8_t v___x_1277_; 
v___x_1277_ = l_Nat_blt(v_y_1275_, v_x_1274_);
if (v___x_1277_ == 0)
{
uint8_t v___x_1278_; 
v___x_1278_ = 1;
return v___x_1278_;
}
else
{
uint8_t v___x_1279_; 
v___x_1279_ = 0;
return v___x_1279_;
}
}
else
{
uint8_t v___x_1280_; 
v___x_1280_ = 2;
return v___x_1280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_revlex___boxed(lean_object* v_x_1281_, lean_object* v_y_1282_){
_start:
{
uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_res_1283_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1281_, v_y_1282_);
lean_dec(v_y_1282_);
lean_dec(v_x_1281_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_powerRevlex(lean_object* v_k_u2081_1285_, lean_object* v_k_u2082_1286_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = l_Nat_blt(v_k_u2081_1285_, v_k_u2082_1286_);
if (v___x_1287_ == 0)
{
uint8_t v___x_1288_; 
v___x_1288_ = l_Nat_blt(v_k_u2082_1286_, v_k_u2081_1285_);
if (v___x_1288_ == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = 1;
return v___x_1289_;
}
else
{
uint8_t v___x_1290_; 
v___x_1290_ = 0;
return v___x_1290_;
}
}
else
{
uint8_t v___x_1291_; 
v___x_1291_ = 2;
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_powerRevlex___boxed(lean_object* v_k_u2081_1292_, lean_object* v_k_u2082_1293_){
_start:
{
uint8_t v_res_1294_; lean_object* v_r_1295_; 
v_res_1294_ = l_Lean_Grind_CommRing_powerRevlex(v_k_u2081_1292_, v_k_u2082_1293_);
lean_dec(v_k_u2082_1293_);
lean_dec(v_k_u2081_1292_);
v_r_1295_ = lean_box(v_res_1294_);
return v_r_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(uint8_t v_c_1296_, lean_object* v_h__1_1297_, lean_object* v_h__2_1298_){
_start:
{
if (v_c_1296_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec(v_h__1_1297_);
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_apply_1(v_h__2_1298_, v___x_1299_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_dec(v_h__2_1298_);
v___x_1301_ = lean_box(0);
v___x_1302_ = lean_apply_1(v_h__1_1297_, v___x_1301_);
return v___x_1302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg___boxed(lean_object* v_c_1303_, lean_object* v_h__1_1304_, lean_object* v_h__2_1305_){
_start:
{
uint8_t v_c_22__boxed_1306_; lean_object* v_res_1307_; 
v_c_22__boxed_1306_ = lean_unbox(v_c_1303_);
v_res_1307_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(v_c_22__boxed_1306_, v_h__1_1304_, v_h__2_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(lean_object* v_motive_1308_, uint8_t v_c_1309_, lean_object* v_h__1_1310_, lean_object* v_h__2_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(v_c_1309_, v_h__1_1310_, v_h__2_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___boxed(lean_object* v_motive_1313_, lean_object* v_c_1314_, lean_object* v_h__1_1315_, lean_object* v_h__2_1316_){
_start:
{
uint8_t v_c_33__boxed_1317_; lean_object* v_res_1318_; 
v_c_33__boxed_1317_ = lean_unbox(v_c_1314_);
v_res_1318_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(v_motive_1313_, v_c_33__boxed_1317_, v_h__1_1315_, v_h__2_1316_);
return v_res_1318_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_revlex(lean_object* v_p_u2081_1319_, lean_object* v_p_u2082_1320_){
_start:
{
lean_object* v_x_1321_; lean_object* v_k_1322_; lean_object* v_x_1323_; lean_object* v_k_1324_; uint8_t v___x_1325_; 
v_x_1321_ = lean_ctor_get(v_p_u2081_1319_, 0);
v_k_1322_ = lean_ctor_get(v_p_u2081_1319_, 1);
v_x_1323_ = lean_ctor_get(v_p_u2082_1320_, 0);
v_k_1324_ = lean_ctor_get(v_p_u2082_1320_, 1);
v___x_1325_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1321_, v_x_1323_);
if (v___x_1325_ == 1)
{
uint8_t v___x_1326_; 
v___x_1326_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1322_, v_k_1324_);
return v___x_1326_;
}
else
{
return v___x_1325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_revlex___boxed(lean_object* v_p_u2081_1327_, lean_object* v_p_u2082_1328_){
_start:
{
uint8_t v_res_1329_; lean_object* v_r_1330_; 
v_res_1329_ = l_Lean_Grind_CommRing_Power_revlex(v_p_u2081_1327_, v_p_u2082_1328_);
lean_dec_ref(v_p_u2082_1328_);
lean_dec_ref(v_p_u2081_1327_);
v_r_1330_ = lean_box(v_res_1329_);
return v_r_1330_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexWF(lean_object* v_m_u2081_1331_, lean_object* v_m_u2082_1332_){
_start:
{
if (lean_obj_tag(v_m_u2081_1331_) == 0)
{
if (lean_obj_tag(v_m_u2082_1332_) == 0)
{
uint8_t v___x_1333_; 
v___x_1333_ = 1;
return v___x_1333_;
}
else
{
uint8_t v___x_1334_; 
v___x_1334_ = 2;
return v___x_1334_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1332_) == 0)
{
uint8_t v___x_1335_; 
v___x_1335_ = 0;
return v___x_1335_;
}
else
{
lean_object* v_p_1336_; lean_object* v_p_1337_; lean_object* v_m_1338_; lean_object* v_m_1339_; lean_object* v_x_1340_; lean_object* v_k_1341_; lean_object* v_x_1342_; lean_object* v_k_1343_; uint8_t v___x_1344_; 
v_p_1336_ = lean_ctor_get(v_m_u2081_1331_, 0);
v_p_1337_ = lean_ctor_get(v_m_u2082_1332_, 0);
v_m_1338_ = lean_ctor_get(v_m_u2081_1331_, 1);
v_m_1339_ = lean_ctor_get(v_m_u2082_1332_, 1);
v_x_1340_ = lean_ctor_get(v_p_1336_, 0);
v_k_1341_ = lean_ctor_get(v_p_1336_, 1);
v_x_1342_ = lean_ctor_get(v_p_1337_, 0);
v_k_1343_ = lean_ctor_get(v_p_1337_, 1);
v___x_1344_ = lean_nat_dec_eq(v_x_1340_, v_x_1342_);
if (v___x_1344_ == 0)
{
uint8_t v___x_1345_; 
v___x_1345_ = l_Nat_blt(v_x_1340_, v_x_1342_);
if (v___x_1345_ == 0)
{
uint8_t v___x_1346_; 
v___x_1346_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1331_, v_m_1339_);
if (v___x_1346_ == 1)
{
uint8_t v___x_1347_; 
v___x_1347_ = 2;
return v___x_1347_;
}
else
{
return v___x_1346_;
}
}
else
{
uint8_t v___x_1348_; 
v___x_1348_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1338_, v_m_u2082_1332_);
if (v___x_1348_ == 1)
{
uint8_t v___x_1349_; 
v___x_1349_ = 0;
return v___x_1349_;
}
else
{
return v___x_1348_;
}
}
}
else
{
uint8_t v___x_1350_; 
v___x_1350_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1338_, v_m_1339_);
if (v___x_1350_ == 1)
{
uint8_t v___x_1351_; 
v___x_1351_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1341_, v_k_1343_);
return v___x_1351_;
}
else
{
return v___x_1350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexWF___boxed(lean_object* v_m_u2081_1352_, lean_object* v_m_u2082_1353_){
_start:
{
uint8_t v_res_1354_; lean_object* v_r_1355_; 
v_res_1354_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1352_, v_m_u2082_1353_);
lean_dec(v_m_u2082_1353_);
lean_dec(v_m_u2081_1352_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(lean_object* v_m_u2081_1356_, lean_object* v_m_u2082_1357_, lean_object* v_h__1_1358_, lean_object* v_h__2_1359_, lean_object* v_h__3_1360_, lean_object* v_h__4_1361_){
_start:
{
if (lean_obj_tag(v_m_u2081_1356_) == 0)
{
lean_dec(v_h__4_1361_);
lean_dec(v_h__3_1360_);
if (lean_obj_tag(v_m_u2082_1357_) == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec(v_h__2_1359_);
v___x_1362_ = lean_box(0);
v___x_1363_ = lean_apply_1(v_h__1_1358_, v___x_1362_);
return v___x_1363_;
}
else
{
lean_object* v_p_1364_; lean_object* v_m_1365_; lean_object* v___x_1366_; 
lean_dec(v_h__1_1358_);
v_p_1364_ = lean_ctor_get(v_m_u2082_1357_, 0);
lean_inc_ref(v_p_1364_);
v_m_1365_ = lean_ctor_get(v_m_u2082_1357_, 1);
lean_inc(v_m_1365_);
lean_dec_ref(v_m_u2082_1357_);
v___x_1366_ = lean_apply_2(v_h__2_1359_, v_p_1364_, v_m_1365_);
return v___x_1366_;
}
}
else
{
lean_dec(v_h__2_1359_);
lean_dec(v_h__1_1358_);
if (lean_obj_tag(v_m_u2082_1357_) == 0)
{
lean_object* v_p_1367_; lean_object* v_m_1368_; lean_object* v___x_1369_; 
lean_dec(v_h__4_1361_);
v_p_1367_ = lean_ctor_get(v_m_u2081_1356_, 0);
lean_inc_ref(v_p_1367_);
v_m_1368_ = lean_ctor_get(v_m_u2081_1356_, 1);
lean_inc(v_m_1368_);
lean_dec_ref(v_m_u2081_1356_);
v___x_1369_ = lean_apply_2(v_h__3_1360_, v_p_1367_, v_m_1368_);
return v___x_1369_;
}
else
{
lean_object* v_p_1370_; lean_object* v_m_1371_; lean_object* v_p_1372_; lean_object* v_m_1373_; lean_object* v___x_1374_; 
lean_dec(v_h__3_1360_);
v_p_1370_ = lean_ctor_get(v_m_u2081_1356_, 0);
lean_inc_ref(v_p_1370_);
v_m_1371_ = lean_ctor_get(v_m_u2081_1356_, 1);
lean_inc(v_m_1371_);
lean_dec_ref(v_m_u2081_1356_);
v_p_1372_ = lean_ctor_get(v_m_u2082_1357_, 0);
lean_inc_ref(v_p_1372_);
v_m_1373_ = lean_ctor_get(v_m_u2082_1357_, 1);
lean_inc(v_m_1373_);
lean_dec_ref(v_m_u2082_1357_);
v___x_1374_ = lean_apply_4(v_h__4_1361_, v_p_1370_, v_m_1371_, v_p_1372_, v_m_1373_);
return v___x_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter(lean_object* v_motive_1375_, lean_object* v_m_u2081_1376_, lean_object* v_m_u2082_1377_, lean_object* v_h__1_1378_, lean_object* v_h__2_1379_, lean_object* v_h__3_1380_, lean_object* v_h__4_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(v_m_u2081_1376_, v_m_u2082_1377_, v_h__1_1378_, v_h__2_1379_, v_h__3_1380_, v_h__4_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexFuel(lean_object* v_fuel_1383_, lean_object* v_m_u2081_1384_, lean_object* v_m_u2082_1385_){
_start:
{
lean_object* v_zero_1386_; uint8_t v_isZero_1387_; 
v_zero_1386_ = lean_unsigned_to_nat(0u);
v_isZero_1387_ = lean_nat_dec_eq(v_fuel_1383_, v_zero_1386_);
if (v_isZero_1387_ == 1)
{
uint8_t v___x_1388_; 
v___x_1388_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1384_, v_m_u2082_1385_);
return v___x_1388_;
}
else
{
if (lean_obj_tag(v_m_u2081_1384_) == 0)
{
if (lean_obj_tag(v_m_u2082_1385_) == 0)
{
uint8_t v___x_1389_; 
v___x_1389_ = 1;
return v___x_1389_;
}
else
{
uint8_t v___x_1390_; 
v___x_1390_ = 2;
return v___x_1390_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1385_) == 0)
{
uint8_t v___x_1391_; 
v___x_1391_ = 0;
return v___x_1391_;
}
else
{
lean_object* v_p_1392_; lean_object* v_p_1393_; lean_object* v_m_1394_; lean_object* v_m_1395_; lean_object* v_x_1396_; lean_object* v_k_1397_; lean_object* v_x_1398_; lean_object* v_k_1399_; lean_object* v_one_1400_; lean_object* v_n_1401_; uint8_t v___x_1402_; 
v_p_1392_ = lean_ctor_get(v_m_u2081_1384_, 0);
v_p_1393_ = lean_ctor_get(v_m_u2082_1385_, 0);
v_m_1394_ = lean_ctor_get(v_m_u2081_1384_, 1);
v_m_1395_ = lean_ctor_get(v_m_u2082_1385_, 1);
v_x_1396_ = lean_ctor_get(v_p_1392_, 0);
v_k_1397_ = lean_ctor_get(v_p_1392_, 1);
v_x_1398_ = lean_ctor_get(v_p_1393_, 0);
v_k_1399_ = lean_ctor_get(v_p_1393_, 1);
v_one_1400_ = lean_unsigned_to_nat(1u);
v_n_1401_ = lean_nat_sub(v_fuel_1383_, v_one_1400_);
v___x_1402_ = lean_nat_dec_eq(v_x_1396_, v_x_1398_);
if (v___x_1402_ == 0)
{
uint8_t v___x_1403_; 
v___x_1403_ = l_Nat_blt(v_x_1396_, v_x_1398_);
if (v___x_1403_ == 0)
{
uint8_t v___x_1404_; 
v___x_1404_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1401_, v_m_u2081_1384_, v_m_1395_);
lean_dec(v_n_1401_);
if (v___x_1404_ == 1)
{
uint8_t v___x_1405_; 
v___x_1405_ = 2;
return v___x_1405_;
}
else
{
return v___x_1404_;
}
}
else
{
uint8_t v___x_1406_; 
v___x_1406_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1401_, v_m_1394_, v_m_u2082_1385_);
lean_dec(v_n_1401_);
if (v___x_1406_ == 1)
{
uint8_t v___x_1407_; 
v___x_1407_ = 0;
return v___x_1407_;
}
else
{
return v___x_1406_;
}
}
}
else
{
uint8_t v___x_1408_; 
v___x_1408_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1401_, v_m_1394_, v_m_1395_);
lean_dec(v_n_1401_);
if (v___x_1408_ == 1)
{
uint8_t v___x_1409_; 
v___x_1409_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1397_, v_k_1399_);
return v___x_1409_;
}
else
{
return v___x_1408_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexFuel___boxed(lean_object* v_fuel_1410_, lean_object* v_m_u2081_1411_, lean_object* v_m_u2082_1412_){
_start:
{
uint8_t v_res_1413_; lean_object* v_r_1414_; 
v_res_1413_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_fuel_1410_, v_m_u2081_1411_, v_m_u2082_1412_);
lean_dec(v_m_u2082_1412_);
lean_dec(v_m_u2081_1411_);
lean_dec(v_fuel_1410_);
v_r_1414_ = lean_box(v_res_1413_);
return v_r_1414_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlex(lean_object* v_m_u2081_1415_, lean_object* v_m_u2082_1416_){
_start:
{
lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = lean_unsigned_to_nat(1000000u);
v___x_1418_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v___x_1417_, v_m_u2081_1415_, v_m_u2082_1416_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlex___boxed(lean_object* v_m_u2081_1419_, lean_object* v_m_u2082_1420_){
_start:
{
uint8_t v_res_1421_; lean_object* v_r_1422_; 
v_res_1421_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1419_, v_m_u2082_1420_);
lean_dec(v_m_u2082_1420_);
lean_dec(v_m_u2081_1419_);
v_r_1422_ = lean_box(v_res_1421_);
return v_r_1422_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object* v_m_u2081_1423_, lean_object* v_m_u2082_1424_){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1425_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2081_1423_);
v___x_1426_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2082_1424_);
v___x_1427_ = lean_nat_dec_lt(v___x_1425_, v___x_1426_);
if (v___x_1427_ == 0)
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_nat_dec_eq(v___x_1425_, v___x_1426_);
lean_dec(v___x_1426_);
lean_dec(v___x_1425_);
if (v___x_1428_ == 0)
{
uint8_t v___x_1429_; 
v___x_1429_ = 2;
return v___x_1429_;
}
else
{
uint8_t v___x_1430_; 
v___x_1430_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1423_, v_m_u2082_1424_);
return v___x_1430_;
}
}
else
{
uint8_t v___x_1431_; 
lean_dec(v___x_1426_);
lean_dec(v___x_1425_);
v___x_1431_ = 0;
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_grevlex___boxed(lean_object* v_m_u2081_1432_, lean_object* v_m_u2082_1433_){
_start:
{
uint8_t v_res_1434_; lean_object* v_r_1435_; 
v_res_1434_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_u2081_1432_, v_m_u2082_1433_);
lean_dec(v_m_u2082_1433_);
lean_dec(v_m_u2081_1432_);
v_r_1435_ = lean_box(v_res_1434_);
return v_r_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx(lean_object* v_x_1436_){
_start:
{
if (lean_obj_tag(v_x_1436_) == 0)
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_unsigned_to_nat(0u);
return v___x_1437_;
}
else
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_unsigned_to_nat(1u);
return v___x_1438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___boxed(lean_object* v_x_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_Grind_CommRing_Poly_ctorIdx(v_x_1439_);
lean_dec_ref(v_x_1439_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___redArg(lean_object* v_t_1441_, lean_object* v_k_1442_){
_start:
{
if (lean_obj_tag(v_t_1441_) == 0)
{
lean_object* v_k_1443_; lean_object* v___x_1444_; 
v_k_1443_ = lean_ctor_get(v_t_1441_, 0);
lean_inc(v_k_1443_);
lean_dec_ref(v_t_1441_);
v___x_1444_ = lean_apply_1(v_k_1442_, v_k_1443_);
return v___x_1444_;
}
else
{
lean_object* v_k_1445_; lean_object* v_v_1446_; lean_object* v_p_1447_; lean_object* v___x_1448_; 
v_k_1445_ = lean_ctor_get(v_t_1441_, 0);
lean_inc(v_k_1445_);
v_v_1446_ = lean_ctor_get(v_t_1441_, 1);
lean_inc(v_v_1446_);
v_p_1447_ = lean_ctor_get(v_t_1441_, 2);
lean_inc_ref(v_p_1447_);
lean_dec_ref(v_t_1441_);
v___x_1448_ = lean_apply_3(v_k_1442_, v_k_1445_, v_v_1446_, v_p_1447_);
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim(lean_object* v_motive_1449_, lean_object* v_ctorIdx_1450_, lean_object* v_t_1451_, lean_object* v_h_1452_, lean_object* v_k_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1451_, v_k_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___boxed(lean_object* v_motive_1455_, lean_object* v_ctorIdx_1456_, lean_object* v_t_1457_, lean_object* v_h_1458_, lean_object* v_k_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_Grind_CommRing_Poly_ctorElim(v_motive_1455_, v_ctorIdx_1456_, v_t_1457_, v_h_1458_, v_k_1459_);
lean_dec(v_ctorIdx_1456_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim___redArg(lean_object* v_t_1461_, lean_object* v_num_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1461_, v_num_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim(lean_object* v_motive_1464_, lean_object* v_t_1465_, lean_object* v_h_1466_, lean_object* v_num_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1465_, v_num_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim___redArg(lean_object* v_t_1469_, lean_object* v_add_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1469_, v_add_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim(lean_object* v_motive_1472_, lean_object* v_t_1473_, lean_object* v_h_1474_, lean_object* v_add_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1473_, v_add_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPoly_beq(lean_object* v_x_1477_, lean_object* v_x_1478_){
_start:
{
if (lean_obj_tag(v_x_1477_) == 0)
{
if (lean_obj_tag(v_x_1478_) == 0)
{
lean_object* v_k_1479_; lean_object* v_k_1480_; uint8_t v___x_1481_; 
v_k_1479_ = lean_ctor_get(v_x_1477_, 0);
v_k_1480_ = lean_ctor_get(v_x_1478_, 0);
v___x_1481_ = lean_int_dec_eq(v_k_1479_, v_k_1480_);
return v___x_1481_;
}
else
{
uint8_t v___x_1482_; 
v___x_1482_ = 0;
return v___x_1482_;
}
}
else
{
if (lean_obj_tag(v_x_1478_) == 1)
{
lean_object* v_k_1483_; lean_object* v_v_1484_; lean_object* v_p_1485_; lean_object* v_k_1486_; lean_object* v_v_1487_; lean_object* v_p_1488_; uint8_t v___x_1489_; 
v_k_1483_ = lean_ctor_get(v_x_1477_, 0);
v_v_1484_ = lean_ctor_get(v_x_1477_, 1);
v_p_1485_ = lean_ctor_get(v_x_1477_, 2);
v_k_1486_ = lean_ctor_get(v_x_1478_, 0);
v_v_1487_ = lean_ctor_get(v_x_1478_, 1);
v_p_1488_ = lean_ctor_get(v_x_1478_, 2);
v___x_1489_ = lean_int_dec_eq(v_k_1483_, v_k_1486_);
if (v___x_1489_ == 0)
{
return v___x_1489_;
}
else
{
uint8_t v___x_1490_; 
v___x_1490_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_v_1484_, v_v_1487_);
if (v___x_1490_ == 0)
{
return v___x_1490_;
}
else
{
v_x_1477_ = v_p_1485_;
v_x_1478_ = v_p_1488_;
goto _start;
}
}
}
else
{
uint8_t v___x_1492_; 
v___x_1492_ = 0;
return v___x_1492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPoly_beq___boxed(lean_object* v_x_1493_, lean_object* v_x_1494_){
_start:
{
uint8_t v_res_1495_; lean_object* v_r_1496_; 
v_res_1495_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_x_1493_, v_x_1494_);
lean_dec_ref(v_x_1494_);
lean_dec_ref(v_x_1493_);
v_r_1496_ = lean_box(v_res_1495_);
return v_r_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_1499_, lean_object* v_x_1500_, lean_object* v_h__1_1501_, lean_object* v_h__2_1502_, lean_object* v_h__3_1503_){
_start:
{
if (lean_obj_tag(v_x_1499_) == 0)
{
lean_dec(v_h__2_1502_);
if (lean_obj_tag(v_x_1500_) == 0)
{
lean_object* v_k_1504_; lean_object* v_k_1505_; lean_object* v___x_1506_; 
lean_dec(v_h__3_1503_);
v_k_1504_ = lean_ctor_get(v_x_1499_, 0);
lean_inc(v_k_1504_);
lean_dec_ref(v_x_1499_);
v_k_1505_ = lean_ctor_get(v_x_1500_, 0);
lean_inc(v_k_1505_);
lean_dec_ref(v_x_1500_);
v___x_1506_ = lean_apply_2(v_h__1_1501_, v_k_1504_, v_k_1505_);
return v___x_1506_;
}
else
{
lean_object* v___x_1507_; 
lean_dec(v_h__1_1501_);
v___x_1507_ = lean_apply_4(v_h__3_1503_, v_x_1499_, v_x_1500_, lean_box(0), lean_box(0));
return v___x_1507_;
}
}
else
{
lean_dec(v_h__1_1501_);
if (lean_obj_tag(v_x_1500_) == 1)
{
lean_object* v_k_1508_; lean_object* v_v_1509_; lean_object* v_p_1510_; lean_object* v_k_1511_; lean_object* v_v_1512_; lean_object* v_p_1513_; lean_object* v___x_1514_; 
lean_dec(v_h__3_1503_);
v_k_1508_ = lean_ctor_get(v_x_1499_, 0);
lean_inc(v_k_1508_);
v_v_1509_ = lean_ctor_get(v_x_1499_, 1);
lean_inc(v_v_1509_);
v_p_1510_ = lean_ctor_get(v_x_1499_, 2);
lean_inc_ref(v_p_1510_);
lean_dec_ref(v_x_1499_);
v_k_1511_ = lean_ctor_get(v_x_1500_, 0);
lean_inc(v_k_1511_);
v_v_1512_ = lean_ctor_get(v_x_1500_, 1);
lean_inc(v_v_1512_);
v_p_1513_ = lean_ctor_get(v_x_1500_, 2);
lean_inc_ref(v_p_1513_);
lean_dec_ref(v_x_1500_);
v___x_1514_ = lean_apply_6(v_h__2_1502_, v_k_1508_, v_v_1509_, v_p_1510_, v_k_1511_, v_v_1512_, v_p_1513_);
return v___x_1514_;
}
else
{
lean_object* v___x_1515_; 
lean_dec(v_h__2_1502_);
v___x_1515_ = lean_apply_4(v_h__3_1503_, v_x_1499_, v_x_1500_, lean_box(0), lean_box(0));
return v___x_1515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_, lean_object* v_h__1_1519_, lean_object* v_h__2_1520_, lean_object* v_h__3_1521_){
_start:
{
if (lean_obj_tag(v_x_1517_) == 0)
{
lean_dec(v_h__2_1520_);
if (lean_obj_tag(v_x_1518_) == 0)
{
lean_object* v_k_1522_; lean_object* v_k_1523_; lean_object* v___x_1524_; 
lean_dec(v_h__3_1521_);
v_k_1522_ = lean_ctor_get(v_x_1517_, 0);
lean_inc(v_k_1522_);
lean_dec_ref(v_x_1517_);
v_k_1523_ = lean_ctor_get(v_x_1518_, 0);
lean_inc(v_k_1523_);
lean_dec_ref(v_x_1518_);
v___x_1524_ = lean_apply_2(v_h__1_1519_, v_k_1522_, v_k_1523_);
return v___x_1524_;
}
else
{
lean_object* v___x_1525_; 
lean_dec(v_h__1_1519_);
v___x_1525_ = lean_apply_4(v_h__3_1521_, v_x_1517_, v_x_1518_, lean_box(0), lean_box(0));
return v___x_1525_;
}
}
else
{
lean_dec(v_h__1_1519_);
if (lean_obj_tag(v_x_1518_) == 1)
{
lean_object* v_k_1526_; lean_object* v_v_1527_; lean_object* v_p_1528_; lean_object* v_k_1529_; lean_object* v_v_1530_; lean_object* v_p_1531_; lean_object* v___x_1532_; 
lean_dec(v_h__3_1521_);
v_k_1526_ = lean_ctor_get(v_x_1517_, 0);
lean_inc(v_k_1526_);
v_v_1527_ = lean_ctor_get(v_x_1517_, 1);
lean_inc(v_v_1527_);
v_p_1528_ = lean_ctor_get(v_x_1517_, 2);
lean_inc_ref(v_p_1528_);
lean_dec_ref(v_x_1517_);
v_k_1529_ = lean_ctor_get(v_x_1518_, 0);
lean_inc(v_k_1529_);
v_v_1530_ = lean_ctor_get(v_x_1518_, 1);
lean_inc(v_v_1530_);
v_p_1531_ = lean_ctor_get(v_x_1518_, 2);
lean_inc_ref(v_p_1531_);
lean_dec_ref(v_x_1518_);
v___x_1532_ = lean_apply_6(v_h__2_1520_, v_k_1526_, v_v_1527_, v_p_1528_, v_k_1529_, v_v_1530_, v_p_1531_);
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; 
lean_dec(v_h__2_1520_);
v___x_1533_ = lean_apply_4(v_h__3_1521_, v_x_1517_, v_x_1518_, lean_box(0), lean_box(0));
return v___x_1533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr(lean_object* v_x_1546_, lean_object* v_prec_1547_){
_start:
{
lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; 
if (lean_obj_tag(v_x_1546_) == 0)
{
lean_object* v_k_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1580_; 
v_k_1557_ = lean_ctor_get(v_x_1546_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_x_1546_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1559_ = v_x_1546_;
v_isShared_1560_ = v_isSharedCheck_1580_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_k_1557_);
lean_dec(v_x_1546_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1580_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___y_1562_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = lean_unsigned_to_nat(1024u);
v___x_1577_ = lean_nat_dec_le(v___x_1576_, v_prec_1547_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1562_ = v___x_1578_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1562_ = v___x_1579_;
goto v___jp_1561_;
}
v___jp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1563_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__2));
v___x_1564_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1565_ = lean_int_dec_lt(v_k_1557_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1566_ = l_Int_repr(v_k_1557_);
lean_dec(v_k_1557_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set_tag(v___x_1559_, 3);
lean_ctor_set(v___x_1559_, 0, v___x_1566_);
v___x_1568_ = v___x_1559_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
v___y_1549_ = v___y_1562_;
v___y_1550_ = v___x_1563_;
v___y_1551_ = v___x_1568_;
goto v___jp_1548_;
}
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1570_ = lean_unsigned_to_nat(1024u);
v___x_1571_ = l_Int_repr(v_k_1557_);
lean_dec(v_k_1557_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set_tag(v___x_1559_, 3);
lean_ctor_set(v___x_1559_, 0, v___x_1571_);
v___x_1573_ = v___x_1559_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Repr_addAppParen(v___x_1573_, v___x_1570_);
v___y_1549_ = v___y_1562_;
v___y_1550_ = v___x_1563_;
v___y_1551_ = v___x_1574_;
goto v___jp_1548_;
}
}
}
}
}
else
{
lean_object* v_k_1581_; lean_object* v_v_1582_; lean_object* v_p_1583_; lean_object* v___x_1584_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1602_; uint8_t v___x_1612_; 
v_k_1581_ = lean_ctor_get(v_x_1546_, 0);
lean_inc(v_k_1581_);
v_v_1582_ = lean_ctor_get(v_x_1546_, 1);
lean_inc(v_v_1582_);
v_p_1583_ = lean_ctor_get(v_x_1546_, 2);
lean_inc_ref(v_p_1583_);
lean_dec_ref(v_x_1546_);
v___x_1584_ = lean_unsigned_to_nat(1024u);
v___x_1612_ = lean_nat_dec_le(v___x_1584_, v_prec_1547_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1602_ = v___x_1613_;
goto v___jp_1601_;
}
else
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1602_ = v___x_1614_;
goto v___jp_1601_;
}
v___jp_1585_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___y_1587_);
lean_ctor_set(v___x_1590_, 1, v___y_1589_);
lean_inc(v___y_1588_);
v___x_1591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
lean_ctor_set(v___x_1591_, 1, v___y_1588_);
v___x_1592_ = l_Lean_Grind_CommRing_instReprMon_repr(v_v_1582_, v___x_1584_);
v___x_1593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v___y_1588_);
v___x_1595_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_p_1583_, v___x_1584_);
v___x_1596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1594_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___y_1586_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = 0;
v___x_1599_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set_uint8(v___x_1599_, sizeof(void*)*1, v___x_1598_);
v___x_1600_ = l_Repr_addAppParen(v___x_1599_, v_prec_1547_);
return v___x_1600_;
}
v___jp_1601_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1603_ = lean_box(1);
v___x_1604_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__5));
v___x_1605_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1606_ = lean_int_dec_lt(v_k_1581_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = l_Int_repr(v_k_1581_);
lean_dec(v_k_1581_);
v___x_1608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
v___y_1586_ = v___y_1602_;
v___y_1587_ = v___x_1604_;
v___y_1588_ = v___x_1603_;
v___y_1589_ = v___x_1608_;
goto v___jp_1585_;
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = l_Int_repr(v_k_1581_);
lean_dec(v_k_1581_);
v___x_1610_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
v___x_1611_ = l_Repr_addAppParen(v___x_1610_, v___x_1584_);
v___y_1586_ = v___y_1602_;
v___y_1587_ = v___x_1604_;
v___y_1588_ = v___x_1603_;
v___y_1589_ = v___x_1611_;
goto v___jp_1585_;
}
}
}
v___jp_1548_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___y_1550_);
lean_ctor_set(v___x_1552_, 1, v___y_1551_);
v___x_1553_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___y_1549_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = 0;
v___x_1555_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*1, v___x_1554_);
v___x_1556_ = l_Repr_addAppParen(v___x_1555_, v_prec_1547_);
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___boxed(lean_object* v_x_1615_, lean_object* v_prec_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_x_1615_, v_prec_1616_);
lean_dec(v_prec_1616_);
return v_res_1617_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
return v___x_1621_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default(void){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_1622_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly(void){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
return v___x_1623_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePoly_hash(lean_object* v_x_1624_){
_start:
{
if (lean_obj_tag(v_x_1624_) == 0)
{
lean_object* v_k_1625_; uint64_t v___x_1626_; lean_object* v_intZero_1627_; uint8_t v_isNeg_1628_; 
v_k_1625_ = lean_ctor_get(v_x_1624_, 0);
v___x_1626_ = 0ULL;
v_intZero_1627_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1628_ = lean_int_dec_lt(v_k_1625_, v_intZero_1627_);
if (v_isNeg_1628_ == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; uint64_t v___x_1632_; uint64_t v___x_1633_; 
v_a_1629_ = lean_nat_abs(v_k_1625_);
v___x_1630_ = lean_unsigned_to_nat(2u);
v___x_1631_ = lean_nat_mul(v___x_1630_, v_a_1629_);
lean_dec(v_a_1629_);
v___x_1632_ = lean_uint64_of_nat(v___x_1631_);
lean_dec(v___x_1631_);
v___x_1633_ = lean_uint64_mix_hash(v___x_1626_, v___x_1632_);
return v___x_1633_;
}
else
{
lean_object* v_abs_1634_; lean_object* v_one_1635_; lean_object* v_a_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint64_t v___x_1640_; uint64_t v___x_1641_; 
v_abs_1634_ = lean_nat_abs(v_k_1625_);
v_one_1635_ = lean_unsigned_to_nat(1u);
v_a_1636_ = lean_nat_sub(v_abs_1634_, v_one_1635_);
lean_dec(v_abs_1634_);
v___x_1637_ = lean_unsigned_to_nat(2u);
v___x_1638_ = lean_nat_mul(v___x_1637_, v_a_1636_);
lean_dec(v_a_1636_);
v___x_1639_ = lean_nat_add(v___x_1638_, v_one_1635_);
lean_dec(v___x_1638_);
v___x_1640_ = lean_uint64_of_nat(v___x_1639_);
lean_dec(v___x_1639_);
v___x_1641_ = lean_uint64_mix_hash(v___x_1626_, v___x_1640_);
return v___x_1641_;
}
}
else
{
lean_object* v_k_1642_; lean_object* v_v_1643_; lean_object* v_p_1644_; uint64_t v___x_1645_; uint64_t v___y_1647_; lean_object* v_intZero_1653_; uint8_t v_isNeg_1654_; 
v_k_1642_ = lean_ctor_get(v_x_1624_, 0);
v_v_1643_ = lean_ctor_get(v_x_1624_, 1);
v_p_1644_ = lean_ctor_get(v_x_1624_, 2);
v___x_1645_ = 1ULL;
v_intZero_1653_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1654_ = lean_int_dec_lt(v_k_1642_, v_intZero_1653_);
if (v_isNeg_1654_ == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint64_t v___x_1658_; 
v_a_1655_ = lean_nat_abs(v_k_1642_);
v___x_1656_ = lean_unsigned_to_nat(2u);
v___x_1657_ = lean_nat_mul(v___x_1656_, v_a_1655_);
lean_dec(v_a_1655_);
v___x_1658_ = lean_uint64_of_nat(v___x_1657_);
lean_dec(v___x_1657_);
v___y_1647_ = v___x_1658_;
goto v___jp_1646_;
}
else
{
lean_object* v_abs_1659_; lean_object* v_one_1660_; lean_object* v_a_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint64_t v___x_1665_; 
v_abs_1659_ = lean_nat_abs(v_k_1642_);
v_one_1660_ = lean_unsigned_to_nat(1u);
v_a_1661_ = lean_nat_sub(v_abs_1659_, v_one_1660_);
lean_dec(v_abs_1659_);
v___x_1662_ = lean_unsigned_to_nat(2u);
v___x_1663_ = lean_nat_mul(v___x_1662_, v_a_1661_);
lean_dec(v_a_1661_);
v___x_1664_ = lean_nat_add(v___x_1663_, v_one_1660_);
lean_dec(v___x_1663_);
v___x_1665_ = lean_uint64_of_nat(v___x_1664_);
lean_dec(v___x_1664_);
v___y_1647_ = v___x_1665_;
goto v___jp_1646_;
}
v___jp_1646_:
{
uint64_t v___x_1648_; uint64_t v___x_1649_; uint64_t v___x_1650_; uint64_t v___x_1651_; uint64_t v___x_1652_; 
v___x_1648_ = lean_uint64_mix_hash(v___x_1645_, v___y_1647_);
v___x_1649_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_v_1643_);
v___x_1650_ = lean_uint64_mix_hash(v___x_1648_, v___x_1649_);
v___x_1651_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_p_1644_);
v___x_1652_ = lean_uint64_mix_hash(v___x_1650_, v___x_1651_);
return v___x_1652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePoly_hash___boxed(lean_object* v_x_1666_){
_start:
{
uint64_t v_res_1667_; lean_object* v_r_1668_; 
v_res_1667_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_x_1666_);
lean_dec_ref(v_x_1666_);
v_r_1668_ = lean_box_uint64(v_res_1667_);
return v_r_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg(lean_object* v_inst_1671_, lean_object* v_ctx_1672_, lean_object* v_p_1673_){
_start:
{
lean_object* v_toSemiring_1674_; lean_object* v_intCast_1675_; lean_object* v_toAdd_1676_; lean_object* v___x_1677_; 
v_toSemiring_1674_ = lean_ctor_get(v_inst_1671_, 0);
v_intCast_1675_ = lean_ctor_get(v_inst_1671_, 3);
v_toAdd_1676_ = lean_ctor_get(v_toSemiring_1674_, 0);
lean_inc(v_toAdd_1676_);
lean_inc_ref(v_inst_1671_);
v___x_1677_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1671_);
if (lean_obj_tag(v_p_1673_) == 0)
{
lean_object* v_k_1678_; lean_object* v___x_1679_; 
lean_inc(v_intCast_1675_);
lean_dec_ref(v___x_1677_);
lean_dec(v_toAdd_1676_);
lean_dec_ref(v_inst_1671_);
v_k_1678_ = lean_ctor_get(v_p_1673_, 0);
lean_inc(v_k_1678_);
lean_dec_ref(v_p_1673_);
v___x_1679_ = lean_apply_1(v_intCast_1675_, v_k_1678_);
return v___x_1679_;
}
else
{
lean_object* v_zsmul_1680_; lean_object* v_k_1681_; lean_object* v_v_1682_; lean_object* v_p_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_zsmul_1680_ = lean_ctor_get(v___x_1677_, 2);
lean_inc(v_zsmul_1680_);
lean_dec_ref(v___x_1677_);
v_k_1681_ = lean_ctor_get(v_p_1673_, 0);
lean_inc(v_k_1681_);
v_v_1682_ = lean_ctor_get(v_p_1673_, 1);
lean_inc(v_v_1682_);
v_p_1683_ = lean_ctor_get(v_p_1673_, 2);
lean_inc_ref(v_p_1683_);
lean_dec_ref(v_p_1673_);
lean_inc_ref(v_toSemiring_1674_);
v___x_1684_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_toSemiring_1674_, v_ctx_1672_, v_v_1682_);
v___x_1685_ = lean_apply_2(v_zsmul_1680_, v_k_1681_, v___x_1684_);
v___x_1686_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1671_, v_ctx_1672_, v_p_1683_);
v___x_1687_ = lean_apply_2(v_toAdd_1676_, v___x_1685_, v___x_1686_);
return v___x_1687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg___boxed(lean_object* v_inst_1688_, lean_object* v_ctx_1689_, lean_object* v_p_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1688_, v_ctx_1689_, v_p_1690_);
lean_dec_ref(v_ctx_1689_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote(lean_object* v_00_u03b1_1692_, lean_object* v_inst_1693_, lean_object* v_ctx_1694_, lean_object* v_p_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1693_, v_ctx_1694_, v_p_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___boxed(lean_object* v_00_u03b1_1697_, lean_object* v_inst_1698_, lean_object* v_ctx_1699_, lean_object* v_p_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Grind_CommRing_Poly_denote(v_00_u03b1_1697_, v_inst_1698_, v_ctx_1699_, v_p_1700_);
lean_dec_ref(v_ctx_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg(lean_object* v_inst_1702_, lean_object* v_ctx_1703_, lean_object* v_k_1704_, lean_object* v_m_1705_){
_start:
{
lean_object* v_toSemiring_1706_; lean_object* v___x_1707_; lean_object* v_zsmul_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v_toSemiring_1706_ = lean_ctor_get(v_inst_1702_, 0);
lean_inc_ref(v_toSemiring_1706_);
v___x_1707_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1702_);
v_zsmul_1708_ = lean_ctor_get(v___x_1707_, 2);
lean_inc(v_zsmul_1708_);
lean_dec_ref(v___x_1707_);
v___x_1709_ = lean_unsigned_to_nat(1u);
v___x_1710_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1711_ = lean_int_dec_eq(v_k_1704_, v___x_1710_);
if (v___x_1711_ == 0)
{
if (lean_obj_tag(v_m_1705_) == 0)
{
lean_object* v_ofNat_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_ofNat_1712_ = lean_ctor_get(v_toSemiring_1706_, 3);
lean_inc(v_ofNat_1712_);
lean_dec_ref(v_toSemiring_1706_);
v___x_1713_ = lean_apply_1(v_ofNat_1712_, v___x_1709_);
v___x_1714_ = lean_apply_2(v_zsmul_1708_, v_k_1704_, v___x_1713_);
return v___x_1714_;
}
else
{
lean_object* v_p_1715_; lean_object* v_m_1716_; lean_object* v_ofNat_1717_; lean_object* v_npow_1718_; lean_object* v_x_1719_; lean_object* v_k_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v_p_1715_ = lean_ctor_get(v_m_1705_, 0);
lean_inc_ref(v_p_1715_);
v_m_1716_ = lean_ctor_get(v_m_1705_, 1);
lean_inc(v_m_1716_);
lean_dec_ref(v_m_1705_);
v_ofNat_1717_ = lean_ctor_get(v_toSemiring_1706_, 3);
v_npow_1718_ = lean_ctor_get(v_toSemiring_1706_, 5);
v_x_1719_ = lean_ctor_get(v_p_1715_, 0);
lean_inc(v_x_1719_);
v_k_1720_ = lean_ctor_get(v_p_1715_, 1);
lean_inc(v_k_1720_);
lean_dec_ref(v_p_1715_);
v___x_1721_ = lean_unsigned_to_nat(0u);
v___x_1722_ = lean_nat_dec_eq(v_k_1720_, v___x_1721_);
if (v___x_1722_ == 0)
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_nat_dec_eq(v_k_1720_, v___x_1709_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1724_ = l_Lean_RArray_getImpl___redArg(v_ctx_1703_, v_x_1719_);
lean_dec(v_x_1719_);
lean_inc(v_npow_1718_);
v___x_1725_ = lean_apply_2(v_npow_1718_, v___x_1724_, v_k_1720_);
v___x_1726_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1706_, v_ctx_1703_, v_m_1716_, v___x_1725_);
v___x_1727_ = lean_apply_2(v_zsmul_1708_, v_k_1704_, v___x_1726_);
return v___x_1727_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v_k_1720_);
v___x_1728_ = l_Lean_RArray_getImpl___redArg(v_ctx_1703_, v_x_1719_);
lean_dec(v_x_1719_);
v___x_1729_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1706_, v_ctx_1703_, v_m_1716_, v___x_1728_);
v___x_1730_ = lean_apply_2(v_zsmul_1708_, v_k_1704_, v___x_1729_);
return v___x_1730_;
}
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v_k_1720_);
lean_dec(v_x_1719_);
lean_inc(v_ofNat_1717_);
v___x_1731_ = lean_apply_1(v_ofNat_1717_, v___x_1709_);
v___x_1732_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1706_, v_ctx_1703_, v_m_1716_, v___x_1731_);
v___x_1733_ = lean_apply_2(v_zsmul_1708_, v_k_1704_, v___x_1732_);
return v___x_1733_;
}
}
}
else
{
lean_dec(v_zsmul_1708_);
lean_dec(v_k_1704_);
if (lean_obj_tag(v_m_1705_) == 0)
{
lean_object* v_ofNat_1734_; lean_object* v___x_1735_; 
v_ofNat_1734_ = lean_ctor_get(v_toSemiring_1706_, 3);
lean_inc(v_ofNat_1734_);
lean_dec_ref(v_toSemiring_1706_);
v___x_1735_ = lean_apply_1(v_ofNat_1734_, v___x_1709_);
return v___x_1735_;
}
else
{
lean_object* v_p_1736_; lean_object* v_m_1737_; lean_object* v_ofNat_1738_; lean_object* v_npow_1739_; lean_object* v_x_1740_; lean_object* v_k_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v_p_1736_ = lean_ctor_get(v_m_1705_, 0);
lean_inc_ref(v_p_1736_);
v_m_1737_ = lean_ctor_get(v_m_1705_, 1);
lean_inc(v_m_1737_);
lean_dec_ref(v_m_1705_);
v_ofNat_1738_ = lean_ctor_get(v_toSemiring_1706_, 3);
v_npow_1739_ = lean_ctor_get(v_toSemiring_1706_, 5);
v_x_1740_ = lean_ctor_get(v_p_1736_, 0);
lean_inc(v_x_1740_);
v_k_1741_ = lean_ctor_get(v_p_1736_, 1);
lean_inc(v_k_1741_);
lean_dec_ref(v_p_1736_);
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = lean_nat_dec_eq(v_k_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_nat_dec_eq(v_k_1741_, v___x_1709_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = l_Lean_RArray_getImpl___redArg(v_ctx_1703_, v_x_1740_);
lean_dec(v_x_1740_);
lean_inc(v_npow_1739_);
v___x_1746_ = lean_apply_2(v_npow_1739_, v___x_1745_, v_k_1741_);
v___x_1747_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1706_, v_ctx_1703_, v_m_1737_, v___x_1746_);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec(v_k_1741_);
v___x_1748_ = l_Lean_RArray_getImpl___redArg(v_ctx_1703_, v_x_1740_);
lean_dec(v_x_1740_);
v___x_1749_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1706_, v_ctx_1703_, v_m_1737_, v___x_1748_);
return v___x_1749_;
}
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v_k_1741_);
lean_dec(v_x_1740_);
lean_inc(v_ofNat_1738_);
v___x_1750_ = lean_apply_1(v_ofNat_1738_, v___x_1709_);
v___x_1751_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1706_, v_ctx_1703_, v_m_1737_, v___x_1750_);
return v___x_1751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg___boxed(lean_object* v_inst_1752_, lean_object* v_ctx_1753_, lean_object* v_k_1754_, lean_object* v_m_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Grind_CommRing_denoteTerm___redArg(v_inst_1752_, v_ctx_1753_, v_k_1754_, v_m_1755_);
lean_dec_ref(v_ctx_1753_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm(lean_object* v_00_u03b1_1757_, lean_object* v_inst_1758_, lean_object* v_ctx_1759_, lean_object* v_k_1760_, lean_object* v_m_1761_){
_start:
{
lean_object* v_toSemiring_1762_; lean_object* v___x_1763_; lean_object* v_zsmul_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v_toSemiring_1762_ = lean_ctor_get(v_inst_1758_, 0);
lean_inc_ref(v_toSemiring_1762_);
v___x_1763_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1758_);
v_zsmul_1764_ = lean_ctor_get(v___x_1763_, 2);
lean_inc(v_zsmul_1764_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = lean_unsigned_to_nat(1u);
v___x_1766_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1767_ = lean_int_dec_eq(v_k_1760_, v___x_1766_);
if (v___x_1767_ == 0)
{
if (lean_obj_tag(v_m_1761_) == 0)
{
lean_object* v_ofNat_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_ofNat_1768_ = lean_ctor_get(v_toSemiring_1762_, 3);
lean_inc(v_ofNat_1768_);
lean_dec_ref(v_toSemiring_1762_);
v___x_1769_ = lean_apply_1(v_ofNat_1768_, v___x_1765_);
v___x_1770_ = lean_apply_2(v_zsmul_1764_, v_k_1760_, v___x_1769_);
return v___x_1770_;
}
else
{
lean_object* v_p_1771_; lean_object* v_m_1772_; lean_object* v_ofNat_1773_; lean_object* v_npow_1774_; lean_object* v_x_1775_; lean_object* v_k_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v_p_1771_ = lean_ctor_get(v_m_1761_, 0);
lean_inc_ref(v_p_1771_);
v_m_1772_ = lean_ctor_get(v_m_1761_, 1);
lean_inc(v_m_1772_);
lean_dec_ref(v_m_1761_);
v_ofNat_1773_ = lean_ctor_get(v_toSemiring_1762_, 3);
v_npow_1774_ = lean_ctor_get(v_toSemiring_1762_, 5);
v_x_1775_ = lean_ctor_get(v_p_1771_, 0);
lean_inc(v_x_1775_);
v_k_1776_ = lean_ctor_get(v_p_1771_, 1);
lean_inc(v_k_1776_);
lean_dec_ref(v_p_1771_);
v___x_1777_ = lean_unsigned_to_nat(0u);
v___x_1778_ = lean_nat_dec_eq(v_k_1776_, v___x_1777_);
if (v___x_1778_ == 0)
{
uint8_t v___x_1779_; 
v___x_1779_ = lean_nat_dec_eq(v_k_1776_, v___x_1765_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1780_ = l_Lean_RArray_getImpl___redArg(v_ctx_1759_, v_x_1775_);
lean_dec(v_x_1775_);
lean_inc(v_npow_1774_);
v___x_1781_ = lean_apply_2(v_npow_1774_, v___x_1780_, v_k_1776_);
v___x_1782_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1762_, v_ctx_1759_, v_m_1772_, v___x_1781_);
v___x_1783_ = lean_apply_2(v_zsmul_1764_, v_k_1760_, v___x_1782_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_dec(v_k_1776_);
v___x_1784_ = l_Lean_RArray_getImpl___redArg(v_ctx_1759_, v_x_1775_);
lean_dec(v_x_1775_);
v___x_1785_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1762_, v_ctx_1759_, v_m_1772_, v___x_1784_);
v___x_1786_ = lean_apply_2(v_zsmul_1764_, v_k_1760_, v___x_1785_);
return v___x_1786_;
}
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_dec(v_k_1776_);
lean_dec(v_x_1775_);
lean_inc(v_ofNat_1773_);
v___x_1787_ = lean_apply_1(v_ofNat_1773_, v___x_1765_);
v___x_1788_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1762_, v_ctx_1759_, v_m_1772_, v___x_1787_);
v___x_1789_ = lean_apply_2(v_zsmul_1764_, v_k_1760_, v___x_1788_);
return v___x_1789_;
}
}
}
else
{
lean_dec(v_zsmul_1764_);
lean_dec(v_k_1760_);
if (lean_obj_tag(v_m_1761_) == 0)
{
lean_object* v_ofNat_1790_; lean_object* v___x_1791_; 
v_ofNat_1790_ = lean_ctor_get(v_toSemiring_1762_, 3);
lean_inc(v_ofNat_1790_);
lean_dec_ref(v_toSemiring_1762_);
v___x_1791_ = lean_apply_1(v_ofNat_1790_, v___x_1765_);
return v___x_1791_;
}
else
{
lean_object* v_p_1792_; lean_object* v_m_1793_; lean_object* v_ofNat_1794_; lean_object* v_npow_1795_; lean_object* v_x_1796_; lean_object* v_k_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v_p_1792_ = lean_ctor_get(v_m_1761_, 0);
lean_inc_ref(v_p_1792_);
v_m_1793_ = lean_ctor_get(v_m_1761_, 1);
lean_inc(v_m_1793_);
lean_dec_ref(v_m_1761_);
v_ofNat_1794_ = lean_ctor_get(v_toSemiring_1762_, 3);
v_npow_1795_ = lean_ctor_get(v_toSemiring_1762_, 5);
v_x_1796_ = lean_ctor_get(v_p_1792_, 0);
lean_inc(v_x_1796_);
v_k_1797_ = lean_ctor_get(v_p_1792_, 1);
lean_inc(v_k_1797_);
lean_dec_ref(v_p_1792_);
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = lean_nat_dec_eq(v_k_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
uint8_t v___x_1800_; 
v___x_1800_ = lean_nat_dec_eq(v_k_1797_, v___x_1765_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = l_Lean_RArray_getImpl___redArg(v_ctx_1759_, v_x_1796_);
lean_dec(v_x_1796_);
lean_inc(v_npow_1795_);
v___x_1802_ = lean_apply_2(v_npow_1795_, v___x_1801_, v_k_1797_);
v___x_1803_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1762_, v_ctx_1759_, v_m_1793_, v___x_1802_);
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec(v_k_1797_);
v___x_1804_ = l_Lean_RArray_getImpl___redArg(v_ctx_1759_, v_x_1796_);
lean_dec(v_x_1796_);
v___x_1805_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1762_, v_ctx_1759_, v_m_1793_, v___x_1804_);
return v___x_1805_;
}
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_dec(v_k_1797_);
lean_dec(v_x_1796_);
lean_inc(v_ofNat_1794_);
v___x_1806_ = lean_apply_1(v_ofNat_1794_, v___x_1765_);
v___x_1807_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1762_, v_ctx_1759_, v_m_1793_, v___x_1806_);
return v___x_1807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___boxed(lean_object* v_00_u03b1_1808_, lean_object* v_inst_1809_, lean_object* v_ctx_1810_, lean_object* v_k_1811_, lean_object* v_m_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_Grind_CommRing_denoteTerm(v_00_u03b1_1808_, v_inst_1809_, v_ctx_1810_, v_k_1811_, v_m_1812_);
lean_dec_ref(v_ctx_1810_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(lean_object* v_inst_1814_, lean_object* v_ctx_1815_, lean_object* v_p_1816_, lean_object* v_acc_1817_){
_start:
{
if (lean_obj_tag(v_p_1816_) == 0)
{
lean_object* v_toSemiring_1818_; lean_object* v_intCast_1819_; lean_object* v_toAdd_1820_; lean_object* v_k_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v_toSemiring_1818_ = lean_ctor_get(v_inst_1814_, 0);
lean_inc_ref(v_toSemiring_1818_);
v_intCast_1819_ = lean_ctor_get(v_inst_1814_, 3);
lean_inc(v_intCast_1819_);
lean_dec_ref(v_inst_1814_);
v_toAdd_1820_ = lean_ctor_get(v_toSemiring_1818_, 0);
lean_inc(v_toAdd_1820_);
lean_dec_ref(v_toSemiring_1818_);
v_k_1821_ = lean_ctor_get(v_p_1816_, 0);
lean_inc(v_k_1821_);
lean_dec_ref(v_p_1816_);
v___x_1822_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1823_ = lean_int_dec_eq(v_k_1821_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_apply_1(v_intCast_1819_, v_k_1821_);
v___x_1825_ = lean_apply_2(v_toAdd_1820_, v_acc_1817_, v___x_1824_);
return v___x_1825_;
}
else
{
lean_dec(v_k_1821_);
lean_dec(v_toAdd_1820_);
lean_dec(v_intCast_1819_);
return v_acc_1817_;
}
}
else
{
lean_object* v_toSemiring_1826_; lean_object* v_toAdd_1827_; lean_object* v_ofNat_1828_; lean_object* v_npow_1829_; lean_object* v_k_1830_; lean_object* v_v_1831_; lean_object* v_p_1832_; lean_object* v___y_1834_; lean_object* v___x_1837_; lean_object* v_zsmul_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v_toSemiring_1826_ = lean_ctor_get(v_inst_1814_, 0);
v_toAdd_1827_ = lean_ctor_get(v_toSemiring_1826_, 0);
v_ofNat_1828_ = lean_ctor_get(v_toSemiring_1826_, 3);
v_npow_1829_ = lean_ctor_get(v_toSemiring_1826_, 5);
v_k_1830_ = lean_ctor_get(v_p_1816_, 0);
lean_inc(v_k_1830_);
v_v_1831_ = lean_ctor_get(v_p_1816_, 1);
lean_inc(v_v_1831_);
v_p_1832_ = lean_ctor_get(v_p_1816_, 2);
lean_inc_ref(v_p_1832_);
lean_dec_ref(v_p_1816_);
lean_inc_ref(v_inst_1814_);
v___x_1837_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1814_);
v_zsmul_1838_ = lean_ctor_get(v___x_1837_, 2);
lean_inc(v_zsmul_1838_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = lean_unsigned_to_nat(1u);
v___x_1840_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1841_ = lean_int_dec_eq(v_k_1830_, v___x_1840_);
if (v___x_1841_ == 0)
{
if (lean_obj_tag(v_v_1831_) == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
lean_inc(v_ofNat_1828_);
v___x_1842_ = lean_apply_1(v_ofNat_1828_, v___x_1839_);
v___x_1843_ = lean_apply_2(v_zsmul_1838_, v_k_1830_, v___x_1842_);
v___y_1834_ = v___x_1843_;
goto v___jp_1833_;
}
else
{
lean_object* v_p_1844_; lean_object* v_m_1845_; lean_object* v_x_1846_; lean_object* v_k_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v_p_1844_ = lean_ctor_get(v_v_1831_, 0);
lean_inc_ref(v_p_1844_);
v_m_1845_ = lean_ctor_get(v_v_1831_, 1);
lean_inc(v_m_1845_);
lean_dec_ref(v_v_1831_);
v_x_1846_ = lean_ctor_get(v_p_1844_, 0);
lean_inc(v_x_1846_);
v_k_1847_ = lean_ctor_get(v_p_1844_, 1);
lean_inc(v_k_1847_);
lean_dec_ref(v_p_1844_);
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = lean_nat_dec_eq(v_k_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_nat_dec_eq(v_k_1847_, v___x_1839_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1851_ = l_Lean_RArray_getImpl___redArg(v_ctx_1815_, v_x_1846_);
lean_dec(v_x_1846_);
lean_inc(v_npow_1829_);
v___x_1852_ = lean_apply_2(v_npow_1829_, v___x_1851_, v_k_1847_);
lean_inc_ref(v_toSemiring_1826_);
v___x_1853_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1826_, v_ctx_1815_, v_m_1845_, v___x_1852_);
v___x_1854_ = lean_apply_2(v_zsmul_1838_, v_k_1830_, v___x_1853_);
v___y_1834_ = v___x_1854_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec(v_k_1847_);
v___x_1855_ = l_Lean_RArray_getImpl___redArg(v_ctx_1815_, v_x_1846_);
lean_dec(v_x_1846_);
lean_inc_ref(v_toSemiring_1826_);
v___x_1856_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1826_, v_ctx_1815_, v_m_1845_, v___x_1855_);
v___x_1857_ = lean_apply_2(v_zsmul_1838_, v_k_1830_, v___x_1856_);
v___y_1834_ = v___x_1857_;
goto v___jp_1833_;
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_dec(v_k_1847_);
lean_dec(v_x_1846_);
lean_inc(v_ofNat_1828_);
v___x_1858_ = lean_apply_1(v_ofNat_1828_, v___x_1839_);
lean_inc_ref(v_toSemiring_1826_);
v___x_1859_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1826_, v_ctx_1815_, v_m_1845_, v___x_1858_);
v___x_1860_ = lean_apply_2(v_zsmul_1838_, v_k_1830_, v___x_1859_);
v___y_1834_ = v___x_1860_;
goto v___jp_1833_;
}
}
}
else
{
lean_dec(v_zsmul_1838_);
lean_dec(v_k_1830_);
if (lean_obj_tag(v_v_1831_) == 0)
{
lean_object* v___x_1861_; 
lean_inc(v_ofNat_1828_);
v___x_1861_ = lean_apply_1(v_ofNat_1828_, v___x_1839_);
v___y_1834_ = v___x_1861_;
goto v___jp_1833_;
}
else
{
lean_object* v_p_1862_; lean_object* v_m_1863_; lean_object* v_x_1864_; lean_object* v_k_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v_p_1862_ = lean_ctor_get(v_v_1831_, 0);
lean_inc_ref(v_p_1862_);
v_m_1863_ = lean_ctor_get(v_v_1831_, 1);
lean_inc(v_m_1863_);
lean_dec_ref(v_v_1831_);
v_x_1864_ = lean_ctor_get(v_p_1862_, 0);
lean_inc(v_x_1864_);
v_k_1865_ = lean_ctor_get(v_p_1862_, 1);
lean_inc(v_k_1865_);
lean_dec_ref(v_p_1862_);
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = lean_nat_dec_eq(v_k_1865_, v___x_1866_);
if (v___x_1867_ == 0)
{
uint8_t v___x_1868_; 
v___x_1868_ = lean_nat_dec_eq(v_k_1865_, v___x_1839_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = l_Lean_RArray_getImpl___redArg(v_ctx_1815_, v_x_1864_);
lean_dec(v_x_1864_);
lean_inc(v_npow_1829_);
v___x_1870_ = lean_apply_2(v_npow_1829_, v___x_1869_, v_k_1865_);
lean_inc_ref(v_toSemiring_1826_);
v___x_1871_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1826_, v_ctx_1815_, v_m_1863_, v___x_1870_);
v___y_1834_ = v___x_1871_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
lean_dec(v_k_1865_);
v___x_1872_ = l_Lean_RArray_getImpl___redArg(v_ctx_1815_, v_x_1864_);
lean_dec(v_x_1864_);
lean_inc_ref(v_toSemiring_1826_);
v___x_1873_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1826_, v_ctx_1815_, v_m_1863_, v___x_1872_);
v___y_1834_ = v___x_1873_;
goto v___jp_1833_;
}
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec(v_k_1865_);
lean_dec(v_x_1864_);
lean_inc(v_ofNat_1828_);
v___x_1874_ = lean_apply_1(v_ofNat_1828_, v___x_1839_);
lean_inc_ref(v_toSemiring_1826_);
v___x_1875_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1826_, v_ctx_1815_, v_m_1863_, v___x_1874_);
v___y_1834_ = v___x_1875_;
goto v___jp_1833_;
}
}
}
v___jp_1833_:
{
lean_object* v___x_1835_; 
lean_inc(v_toAdd_1827_);
v___x_1835_ = lean_apply_2(v_toAdd_1827_, v_acc_1817_, v___y_1834_);
v_p_1816_ = v_p_1832_;
v_acc_1817_ = v___x_1835_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg___boxed(lean_object* v_inst_1876_, lean_object* v_ctx_1877_, lean_object* v_p_1878_, lean_object* v_acc_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1876_, v_ctx_1877_, v_p_1878_, v_acc_1879_);
lean_dec_ref(v_ctx_1877_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go(lean_object* v_00_u03b1_1881_, lean_object* v_inst_1882_, lean_object* v_ctx_1883_, lean_object* v_p_1884_, lean_object* v_acc_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1882_, v_ctx_1883_, v_p_1884_, v_acc_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___boxed(lean_object* v_00_u03b1_1887_, lean_object* v_inst_1888_, lean_object* v_ctx_1889_, lean_object* v_p_1890_, lean_object* v_acc_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_Grind_CommRing_Poly_denote_x27_go(v_00_u03b1_1887_, v_inst_1888_, v_ctx_1889_, v_p_1890_, v_acc_1891_);
lean_dec_ref(v_ctx_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg(lean_object* v_inst_1893_, lean_object* v_ctx_1894_, lean_object* v_p_1895_){
_start:
{
if (lean_obj_tag(v_p_1895_) == 0)
{
lean_object* v_intCast_1896_; lean_object* v_k_1897_; lean_object* v___x_1898_; 
v_intCast_1896_ = lean_ctor_get(v_inst_1893_, 3);
lean_inc(v_intCast_1896_);
lean_dec_ref(v_inst_1893_);
v_k_1897_ = lean_ctor_get(v_p_1895_, 0);
lean_inc(v_k_1897_);
lean_dec_ref(v_p_1895_);
v___x_1898_ = lean_apply_1(v_intCast_1896_, v_k_1897_);
return v___x_1898_;
}
else
{
lean_object* v_toSemiring_1899_; lean_object* v_k_1900_; lean_object* v_v_1901_; lean_object* v_p_1902_; lean_object* v___x_1903_; lean_object* v_zsmul_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v_toSemiring_1899_ = lean_ctor_get(v_inst_1893_, 0);
v_k_1900_ = lean_ctor_get(v_p_1895_, 0);
lean_inc(v_k_1900_);
v_v_1901_ = lean_ctor_get(v_p_1895_, 1);
lean_inc(v_v_1901_);
v_p_1902_ = lean_ctor_get(v_p_1895_, 2);
lean_inc_ref(v_p_1902_);
lean_dec_ref(v_p_1895_);
lean_inc_ref(v_inst_1893_);
v___x_1903_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1893_);
v_zsmul_1904_ = lean_ctor_get(v___x_1903_, 2);
lean_inc(v_zsmul_1904_);
lean_dec_ref(v___x_1903_);
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1907_ = lean_int_dec_eq(v_k_1900_, v___x_1906_);
if (v___x_1907_ == 0)
{
if (lean_obj_tag(v_v_1901_) == 0)
{
lean_object* v_ofNat_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_ofNat_1908_ = lean_ctor_get(v_toSemiring_1899_, 3);
lean_inc(v_ofNat_1908_);
v___x_1909_ = lean_apply_1(v_ofNat_1908_, v___x_1905_);
v___x_1910_ = lean_apply_2(v_zsmul_1904_, v_k_1900_, v___x_1909_);
v___x_1911_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1893_, v_ctx_1894_, v_p_1902_, v___x_1910_);
return v___x_1911_;
}
else
{
lean_object* v_p_1912_; lean_object* v_m_1913_; lean_object* v_ofNat_1914_; lean_object* v_npow_1915_; lean_object* v_x_1916_; lean_object* v_k_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v_p_1912_ = lean_ctor_get(v_v_1901_, 0);
lean_inc_ref(v_p_1912_);
v_m_1913_ = lean_ctor_get(v_v_1901_, 1);
lean_inc(v_m_1913_);
lean_dec_ref(v_v_1901_);
v_ofNat_1914_ = lean_ctor_get(v_toSemiring_1899_, 3);
v_npow_1915_ = lean_ctor_get(v_toSemiring_1899_, 5);
v_x_1916_ = lean_ctor_get(v_p_1912_, 0);
lean_inc(v_x_1916_);
v_k_1917_ = lean_ctor_get(v_p_1912_, 1);
lean_inc(v_k_1917_);
lean_dec_ref(v_p_1912_);
v___x_1918_ = lean_unsigned_to_nat(0u);
v___x_1919_ = lean_nat_dec_eq(v_k_1917_, v___x_1918_);
if (v___x_1919_ == 0)
{
uint8_t v___x_1920_; 
v___x_1920_ = lean_nat_dec_eq(v_k_1917_, v___x_1905_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1921_ = l_Lean_RArray_getImpl___redArg(v_ctx_1894_, v_x_1916_);
lean_dec(v_x_1916_);
lean_inc(v_npow_1915_);
v___x_1922_ = lean_apply_2(v_npow_1915_, v___x_1921_, v_k_1917_);
lean_inc_ref(v_toSemiring_1899_);
v___x_1923_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1899_, v_ctx_1894_, v_m_1913_, v___x_1922_);
v___x_1924_ = lean_apply_2(v_zsmul_1904_, v_k_1900_, v___x_1923_);
v___x_1925_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1893_, v_ctx_1894_, v_p_1902_, v___x_1924_);
return v___x_1925_;
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_dec(v_k_1917_);
v___x_1926_ = l_Lean_RArray_getImpl___redArg(v_ctx_1894_, v_x_1916_);
lean_dec(v_x_1916_);
lean_inc_ref(v_toSemiring_1899_);
v___x_1927_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1899_, v_ctx_1894_, v_m_1913_, v___x_1926_);
v___x_1928_ = lean_apply_2(v_zsmul_1904_, v_k_1900_, v___x_1927_);
v___x_1929_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1893_, v_ctx_1894_, v_p_1902_, v___x_1928_);
return v___x_1929_;
}
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
lean_dec(v_k_1917_);
lean_dec(v_x_1916_);
lean_inc(v_ofNat_1914_);
v___x_1930_ = lean_apply_1(v_ofNat_1914_, v___x_1905_);
lean_inc_ref(v_toSemiring_1899_);
v___x_1931_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1899_, v_ctx_1894_, v_m_1913_, v___x_1930_);
v___x_1932_ = lean_apply_2(v_zsmul_1904_, v_k_1900_, v___x_1931_);
v___x_1933_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1893_, v_ctx_1894_, v_p_1902_, v___x_1932_);
return v___x_1933_;
}
}
}
else
{
lean_dec(v_zsmul_1904_);
lean_dec(v_k_1900_);
if (lean_obj_tag(v_v_1901_) == 0)
{
lean_object* v_ofNat_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_ofNat_1934_ = lean_ctor_get(v_toSemiring_1899_, 3);
lean_inc(v_ofNat_1934_);
v___x_1935_ = lean_apply_1(v_ofNat_1934_, v___x_1905_);
v___x_1936_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1893_, v_ctx_1894_, v_p_1902_, v___x_1935_);
return v___x_1936_;
}
else
{
lean_object* v_p_1937_; lean_object* v_m_1938_; lean_object* v_ofNat_1939_; lean_object* v_npow_1940_; lean_object* v_x_1941_; lean_object* v_k_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v_p_1937_ = lean_ctor_get(v_v_1901_, 0);
lean_inc_ref(v_p_1937_);
v_m_1938_ = lean_ctor_get(v_v_1901_, 1);
lean_inc(v_m_1938_);
lean_dec_ref(v_v_1901_);
v_ofNat_1939_ = lean_ctor_get(v_toSemiring_1899_, 3);
v_npow_1940_ = lean_ctor_get(v_toSemiring_1899_, 5);
v_x_1941_ = lean_ctor_get(v_p_1937_, 0);
lean_inc(v_x_1941_);
v_k_1942_ = lean_ctor_get(v_p_1937_, 1);
lean_inc(v_k_1942_);
lean_dec_ref(v_p_1937_);
v___x_1943_ = lean_unsigned_to_nat(0u);
v___x_1944_ = lean_nat_dec_eq(v_k_1942_, v___x_1943_);
if (v___x_1944_ == 0)
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_nat_dec_eq(v_k_1942_, v___x_1905_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1946_ = l_Lean_RArray_getImpl___redArg(v_ctx_1894_, v_x_1941_);
lean_dec(v_x_1941_);
lean_inc(v_npow_1940_);
v___x_1947_ = lean_apply_2(v_npow_1940_, v___x_1946_, v_k_1942_);
lean_inc_ref(v_toSemiring_1899_);
v___x_1948_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1899_, v_ctx_1894_, v_m_1938_, v___x_1947_);
v___x_1949_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1893_, v_ctx_1894_, v_p_1902_, v___x_1948_);
return v___x_1949_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_dec(v_k_1942_);
v___x_1950_ = l_Lean_RArray_getImpl___redArg(v_ctx_1894_, v_x_1941_);
lean_dec(v_x_1941_);
lean_inc_ref(v_toSemiring_1899_);
v___x_1951_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1899_, v_ctx_1894_, v_m_1938_, v___x_1950_);
v___x_1952_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1893_, v_ctx_1894_, v_p_1902_, v___x_1951_);
return v___x_1952_;
}
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec(v_k_1942_);
lean_dec(v_x_1941_);
lean_inc(v_ofNat_1939_);
v___x_1953_ = lean_apply_1(v_ofNat_1939_, v___x_1905_);
lean_inc_ref(v_toSemiring_1899_);
v___x_1954_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1899_, v_ctx_1894_, v_m_1938_, v___x_1953_);
v___x_1955_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1893_, v_ctx_1894_, v_p_1902_, v___x_1954_);
return v___x_1955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg___boxed(lean_object* v_inst_1956_, lean_object* v_ctx_1957_, lean_object* v_p_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_Grind_CommRing_Poly_denote_x27___redArg(v_inst_1956_, v_ctx_1957_, v_p_1958_);
lean_dec_ref(v_ctx_1957_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27(lean_object* v_00_u03b1_1960_, lean_object* v_inst_1961_, lean_object* v_ctx_1962_, lean_object* v_p_1963_){
_start:
{
if (lean_obj_tag(v_p_1963_) == 0)
{
lean_object* v_intCast_1964_; lean_object* v_k_1965_; lean_object* v___x_1966_; 
v_intCast_1964_ = lean_ctor_get(v_inst_1961_, 3);
lean_inc(v_intCast_1964_);
lean_dec_ref(v_inst_1961_);
v_k_1965_ = lean_ctor_get(v_p_1963_, 0);
lean_inc(v_k_1965_);
lean_dec_ref(v_p_1963_);
v___x_1966_ = lean_apply_1(v_intCast_1964_, v_k_1965_);
return v___x_1966_;
}
else
{
lean_object* v_toSemiring_1967_; lean_object* v_k_1968_; lean_object* v_v_1969_; lean_object* v_p_1970_; lean_object* v___x_1971_; lean_object* v_zsmul_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v_toSemiring_1967_ = lean_ctor_get(v_inst_1961_, 0);
v_k_1968_ = lean_ctor_get(v_p_1963_, 0);
lean_inc(v_k_1968_);
v_v_1969_ = lean_ctor_get(v_p_1963_, 1);
lean_inc(v_v_1969_);
v_p_1970_ = lean_ctor_get(v_p_1963_, 2);
lean_inc_ref(v_p_1970_);
lean_dec_ref(v_p_1963_);
lean_inc_ref(v_inst_1961_);
v___x_1971_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1961_);
v_zsmul_1972_ = lean_ctor_get(v___x_1971_, 2);
lean_inc(v_zsmul_1972_);
lean_dec_ref(v___x_1971_);
v___x_1973_ = lean_unsigned_to_nat(1u);
v___x_1974_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1975_ = lean_int_dec_eq(v_k_1968_, v___x_1974_);
if (v___x_1975_ == 0)
{
if (lean_obj_tag(v_v_1969_) == 0)
{
lean_object* v_ofNat_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_ofNat_1976_ = lean_ctor_get(v_toSemiring_1967_, 3);
lean_inc(v_ofNat_1976_);
v___x_1977_ = lean_apply_1(v_ofNat_1976_, v___x_1973_);
v___x_1978_ = lean_apply_2(v_zsmul_1972_, v_k_1968_, v___x_1977_);
v___x_1979_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1961_, v_ctx_1962_, v_p_1970_, v___x_1978_);
return v___x_1979_;
}
else
{
lean_object* v_p_1980_; lean_object* v_m_1981_; lean_object* v_ofNat_1982_; lean_object* v_npow_1983_; lean_object* v_x_1984_; lean_object* v_k_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v_p_1980_ = lean_ctor_get(v_v_1969_, 0);
lean_inc_ref(v_p_1980_);
v_m_1981_ = lean_ctor_get(v_v_1969_, 1);
lean_inc(v_m_1981_);
lean_dec_ref(v_v_1969_);
v_ofNat_1982_ = lean_ctor_get(v_toSemiring_1967_, 3);
v_npow_1983_ = lean_ctor_get(v_toSemiring_1967_, 5);
v_x_1984_ = lean_ctor_get(v_p_1980_, 0);
lean_inc(v_x_1984_);
v_k_1985_ = lean_ctor_get(v_p_1980_, 1);
lean_inc(v_k_1985_);
lean_dec_ref(v_p_1980_);
v___x_1986_ = lean_unsigned_to_nat(0u);
v___x_1987_ = lean_nat_dec_eq(v_k_1985_, v___x_1986_);
if (v___x_1987_ == 0)
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_nat_dec_eq(v_k_1985_, v___x_1973_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1989_ = l_Lean_RArray_getImpl___redArg(v_ctx_1962_, v_x_1984_);
lean_dec(v_x_1984_);
lean_inc(v_npow_1983_);
v___x_1990_ = lean_apply_2(v_npow_1983_, v___x_1989_, v_k_1985_);
lean_inc_ref(v_toSemiring_1967_);
v___x_1991_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1967_, v_ctx_1962_, v_m_1981_, v___x_1990_);
v___x_1992_ = lean_apply_2(v_zsmul_1972_, v_k_1968_, v___x_1991_);
v___x_1993_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1961_, v_ctx_1962_, v_p_1970_, v___x_1992_);
return v___x_1993_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_dec(v_k_1985_);
v___x_1994_ = l_Lean_RArray_getImpl___redArg(v_ctx_1962_, v_x_1984_);
lean_dec(v_x_1984_);
lean_inc_ref(v_toSemiring_1967_);
v___x_1995_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1967_, v_ctx_1962_, v_m_1981_, v___x_1994_);
v___x_1996_ = lean_apply_2(v_zsmul_1972_, v_k_1968_, v___x_1995_);
v___x_1997_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1961_, v_ctx_1962_, v_p_1970_, v___x_1996_);
return v___x_1997_;
}
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec(v_k_1985_);
lean_dec(v_x_1984_);
lean_inc(v_ofNat_1982_);
v___x_1998_ = lean_apply_1(v_ofNat_1982_, v___x_1973_);
lean_inc_ref(v_toSemiring_1967_);
v___x_1999_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1967_, v_ctx_1962_, v_m_1981_, v___x_1998_);
v___x_2000_ = lean_apply_2(v_zsmul_1972_, v_k_1968_, v___x_1999_);
v___x_2001_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1961_, v_ctx_1962_, v_p_1970_, v___x_2000_);
return v___x_2001_;
}
}
}
else
{
lean_dec(v_zsmul_1972_);
lean_dec(v_k_1968_);
if (lean_obj_tag(v_v_1969_) == 0)
{
lean_object* v_ofNat_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_ofNat_2002_ = lean_ctor_get(v_toSemiring_1967_, 3);
lean_inc(v_ofNat_2002_);
v___x_2003_ = lean_apply_1(v_ofNat_2002_, v___x_1973_);
v___x_2004_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1961_, v_ctx_1962_, v_p_1970_, v___x_2003_);
return v___x_2004_;
}
else
{
lean_object* v_p_2005_; lean_object* v_m_2006_; lean_object* v_ofNat_2007_; lean_object* v_npow_2008_; lean_object* v_x_2009_; lean_object* v_k_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v_p_2005_ = lean_ctor_get(v_v_1969_, 0);
lean_inc_ref(v_p_2005_);
v_m_2006_ = lean_ctor_get(v_v_1969_, 1);
lean_inc(v_m_2006_);
lean_dec_ref(v_v_1969_);
v_ofNat_2007_ = lean_ctor_get(v_toSemiring_1967_, 3);
v_npow_2008_ = lean_ctor_get(v_toSemiring_1967_, 5);
v_x_2009_ = lean_ctor_get(v_p_2005_, 0);
lean_inc(v_x_2009_);
v_k_2010_ = lean_ctor_get(v_p_2005_, 1);
lean_inc(v_k_2010_);
lean_dec_ref(v_p_2005_);
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2012_ = lean_nat_dec_eq(v_k_2010_, v___x_2011_);
if (v___x_2012_ == 0)
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_nat_dec_eq(v_k_2010_, v___x_1973_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2014_ = l_Lean_RArray_getImpl___redArg(v_ctx_1962_, v_x_2009_);
lean_dec(v_x_2009_);
lean_inc(v_npow_2008_);
v___x_2015_ = lean_apply_2(v_npow_2008_, v___x_2014_, v_k_2010_);
lean_inc_ref(v_toSemiring_1967_);
v___x_2016_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1967_, v_ctx_1962_, v_m_2006_, v___x_2015_);
v___x_2017_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1961_, v_ctx_1962_, v_p_1970_, v___x_2016_);
return v___x_2017_;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_dec(v_k_2010_);
v___x_2018_ = l_Lean_RArray_getImpl___redArg(v_ctx_1962_, v_x_2009_);
lean_dec(v_x_2009_);
lean_inc_ref(v_toSemiring_1967_);
v___x_2019_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1967_, v_ctx_1962_, v_m_2006_, v___x_2018_);
v___x_2020_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1961_, v_ctx_1962_, v_p_1970_, v___x_2019_);
return v___x_2020_;
}
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec(v_k_2010_);
lean_dec(v_x_2009_);
lean_inc(v_ofNat_2007_);
v___x_2021_ = lean_apply_1(v_ofNat_2007_, v___x_1973_);
lean_inc_ref(v_toSemiring_1967_);
v___x_2022_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1967_, v_ctx_1962_, v_m_2006_, v___x_2021_);
v___x_2023_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1961_, v_ctx_1962_, v_p_1970_, v___x_2022_);
return v___x_2023_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___boxed(lean_object* v_00_u03b1_2024_, lean_object* v_inst_2025_, lean_object* v_ctx_2026_, lean_object* v_p_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_Grind_CommRing_Poly_denote_x27(v_00_u03b1_2024_, v_inst_2025_, v_ctx_2026_, v_p_2027_);
lean_dec_ref(v_ctx_2026_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object* v_m_2029_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2031_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2032_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set(v___x_2032_, 1, v_m_2029_);
lean_ctor_set(v___x_2032_, 2, v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object* v_x_2033_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = l_Lean_Grind_CommRing_Mon_ofVar(v_x_2033_);
v___x_2035_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_isSorted(lean_object* v_x_2036_){
_start:
{
if (lean_obj_tag(v_x_2036_) == 0)
{
uint8_t v___x_2037_; 
v___x_2037_ = 1;
return v___x_2037_;
}
else
{
lean_object* v_p_2038_; 
v_p_2038_ = lean_ctor_get(v_x_2036_, 2);
if (lean_obj_tag(v_p_2038_) == 0)
{
uint8_t v___x_2039_; 
v___x_2039_ = 1;
return v___x_2039_;
}
else
{
lean_object* v_v_2040_; lean_object* v_v_2041_; uint8_t v___x_2042_; uint8_t v___x_2043_; uint8_t v___x_2044_; 
v_v_2040_ = lean_ctor_get(v_x_2036_, 1);
v_v_2041_ = lean_ctor_get(v_p_2038_, 1);
v___x_2042_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2040_, v_v_2041_);
v___x_2043_ = 2;
v___x_2044_ = l_instDecidableEqOrdering(v___x_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
return v___x_2044_;
}
else
{
v_x_2036_ = v_p_2038_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isSorted___boxed(lean_object* v_x_2046_){
_start:
{
uint8_t v_res_2047_; lean_object* v_r_2048_; 
v_res_2047_ = l_Lean_Grind_CommRing_Poly_isSorted(v_x_2046_);
lean_dec_ref(v_x_2046_);
v_r_2048_ = lean_box(v_res_2047_);
return v_r_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go(lean_object* v_k_2049_, lean_object* v_a_2050_){
_start:
{
if (lean_obj_tag(v_a_2050_) == 0)
{
lean_object* v_k_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2059_; 
v_k_2051_ = lean_ctor_get(v_a_2050_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_a_2050_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2053_ = v_a_2050_;
v_isShared_2054_ = v_isSharedCheck_2059_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_k_2051_);
lean_dec(v_a_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2059_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2055_ = lean_int_add(v_k_2051_, v_k_2049_);
lean_dec(v_k_2051_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2055_);
v___x_2057_ = v___x_2053_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
else
{
lean_object* v_k_2060_; lean_object* v_v_2061_; lean_object* v_p_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2070_; 
v_k_2060_ = lean_ctor_get(v_a_2050_, 0);
v_v_2061_ = lean_ctor_get(v_a_2050_, 1);
v_p_2062_ = lean_ctor_get(v_a_2050_, 2);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_a_2050_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2064_ = v_a_2050_;
v_isShared_2065_ = v_isSharedCheck_2070_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_p_2062_);
lean_inc(v_v_2061_);
lean_inc(v_k_2060_);
lean_dec(v_a_2050_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2070_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2066_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2049_, v_p_2062_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 2, v___x_2066_);
v___x_2068_ = v___x_2064_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_k_2060_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_v_2061_);
lean_ctor_set(v_reuseFailAlloc_2069_, 2, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go___boxed(lean_object* v_k_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2071_, v_a_2072_);
lean_dec(v_k_2071_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object* v_p_2074_, lean_object* v_k_2075_){
_start:
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2077_ = lean_int_dec_eq(v_k_2075_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2075_, v_p_2074_);
return v___x_2078_;
}
else
{
return v_p_2074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst___boxed(lean_object* v_p_2079_, lean_object* v_k_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2079_, v_k_2080_);
lean_dec(v_k_2080_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object* v_p_2082_, lean_object* v_h__1_2083_, lean_object* v_h__2_2084_){
_start:
{
if (lean_obj_tag(v_p_2082_) == 0)
{
lean_object* v_k_2085_; lean_object* v___x_2086_; 
lean_dec(v_h__2_2084_);
v_k_2085_ = lean_ctor_get(v_p_2082_, 0);
lean_inc(v_k_2085_);
lean_dec_ref(v_p_2082_);
v___x_2086_ = lean_apply_1(v_h__1_2083_, v_k_2085_);
return v___x_2086_;
}
else
{
lean_object* v_k_2087_; lean_object* v_v_2088_; lean_object* v_p_2089_; lean_object* v___x_2090_; 
lean_dec(v_h__1_2083_);
v_k_2087_ = lean_ctor_get(v_p_2082_, 0);
lean_inc(v_k_2087_);
v_v_2088_ = lean_ctor_get(v_p_2082_, 1);
lean_inc(v_v_2088_);
v_p_2089_ = lean_ctor_get(v_p_2082_, 2);
lean_inc_ref(v_p_2089_);
lean_dec_ref(v_p_2082_);
v___x_2090_ = lean_apply_3(v_h__2_2084_, v_k_2087_, v_v_2088_, v_p_2089_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object* v_motive_2091_, lean_object* v_p_2092_, lean_object* v_h__1_2093_, lean_object* v_h__2_2094_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(v_p_2092_, v_h__1_2093_, v_h__2_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert_go(lean_object* v_k_2096_, lean_object* v_m_2097_, lean_object* v_a_2098_){
_start:
{
if (lean_obj_tag(v_a_2098_) == 0)
{
lean_object* v___x_2099_; 
v___x_2099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2099_, 0, v_k_2096_);
lean_ctor_set(v___x_2099_, 1, v_m_2097_);
lean_ctor_set(v___x_2099_, 2, v_a_2098_);
return v___x_2099_;
}
else
{
lean_object* v_k_2100_; lean_object* v_v_2101_; lean_object* v_p_2102_; uint8_t v___x_2103_; 
v_k_2100_ = lean_ctor_get(v_a_2098_, 0);
v_v_2101_ = lean_ctor_get(v_a_2098_, 1);
v_p_2102_ = lean_ctor_get(v_a_2098_, 2);
v___x_2103_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2097_, v_v_2101_);
switch(v___x_2103_)
{
case 0:
{
lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2111_; 
lean_inc_ref(v_p_2102_);
lean_inc(v_v_2101_);
lean_inc(v_k_2100_);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_a_2098_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; lean_object* v_unused_2113_; lean_object* v_unused_2114_; 
v_unused_2112_ = lean_ctor_get(v_a_2098_, 2);
lean_dec(v_unused_2112_);
v_unused_2113_ = lean_ctor_get(v_a_2098_, 1);
lean_dec(v_unused_2113_);
v_unused_2114_ = lean_ctor_get(v_a_2098_, 0);
lean_dec(v_unused_2114_);
v___x_2105_ = v_a_2098_;
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
else
{
lean_dec(v_a_2098_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2096_, v_m_2097_, v_p_2102_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 2, v___x_2107_);
v___x_2109_ = v___x_2105_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_k_2100_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_v_2101_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
case 1:
{
lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2124_; 
lean_inc_ref(v_p_2102_);
lean_inc(v_k_2100_);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_a_2098_);
if (v_isSharedCheck_2124_ == 0)
{
lean_object* v_unused_2125_; lean_object* v_unused_2126_; lean_object* v_unused_2127_; 
v_unused_2125_ = lean_ctor_get(v_a_2098_, 2);
lean_dec(v_unused_2125_);
v_unused_2126_ = lean_ctor_get(v_a_2098_, 1);
lean_dec(v_unused_2126_);
v_unused_2127_ = lean_ctor_get(v_a_2098_, 0);
lean_dec(v_unused_2127_);
v___x_2116_ = v_a_2098_;
v_isShared_2117_ = v_isSharedCheck_2124_;
goto v_resetjp_2115_;
}
else
{
lean_dec(v_a_2098_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2124_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v_k_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v_k_2118_ = lean_int_add(v_k_2096_, v_k_2100_);
lean_dec(v_k_2100_);
lean_dec(v_k_2096_);
v___x_2119_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2120_ = lean_int_dec_eq(v_k_2118_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2122_; 
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 1, v_m_2097_);
lean_ctor_set(v___x_2116_, 0, v_k_2118_);
v___x_2122_ = v___x_2116_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_k_2118_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_m_2097_);
lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_p_2102_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
else
{
lean_dec(v_k_2118_);
lean_del_object(v___x_2116_);
lean_dec(v_m_2097_);
return v_p_2102_;
}
}
}
default: 
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2128_, 0, v_k_2096_);
lean_ctor_set(v___x_2128_, 1, v_m_2097_);
lean_ctor_set(v___x_2128_, 2, v_a_2098_);
return v___x_2128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert(lean_object* v_k_2129_, lean_object* v_m_2130_, lean_object* v_p_2131_){
_start:
{
lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2133_ = lean_int_dec_eq(v_k_2129_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = lean_box(0);
v___x_2135_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2130_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2129_, v_m_2130_, v_p_2131_);
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; 
lean_dec(v_m_2130_);
v___x_2137_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2131_, v_k_2129_);
lean_dec(v_k_2129_);
return v___x_2137_;
}
}
else
{
lean_dec(v_m_2130_);
lean_dec(v_k_2129_);
return v_p_2131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_concat(lean_object* v_p_u2081_2138_, lean_object* v_p_u2082_2139_){
_start:
{
if (lean_obj_tag(v_p_u2081_2138_) == 0)
{
lean_object* v_k_2140_; lean_object* v___x_2141_; 
v_k_2140_ = lean_ctor_get(v_p_u2081_2138_, 0);
lean_inc(v_k_2140_);
lean_dec_ref(v_p_u2081_2138_);
v___x_2141_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2139_, v_k_2140_);
lean_dec(v_k_2140_);
return v___x_2141_;
}
else
{
lean_object* v_k_2142_; lean_object* v_v_2143_; lean_object* v_p_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2152_; 
v_k_2142_ = lean_ctor_get(v_p_u2081_2138_, 0);
v_v_2143_ = lean_ctor_get(v_p_u2081_2138_, 1);
v_p_2144_ = lean_ctor_get(v_p_u2081_2138_, 2);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_p_u2081_2138_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2146_ = v_p_u2081_2138_;
v_isShared_2147_ = v_isSharedCheck_2152_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_p_2144_);
lean_inc(v_v_2143_);
lean_inc(v_k_2142_);
lean_dec(v_p_u2081_2138_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2152_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = l_Lean_Grind_CommRing_Poly_concat(v_p_2144_, v_p_u2082_2139_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 2, v___x_2148_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_k_2142_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_v_2143_);
lean_ctor_set(v_reuseFailAlloc_2151_, 2, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go(lean_object* v_k_2153_, lean_object* v_a_2154_){
_start:
{
if (lean_obj_tag(v_a_2154_) == 0)
{
lean_object* v_k_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2163_; 
v_k_2155_ = lean_ctor_get(v_a_2154_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_a_2154_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2157_ = v_a_2154_;
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_k_2155_);
lean_dec(v_a_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2159_ = lean_int_mul(v_k_2153_, v_k_2155_);
lean_dec(v_k_2155_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2159_);
v___x_2161_ = v___x_2157_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
else
{
lean_object* v_k_2164_; lean_object* v_v_2165_; lean_object* v_p_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2175_; 
v_k_2164_ = lean_ctor_get(v_a_2154_, 0);
v_v_2165_ = lean_ctor_get(v_a_2154_, 1);
v_p_2166_ = lean_ctor_get(v_a_2154_, 2);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_a_2154_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2168_ = v_a_2154_;
v_isShared_2169_ = v_isSharedCheck_2175_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_p_2166_);
lean_inc(v_v_2165_);
lean_inc(v_k_2164_);
lean_dec(v_a_2154_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2175_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2170_ = lean_int_mul(v_k_2153_, v_k_2164_);
lean_dec(v_k_2164_);
v___x_2171_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2153_, v_p_2166_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 2, v___x_2171_);
lean_ctor_set(v___x_2168_, 0, v___x_2170_);
v___x_2173_ = v___x_2168_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_v_2165_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go___boxed(lean_object* v_k_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2176_, v_a_2177_);
lean_dec(v_k_2176_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object* v_k_2179_, lean_object* v_p_2180_){
_start:
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2182_ = lean_int_dec_eq(v_k_2179_, v___x_2181_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2183_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2184_ = lean_int_dec_eq(v_k_2179_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2179_, v_p_2180_);
return v___x_2185_;
}
else
{
return v_p_2180_;
}
}
else
{
lean_object* v___x_2186_; 
lean_dec_ref(v_p_2180_);
v___x_2186_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst___boxed(lean_object* v_k_2187_, lean_object* v_p_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2187_, v_p_2188_);
lean_dec(v_k_2187_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go(lean_object* v_k_2190_, lean_object* v_m_2191_, lean_object* v_a_2192_){
_start:
{
if (lean_obj_tag(v_a_2192_) == 0)
{
lean_object* v_k_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v_k_2193_ = lean_ctor_get(v_a_2192_, 0);
lean_inc(v_k_2193_);
lean_dec_ref(v_a_2192_);
v___x_2194_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2195_ = lean_int_dec_eq(v_k_2193_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2196_ = lean_int_mul(v_k_2190_, v_k_2193_);
lean_dec(v_k_2193_);
v___x_2197_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2198_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2196_);
lean_ctor_set(v___x_2198_, 1, v_m_2191_);
lean_ctor_set(v___x_2198_, 2, v___x_2197_);
return v___x_2198_;
}
else
{
lean_object* v___x_2199_; 
lean_dec(v_k_2193_);
lean_dec(v_m_2191_);
v___x_2199_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2199_;
}
}
else
{
lean_object* v_k_2200_; lean_object* v_v_2201_; lean_object* v_p_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2212_; 
v_k_2200_ = lean_ctor_get(v_a_2192_, 0);
v_v_2201_ = lean_ctor_get(v_a_2192_, 1);
v_p_2202_ = lean_ctor_get(v_a_2192_, 2);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_a_2192_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2204_ = v_a_2192_;
v_isShared_2205_ = v_isSharedCheck_2212_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_p_2202_);
lean_inc(v_v_2201_);
lean_inc(v_k_2200_);
lean_dec(v_a_2192_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2212_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2206_ = lean_int_mul(v_k_2190_, v_k_2200_);
lean_dec(v_k_2200_);
lean_inc(v_m_2191_);
v___x_2207_ = l_Lean_Grind_CommRing_Mon_mul(v_m_2191_, v_v_2201_);
v___x_2208_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2190_, v_m_2191_, v_p_2202_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 2, v___x_2208_);
lean_ctor_set(v___x_2204_, 1, v___x_2207_);
lean_ctor_set(v___x_2204_, 0, v___x_2206_);
v___x_2210_ = v___x_2204_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2206_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v___x_2207_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go___boxed(lean_object* v_k_2213_, lean_object* v_m_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2213_, v_m_2214_, v_a_2215_);
lean_dec(v_k_2213_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object* v_k_2217_, lean_object* v_m_2218_, lean_object* v_p_2219_){
_start:
{
lean_object* v___x_2220_; uint8_t v___x_2221_; 
v___x_2220_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2221_ = lean_int_dec_eq(v_k_2217_, v___x_2220_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; uint8_t v___x_2223_; 
v___x_2222_ = lean_box(0);
v___x_2223_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2218_, v___x_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2217_, v_m_2218_, v_p_2219_);
return v___x_2224_;
}
else
{
lean_object* v___x_2225_; 
lean_dec(v_m_2218_);
v___x_2225_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2217_, v_p_2219_);
return v___x_2225_;
}
}
else
{
lean_object* v___x_2226_; 
lean_dec_ref(v_p_2219_);
lean_dec(v_m_2218_);
v___x_2226_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon___boxed(lean_object* v_k_2227_, lean_object* v_m_2228_, lean_object* v_p_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2227_, v_m_2228_, v_p_2229_);
lean_dec(v_k_2227_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go(lean_object* v_k_2231_, lean_object* v_m_2232_, lean_object* v_p_2233_, lean_object* v_acc_2234_){
_start:
{
if (lean_obj_tag(v_p_2233_) == 0)
{
lean_object* v_k_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v_k_2235_ = lean_ctor_get(v_p_2233_, 0);
lean_inc(v_k_2235_);
lean_dec_ref(v_p_2233_);
v___x_2236_ = lean_int_mul(v_k_2231_, v_k_2235_);
lean_dec(v_k_2235_);
v___x_2237_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2236_, v_m_2232_, v_acc_2234_);
return v___x_2237_;
}
else
{
lean_object* v_k_2238_; lean_object* v_v_2239_; lean_object* v_p_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v_k_2238_ = lean_ctor_get(v_p_2233_, 0);
lean_inc(v_k_2238_);
v_v_2239_ = lean_ctor_get(v_p_2233_, 1);
lean_inc(v_v_2239_);
v_p_2240_ = lean_ctor_get(v_p_2233_, 2);
lean_inc_ref(v_p_2240_);
lean_dec_ref(v_p_2233_);
v___x_2241_ = lean_int_mul(v_k_2231_, v_k_2238_);
lean_dec(v_k_2238_);
lean_inc(v_m_2232_);
v___x_2242_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_2232_, v_v_2239_);
v___x_2243_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2241_, v___x_2242_, v_acc_2234_);
v_p_2233_ = v_p_2240_;
v_acc_2234_ = v___x_2243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go___boxed(lean_object* v_k_2245_, lean_object* v_m_2246_, lean_object* v_p_2247_, lean_object* v_acc_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2245_, v_m_2246_, v_p_2247_, v_acc_2248_);
lean_dec(v_k_2245_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc(lean_object* v_k_2250_, lean_object* v_m_2251_, lean_object* v_p_2252_){
_start:
{
lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2254_ = lean_int_dec_eq(v_k_2250_, v___x_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2251_, v___x_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2258_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2250_, v_m_2251_, v_p_2252_, v___x_2257_);
return v___x_2258_;
}
else
{
lean_object* v___x_2259_; 
lean_dec(v_m_2251_);
v___x_2259_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2250_, v_p_2252_);
return v___x_2259_;
}
}
else
{
lean_object* v___x_2260_; 
lean_dec_ref(v_p_2252_);
lean_dec(v_m_2251_);
v___x_2260_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc___boxed(lean_object* v_k_2261_, lean_object* v_m_2262_, lean_object* v_p_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2261_, v_m_2262_, v_p_2263_);
lean_dec(v_k_2261_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_go(lean_object* v_fuel_2265_, lean_object* v_p_u2081_2266_, lean_object* v_p_u2082_2267_){
_start:
{
lean_object* v_zero_2268_; uint8_t v_isZero_2269_; 
v_zero_2268_ = lean_unsigned_to_nat(0u);
v_isZero_2269_ = lean_nat_dec_eq(v_fuel_2265_, v_zero_2268_);
if (v_isZero_2269_ == 1)
{
lean_object* v___x_2270_; 
lean_dec(v_fuel_2265_);
v___x_2270_ = l_Lean_Grind_CommRing_Poly_concat(v_p_u2081_2266_, v_p_u2082_2267_);
return v___x_2270_;
}
else
{
if (lean_obj_tag(v_p_u2081_2266_) == 0)
{
lean_dec(v_fuel_2265_);
if (lean_obj_tag(v_p_u2082_2267_) == 0)
{
lean_object* v_k_2271_; lean_object* v_k_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2280_; 
v_k_2271_ = lean_ctor_get(v_p_u2081_2266_, 0);
lean_inc(v_k_2271_);
lean_dec_ref(v_p_u2081_2266_);
v_k_2272_ = lean_ctor_get(v_p_u2082_2267_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_p_u2082_2267_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2274_ = v_p_u2082_2267_;
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_k_2272_);
lean_dec(v_p_u2082_2267_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2276_ = lean_int_add(v_k_2271_, v_k_2272_);
lean_dec(v_k_2272_);
lean_dec(v_k_2271_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2276_);
v___x_2278_ = v___x_2274_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
else
{
lean_object* v_k_2281_; lean_object* v___x_2282_; 
v_k_2281_ = lean_ctor_get(v_p_u2081_2266_, 0);
lean_inc(v_k_2281_);
lean_dec_ref(v_p_u2081_2266_);
v___x_2282_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2267_, v_k_2281_);
lean_dec(v_k_2281_);
return v___x_2282_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_2267_) == 0)
{
lean_object* v_k_2283_; lean_object* v___x_2284_; 
lean_dec(v_fuel_2265_);
v_k_2283_ = lean_ctor_get(v_p_u2082_2267_, 0);
lean_inc(v_k_2283_);
lean_dec_ref(v_p_u2082_2267_);
v___x_2284_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2081_2266_, v_k_2283_);
lean_dec(v_k_2283_);
return v___x_2284_;
}
else
{
lean_object* v_k_2285_; lean_object* v_v_2286_; lean_object* v_p_2287_; lean_object* v_k_2288_; lean_object* v_v_2289_; lean_object* v_p_2290_; lean_object* v_one_2291_; lean_object* v_n_2292_; uint8_t v___x_2293_; 
v_k_2285_ = lean_ctor_get(v_p_u2081_2266_, 0);
v_v_2286_ = lean_ctor_get(v_p_u2081_2266_, 1);
v_p_2287_ = lean_ctor_get(v_p_u2081_2266_, 2);
v_k_2288_ = lean_ctor_get(v_p_u2082_2267_, 0);
v_v_2289_ = lean_ctor_get(v_p_u2082_2267_, 1);
v_p_2290_ = lean_ctor_get(v_p_u2082_2267_, 2);
v_one_2291_ = lean_unsigned_to_nat(1u);
v_n_2292_ = lean_nat_sub(v_fuel_2265_, v_one_2291_);
lean_dec(v_fuel_2265_);
v___x_2293_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2286_, v_v_2289_);
switch(v___x_2293_)
{
case 0:
{
lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2301_; 
lean_inc_ref(v_p_2290_);
lean_inc(v_v_2289_);
lean_inc(v_k_2288_);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_p_u2082_2267_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; lean_object* v_unused_2303_; lean_object* v_unused_2304_; 
v_unused_2302_ = lean_ctor_get(v_p_u2082_2267_, 2);
lean_dec(v_unused_2302_);
v_unused_2303_ = lean_ctor_get(v_p_u2082_2267_, 1);
lean_dec(v_unused_2303_);
v_unused_2304_ = lean_ctor_get(v_p_u2082_2267_, 0);
lean_dec(v_unused_2304_);
v___x_2295_ = v_p_u2082_2267_;
v_isShared_2296_ = v_isSharedCheck_2301_;
goto v_resetjp_2294_;
}
else
{
lean_dec(v_p_u2082_2267_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2301_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2297_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2292_, v_p_u2081_2266_, v_p_2290_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 2, v___x_2297_);
v___x_2299_ = v___x_2295_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_k_2288_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_v_2289_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
case 1:
{
lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2316_; 
lean_inc_ref(v_p_2290_);
lean_inc(v_k_2288_);
lean_inc_ref(v_p_2287_);
lean_inc(v_v_2286_);
lean_inc(v_k_2285_);
lean_dec_ref(v_p_u2081_2266_);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_p_u2082_2267_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; lean_object* v_unused_2318_; lean_object* v_unused_2319_; 
v_unused_2317_ = lean_ctor_get(v_p_u2082_2267_, 2);
lean_dec(v_unused_2317_);
v_unused_2318_ = lean_ctor_get(v_p_u2082_2267_, 1);
lean_dec(v_unused_2318_);
v_unused_2319_ = lean_ctor_get(v_p_u2082_2267_, 0);
lean_dec(v_unused_2319_);
v___x_2306_ = v_p_u2082_2267_;
v_isShared_2307_ = v_isSharedCheck_2316_;
goto v_resetjp_2305_;
}
else
{
lean_dec(v_p_u2082_2267_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2316_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_k_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v_k_2308_ = lean_int_add(v_k_2285_, v_k_2288_);
lean_dec(v_k_2288_);
lean_dec(v_k_2285_);
v___x_2309_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2310_ = lean_int_dec_eq(v_k_2308_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2292_, v_p_2287_, v_p_2290_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 2, v___x_2311_);
lean_ctor_set(v___x_2306_, 1, v_v_2286_);
lean_ctor_set(v___x_2306_, 0, v_k_2308_);
v___x_2313_ = v___x_2306_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_k_2308_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_v_2286_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
else
{
lean_dec(v_k_2308_);
lean_del_object(v___x_2306_);
lean_dec(v_v_2286_);
v_fuel_2265_ = v_n_2292_;
v_p_u2081_2266_ = v_p_2287_;
v_p_u2082_2267_ = v_p_2290_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2327_; 
lean_inc_ref(v_p_2287_);
lean_inc(v_v_2286_);
lean_inc(v_k_2285_);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_p_u2081_2266_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; lean_object* v_unused_2329_; lean_object* v_unused_2330_; 
v_unused_2328_ = lean_ctor_get(v_p_u2081_2266_, 2);
lean_dec(v_unused_2328_);
v_unused_2329_ = lean_ctor_get(v_p_u2081_2266_, 1);
lean_dec(v_unused_2329_);
v_unused_2330_ = lean_ctor_get(v_p_u2081_2266_, 0);
lean_dec(v_unused_2330_);
v___x_2321_ = v_p_u2081_2266_;
v_isShared_2322_ = v_isSharedCheck_2327_;
goto v_resetjp_2320_;
}
else
{
lean_dec(v_p_u2081_2266_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2327_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2323_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2292_, v_p_2287_, v_p_u2082_2267_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 2, v___x_2323_);
v___x_2325_ = v___x_2321_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_k_2285_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_v_2286_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object* v_p_u2081_2331_, lean_object* v_p_u2082_2332_){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = lean_unsigned_to_nat(1000000u);
v___x_2334_ = l_Lean_Grind_CommRing_Poly_combine_go(v___x_2333_, v_p_u2081_2331_, v_p_u2082_2332_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object* v_p_u2081_2335_, lean_object* v_p_u2082_2336_, lean_object* v_h__1_2337_, lean_object* v_h__2_2338_, lean_object* v_h__3_2339_, lean_object* v_h__4_2340_){
_start:
{
if (lean_obj_tag(v_p_u2081_2335_) == 0)
{
lean_dec(v_h__4_2340_);
lean_dec(v_h__3_2339_);
if (lean_obj_tag(v_p_u2082_2336_) == 0)
{
lean_object* v_k_2341_; lean_object* v_k_2342_; lean_object* v___x_2343_; 
lean_dec(v_h__2_2338_);
v_k_2341_ = lean_ctor_get(v_p_u2081_2335_, 0);
lean_inc(v_k_2341_);
lean_dec_ref(v_p_u2081_2335_);
v_k_2342_ = lean_ctor_get(v_p_u2082_2336_, 0);
lean_inc(v_k_2342_);
lean_dec_ref(v_p_u2082_2336_);
v___x_2343_ = lean_apply_2(v_h__1_2337_, v_k_2341_, v_k_2342_);
return v___x_2343_;
}
else
{
lean_object* v_k_2344_; lean_object* v_k_2345_; lean_object* v_v_2346_; lean_object* v_p_2347_; lean_object* v___x_2348_; 
lean_dec(v_h__1_2337_);
v_k_2344_ = lean_ctor_get(v_p_u2081_2335_, 0);
lean_inc(v_k_2344_);
lean_dec_ref(v_p_u2081_2335_);
v_k_2345_ = lean_ctor_get(v_p_u2082_2336_, 0);
lean_inc(v_k_2345_);
v_v_2346_ = lean_ctor_get(v_p_u2082_2336_, 1);
lean_inc(v_v_2346_);
v_p_2347_ = lean_ctor_get(v_p_u2082_2336_, 2);
lean_inc_ref(v_p_2347_);
lean_dec_ref(v_p_u2082_2336_);
v___x_2348_ = lean_apply_4(v_h__2_2338_, v_k_2344_, v_k_2345_, v_v_2346_, v_p_2347_);
return v___x_2348_;
}
}
else
{
lean_dec(v_h__2_2338_);
lean_dec(v_h__1_2337_);
if (lean_obj_tag(v_p_u2082_2336_) == 0)
{
lean_object* v_k_2349_; lean_object* v_v_2350_; lean_object* v_p_2351_; lean_object* v_k_2352_; lean_object* v___x_2353_; 
lean_dec(v_h__4_2340_);
v_k_2349_ = lean_ctor_get(v_p_u2081_2335_, 0);
lean_inc(v_k_2349_);
v_v_2350_ = lean_ctor_get(v_p_u2081_2335_, 1);
lean_inc(v_v_2350_);
v_p_2351_ = lean_ctor_get(v_p_u2081_2335_, 2);
lean_inc_ref(v_p_2351_);
lean_dec_ref(v_p_u2081_2335_);
v_k_2352_ = lean_ctor_get(v_p_u2082_2336_, 0);
lean_inc(v_k_2352_);
lean_dec_ref(v_p_u2082_2336_);
v___x_2353_ = lean_apply_4(v_h__3_2339_, v_k_2349_, v_v_2350_, v_p_2351_, v_k_2352_);
return v___x_2353_;
}
else
{
lean_object* v_k_2354_; lean_object* v_v_2355_; lean_object* v_p_2356_; lean_object* v_k_2357_; lean_object* v_v_2358_; lean_object* v_p_2359_; lean_object* v___x_2360_; 
lean_dec(v_h__3_2339_);
v_k_2354_ = lean_ctor_get(v_p_u2081_2335_, 0);
lean_inc(v_k_2354_);
v_v_2355_ = lean_ctor_get(v_p_u2081_2335_, 1);
lean_inc(v_v_2355_);
v_p_2356_ = lean_ctor_get(v_p_u2081_2335_, 2);
lean_inc_ref(v_p_2356_);
lean_dec_ref(v_p_u2081_2335_);
v_k_2357_ = lean_ctor_get(v_p_u2082_2336_, 0);
lean_inc(v_k_2357_);
v_v_2358_ = lean_ctor_get(v_p_u2082_2336_, 1);
lean_inc(v_v_2358_);
v_p_2359_ = lean_ctor_get(v_p_u2082_2336_, 2);
lean_inc_ref(v_p_2359_);
lean_dec_ref(v_p_u2082_2336_);
v___x_2360_ = lean_apply_6(v_h__4_2340_, v_k_2354_, v_v_2355_, v_p_2356_, v_k_2357_, v_v_2358_, v_p_2359_);
return v___x_2360_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object* v_motive_2361_, lean_object* v_p_u2081_2362_, lean_object* v_p_u2082_2363_, lean_object* v_h__1_2364_, lean_object* v_h__2_2365_, lean_object* v_h__3_2366_, lean_object* v_h__4_2367_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(v_p_u2081_2362_, v_p_u2082_2363_, v_h__1_2364_, v_h__2_2365_, v_h__3_2366_, v_h__4_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t v_x_2369_, lean_object* v_h__1_2370_, lean_object* v_h__2_2371_, lean_object* v_h__3_2372_){
_start:
{
switch(v_x_2369_)
{
case 0:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec(v_h__2_2371_);
lean_dec(v_h__1_2370_);
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_apply_1(v_h__3_2372_, v___x_2373_);
return v___x_2374_;
}
case 1:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
lean_dec(v_h__3_2372_);
lean_dec(v_h__2_2371_);
v___x_2375_ = lean_box(0);
v___x_2376_ = lean_apply_1(v_h__1_2370_, v___x_2375_);
return v___x_2376_;
}
default: 
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_dec(v_h__3_2372_);
lean_dec(v_h__1_2370_);
v___x_2377_ = lean_box(0);
v___x_2378_ = lean_apply_1(v_h__2_2371_, v___x_2377_);
return v___x_2378_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object* v_x_2379_, lean_object* v_h__1_2380_, lean_object* v_h__2_2381_, lean_object* v_h__3_2382_){
_start:
{
uint8_t v_x_30__boxed_2383_; lean_object* v_res_2384_; 
v_x_30__boxed_2383_ = lean_unbox(v_x_2379_);
v_res_2384_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(v_x_30__boxed_2383_, v_h__1_2380_, v_h__2_2381_, v_h__3_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object* v_motive_2385_, uint8_t v_x_2386_, lean_object* v_h__1_2387_, lean_object* v_h__2_2388_, lean_object* v_h__3_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(v_x_2386_, v_h__1_2387_, v_h__2_2388_, v_h__3_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object* v_motive_2391_, lean_object* v_x_2392_, lean_object* v_h__1_2393_, lean_object* v_h__2_2394_, lean_object* v_h__3_2395_){
_start:
{
uint8_t v_x_45__boxed_2396_; lean_object* v_res_2397_; 
v_x_45__boxed_2396_ = lean_unbox(v_x_2392_);
v_res_2397_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(v_motive_2391_, v_x_45__boxed_2396_, v_h__1_2393_, v_h__2_2394_, v_h__3_2395_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul_go(lean_object* v_p_u2082_2398_, lean_object* v_p_u2081_2399_, lean_object* v_acc_2400_){
_start:
{
if (lean_obj_tag(v_p_u2081_2399_) == 0)
{
lean_object* v_k_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_k_2401_ = lean_ctor_get(v_p_u2081_2399_, 0);
lean_inc(v_k_2401_);
lean_dec_ref(v_p_u2081_2399_);
v___x_2402_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2401_, v_p_u2082_2398_);
lean_dec(v_k_2401_);
v___x_2403_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2400_, v___x_2402_);
return v___x_2403_;
}
else
{
lean_object* v_k_2404_; lean_object* v_v_2405_; lean_object* v_p_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v_k_2404_ = lean_ctor_get(v_p_u2081_2399_, 0);
lean_inc(v_k_2404_);
v_v_2405_ = lean_ctor_get(v_p_u2081_2399_, 1);
lean_inc(v_v_2405_);
v_p_2406_ = lean_ctor_get(v_p_u2081_2399_, 2);
lean_inc_ref(v_p_2406_);
lean_dec_ref(v_p_u2081_2399_);
lean_inc_ref(v_p_u2082_2398_);
v___x_2407_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2404_, v_v_2405_, v_p_u2082_2398_);
lean_dec(v_k_2404_);
v___x_2408_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2400_, v___x_2407_);
v_p_u2081_2399_ = v_p_2406_;
v_acc_2400_ = v___x_2408_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul(lean_object* v_p_u2081_2410_, lean_object* v_p_u2082_2411_){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2413_ = l_Lean_Grind_CommRing_Poly_mul_go(v_p_u2082_2411_, v_p_u2081_2410_, v___x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc_go(lean_object* v_p_u2082_2414_, lean_object* v_p_u2081_2415_, lean_object* v_acc_2416_){
_start:
{
if (lean_obj_tag(v_p_u2081_2415_) == 0)
{
lean_object* v_k_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v_k_2417_ = lean_ctor_get(v_p_u2081_2415_, 0);
lean_inc(v_k_2417_);
lean_dec_ref(v_p_u2081_2415_);
v___x_2418_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2417_, v_p_u2082_2414_);
lean_dec(v_k_2417_);
v___x_2419_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2416_, v___x_2418_);
return v___x_2419_;
}
else
{
lean_object* v_k_2420_; lean_object* v_v_2421_; lean_object* v_p_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v_k_2420_ = lean_ctor_get(v_p_u2081_2415_, 0);
lean_inc(v_k_2420_);
v_v_2421_ = lean_ctor_get(v_p_u2081_2415_, 1);
lean_inc(v_v_2421_);
v_p_2422_ = lean_ctor_get(v_p_u2081_2415_, 2);
lean_inc_ref(v_p_2422_);
lean_dec_ref(v_p_u2081_2415_);
lean_inc_ref(v_p_u2082_2414_);
v___x_2423_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2420_, v_v_2421_, v_p_u2082_2414_);
lean_dec(v_k_2420_);
v___x_2424_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2416_, v___x_2423_);
v_p_u2081_2415_ = v_p_2422_;
v_acc_2416_ = v___x_2424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object* v_p_u2081_2426_, lean_object* v_p_u2082_2427_){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2429_ = l_Lean_Grind_CommRing_Poly_mul__nc_go(v_p_u2082_2427_, v_p_u2081_2426_, v___x_2428_);
return v___x_2429_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_pow___closed__0(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow(lean_object* v_p_2432_, lean_object* v_k_2433_){
_start:
{
lean_object* v_zero_2434_; uint8_t v_isZero_2435_; 
v_zero_2434_ = lean_unsigned_to_nat(0u);
v_isZero_2435_ = lean_nat_dec_eq(v_k_2433_, v_zero_2434_);
if (v_isZero_2435_ == 1)
{
lean_object* v___x_2436_; 
lean_dec_ref(v_p_2432_);
v___x_2436_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2436_;
}
else
{
lean_object* v_one_2437_; lean_object* v_n_2438_; uint8_t v___x_2439_; 
v_one_2437_ = lean_unsigned_to_nat(1u);
v_n_2438_ = lean_nat_sub(v_k_2433_, v_one_2437_);
v___x_2439_ = lean_nat_dec_eq(v_n_2438_, v_zero_2434_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
lean_inc_ref(v_p_2432_);
v___x_2440_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2432_, v_n_2438_);
lean_dec(v_n_2438_);
v___x_2441_ = l_Lean_Grind_CommRing_Poly_mul(v_p_2432_, v___x_2440_);
return v___x_2441_;
}
else
{
lean_dec(v_n_2438_);
return v_p_2432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow___boxed(lean_object* v_p_2442_, lean_object* v_k_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2442_, v_k_2443_);
lean_dec(v_k_2443_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc(lean_object* v_p_2445_, lean_object* v_k_2446_){
_start:
{
lean_object* v_zero_2447_; uint8_t v_isZero_2448_; 
v_zero_2447_ = lean_unsigned_to_nat(0u);
v_isZero_2448_ = lean_nat_dec_eq(v_k_2446_, v_zero_2447_);
if (v_isZero_2448_ == 1)
{
lean_object* v___x_2449_; 
lean_dec_ref(v_p_2445_);
v___x_2449_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2449_;
}
else
{
lean_object* v_one_2450_; lean_object* v_n_2451_; uint8_t v___x_2452_; 
v_one_2450_ = lean_unsigned_to_nat(1u);
v_n_2451_ = lean_nat_sub(v_k_2446_, v_one_2450_);
v___x_2452_ = lean_nat_dec_eq(v_n_2451_, v_zero_2447_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
lean_inc_ref(v_p_2445_);
v___x_2453_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2445_, v_n_2451_);
lean_dec(v_n_2451_);
v___x_2454_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2453_, v_p_2445_);
return v___x_2454_;
}
else
{
lean_dec(v_n_2451_);
return v_p_2445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc___boxed(lean_object* v_p_2455_, lean_object* v_k_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2455_, v_k_2456_);
lean_dec(v_k_2456_);
return v_res_2457_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2459_ = lean_int_neg(v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object* v_x_2460_){
_start:
{
switch(lean_obj_tag(v_x_2460_))
{
case 0:
{
lean_object* v_k_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
v_k_2461_ = lean_ctor_get(v_x_2460_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_x_2460_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v_x_2460_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_k_2461_);
lean_dec(v_x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_k_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
case 1:
{
lean_object* v_k_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2477_; 
v_k_2469_ = lean_ctor_get(v_x_2460_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_x_2460_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2471_ = v_x_2460_;
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_k_2469_);
lean_dec(v_x_2460_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = lean_nat_to_int(v_k_2469_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set_tag(v___x_2471_, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2473_);
v___x_2475_ = v___x_2471_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
case 2:
{
lean_object* v_k_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
v_k_2478_ = lean_ctor_get(v_x_2460_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v_x_2460_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v_x_2460_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_k_2478_);
lean_dec(v_x_2460_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set_tag(v___x_2480_, 0);
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_k_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
case 3:
{
lean_object* v_i_2486_; lean_object* v___x_2487_; 
v_i_2486_ = lean_ctor_get(v_x_2460_, 0);
lean_inc(v_i_2486_);
lean_dec_ref(v_x_2460_);
v___x_2487_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2486_);
return v___x_2487_;
}
case 4:
{
lean_object* v_a_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_a_2488_ = lean_ctor_get(v_x_2460_, 0);
lean_inc_ref(v_a_2488_);
lean_dec_ref(v_x_2460_);
v___x_2489_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2490_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2488_);
v___x_2491_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2489_, v___x_2490_);
return v___x_2491_;
}
case 5:
{
lean_object* v_a_2492_; lean_object* v_b_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v_a_2492_ = lean_ctor_get(v_x_2460_, 0);
lean_inc_ref(v_a_2492_);
v_b_2493_ = lean_ctor_get(v_x_2460_, 1);
lean_inc_ref(v_b_2493_);
lean_dec_ref(v_x_2460_);
v___x_2494_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2492_);
v___x_2495_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2493_);
v___x_2496_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2494_, v___x_2495_);
return v___x_2496_;
}
case 6:
{
lean_object* v_a_2497_; lean_object* v_b_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v_a_2497_ = lean_ctor_get(v_x_2460_, 0);
lean_inc_ref(v_a_2497_);
v_b_2498_ = lean_ctor_get(v_x_2460_, 1);
lean_inc_ref(v_b_2498_);
lean_dec_ref(v_x_2460_);
v___x_2499_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2497_);
v___x_2500_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2501_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2498_);
v___x_2502_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2500_, v___x_2501_);
v___x_2503_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2499_, v___x_2502_);
return v___x_2503_;
}
case 7:
{
lean_object* v_a_2504_; lean_object* v_b_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v_a_2504_ = lean_ctor_get(v_x_2460_, 0);
lean_inc_ref(v_a_2504_);
v_b_2505_ = lean_ctor_get(v_x_2460_, 1);
lean_inc_ref(v_b_2505_);
lean_dec_ref(v_x_2460_);
v___x_2506_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2504_);
v___x_2507_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2505_);
v___x_2508_ = l_Lean_Grind_CommRing_Poly_mul(v___x_2506_, v___x_2507_);
return v___x_2508_;
}
default: 
{
lean_object* v_a_2509_; lean_object* v_k_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2542_; 
v_a_2509_ = lean_ctor_get(v_x_2460_, 0);
v_k_2510_ = lean_ctor_get(v_x_2460_, 1);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_x_2460_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2512_ = v_x_2460_;
v_isShared_2513_ = v_isSharedCheck_2542_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_k_2510_);
lean_inc(v_a_2509_);
lean_dec(v_x_2460_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2542_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v_n_2515_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2518_ = lean_unsigned_to_nat(0u);
v___x_2519_ = lean_nat_dec_eq(v_k_2510_, v___x_2518_);
if (v___x_2519_ == 0)
{
switch(lean_obj_tag(v_a_2509_))
{
case 0:
{
lean_object* v_k_2520_; 
lean_del_object(v___x_2512_);
v_k_2520_ = lean_ctor_get(v_a_2509_, 0);
lean_inc(v_k_2520_);
lean_dec_ref(v_a_2509_);
v_n_2515_ = v_k_2520_;
goto v___jp_2514_;
}
case 2:
{
lean_object* v_k_2521_; 
lean_del_object(v___x_2512_);
v_k_2521_ = lean_ctor_get(v_a_2509_, 0);
lean_inc(v_k_2521_);
lean_dec_ref(v_a_2509_);
v_n_2515_ = v_k_2521_;
goto v___jp_2514_;
}
case 1:
{
lean_object* v_k_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2531_; 
lean_del_object(v___x_2512_);
v_k_2522_ = lean_ctor_get(v_a_2509_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_a_2509_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2524_ = v_a_2509_;
v_isShared_2525_ = v_isSharedCheck_2531_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_k_2522_);
lean_dec(v_a_2509_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2531_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2526_ = lean_nat_to_int(v_k_2522_);
v___x_2527_ = l_Int_pow(v___x_2526_, v_k_2510_);
lean_dec(v_k_2510_);
lean_dec(v___x_2526_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set_tag(v___x_2524_, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2527_);
v___x_2529_ = v___x_2524_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
case 3:
{
lean_object* v_i_2532_; lean_object* v___x_2534_; 
v_i_2532_ = lean_ctor_get(v_a_2509_, 0);
lean_inc(v_i_2532_);
lean_dec_ref(v_a_2509_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set_tag(v___x_2512_, 0);
lean_ctor_set(v___x_2512_, 0, v_i_2532_);
v___x_2534_ = v___x_2512_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_i_2532_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_k_2510_);
v___x_2534_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = lean_box(0);
v___x_2536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2536_);
return v___x_2537_;
}
}
default: 
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
lean_del_object(v___x_2512_);
v___x_2539_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2509_);
v___x_2540_ = l_Lean_Grind_CommRing_Poly_pow(v___x_2539_, v_k_2510_);
lean_dec(v_k_2510_);
return v___x_2540_;
}
}
}
else
{
lean_object* v___x_2541_; 
lean_del_object(v___x_2512_);
lean_dec(v_k_2510_);
lean_dec_ref(v_a_2509_);
v___x_2541_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2541_;
}
v___jp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = l_Int_pow(v_n_2515_, v_k_2510_);
lean_dec(v_k_2510_);
lean_dec(v_n_2515_);
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
return v___x_2517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf(lean_object* v_m_2543_, lean_object* v_x_2544_){
_start:
{
if (lean_obj_tag(v_m_2543_) == 0)
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_unsigned_to_nat(0u);
return v___x_2545_;
}
else
{
lean_object* v_p_2546_; lean_object* v_m_2547_; lean_object* v_x_2548_; lean_object* v_k_2549_; uint8_t v___x_2550_; 
v_p_2546_ = lean_ctor_get(v_m_2543_, 0);
v_m_2547_ = lean_ctor_get(v_m_2543_, 1);
v_x_2548_ = lean_ctor_get(v_p_2546_, 0);
v_k_2549_ = lean_ctor_get(v_p_2546_, 1);
v___x_2550_ = lean_nat_dec_eq(v_x_2548_, v_x_2544_);
if (v___x_2550_ == 0)
{
v_m_2543_ = v_m_2547_;
goto _start;
}
else
{
lean_inc(v_k_2549_);
return v_k_2549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf___boxed(lean_object* v_m_2552_, lean_object* v_x_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_2552_, v_x_2553_);
lean_dec(v_x_2553_);
lean_dec(v_m_2552_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar(lean_object* v_m_2555_, lean_object* v_x_2556_){
_start:
{
if (lean_obj_tag(v_m_2555_) == 0)
{
return v_m_2555_;
}
else
{
lean_object* v_p_2557_; lean_object* v_m_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2568_; 
v_p_2557_ = lean_ctor_get(v_m_2555_, 0);
v_m_2558_ = lean_ctor_get(v_m_2555_, 1);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_m_2555_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2560_ = v_m_2555_;
v_isShared_2561_ = v_isSharedCheck_2568_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_m_2558_);
lean_inc(v_p_2557_);
lean_dec(v_m_2555_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2568_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v_x_2562_; uint8_t v___x_2563_; 
v_x_2562_ = lean_ctor_get(v_p_2557_, 0);
v___x_2563_ = lean_nat_dec_eq(v_x_2562_, v_x_2556_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2564_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2558_, v_x_2556_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 1, v___x_2564_);
v___x_2566_ = v___x_2560_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_p_2557_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
else
{
lean_del_object(v___x_2560_);
lean_dec_ref(v_p_2557_);
return v_m_2558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar___boxed(lean_object* v_m_2569_, lean_object* v_x_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2569_, v_x_2570_);
lean_dec(v_x_2570_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27(lean_object* v_c_2572_, lean_object* v_x_2573_, lean_object* v_p_2574_, lean_object* v_acc_2575_){
_start:
{
if (lean_obj_tag(v_p_2574_) == 0)
{
lean_object* v_k_2576_; lean_object* v___x_2577_; 
v_k_2576_ = lean_ctor_get(v_p_2574_, 0);
lean_inc(v_k_2576_);
lean_dec_ref(v_p_2574_);
v___x_2577_ = l_Lean_Grind_CommRing_Poly_addConst(v_acc_2575_, v_k_2576_);
lean_dec(v_k_2576_);
return v___x_2577_;
}
else
{
lean_object* v_k_2578_; lean_object* v_v_2579_; lean_object* v_p_2580_; lean_object* v_n_2581_; uint8_t v___y_2583_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v_k_2578_ = lean_ctor_get(v_p_2574_, 0);
lean_inc(v_k_2578_);
v_v_2579_ = lean_ctor_get(v_p_2574_, 1);
lean_inc(v_v_2579_);
v_p_2580_ = lean_ctor_get(v_p_2574_, 2);
lean_inc_ref(v_p_2580_);
lean_dec_ref(v_p_2574_);
v_n_2581_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_2579_, v_x_2573_);
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = lean_nat_dec_lt(v___x_2591_, v_n_2581_);
if (v___x_2592_ == 0)
{
v___y_2583_ = v___x_2592_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2593_ = l_Int_pow(v_c_2572_, v_n_2581_);
v___x_2594_ = l_Int_decidableDvd(v___x_2593_, v_k_2578_);
lean_dec(v___x_2593_);
v___y_2583_ = v___x_2594_;
goto v___jp_2582_;
}
v___jp_2582_:
{
if (v___y_2583_ == 0)
{
lean_object* v___x_2584_; 
lean_dec(v_n_2581_);
v___x_2584_ = l_Lean_Grind_CommRing_Poly_insert(v_k_2578_, v_v_2579_, v_acc_2575_);
v_p_2574_ = v_p_2580_;
v_acc_2575_ = v___x_2584_;
goto _start;
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2586_ = l_Int_pow(v_c_2572_, v_n_2581_);
lean_dec(v_n_2581_);
v___x_2587_ = lean_int_ediv(v_k_2578_, v___x_2586_);
lean_dec(v___x_2586_);
lean_dec(v_k_2578_);
v___x_2588_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_v_2579_, v_x_2573_);
v___x_2589_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2587_, v___x_2588_, v_acc_2575_);
v_p_2574_ = v_p_2580_;
v_acc_2575_ = v___x_2589_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27___boxed(lean_object* v_c_2595_, lean_object* v_x_2596_, lean_object* v_p_2597_, lean_object* v_acc_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2595_, v_x_2596_, v_p_2597_, v_acc_2598_);
lean_dec(v_x_2596_);
lean_dec(v_c_2595_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar(lean_object* v_c_2600_, lean_object* v_x_2601_, lean_object* v_p_2602_){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2604_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2600_, v_x_2601_, v_p_2602_, v___x_2603_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar___boxed(lean_object* v_c_2605_, lean_object* v_x_2606_, lean_object* v_p_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Lean_Grind_CommRing_Poly_cancelVar(v_c_2605_, v_x_2606_, v_p_2607_);
lean_dec(v_x_2606_);
lean_dec(v_c_2605_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(lean_object* v_x_2609_, lean_object* v_h__1_2610_, lean_object* v_h__2_2611_, lean_object* v_h__3_2612_, lean_object* v_h__4_2613_, lean_object* v_h__5_2614_, lean_object* v_h__6_2615_, lean_object* v_h__7_2616_, lean_object* v_h__8_2617_, lean_object* v_h__9_2618_){
_start:
{
switch(lean_obj_tag(v_x_2609_))
{
case 0:
{
lean_object* v_k_2619_; lean_object* v___x_2620_; 
lean_dec(v_h__9_2618_);
lean_dec(v_h__8_2617_);
lean_dec(v_h__7_2616_);
lean_dec(v_h__6_2615_);
lean_dec(v_h__5_2614_);
lean_dec(v_h__4_2613_);
lean_dec(v_h__3_2612_);
lean_dec(v_h__2_2611_);
v_k_2619_ = lean_ctor_get(v_x_2609_, 0);
lean_inc(v_k_2619_);
lean_dec_ref(v_x_2609_);
v___x_2620_ = lean_apply_1(v_h__1_2610_, v_k_2619_);
return v___x_2620_;
}
case 1:
{
lean_object* v_k_2621_; lean_object* v___x_2622_; 
lean_dec(v_h__9_2618_);
lean_dec(v_h__8_2617_);
lean_dec(v_h__7_2616_);
lean_dec(v_h__6_2615_);
lean_dec(v_h__5_2614_);
lean_dec(v_h__4_2613_);
lean_dec(v_h__2_2611_);
lean_dec(v_h__1_2610_);
v_k_2621_ = lean_ctor_get(v_x_2609_, 0);
lean_inc(v_k_2621_);
lean_dec_ref(v_x_2609_);
v___x_2622_ = lean_apply_1(v_h__3_2612_, v_k_2621_);
return v___x_2622_;
}
case 2:
{
lean_object* v_k_2623_; lean_object* v___x_2624_; 
lean_dec(v_h__9_2618_);
lean_dec(v_h__8_2617_);
lean_dec(v_h__7_2616_);
lean_dec(v_h__6_2615_);
lean_dec(v_h__5_2614_);
lean_dec(v_h__4_2613_);
lean_dec(v_h__3_2612_);
lean_dec(v_h__1_2610_);
v_k_2623_ = lean_ctor_get(v_x_2609_, 0);
lean_inc(v_k_2623_);
lean_dec_ref(v_x_2609_);
v___x_2624_ = lean_apply_1(v_h__2_2611_, v_k_2623_);
return v___x_2624_;
}
case 3:
{
lean_object* v_i_2625_; lean_object* v___x_2626_; 
lean_dec(v_h__9_2618_);
lean_dec(v_h__8_2617_);
lean_dec(v_h__7_2616_);
lean_dec(v_h__6_2615_);
lean_dec(v_h__5_2614_);
lean_dec(v_h__3_2612_);
lean_dec(v_h__2_2611_);
lean_dec(v_h__1_2610_);
v_i_2625_ = lean_ctor_get(v_x_2609_, 0);
lean_inc(v_i_2625_);
lean_dec_ref(v_x_2609_);
v___x_2626_ = lean_apply_1(v_h__4_2613_, v_i_2625_);
return v___x_2626_;
}
case 4:
{
lean_object* v_a_2627_; lean_object* v___x_2628_; 
lean_dec(v_h__9_2618_);
lean_dec(v_h__8_2617_);
lean_dec(v_h__6_2615_);
lean_dec(v_h__5_2614_);
lean_dec(v_h__4_2613_);
lean_dec(v_h__3_2612_);
lean_dec(v_h__2_2611_);
lean_dec(v_h__1_2610_);
v_a_2627_ = lean_ctor_get(v_x_2609_, 0);
lean_inc_ref(v_a_2627_);
lean_dec_ref(v_x_2609_);
v___x_2628_ = lean_apply_1(v_h__7_2616_, v_a_2627_);
return v___x_2628_;
}
case 5:
{
lean_object* v_a_2629_; lean_object* v_b_2630_; lean_object* v___x_2631_; 
lean_dec(v_h__9_2618_);
lean_dec(v_h__8_2617_);
lean_dec(v_h__7_2616_);
lean_dec(v_h__6_2615_);
lean_dec(v_h__4_2613_);
lean_dec(v_h__3_2612_);
lean_dec(v_h__2_2611_);
lean_dec(v_h__1_2610_);
v_a_2629_ = lean_ctor_get(v_x_2609_, 0);
lean_inc_ref(v_a_2629_);
v_b_2630_ = lean_ctor_get(v_x_2609_, 1);
lean_inc_ref(v_b_2630_);
lean_dec_ref(v_x_2609_);
v___x_2631_ = lean_apply_2(v_h__5_2614_, v_a_2629_, v_b_2630_);
return v___x_2631_;
}
case 6:
{
lean_object* v_a_2632_; lean_object* v_b_2633_; lean_object* v___x_2634_; 
lean_dec(v_h__9_2618_);
lean_dec(v_h__7_2616_);
lean_dec(v_h__6_2615_);
lean_dec(v_h__5_2614_);
lean_dec(v_h__4_2613_);
lean_dec(v_h__3_2612_);
lean_dec(v_h__2_2611_);
lean_dec(v_h__1_2610_);
v_a_2632_ = lean_ctor_get(v_x_2609_, 0);
lean_inc_ref(v_a_2632_);
v_b_2633_ = lean_ctor_get(v_x_2609_, 1);
lean_inc_ref(v_b_2633_);
lean_dec_ref(v_x_2609_);
v___x_2634_ = lean_apply_2(v_h__8_2617_, v_a_2632_, v_b_2633_);
return v___x_2634_;
}
case 7:
{
lean_object* v_a_2635_; lean_object* v_b_2636_; lean_object* v___x_2637_; 
lean_dec(v_h__9_2618_);
lean_dec(v_h__8_2617_);
lean_dec(v_h__7_2616_);
lean_dec(v_h__5_2614_);
lean_dec(v_h__4_2613_);
lean_dec(v_h__3_2612_);
lean_dec(v_h__2_2611_);
lean_dec(v_h__1_2610_);
v_a_2635_ = lean_ctor_get(v_x_2609_, 0);
lean_inc_ref(v_a_2635_);
v_b_2636_ = lean_ctor_get(v_x_2609_, 1);
lean_inc_ref(v_b_2636_);
lean_dec_ref(v_x_2609_);
v___x_2637_ = lean_apply_2(v_h__6_2615_, v_a_2635_, v_b_2636_);
return v___x_2637_;
}
default: 
{
lean_object* v_a_2638_; lean_object* v_k_2639_; lean_object* v___x_2640_; 
lean_dec(v_h__8_2617_);
lean_dec(v_h__7_2616_);
lean_dec(v_h__6_2615_);
lean_dec(v_h__5_2614_);
lean_dec(v_h__4_2613_);
lean_dec(v_h__3_2612_);
lean_dec(v_h__2_2611_);
lean_dec(v_h__1_2610_);
v_a_2638_ = lean_ctor_get(v_x_2609_, 0);
lean_inc_ref(v_a_2638_);
v_k_2639_ = lean_ctor_get(v_x_2609_, 1);
lean_inc(v_k_2639_);
lean_dec_ref(v_x_2609_);
v___x_2640_ = lean_apply_2(v_h__9_2618_, v_a_2638_, v_k_2639_);
return v___x_2640_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter(lean_object* v_motive_2641_, lean_object* v_x_2642_, lean_object* v_h__1_2643_, lean_object* v_h__2_2644_, lean_object* v_h__3_2645_, lean_object* v_h__4_2646_, lean_object* v_h__5_2647_, lean_object* v_h__6_2648_, lean_object* v_h__7_2649_, lean_object* v_h__8_2650_, lean_object* v_h__9_2651_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(v_x_2642_, v_h__1_2643_, v_h__2_2644_, v_h__3_2645_, v_h__4_2646_, v_h__5_2647_, v_h__6_2648_, v_h__7_2649_, v_h__8_2650_, v_h__9_2651_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter___redArg(lean_object* v_a_2653_, lean_object* v_h__1_2654_, lean_object* v_h__2_2655_, lean_object* v_h__3_2656_, lean_object* v_h__4_2657_, lean_object* v_h__5_2658_){
_start:
{
switch(lean_obj_tag(v_a_2653_))
{
case 0:
{
lean_object* v_k_2659_; lean_object* v___x_2660_; 
lean_dec(v_h__5_2658_);
lean_dec(v_h__4_2657_);
lean_dec(v_h__3_2656_);
lean_dec(v_h__2_2655_);
v_k_2659_ = lean_ctor_get(v_a_2653_, 0);
lean_inc(v_k_2659_);
lean_dec_ref(v_a_2653_);
v___x_2660_ = lean_apply_1(v_h__1_2654_, v_k_2659_);
return v___x_2660_;
}
case 2:
{
lean_object* v_k_2661_; lean_object* v___x_2662_; 
lean_dec(v_h__5_2658_);
lean_dec(v_h__4_2657_);
lean_dec(v_h__3_2656_);
lean_dec(v_h__1_2654_);
v_k_2661_ = lean_ctor_get(v_a_2653_, 0);
lean_inc(v_k_2661_);
lean_dec_ref(v_a_2653_);
v___x_2662_ = lean_apply_1(v_h__2_2655_, v_k_2661_);
return v___x_2662_;
}
case 1:
{
lean_object* v_k_2663_; lean_object* v___x_2664_; 
lean_dec(v_h__5_2658_);
lean_dec(v_h__4_2657_);
lean_dec(v_h__2_2655_);
lean_dec(v_h__1_2654_);
v_k_2663_ = lean_ctor_get(v_a_2653_, 0);
lean_inc(v_k_2663_);
lean_dec_ref(v_a_2653_);
v___x_2664_ = lean_apply_1(v_h__3_2656_, v_k_2663_);
return v___x_2664_;
}
case 3:
{
lean_object* v_i_2665_; lean_object* v___x_2666_; 
lean_dec(v_h__5_2658_);
lean_dec(v_h__3_2656_);
lean_dec(v_h__2_2655_);
lean_dec(v_h__1_2654_);
v_i_2665_ = lean_ctor_get(v_a_2653_, 0);
lean_inc(v_i_2665_);
lean_dec_ref(v_a_2653_);
v___x_2666_ = lean_apply_1(v_h__4_2657_, v_i_2665_);
return v___x_2666_;
}
default: 
{
lean_object* v___x_2667_; 
lean_dec(v_h__4_2657_);
lean_dec(v_h__3_2656_);
lean_dec(v_h__2_2655_);
lean_dec(v_h__1_2654_);
v___x_2667_ = lean_apply_5(v_h__5_2658_, v_a_2653_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2667_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter(lean_object* v_motive_2668_, lean_object* v_a_2669_, lean_object* v_h__1_2670_, lean_object* v_h__2_2671_, lean_object* v_h__3_2672_, lean_object* v_h__4_2673_, lean_object* v_h__5_2674_){
_start:
{
switch(lean_obj_tag(v_a_2669_))
{
case 0:
{
lean_object* v_k_2675_; lean_object* v___x_2676_; 
lean_dec(v_h__5_2674_);
lean_dec(v_h__4_2673_);
lean_dec(v_h__3_2672_);
lean_dec(v_h__2_2671_);
v_k_2675_ = lean_ctor_get(v_a_2669_, 0);
lean_inc(v_k_2675_);
lean_dec_ref(v_a_2669_);
v___x_2676_ = lean_apply_1(v_h__1_2670_, v_k_2675_);
return v___x_2676_;
}
case 2:
{
lean_object* v_k_2677_; lean_object* v___x_2678_; 
lean_dec(v_h__5_2674_);
lean_dec(v_h__4_2673_);
lean_dec(v_h__3_2672_);
lean_dec(v_h__1_2670_);
v_k_2677_ = lean_ctor_get(v_a_2669_, 0);
lean_inc(v_k_2677_);
lean_dec_ref(v_a_2669_);
v___x_2678_ = lean_apply_1(v_h__2_2671_, v_k_2677_);
return v___x_2678_;
}
case 1:
{
lean_object* v_k_2679_; lean_object* v___x_2680_; 
lean_dec(v_h__5_2674_);
lean_dec(v_h__4_2673_);
lean_dec(v_h__2_2671_);
lean_dec(v_h__1_2670_);
v_k_2679_ = lean_ctor_get(v_a_2669_, 0);
lean_inc(v_k_2679_);
lean_dec_ref(v_a_2669_);
v___x_2680_ = lean_apply_1(v_h__3_2672_, v_k_2679_);
return v___x_2680_;
}
case 3:
{
lean_object* v_i_2681_; lean_object* v___x_2682_; 
lean_dec(v_h__5_2674_);
lean_dec(v_h__3_2672_);
lean_dec(v_h__2_2671_);
lean_dec(v_h__1_2670_);
v_i_2681_ = lean_ctor_get(v_a_2669_, 0);
lean_inc(v_i_2681_);
lean_dec_ref(v_a_2669_);
v___x_2682_ = lean_apply_1(v_h__4_2673_, v_i_2681_);
return v___x_2682_;
}
default: 
{
lean_object* v___x_2683_; 
lean_dec(v_h__4_2673_);
lean_dec(v_h__3_2672_);
lean_dec(v_h__2_2671_);
lean_dec(v_h__1_2670_);
v___x_2683_ = lean_apply_5(v_h__5_2674_, v_a_2669_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly__nc(lean_object* v_x_2684_){
_start:
{
switch(lean_obj_tag(v_x_2684_))
{
case 0:
{
lean_object* v_k_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
v_k_2685_ = lean_ctor_get(v_x_2684_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_x_2684_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v_x_2684_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_k_2685_);
lean_dec(v_x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_k_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
case 1:
{
lean_object* v_k_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2701_; 
v_k_2693_ = lean_ctor_get(v_x_2684_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_x_2684_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2695_ = v_x_2684_;
v_isShared_2696_ = v_isSharedCheck_2701_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_k_2693_);
lean_dec(v_x_2684_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2701_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = lean_nat_to_int(v_k_2693_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set_tag(v___x_2695_, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2697_);
v___x_2699_ = v___x_2695_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
case 2:
{
lean_object* v_k_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
v_k_2702_ = lean_ctor_get(v_x_2684_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_x_2684_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v_x_2684_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_k_2702_);
lean_dec(v_x_2684_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set_tag(v___x_2704_, 0);
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_k_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
case 3:
{
lean_object* v_i_2710_; lean_object* v___x_2711_; 
v_i_2710_ = lean_ctor_get(v_x_2684_, 0);
lean_inc(v_i_2710_);
lean_dec_ref(v_x_2684_);
v___x_2711_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2710_);
return v___x_2711_;
}
case 4:
{
lean_object* v_a_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_a_2712_ = lean_ctor_get(v_x_2684_, 0);
lean_inc_ref(v_a_2712_);
lean_dec_ref(v_x_2684_);
v___x_2713_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2714_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2712_);
v___x_2715_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2713_, v___x_2714_);
return v___x_2715_;
}
case 5:
{
lean_object* v_a_2716_; lean_object* v_b_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v_a_2716_ = lean_ctor_get(v_x_2684_, 0);
lean_inc_ref(v_a_2716_);
v_b_2717_ = lean_ctor_get(v_x_2684_, 1);
lean_inc_ref(v_b_2717_);
lean_dec_ref(v_x_2684_);
v___x_2718_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2716_);
v___x_2719_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2717_);
v___x_2720_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2718_, v___x_2719_);
return v___x_2720_;
}
case 6:
{
lean_object* v_a_2721_; lean_object* v_b_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v_a_2721_ = lean_ctor_get(v_x_2684_, 0);
lean_inc_ref(v_a_2721_);
v_b_2722_ = lean_ctor_get(v_x_2684_, 1);
lean_inc_ref(v_b_2722_);
lean_dec_ref(v_x_2684_);
v___x_2723_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2721_);
v___x_2724_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2725_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2722_);
v___x_2726_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2724_, v___x_2725_);
v___x_2727_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2723_, v___x_2726_);
return v___x_2727_;
}
case 7:
{
lean_object* v_a_2728_; lean_object* v_b_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v_a_2728_ = lean_ctor_get(v_x_2684_, 0);
lean_inc_ref(v_a_2728_);
v_b_2729_ = lean_ctor_get(v_x_2684_, 1);
lean_inc_ref(v_b_2729_);
lean_dec_ref(v_x_2684_);
v___x_2730_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2728_);
v___x_2731_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2729_);
v___x_2732_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2730_, v___x_2731_);
return v___x_2732_;
}
default: 
{
lean_object* v_a_2733_; lean_object* v_k_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2766_; 
v_a_2733_ = lean_ctor_get(v_x_2684_, 0);
v_k_2734_ = lean_ctor_get(v_x_2684_, 1);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_x_2684_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2736_ = v_x_2684_;
v_isShared_2737_ = v_isSharedCheck_2766_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_k_2734_);
lean_inc(v_a_2733_);
lean_dec(v_x_2684_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2766_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v_n_2739_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = lean_unsigned_to_nat(0u);
v___x_2743_ = lean_nat_dec_eq(v_k_2734_, v___x_2742_);
if (v___x_2743_ == 0)
{
switch(lean_obj_tag(v_a_2733_))
{
case 0:
{
lean_object* v_k_2744_; 
lean_del_object(v___x_2736_);
v_k_2744_ = lean_ctor_get(v_a_2733_, 0);
lean_inc(v_k_2744_);
lean_dec_ref(v_a_2733_);
v_n_2739_ = v_k_2744_;
goto v___jp_2738_;
}
case 2:
{
lean_object* v_k_2745_; 
lean_del_object(v___x_2736_);
v_k_2745_ = lean_ctor_get(v_a_2733_, 0);
lean_inc(v_k_2745_);
lean_dec_ref(v_a_2733_);
v_n_2739_ = v_k_2745_;
goto v___jp_2738_;
}
case 1:
{
lean_object* v_k_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2755_; 
lean_del_object(v___x_2736_);
v_k_2746_ = lean_ctor_get(v_a_2733_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_a_2733_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2748_ = v_a_2733_;
v_isShared_2749_ = v_isSharedCheck_2755_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_k_2746_);
lean_dec(v_a_2733_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2755_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2750_ = lean_nat_to_int(v_k_2746_);
v___x_2751_ = l_Int_pow(v___x_2750_, v_k_2734_);
lean_dec(v_k_2734_);
lean_dec(v___x_2750_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set_tag(v___x_2748_, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2751_);
v___x_2753_ = v___x_2748_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
case 3:
{
lean_object* v_i_2756_; lean_object* v___x_2758_; 
v_i_2756_ = lean_ctor_get(v_a_2733_, 0);
lean_inc(v_i_2756_);
lean_dec_ref(v_a_2733_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set_tag(v___x_2736_, 0);
lean_ctor_set(v___x_2736_, 0, v_i_2756_);
v___x_2758_ = v___x_2736_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_i_2756_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_k_2734_);
v___x_2758_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2759_ = lean_box(0);
v___x_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2760_);
return v___x_2761_;
}
}
default: 
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_del_object(v___x_2736_);
v___x_2763_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2733_);
v___x_2764_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_2763_, v_k_2734_);
lean_dec(v_k_2734_);
return v___x_2764_;
}
}
}
else
{
lean_object* v___x_2765_; 
lean_del_object(v___x_2736_);
lean_dec(v_k_2734_);
lean_dec_ref(v_a_2733_);
v___x_2765_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2765_;
}
v___jp_2738_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = l_Int_pow(v_n_2739_, v_k_2734_);
lean_dec(v_k_2734_);
lean_dec(v_n_2739_);
v___x_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
return v___x_2741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_normEq0(lean_object* v_p_2767_, lean_object* v_c_2768_){
_start:
{
if (lean_obj_tag(v_p_2767_) == 0)
{
lean_object* v_k_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v_k_2769_ = lean_ctor_get(v_p_2767_, 0);
v___x_2770_ = lean_nat_to_int(v_c_2768_);
v___x_2771_ = lean_int_emod(v_k_2769_, v___x_2770_);
lean_dec(v___x_2770_);
v___x_2772_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2773_ = lean_int_dec_eq(v___x_2771_, v___x_2772_);
lean_dec(v___x_2771_);
if (v___x_2773_ == 0)
{
return v_p_2767_;
}
else
{
lean_object* v___x_2774_; 
lean_dec_ref(v_p_2767_);
v___x_2774_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2774_;
}
}
else
{
lean_object* v_k_2775_; lean_object* v_v_2776_; lean_object* v_p_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2790_; 
v_k_2775_ = lean_ctor_get(v_p_2767_, 0);
v_v_2776_ = lean_ctor_get(v_p_2767_, 1);
v_p_2777_ = lean_ctor_get(v_p_2767_, 2);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_p_2767_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2779_ = v_p_2767_;
v_isShared_2780_ = v_isSharedCheck_2790_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_p_2777_);
lean_inc(v_v_2776_);
lean_inc(v_k_2775_);
lean_dec(v_p_2767_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2790_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
lean_inc(v_c_2768_);
v___x_2781_ = lean_nat_to_int(v_c_2768_);
v___x_2782_ = lean_int_emod(v_k_2775_, v___x_2781_);
lean_dec(v___x_2781_);
v___x_2783_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2784_ = lean_int_dec_eq(v___x_2782_, v___x_2783_);
lean_dec(v___x_2782_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2785_ = l_Lean_Grind_CommRing_Poly_normEq0(v_p_2777_, v_c_2768_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 2, v___x_2785_);
v___x_2787_ = v___x_2779_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_k_2775_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_v_2776_);
lean_ctor_set(v_reuseFailAlloc_2788_, 2, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
else
{
lean_del_object(v___x_2779_);
lean_dec(v_v_2776_);
lean_dec(v_k_2775_);
v_p_2767_ = v_p_2777_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object* v_p_2791_, lean_object* v_k_2792_, lean_object* v_c_2793_){
_start:
{
if (lean_obj_tag(v_p_2791_) == 0)
{
lean_object* v_k_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2804_; 
v_k_2794_ = lean_ctor_get(v_p_2791_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_p_2791_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2796_ = v_p_2791_;
v_isShared_2797_ = v_isSharedCheck_2804_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_k_2794_);
lean_dec(v_p_2791_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2804_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2798_ = lean_int_add(v_k_2794_, v_k_2792_);
lean_dec(v_k_2794_);
v___x_2799_ = lean_nat_to_int(v_c_2793_);
v___x_2800_ = lean_int_emod(v___x_2798_, v___x_2799_);
lean_dec(v___x_2799_);
lean_dec(v___x_2798_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2800_);
v___x_2802_ = v___x_2796_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2800_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
else
{
lean_object* v_k_2805_; lean_object* v_v_2806_; lean_object* v_p_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2815_; 
v_k_2805_ = lean_ctor_get(v_p_2791_, 0);
v_v_2806_ = lean_ctor_get(v_p_2791_, 1);
v_p_2807_ = lean_ctor_get(v_p_2791_, 2);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_p_2791_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2809_ = v_p_2791_;
v_isShared_2810_ = v_isSharedCheck_2815_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_p_2807_);
lean_inc(v_v_2806_);
lean_inc(v_k_2805_);
lean_dec(v_p_2791_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2815_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2811_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2807_, v_k_2792_, v_c_2793_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 2, v___x_2811_);
v___x_2813_ = v___x_2809_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_k_2805_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_v_2806_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC___boxed(lean_object* v_p_2816_, lean_object* v_k_2817_, lean_object* v_c_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2816_, v_k_2817_, v_c_2818_);
lean_dec(v_k_2817_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC_go(lean_object* v_m_2820_, lean_object* v_c_2821_, lean_object* v_k_2822_, lean_object* v_a_2823_){
_start:
{
if (lean_obj_tag(v_a_2823_) == 0)
{
lean_object* v___x_2824_; 
lean_dec(v_c_2821_);
v___x_2824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2824_, 0, v_k_2822_);
lean_ctor_set(v___x_2824_, 1, v_m_2820_);
lean_ctor_set(v___x_2824_, 2, v_a_2823_);
return v___x_2824_;
}
else
{
lean_object* v_k_2825_; lean_object* v_v_2826_; lean_object* v_p_2827_; uint8_t v___x_2828_; 
v_k_2825_ = lean_ctor_get(v_a_2823_, 0);
v_v_2826_ = lean_ctor_get(v_a_2823_, 1);
v_p_2827_ = lean_ctor_get(v_a_2823_, 2);
v___x_2828_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2820_, v_v_2826_);
switch(v___x_2828_)
{
case 0:
{
lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2836_; 
lean_inc_ref(v_p_2827_);
lean_inc(v_v_2826_);
lean_inc(v_k_2825_);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_a_2823_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; lean_object* v_unused_2838_; lean_object* v_unused_2839_; 
v_unused_2837_ = lean_ctor_get(v_a_2823_, 2);
lean_dec(v_unused_2837_);
v_unused_2838_ = lean_ctor_get(v_a_2823_, 1);
lean_dec(v_unused_2838_);
v_unused_2839_ = lean_ctor_get(v_a_2823_, 0);
lean_dec(v_unused_2839_);
v___x_2830_ = v_a_2823_;
v_isShared_2831_ = v_isSharedCheck_2836_;
goto v_resetjp_2829_;
}
else
{
lean_dec(v_a_2823_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2836_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2832_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_2820_, v_c_2821_, v_k_2822_, v_p_2827_);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 2, v___x_2832_);
v___x_2834_ = v___x_2830_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_k_2825_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_v_2826_);
lean_ctor_set(v_reuseFailAlloc_2835_, 2, v___x_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
case 1:
{
lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2851_; 
lean_inc_ref(v_p_2827_);
lean_inc(v_k_2825_);
v_isSharedCheck_2851_ = !lean_is_exclusive(v_a_2823_);
if (v_isSharedCheck_2851_ == 0)
{
lean_object* v_unused_2852_; lean_object* v_unused_2853_; lean_object* v_unused_2854_; 
v_unused_2852_ = lean_ctor_get(v_a_2823_, 2);
lean_dec(v_unused_2852_);
v_unused_2853_ = lean_ctor_get(v_a_2823_, 1);
lean_dec(v_unused_2853_);
v_unused_2854_ = lean_ctor_get(v_a_2823_, 0);
lean_dec(v_unused_2854_);
v___x_2841_ = v_a_2823_;
v_isShared_2842_ = v_isSharedCheck_2851_;
goto v_resetjp_2840_;
}
else
{
lean_dec(v_a_2823_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2851_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v_k_x27_x27_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; 
v___x_2843_ = lean_int_add(v_k_2822_, v_k_2825_);
lean_dec(v_k_2825_);
lean_dec(v_k_2822_);
v___x_2844_ = lean_nat_to_int(v_c_2821_);
v_k_x27_x27_2845_ = lean_int_emod(v___x_2843_, v___x_2844_);
lean_dec(v___x_2844_);
lean_dec(v___x_2843_);
v___x_2846_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2847_ = lean_int_dec_eq(v_k_x27_x27_2845_, v___x_2846_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2849_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 1, v_m_2820_);
lean_ctor_set(v___x_2841_, 0, v_k_x27_x27_2845_);
v___x_2849_ = v___x_2841_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_k_x27_x27_2845_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_m_2820_);
lean_ctor_set(v_reuseFailAlloc_2850_, 2, v_p_2827_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
else
{
lean_dec(v_k_x27_x27_2845_);
lean_del_object(v___x_2841_);
lean_dec(v_m_2820_);
return v_p_2827_;
}
}
}
default: 
{
lean_object* v___x_2855_; 
lean_dec(v_c_2821_);
v___x_2855_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2855_, 0, v_k_2822_);
lean_ctor_set(v___x_2855_, 1, v_m_2820_);
lean_ctor_set(v___x_2855_, 2, v_a_2823_);
return v___x_2855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC(lean_object* v_k_2856_, lean_object* v_m_2857_, lean_object* v_p_2858_, lean_object* v_c_2859_){
_start:
{
lean_object* v___x_2860_; lean_object* v_k_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
lean_inc(v_c_2859_);
v___x_2860_ = lean_nat_to_int(v_c_2859_);
v_k_2861_ = lean_int_emod(v_k_2856_, v___x_2860_);
lean_dec(v___x_2860_);
v___x_2862_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2863_ = lean_int_dec_eq(v_k_2861_, v___x_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_2857_, v_c_2859_, v_k_2861_, v_p_2858_);
return v___x_2864_;
}
else
{
lean_dec(v_k_2861_);
lean_dec(v_c_2859_);
lean_dec(v_m_2857_);
return v_p_2858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC___boxed(lean_object* v_k_2865_, lean_object* v_m_2866_, lean_object* v_p_2867_, lean_object* v_c_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_Grind_CommRing_Poly_insertC(v_k_2865_, v_m_2866_, v_p_2867_, v_c_2868_);
lean_dec(v_k_2865_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go(lean_object* v_k_2870_, lean_object* v_c_2871_, lean_object* v_a_2872_){
_start:
{
if (lean_obj_tag(v_a_2872_) == 0)
{
lean_object* v_k_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2883_; 
v_k_2873_ = lean_ctor_get(v_a_2872_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_a_2872_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2875_ = v_a_2872_;
v_isShared_2876_ = v_isSharedCheck_2883_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_k_2873_);
lean_dec(v_a_2872_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2883_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2877_ = lean_int_mul(v_k_2870_, v_k_2873_);
lean_dec(v_k_2873_);
v___x_2878_ = lean_nat_to_int(v_c_2871_);
v___x_2879_ = lean_int_emod(v___x_2877_, v___x_2878_);
lean_dec(v___x_2878_);
lean_dec(v___x_2877_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2879_);
v___x_2881_ = v___x_2875_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
else
{
lean_object* v_k_2884_; lean_object* v_v_2885_; lean_object* v_p_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2900_; 
v_k_2884_ = lean_ctor_get(v_a_2872_, 0);
v_v_2885_ = lean_ctor_get(v_a_2872_, 1);
v_p_2886_ = lean_ctor_get(v_a_2872_, 2);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_a_2872_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2888_ = v_a_2872_;
v_isShared_2889_ = v_isSharedCheck_2900_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_p_2886_);
lean_inc(v_v_2885_);
lean_inc(v_k_2884_);
lean_dec(v_a_2872_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2900_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v_k_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; 
v___x_2890_ = lean_int_mul(v_k_2870_, v_k_2884_);
lean_dec(v_k_2884_);
lean_inc(v_c_2871_);
v___x_2891_ = lean_nat_to_int(v_c_2871_);
v_k_2892_ = lean_int_emod(v___x_2890_, v___x_2891_);
lean_dec(v___x_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2894_ = lean_int_dec_eq(v_k_2892_, v___x_2893_);
if (v___x_2894_ == 0)
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2895_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_2870_, v_c_2871_, v_p_2886_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 2, v___x_2895_);
lean_ctor_set(v___x_2888_, 0, v_k_2892_);
v___x_2897_ = v___x_2888_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_k_2892_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_v_2885_);
lean_ctor_set(v_reuseFailAlloc_2898_, 2, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
else
{
lean_dec(v_k_2892_);
lean_del_object(v___x_2888_);
lean_dec(v_v_2885_);
v_a_2872_ = v_p_2886_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go___boxed(lean_object* v_k_2901_, lean_object* v_c_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_2901_, v_c_2902_, v_a_2903_);
lean_dec(v_k_2901_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object* v_k_2905_, lean_object* v_p_2906_, lean_object* v_c_2907_){
_start:
{
lean_object* v___x_2908_; lean_object* v_k_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
lean_inc(v_c_2907_);
v___x_2908_ = lean_nat_to_int(v_c_2907_);
v_k_2909_ = lean_int_emod(v_k_2905_, v___x_2908_);
lean_dec(v___x_2908_);
v___x_2910_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2911_ = lean_int_dec_eq(v_k_2909_, v___x_2910_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; uint8_t v___x_2913_; 
v___x_2912_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2913_ = lean_int_dec_eq(v_k_2909_, v___x_2912_);
lean_dec(v_k_2909_);
if (v___x_2913_ == 0)
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_2905_, v_c_2907_, v_p_2906_);
return v___x_2914_;
}
else
{
lean_dec(v_c_2907_);
return v_p_2906_;
}
}
else
{
lean_object* v___x_2915_; 
lean_dec(v_k_2909_);
lean_dec(v_c_2907_);
lean_dec_ref(v_p_2906_);
v___x_2915_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC___boxed(lean_object* v_k_2916_, lean_object* v_p_2917_, lean_object* v_c_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_2916_, v_p_2917_, v_c_2918_);
lean_dec(v_k_2916_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go(lean_object* v_k_2920_, lean_object* v_m_2921_, lean_object* v_c_2922_, lean_object* v_a_2923_){
_start:
{
if (lean_obj_tag(v_a_2923_) == 0)
{
lean_object* v_k_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v_k_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
v_k_2924_ = lean_ctor_get(v_a_2923_, 0);
lean_inc(v_k_2924_);
lean_dec_ref(v_a_2923_);
v___x_2925_ = lean_int_mul(v_k_2920_, v_k_2924_);
lean_dec(v_k_2924_);
v___x_2926_ = lean_nat_to_int(v_c_2922_);
v_k_2927_ = lean_int_emod(v___x_2925_, v___x_2926_);
lean_dec(v___x_2926_);
lean_dec(v___x_2925_);
v___x_2928_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2929_ = lean_int_dec_eq(v_k_2927_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2931_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2931_, 0, v_k_2927_);
lean_ctor_set(v___x_2931_, 1, v_m_2921_);
lean_ctor_set(v___x_2931_, 2, v___x_2930_);
return v___x_2931_;
}
else
{
lean_object* v___x_2932_; 
lean_dec(v_k_2927_);
lean_dec(v_m_2921_);
v___x_2932_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2932_;
}
}
else
{
lean_object* v_k_2933_; lean_object* v_v_2934_; lean_object* v_p_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2950_; 
v_k_2933_ = lean_ctor_get(v_a_2923_, 0);
v_v_2934_ = lean_ctor_get(v_a_2923_, 1);
v_p_2935_ = lean_ctor_get(v_a_2923_, 2);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_a_2923_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2937_ = v_a_2923_;
v_isShared_2938_ = v_isSharedCheck_2950_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_p_2935_);
lean_inc(v_v_2934_);
lean_inc(v_k_2933_);
lean_dec(v_a_2923_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2950_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v_k_2941_; lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2939_ = lean_int_mul(v_k_2920_, v_k_2933_);
lean_dec(v_k_2933_);
lean_inc(v_c_2922_);
v___x_2940_ = lean_nat_to_int(v_c_2922_);
v_k_2941_ = lean_int_emod(v___x_2939_, v___x_2940_);
lean_dec(v___x_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2943_ = lean_int_dec_eq(v_k_2941_, v___x_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2947_; 
lean_inc(v_m_2921_);
v___x_2944_ = l_Lean_Grind_CommRing_Mon_mul(v_m_2921_, v_v_2934_);
v___x_2945_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_2920_, v_m_2921_, v_c_2922_, v_p_2935_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 2, v___x_2945_);
lean_ctor_set(v___x_2937_, 1, v___x_2944_);
lean_ctor_set(v___x_2937_, 0, v_k_2941_);
v___x_2947_ = v___x_2937_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_k_2941_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_2948_, 2, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
else
{
lean_dec(v_k_2941_);
lean_del_object(v___x_2937_);
lean_dec(v_v_2934_);
v_a_2923_ = v_p_2935_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go___boxed(lean_object* v_k_2951_, lean_object* v_m_2952_, lean_object* v_c_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_2951_, v_m_2952_, v_c_2953_, v_a_2954_);
lean_dec(v_k_2951_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object* v_k_2956_, lean_object* v_m_2957_, lean_object* v_p_2958_, lean_object* v_c_2959_){
_start:
{
lean_object* v___x_2960_; lean_object* v_k_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; 
lean_inc(v_c_2959_);
v___x_2960_ = lean_nat_to_int(v_c_2959_);
v_k_2961_ = lean_int_emod(v_k_2956_, v___x_2960_);
lean_dec(v___x_2960_);
v___x_2962_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2963_ = lean_int_dec_eq(v_k_2961_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; uint8_t v___x_2965_; 
v___x_2964_ = lean_box(0);
v___x_2965_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2957_, v___x_2964_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; 
lean_dec(v_k_2961_);
v___x_2966_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_2956_, v_m_2957_, v_c_2959_, v_p_2958_);
return v___x_2966_;
}
else
{
lean_object* v___x_2967_; 
lean_dec(v_m_2957_);
v___x_2967_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_2961_, v_p_2958_, v_c_2959_);
lean_dec(v_k_2961_);
return v___x_2967_;
}
}
else
{
lean_object* v___x_2968_; 
lean_dec(v_k_2961_);
lean_dec(v_c_2959_);
lean_dec_ref(v_p_2958_);
lean_dec(v_m_2957_);
v___x_2968_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC___boxed(lean_object* v_k_2969_, lean_object* v_m_2970_, lean_object* v_p_2971_, lean_object* v_c_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_2969_, v_m_2970_, v_p_2971_, v_c_2972_);
lean_dec(v_k_2969_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(lean_object* v_k_2974_, lean_object* v_m_2975_, lean_object* v_c_2976_, lean_object* v_p_2977_, lean_object* v_acc_2978_){
_start:
{
if (lean_obj_tag(v_p_2977_) == 0)
{
lean_object* v_k_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_k_2979_ = lean_ctor_get(v_p_2977_, 0);
lean_inc(v_k_2979_);
lean_dec_ref(v_p_2977_);
v___x_2980_ = lean_int_mul(v_k_2974_, v_k_2979_);
lean_dec(v_k_2979_);
v___x_2981_ = lean_nat_to_int(v_c_2976_);
v___x_2982_ = lean_int_emod(v___x_2980_, v___x_2981_);
lean_dec(v___x_2981_);
lean_dec(v___x_2980_);
v___x_2983_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2982_, v_m_2975_, v_acc_2978_);
return v___x_2983_;
}
else
{
lean_object* v_k_2984_; lean_object* v_v_2985_; lean_object* v_p_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v_k_2984_ = lean_ctor_get(v_p_2977_, 0);
lean_inc(v_k_2984_);
v_v_2985_ = lean_ctor_get(v_p_2977_, 1);
lean_inc(v_v_2985_);
v_p_2986_ = lean_ctor_get(v_p_2977_, 2);
lean_inc_ref(v_p_2986_);
lean_dec_ref(v_p_2977_);
v___x_2987_ = lean_int_mul(v_k_2974_, v_k_2984_);
lean_dec(v_k_2984_);
lean_inc(v_c_2976_);
v___x_2988_ = lean_nat_to_int(v_c_2976_);
v___x_2989_ = lean_int_emod(v___x_2987_, v___x_2988_);
lean_dec(v___x_2988_);
lean_dec(v___x_2987_);
lean_inc(v_m_2975_);
v___x_2990_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_2975_, v_v_2985_);
v___x_2991_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2989_, v___x_2990_, v_acc_2978_);
v_p_2977_ = v_p_2986_;
v_acc_2978_ = v___x_2991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go___boxed(lean_object* v_k_2993_, lean_object* v_m_2994_, lean_object* v_c_2995_, lean_object* v_p_2996_, lean_object* v_acc_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_2993_, v_m_2994_, v_c_2995_, v_p_2996_, v_acc_2997_);
lean_dec(v_k_2993_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc(lean_object* v_k_2999_, lean_object* v_m_3000_, lean_object* v_p_3001_, lean_object* v_c_3002_){
_start:
{
lean_object* v___x_3003_; lean_object* v_k_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
lean_inc(v_c_3002_);
v___x_3003_ = lean_nat_to_int(v_c_3002_);
v_k_3004_ = lean_int_emod(v_k_2999_, v___x_3003_);
lean_dec(v___x_3003_);
v___x_3005_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3006_ = lean_int_dec_eq(v_k_3004_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3007_ = lean_box(0);
v___x_3008_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_3000_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_dec(v_k_3004_);
v___x_3009_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3010_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_2999_, v_m_3000_, v_c_3002_, v_p_3001_, v___x_3009_);
return v___x_3010_;
}
else
{
lean_object* v___x_3011_; 
lean_dec(v_m_3000_);
v___x_3011_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3004_, v_p_3001_, v_c_3002_);
lean_dec(v_k_3004_);
return v___x_3011_;
}
}
else
{
lean_object* v___x_3012_; 
lean_dec(v_k_3004_);
lean_dec(v_c_3002_);
lean_dec_ref(v_p_3001_);
lean_dec(v_m_3000_);
v___x_3012_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc___boxed(lean_object* v_k_3013_, lean_object* v_m_3014_, lean_object* v_p_3015_, lean_object* v_c_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3013_, v_m_3014_, v_p_3015_, v_c_3016_);
lean_dec(v_k_3013_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineC(lean_object* v_p_u2081_3018_, lean_object* v_p_u2082_3019_, lean_object* v_c_3020_){
_start:
{
if (lean_obj_tag(v_p_u2081_3018_) == 0)
{
if (lean_obj_tag(v_p_u2082_3019_) == 0)
{
lean_object* v_k_3021_; lean_object* v_k_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3032_; 
v_k_3021_ = lean_ctor_get(v_p_u2081_3018_, 0);
lean_inc(v_k_3021_);
lean_dec_ref(v_p_u2081_3018_);
v_k_3022_ = lean_ctor_get(v_p_u2082_3019_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_p_u2082_3019_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3024_ = v_p_u2082_3019_;
v_isShared_3025_ = v_isSharedCheck_3032_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_k_3022_);
lean_dec(v_p_u2082_3019_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3032_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3026_ = lean_int_add(v_k_3021_, v_k_3022_);
lean_dec(v_k_3022_);
lean_dec(v_k_3021_);
v___x_3027_ = lean_nat_to_int(v_c_3020_);
v___x_3028_ = lean_int_emod(v___x_3026_, v___x_3027_);
lean_dec(v___x_3027_);
lean_dec(v___x_3026_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3028_);
v___x_3030_ = v___x_3024_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
else
{
lean_object* v_k_3033_; lean_object* v___x_3034_; 
v_k_3033_ = lean_ctor_get(v_p_u2081_3018_, 0);
lean_inc(v_k_3033_);
lean_dec_ref(v_p_u2081_3018_);
v___x_3034_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2082_3019_, v_k_3033_, v_c_3020_);
lean_dec(v_k_3033_);
return v___x_3034_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_3019_) == 0)
{
lean_object* v_k_3035_; lean_object* v___x_3036_; 
v_k_3035_ = lean_ctor_get(v_p_u2082_3019_, 0);
lean_inc(v_k_3035_);
lean_dec_ref(v_p_u2082_3019_);
v___x_3036_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2081_3018_, v_k_3035_, v_c_3020_);
lean_dec(v_k_3035_);
return v___x_3036_;
}
else
{
lean_object* v_k_3037_; lean_object* v_v_3038_; lean_object* v_p_3039_; lean_object* v_k_3040_; lean_object* v_v_3041_; lean_object* v_p_3042_; uint8_t v___x_3043_; 
v_k_3037_ = lean_ctor_get(v_p_u2081_3018_, 0);
v_v_3038_ = lean_ctor_get(v_p_u2081_3018_, 1);
v_p_3039_ = lean_ctor_get(v_p_u2081_3018_, 2);
v_k_3040_ = lean_ctor_get(v_p_u2082_3019_, 0);
v_v_3041_ = lean_ctor_get(v_p_u2082_3019_, 1);
v_p_3042_ = lean_ctor_get(v_p_u2082_3019_, 2);
v___x_3043_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_3038_, v_v_3041_);
switch(v___x_3043_)
{
case 0:
{
lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3051_; 
lean_inc_ref(v_p_3042_);
lean_inc(v_v_3041_);
lean_inc(v_k_3040_);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_p_u2082_3019_);
if (v_isSharedCheck_3051_ == 0)
{
lean_object* v_unused_3052_; lean_object* v_unused_3053_; lean_object* v_unused_3054_; 
v_unused_3052_ = lean_ctor_get(v_p_u2082_3019_, 2);
lean_dec(v_unused_3052_);
v_unused_3053_ = lean_ctor_get(v_p_u2082_3019_, 1);
lean_dec(v_unused_3053_);
v_unused_3054_ = lean_ctor_get(v_p_u2082_3019_, 0);
lean_dec(v_unused_3054_);
v___x_3045_ = v_p_u2082_3019_;
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
else
{
lean_dec(v_p_u2082_3019_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_u2081_3018_, v_p_3042_, v_c_3020_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 2, v___x_3047_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_k_3040_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_v_3041_);
lean_ctor_set(v_reuseFailAlloc_3050_, 2, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
case 1:
{
lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3068_; 
lean_inc_ref(v_p_3042_);
lean_inc(v_k_3040_);
lean_inc_ref(v_p_3039_);
lean_inc(v_v_3038_);
lean_inc(v_k_3037_);
lean_dec_ref(v_p_u2081_3018_);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_p_u2082_3019_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; lean_object* v_unused_3070_; lean_object* v_unused_3071_; 
v_unused_3069_ = lean_ctor_get(v_p_u2082_3019_, 2);
lean_dec(v_unused_3069_);
v_unused_3070_ = lean_ctor_get(v_p_u2082_3019_, 1);
lean_dec(v_unused_3070_);
v_unused_3071_ = lean_ctor_get(v_p_u2082_3019_, 0);
lean_dec(v_unused_3071_);
v___x_3056_ = v_p_u2082_3019_;
v_isShared_3057_ = v_isSharedCheck_3068_;
goto v_resetjp_3055_;
}
else
{
lean_dec(v_p_u2082_3019_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3068_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v_k_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v___x_3058_ = lean_int_add(v_k_3037_, v_k_3040_);
lean_dec(v_k_3040_);
lean_dec(v_k_3037_);
lean_inc(v_c_3020_);
v___x_3059_ = lean_nat_to_int(v_c_3020_);
v_k_3060_ = lean_int_emod(v___x_3058_, v___x_3059_);
lean_dec(v___x_3059_);
lean_dec(v___x_3058_);
v___x_3061_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3062_ = lean_int_dec_eq(v_k_3060_, v___x_3061_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3063_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3039_, v_p_3042_, v_c_3020_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 2, v___x_3063_);
lean_ctor_set(v___x_3056_, 1, v_v_3038_);
lean_ctor_set(v___x_3056_, 0, v_k_3060_);
v___x_3065_ = v___x_3056_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_k_3060_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v_v_3038_);
lean_ctor_set(v_reuseFailAlloc_3066_, 2, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
else
{
lean_dec(v_k_3060_);
lean_del_object(v___x_3056_);
lean_dec(v_v_3038_);
v_p_u2081_3018_ = v_p_3039_;
v_p_u2082_3019_ = v_p_3042_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3079_; 
lean_inc_ref(v_p_3039_);
lean_inc(v_v_3038_);
lean_inc(v_k_3037_);
v_isSharedCheck_3079_ = !lean_is_exclusive(v_p_u2081_3018_);
if (v_isSharedCheck_3079_ == 0)
{
lean_object* v_unused_3080_; lean_object* v_unused_3081_; lean_object* v_unused_3082_; 
v_unused_3080_ = lean_ctor_get(v_p_u2081_3018_, 2);
lean_dec(v_unused_3080_);
v_unused_3081_ = lean_ctor_get(v_p_u2081_3018_, 1);
lean_dec(v_unused_3081_);
v_unused_3082_ = lean_ctor_get(v_p_u2081_3018_, 0);
lean_dec(v_unused_3082_);
v___x_3073_ = v_p_u2081_3018_;
v_isShared_3074_ = v_isSharedCheck_3079_;
goto v_resetjp_3072_;
}
else
{
lean_dec(v_p_u2081_3018_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3079_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3075_; lean_object* v___x_3077_; 
v___x_3075_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3039_, v_p_u2082_3019_, v_c_3020_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 2, v___x_3075_);
v___x_3077_ = v___x_3073_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_k_3037_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_v_3038_);
lean_ctor_set(v_reuseFailAlloc_3078_, 2, v___x_3075_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC_go(lean_object* v_p_u2082_3083_, lean_object* v_c_3084_, lean_object* v_p_u2081_3085_, lean_object* v_acc_3086_){
_start:
{
if (lean_obj_tag(v_p_u2081_3085_) == 0)
{
lean_object* v_k_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v_k_3087_ = lean_ctor_get(v_p_u2081_3085_, 0);
lean_inc(v_k_3087_);
lean_dec_ref(v_p_u2081_3085_);
lean_inc(v_c_3084_);
v___x_3088_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3087_, v_p_u2082_3083_, v_c_3084_);
lean_dec(v_k_3087_);
v___x_3089_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3086_, v___x_3088_, v_c_3084_);
return v___x_3089_;
}
else
{
lean_object* v_k_3090_; lean_object* v_v_3091_; lean_object* v_p_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v_k_3090_ = lean_ctor_get(v_p_u2081_3085_, 0);
lean_inc(v_k_3090_);
v_v_3091_ = lean_ctor_get(v_p_u2081_3085_, 1);
lean_inc(v_v_3091_);
v_p_3092_ = lean_ctor_get(v_p_u2081_3085_, 2);
lean_inc_ref(v_p_3092_);
lean_dec_ref(v_p_u2081_3085_);
lean_inc(v_c_3084_);
lean_inc_ref(v_p_u2082_3083_);
v___x_3093_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_3090_, v_v_3091_, v_p_u2082_3083_, v_c_3084_);
lean_dec(v_k_3090_);
lean_inc(v_c_3084_);
v___x_3094_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3086_, v___x_3093_, v_c_3084_);
v_p_u2081_3085_ = v_p_3092_;
v_acc_3086_ = v___x_3094_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC(lean_object* v_p_u2081_3096_, lean_object* v_p_u2082_3097_, lean_object* v_c_3098_){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3100_ = l_Lean_Grind_CommRing_Poly_mulC_go(v_p_u2082_3097_, v_c_3098_, v_p_u2081_3096_, v___x_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc_go(lean_object* v_p_u2082_3101_, lean_object* v_c_3102_, lean_object* v_p_u2081_3103_, lean_object* v_acc_3104_){
_start:
{
if (lean_obj_tag(v_p_u2081_3103_) == 0)
{
lean_object* v_k_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_k_3105_ = lean_ctor_get(v_p_u2081_3103_, 0);
lean_inc(v_k_3105_);
lean_dec_ref(v_p_u2081_3103_);
lean_inc(v_c_3102_);
v___x_3106_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3105_, v_p_u2082_3101_, v_c_3102_);
lean_dec(v_k_3105_);
v___x_3107_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3104_, v___x_3106_, v_c_3102_);
return v___x_3107_;
}
else
{
lean_object* v_k_3108_; lean_object* v_v_3109_; lean_object* v_p_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v_k_3108_ = lean_ctor_get(v_p_u2081_3103_, 0);
lean_inc(v_k_3108_);
v_v_3109_ = lean_ctor_get(v_p_u2081_3103_, 1);
lean_inc(v_v_3109_);
v_p_3110_ = lean_ctor_get(v_p_u2081_3103_, 2);
lean_inc_ref(v_p_3110_);
lean_dec_ref(v_p_u2081_3103_);
lean_inc(v_c_3102_);
lean_inc_ref(v_p_u2082_3101_);
v___x_3111_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3108_, v_v_3109_, v_p_u2082_3101_, v_c_3102_);
lean_dec(v_k_3108_);
lean_inc(v_c_3102_);
v___x_3112_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3104_, v___x_3111_, v_c_3102_);
v_p_u2081_3103_ = v_p_3110_;
v_acc_3104_ = v___x_3112_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc(lean_object* v_p_u2081_3114_, lean_object* v_p_u2082_3115_, lean_object* v_c_3116_){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3118_ = l_Lean_Grind_CommRing_Poly_mulC__nc_go(v_p_u2082_3115_, v_c_3116_, v_p_u2081_3114_, v___x_3117_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC(lean_object* v_p_3119_, lean_object* v_k_3120_, lean_object* v_c_3121_){
_start:
{
lean_object* v_zero_3122_; uint8_t v_isZero_3123_; 
v_zero_3122_ = lean_unsigned_to_nat(0u);
v_isZero_3123_ = lean_nat_dec_eq(v_k_3120_, v_zero_3122_);
if (v_isZero_3123_ == 1)
{
lean_object* v___x_3124_; 
lean_dec(v_c_3121_);
lean_dec_ref(v_p_3119_);
v___x_3124_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3124_;
}
else
{
lean_object* v_one_3125_; lean_object* v_n_3126_; uint8_t v___x_3127_; 
v_one_3125_ = lean_unsigned_to_nat(1u);
v_n_3126_ = lean_nat_sub(v_k_3120_, v_one_3125_);
v___x_3127_ = lean_nat_dec_eq(v_n_3126_, v_zero_3122_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
lean_inc(v_c_3121_);
lean_inc_ref(v_p_3119_);
v___x_3128_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3119_, v_n_3126_, v_c_3121_);
lean_dec(v_n_3126_);
v___x_3129_ = l_Lean_Grind_CommRing_Poly_mulC(v_p_3119_, v___x_3128_, v_c_3121_);
return v___x_3129_;
}
else
{
lean_dec(v_n_3126_);
lean_dec(v_c_3121_);
return v_p_3119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC___boxed(lean_object* v_p_3130_, lean_object* v_k_3131_, lean_object* v_c_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3130_, v_k_3131_, v_c_3132_);
lean_dec(v_k_3131_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc(lean_object* v_p_3134_, lean_object* v_k_3135_, lean_object* v_c_3136_){
_start:
{
lean_object* v_zero_3137_; uint8_t v_isZero_3138_; 
v_zero_3137_ = lean_unsigned_to_nat(0u);
v_isZero_3138_ = lean_nat_dec_eq(v_k_3135_, v_zero_3137_);
if (v_isZero_3138_ == 1)
{
lean_object* v___x_3139_; 
lean_dec(v_c_3136_);
lean_dec_ref(v_p_3134_);
v___x_3139_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3139_;
}
else
{
lean_object* v_one_3140_; lean_object* v_n_3141_; uint8_t v___x_3142_; 
v_one_3140_ = lean_unsigned_to_nat(1u);
v_n_3141_ = lean_nat_sub(v_k_3135_, v_one_3140_);
v___x_3142_ = lean_nat_dec_eq(v_n_3141_, v_zero_3137_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
lean_inc(v_c_3136_);
lean_inc_ref(v_p_3134_);
v___x_3143_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3134_, v_n_3141_, v_c_3136_);
lean_dec(v_n_3141_);
v___x_3144_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3143_, v_p_3134_, v_c_3136_);
return v___x_3144_;
}
else
{
lean_dec(v_n_3141_);
lean_dec(v_c_3136_);
return v_p_3134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc___boxed(lean_object* v_p_3145_, lean_object* v_k_3146_, lean_object* v_c_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3145_, v_k_3146_, v_c_3147_);
lean_dec(v_k_3146_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC_go(lean_object* v_c_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v_k_3152_; 
switch(lean_obj_tag(v_a_3150_))
{
case 1:
{
lean_object* v_k_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3166_; 
v_k_3156_ = lean_ctor_get(v_a_3150_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_a_3150_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3158_ = v_a_3150_;
v_isShared_3159_ = v_isSharedCheck_3166_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_k_3156_);
lean_dec(v_a_3150_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3166_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
v___x_3160_ = lean_nat_to_int(v_k_3156_);
v___x_3161_ = lean_nat_to_int(v_c_3149_);
v___x_3162_ = lean_int_emod(v___x_3160_, v___x_3161_);
lean_dec(v___x_3161_);
lean_dec(v___x_3160_);
if (v_isShared_3159_ == 0)
{
lean_ctor_set_tag(v___x_3158_, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3162_);
v___x_3164_ = v___x_3158_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3162_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
case 3:
{
lean_object* v_i_3167_; lean_object* v___x_3168_; 
lean_dec(v_c_3149_);
v_i_3167_ = lean_ctor_get(v_a_3150_, 0);
lean_inc(v_i_3167_);
lean_dec_ref(v_a_3150_);
v___x_3168_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3167_);
return v___x_3168_;
}
case 4:
{
lean_object* v_a_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_a_3169_ = lean_ctor_get(v_a_3150_, 0);
lean_inc_ref(v_a_3169_);
lean_dec_ref(v_a_3150_);
v___x_3170_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3149_);
v___x_3171_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3149_, v_a_3169_);
v___x_3172_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3170_, v___x_3171_, v_c_3149_);
return v___x_3172_;
}
case 5:
{
lean_object* v_a_3173_; lean_object* v_b_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_a_3173_ = lean_ctor_get(v_a_3150_, 0);
lean_inc_ref(v_a_3173_);
v_b_3174_ = lean_ctor_get(v_a_3150_, 1);
lean_inc_ref(v_b_3174_);
lean_dec_ref(v_a_3150_);
lean_inc(v_c_3149_);
v___x_3175_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3149_, v_a_3173_);
lean_inc(v_c_3149_);
v___x_3176_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3149_, v_b_3174_);
v___x_3177_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3175_, v___x_3176_, v_c_3149_);
return v___x_3177_;
}
case 6:
{
lean_object* v_a_3178_; lean_object* v_b_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v_a_3178_ = lean_ctor_get(v_a_3150_, 0);
lean_inc_ref(v_a_3178_);
v_b_3179_ = lean_ctor_get(v_a_3150_, 1);
lean_inc_ref(v_b_3179_);
lean_dec_ref(v_a_3150_);
lean_inc(v_c_3149_);
v___x_3180_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3149_, v_a_3178_);
v___x_3181_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3149_);
v___x_3182_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3149_, v_b_3179_);
lean_inc(v_c_3149_);
v___x_3183_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3181_, v___x_3182_, v_c_3149_);
v___x_3184_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3180_, v___x_3183_, v_c_3149_);
return v___x_3184_;
}
case 7:
{
lean_object* v_a_3185_; lean_object* v_b_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v_a_3185_ = lean_ctor_get(v_a_3150_, 0);
lean_inc_ref(v_a_3185_);
v_b_3186_ = lean_ctor_get(v_a_3150_, 1);
lean_inc_ref(v_b_3186_);
lean_dec_ref(v_a_3150_);
lean_inc(v_c_3149_);
v___x_3187_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3149_, v_a_3185_);
lean_inc(v_c_3149_);
v___x_3188_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3149_, v_b_3186_);
v___x_3189_ = l_Lean_Grind_CommRing_Poly_mulC(v___x_3187_, v___x_3188_, v_c_3149_);
return v___x_3189_;
}
case 8:
{
lean_object* v_a_3190_; lean_object* v_k_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3218_; 
v_a_3190_ = lean_ctor_get(v_a_3150_, 0);
v_k_3191_ = lean_ctor_get(v_a_3150_, 1);
v_isSharedCheck_3218_ = !lean_is_exclusive(v_a_3150_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3193_ = v_a_3150_;
v_isShared_3194_ = v_isSharedCheck_3218_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_k_3191_);
lean_inc(v_a_3190_);
lean_dec(v_a_3150_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3218_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; uint8_t v___x_3196_; 
v___x_3195_ = lean_unsigned_to_nat(0u);
v___x_3196_ = lean_nat_dec_eq(v_k_3191_, v___x_3195_);
if (v___x_3196_ == 0)
{
switch(lean_obj_tag(v_a_3190_))
{
case 0:
{
lean_object* v_k_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3207_; 
lean_del_object(v___x_3193_);
v_k_3197_ = lean_ctor_get(v_a_3190_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_a_3190_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3199_ = v_a_3190_;
v_isShared_3200_ = v_isSharedCheck_3207_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_k_3197_);
lean_dec(v_a_3190_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3207_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3201_ = l_Int_pow(v_k_3197_, v_k_3191_);
lean_dec(v_k_3191_);
lean_dec(v_k_3197_);
v___x_3202_ = lean_nat_to_int(v_c_3149_);
v___x_3203_ = lean_int_emod(v___x_3201_, v___x_3202_);
lean_dec(v___x_3202_);
lean_dec(v___x_3201_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v___x_3203_);
v___x_3205_ = v___x_3199_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
case 3:
{
lean_object* v_i_3208_; lean_object* v___x_3210_; 
lean_dec(v_c_3149_);
v_i_3208_ = lean_ctor_get(v_a_3190_, 0);
lean_inc(v_i_3208_);
lean_dec_ref(v_a_3190_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set_tag(v___x_3193_, 0);
lean_ctor_set(v___x_3193_, 0, v_i_3208_);
v___x_3210_ = v___x_3193_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_i_3208_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_k_3191_);
v___x_3210_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = lean_box(0);
v___x_3212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3212_);
return v___x_3213_;
}
}
default: 
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_del_object(v___x_3193_);
lean_inc(v_c_3149_);
v___x_3215_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3149_, v_a_3190_);
v___x_3216_ = l_Lean_Grind_CommRing_Poly_powC(v___x_3215_, v_k_3191_, v_c_3149_);
lean_dec(v_k_3191_);
return v___x_3216_;
}
}
}
else
{
lean_object* v___x_3217_; 
lean_del_object(v___x_3193_);
lean_dec(v_k_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_c_3149_);
v___x_3217_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3217_;
}
}
}
default: 
{
lean_object* v_k_3219_; 
v_k_3219_ = lean_ctor_get(v_a_3150_, 0);
lean_inc(v_k_3219_);
lean_dec_ref(v_a_3150_);
v_k_3152_ = v_k_3219_;
goto v___jp_3151_;
}
}
v___jp_3151_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3153_ = lean_nat_to_int(v_c_3149_);
v___x_3154_ = lean_int_emod(v_k_3152_, v___x_3153_);
lean_dec(v___x_3153_);
lean_dec(v_k_3152_);
v___x_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
return v___x_3155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC(lean_object* v_e_3220_, lean_object* v_c_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3221_, v_e_3220_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(lean_object* v_c_3223_, lean_object* v_a_3224_){
_start:
{
lean_object* v_k_3226_; 
switch(lean_obj_tag(v_a_3224_))
{
case 1:
{
lean_object* v_k_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3240_; 
v_k_3230_ = lean_ctor_get(v_a_3224_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_a_3224_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3232_ = v_a_3224_;
v_isShared_3233_ = v_isSharedCheck_3240_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_k_3230_);
lean_dec(v_a_3224_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3240_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3234_ = lean_nat_to_int(v_k_3230_);
v___x_3235_ = lean_nat_to_int(v_c_3223_);
v___x_3236_ = lean_int_emod(v___x_3234_, v___x_3235_);
lean_dec(v___x_3235_);
lean_dec(v___x_3234_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set_tag(v___x_3232_, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3236_);
v___x_3238_ = v___x_3232_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
case 3:
{
lean_object* v_i_3241_; lean_object* v___x_3242_; 
lean_dec(v_c_3223_);
v_i_3241_ = lean_ctor_get(v_a_3224_, 0);
lean_inc(v_i_3241_);
lean_dec_ref(v_a_3224_);
v___x_3242_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3241_);
return v___x_3242_;
}
case 4:
{
lean_object* v_a_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v_a_3243_ = lean_ctor_get(v_a_3224_, 0);
lean_inc_ref(v_a_3243_);
lean_dec_ref(v_a_3224_);
v___x_3244_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3223_);
v___x_3245_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3223_, v_a_3243_);
v___x_3246_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3244_, v___x_3245_, v_c_3223_);
return v___x_3246_;
}
case 5:
{
lean_object* v_a_3247_; lean_object* v_b_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v_a_3247_ = lean_ctor_get(v_a_3224_, 0);
lean_inc_ref(v_a_3247_);
v_b_3248_ = lean_ctor_get(v_a_3224_, 1);
lean_inc_ref(v_b_3248_);
lean_dec_ref(v_a_3224_);
lean_inc(v_c_3223_);
v___x_3249_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3223_, v_a_3247_);
lean_inc(v_c_3223_);
v___x_3250_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3223_, v_b_3248_);
v___x_3251_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3249_, v___x_3250_, v_c_3223_);
return v___x_3251_;
}
case 6:
{
lean_object* v_a_3252_; lean_object* v_b_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_a_3252_ = lean_ctor_get(v_a_3224_, 0);
lean_inc_ref(v_a_3252_);
v_b_3253_ = lean_ctor_get(v_a_3224_, 1);
lean_inc_ref(v_b_3253_);
lean_dec_ref(v_a_3224_);
lean_inc(v_c_3223_);
v___x_3254_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3223_, v_a_3252_);
v___x_3255_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3223_);
v___x_3256_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3223_, v_b_3253_);
lean_inc(v_c_3223_);
v___x_3257_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3255_, v___x_3256_, v_c_3223_);
v___x_3258_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3254_, v___x_3257_, v_c_3223_);
return v___x_3258_;
}
case 7:
{
lean_object* v_a_3259_; lean_object* v_b_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v_a_3259_ = lean_ctor_get(v_a_3224_, 0);
lean_inc_ref(v_a_3259_);
v_b_3260_ = lean_ctor_get(v_a_3224_, 1);
lean_inc_ref(v_b_3260_);
lean_dec_ref(v_a_3224_);
lean_inc(v_c_3223_);
v___x_3261_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3223_, v_a_3259_);
lean_inc(v_c_3223_);
v___x_3262_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3223_, v_b_3260_);
v___x_3263_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3261_, v___x_3262_, v_c_3223_);
return v___x_3263_;
}
case 8:
{
lean_object* v_a_3264_; lean_object* v_k_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3292_; 
v_a_3264_ = lean_ctor_get(v_a_3224_, 0);
v_k_3265_ = lean_ctor_get(v_a_3224_, 1);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_a_3224_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3267_ = v_a_3224_;
v_isShared_3268_ = v_isSharedCheck_3292_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_k_3265_);
lean_inc(v_a_3264_);
lean_dec(v_a_3224_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3292_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; uint8_t v___x_3270_; 
v___x_3269_ = lean_unsigned_to_nat(0u);
v___x_3270_ = lean_nat_dec_eq(v_k_3265_, v___x_3269_);
if (v___x_3270_ == 0)
{
switch(lean_obj_tag(v_a_3264_))
{
case 0:
{
lean_object* v_k_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3281_; 
lean_del_object(v___x_3267_);
v_k_3271_ = lean_ctor_get(v_a_3264_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v_a_3264_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3273_ = v_a_3264_;
v_isShared_3274_ = v_isSharedCheck_3281_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_k_3271_);
lean_dec(v_a_3264_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3281_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3279_; 
v___x_3275_ = l_Int_pow(v_k_3271_, v_k_3265_);
lean_dec(v_k_3265_);
lean_dec(v_k_3271_);
v___x_3276_ = lean_nat_to_int(v_c_3223_);
v___x_3277_ = lean_int_emod(v___x_3275_, v___x_3276_);
lean_dec(v___x_3276_);
lean_dec(v___x_3275_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3277_);
v___x_3279_ = v___x_3273_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3277_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
case 3:
{
lean_object* v_i_3282_; lean_object* v___x_3284_; 
lean_dec(v_c_3223_);
v_i_3282_ = lean_ctor_get(v_a_3264_, 0);
lean_inc(v_i_3282_);
lean_dec_ref(v_a_3264_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set_tag(v___x_3267_, 0);
lean_ctor_set(v___x_3267_, 0, v_i_3282_);
v___x_3284_ = v___x_3267_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_i_3282_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_k_3265_);
v___x_3284_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3285_ = lean_box(0);
v___x_3286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3286_);
return v___x_3287_;
}
}
default: 
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_del_object(v___x_3267_);
lean_inc(v_c_3223_);
v___x_3289_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3223_, v_a_3264_);
v___x_3290_ = l_Lean_Grind_CommRing_Poly_powC__nc(v___x_3289_, v_k_3265_, v_c_3223_);
lean_dec(v_k_3265_);
return v___x_3290_;
}
}
}
else
{
lean_object* v___x_3291_; 
lean_del_object(v___x_3267_);
lean_dec(v_k_3265_);
lean_dec_ref(v_a_3264_);
lean_dec(v_c_3223_);
v___x_3291_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3291_;
}
}
}
default: 
{
lean_object* v_k_3293_; 
v_k_3293_ = lean_ctor_get(v_a_3224_, 0);
lean_inc(v_k_3293_);
lean_dec_ref(v_a_3224_);
v_k_3226_ = v_k_3293_;
goto v___jp_3225_;
}
}
v___jp_3225_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = lean_nat_to_int(v_c_3223_);
v___x_3228_ = lean_int_emod(v_k_3226_, v___x_3227_);
lean_dec(v___x_3227_);
lean_dec(v_k_3226_);
v___x_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
return v___x_3229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc(lean_object* v_e_3294_, lean_object* v_c_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3295_, v_e_3294_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter___redArg(lean_object* v_x_3297_, lean_object* v_h__1_3298_){
_start:
{
lean_object* v_x_3299_; lean_object* v_k_3300_; lean_object* v___x_3301_; 
v_x_3299_ = lean_ctor_get(v_x_3297_, 0);
lean_inc(v_x_3299_);
v_k_3300_ = lean_ctor_get(v_x_3297_, 1);
lean_inc(v_k_3300_);
lean_dec_ref(v_x_3297_);
v___x_3301_ = lean_apply_2(v_h__1_3298_, v_x_3299_, v_k_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter(lean_object* v_motive_3302_, lean_object* v_x_3303_, lean_object* v_h__1_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter___redArg(v_x_3303_, v_h__1_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(lean_object* v_k_3306_, lean_object* v_h__1_3307_, lean_object* v_h__2_3308_, lean_object* v_h__3_3309_){
_start:
{
lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3310_ = lean_unsigned_to_nat(0u);
v___x_3311_ = lean_nat_dec_eq(v_k_3306_, v___x_3310_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3312_; uint8_t v___x_3313_; 
lean_dec(v_h__1_3307_);
v___x_3312_ = lean_unsigned_to_nat(1u);
v___x_3313_ = lean_nat_dec_eq(v_k_3306_, v___x_3312_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; 
lean_dec(v_h__2_3308_);
v___x_3314_ = lean_apply_3(v_h__3_3309_, v_k_3306_, lean_box(0), lean_box(0));
return v___x_3314_;
}
else
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec(v_h__3_3309_);
lean_dec(v_k_3306_);
v___x_3315_ = lean_box(0);
v___x_3316_ = lean_apply_1(v_h__2_3308_, v___x_3315_);
return v___x_3316_;
}
}
else
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_dec(v_h__3_3309_);
lean_dec(v_h__2_3308_);
lean_dec(v_k_3306_);
v___x_3317_ = lean_box(0);
v___x_3318_ = lean_apply_1(v_h__1_3307_, v___x_3317_);
return v___x_3318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(lean_object* v_motive_3319_, lean_object* v_k_3320_, lean_object* v_h__1_3321_, lean_object* v_h__2_3322_, lean_object* v_h__3_3323_){
_start:
{
lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___x_3324_ = lean_unsigned_to_nat(0u);
v___x_3325_ = lean_nat_dec_eq(v_k_3320_, v___x_3324_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; uint8_t v___x_3327_; 
lean_dec(v_h__1_3321_);
v___x_3326_ = lean_unsigned_to_nat(1u);
v___x_3327_ = lean_nat_dec_eq(v_k_3320_, v___x_3326_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; 
lean_dec(v_h__2_3322_);
v___x_3328_ = lean_apply_3(v_h__3_3323_, v_k_3320_, lean_box(0), lean_box(0));
return v___x_3328_;
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
lean_dec(v_h__3_3323_);
lean_dec(v_k_3320_);
v___x_3329_ = lean_box(0);
v___x_3330_ = lean_apply_1(v_h__2_3322_, v___x_3329_);
return v___x_3330_;
}
}
else
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
lean_dec(v_h__3_3323_);
lean_dec(v_h__2_3322_);
lean_dec(v_k_3320_);
v___x_3331_ = lean_box(0);
v___x_3332_ = lean_apply_1(v_h__1_3321_, v___x_3331_);
return v___x_3332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(lean_object* v_m_u2081_3333_, lean_object* v_h__1_3334_, lean_object* v_h__2_3335_, lean_object* v_h__3_3336_){
_start:
{
if (lean_obj_tag(v_m_u2081_3333_) == 0)
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_dec(v_h__3_3336_);
lean_dec(v_h__2_3335_);
v___x_3337_ = lean_box(0);
v___x_3338_ = lean_apply_1(v_h__1_3334_, v___x_3337_);
return v___x_3338_;
}
else
{
lean_object* v_m_3339_; 
lean_dec(v_h__1_3334_);
v_m_3339_ = lean_ctor_get(v_m_u2081_3333_, 1);
if (lean_obj_tag(v_m_3339_) == 0)
{
lean_object* v_p_3340_; lean_object* v___x_3341_; 
lean_dec(v_h__3_3336_);
v_p_3340_ = lean_ctor_get(v_m_u2081_3333_, 0);
lean_inc_ref(v_p_3340_);
lean_dec_ref(v_m_u2081_3333_);
v___x_3341_ = lean_apply_1(v_h__2_3335_, v_p_3340_);
return v___x_3341_;
}
else
{
lean_object* v_p_3342_; lean_object* v___x_3343_; 
lean_inc(v_m_3339_);
lean_dec(v_h__2_3335_);
v_p_3342_ = lean_ctor_get(v_m_u2081_3333_, 0);
lean_inc_ref(v_p_3342_);
lean_dec_ref(v_m_u2081_3333_);
v___x_3343_ = lean_apply_3(v_h__3_3336_, v_p_3342_, v_m_3339_, lean_box(0));
return v___x_3343_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(lean_object* v_motive_3344_, lean_object* v_m_u2081_3345_, lean_object* v_h__1_3346_, lean_object* v_h__2_3347_, lean_object* v_h__3_3348_){
_start:
{
if (lean_obj_tag(v_m_u2081_3345_) == 0)
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
lean_dec(v_h__3_3348_);
lean_dec(v_h__2_3347_);
v___x_3349_ = lean_box(0);
v___x_3350_ = lean_apply_1(v_h__1_3346_, v___x_3349_);
return v___x_3350_;
}
else
{
lean_object* v_m_3351_; 
lean_dec(v_h__1_3346_);
v_m_3351_ = lean_ctor_get(v_m_u2081_3345_, 1);
if (lean_obj_tag(v_m_3351_) == 0)
{
lean_object* v_p_3352_; lean_object* v___x_3353_; 
lean_dec(v_h__3_3348_);
v_p_3352_ = lean_ctor_get(v_m_u2081_3345_, 0);
lean_inc_ref(v_p_3352_);
lean_dec_ref(v_m_u2081_3345_);
v___x_3353_ = lean_apply_1(v_h__2_3347_, v_p_3352_);
return v___x_3353_;
}
else
{
lean_object* v_p_3354_; lean_object* v___x_3355_; 
lean_inc(v_m_3351_);
lean_dec(v_h__2_3347_);
v_p_3354_ = lean_ctor_get(v_m_u2081_3345_, 0);
lean_inc_ref(v_p_3354_);
lean_dec_ref(v_m_u2081_3345_);
v___x_3355_ = lean_apply_3(v_h__3_3348_, v_p_3354_, v_m_3351_, lean_box(0));
return v___x_3355_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(uint8_t v_a_3356_, lean_object* v_h__1_3357_, lean_object* v_h__2_3358_){
_start:
{
if (v_a_3356_ == 1)
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_dec(v_h__2_3358_);
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_apply_1(v_h__1_3357_, v___x_3359_);
return v___x_3360_;
}
else
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
lean_dec(v_h__1_3357_);
v___x_3361_ = lean_box(v_a_3356_);
v___x_3362_ = lean_apply_2(v_h__2_3358_, v___x_3361_, lean_box(0));
return v___x_3362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object* v_a_3363_, lean_object* v_h__1_3364_, lean_object* v_h__2_3365_){
_start:
{
uint8_t v_a_17__boxed_3366_; lean_object* v_res_3367_; 
v_a_17__boxed_3366_ = lean_unbox(v_a_3363_);
v_res_3367_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(v_a_17__boxed_3366_, v_h__1_3364_, v_h__2_3365_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(lean_object* v_motive_3368_, uint8_t v_a_3369_, lean_object* v_h__1_3370_, lean_object* v_h__2_3371_){
_start:
{
if (v_a_3369_ == 1)
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
lean_dec(v_h__2_3371_);
v___x_3372_ = lean_box(0);
v___x_3373_ = lean_apply_1(v_h__1_3370_, v___x_3372_);
return v___x_3373_;
}
else
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
lean_dec(v_h__1_3370_);
v___x_3374_ = lean_box(v_a_3369_);
v___x_3375_ = lean_apply_2(v_h__2_3371_, v___x_3374_, lean_box(0));
return v___x_3375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___boxed(lean_object* v_motive_3376_, lean_object* v_a_3377_, lean_object* v_h__1_3378_, lean_object* v_h__2_3379_){
_start:
{
uint8_t v_a_28__boxed_3380_; lean_object* v_res_3381_; 
v_a_28__boxed_3380_ = lean_unbox(v_a_3377_);
v_res_3381_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(v_motive_3376_, v_a_28__boxed_3380_, v_h__1_3378_, v_h__2_3379_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(lean_object* v_p_3382_, lean_object* v_h__1_3383_, lean_object* v_h__2_3384_, lean_object* v_h__3_3385_){
_start:
{
if (lean_obj_tag(v_p_3382_) == 0)
{
lean_object* v_k_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; 
lean_dec(v_h__3_3385_);
v_k_3386_ = lean_ctor_get(v_p_3382_, 0);
lean_inc(v_k_3386_);
lean_dec_ref(v_p_3382_);
v___x_3387_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3388_ = lean_int_dec_eq(v_k_3386_, v___x_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; 
lean_dec(v_h__1_3383_);
v___x_3389_ = lean_apply_2(v_h__2_3384_, v_k_3386_, lean_box(0));
return v___x_3389_;
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
lean_dec(v_k_3386_);
lean_dec(v_h__2_3384_);
v___x_3390_ = lean_box(0);
v___x_3391_ = lean_apply_1(v_h__1_3383_, v___x_3390_);
return v___x_3391_;
}
}
else
{
lean_object* v_k_3392_; lean_object* v_v_3393_; lean_object* v_p_3394_; lean_object* v___x_3395_; 
lean_dec(v_h__2_3384_);
lean_dec(v_h__1_3383_);
v_k_3392_ = lean_ctor_get(v_p_3382_, 0);
lean_inc(v_k_3392_);
v_v_3393_ = lean_ctor_get(v_p_3382_, 1);
lean_inc(v_v_3393_);
v_p_3394_ = lean_ctor_get(v_p_3382_, 2);
lean_inc_ref(v_p_3394_);
lean_dec_ref(v_p_3382_);
v___x_3395_ = lean_apply_3(v_h__3_3385_, v_k_3392_, v_v_3393_, v_p_3394_);
return v___x_3395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(lean_object* v_motive_3396_, lean_object* v_p_3397_, lean_object* v_h__1_3398_, lean_object* v_h__2_3399_, lean_object* v_h__3_3400_){
_start:
{
if (lean_obj_tag(v_p_3397_) == 0)
{
lean_object* v_k_3401_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
lean_dec(v_h__3_3400_);
v_k_3401_ = lean_ctor_get(v_p_3397_, 0);
lean_inc(v_k_3401_);
lean_dec_ref(v_p_3397_);
v___x_3402_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3403_ = lean_int_dec_eq(v_k_3401_, v___x_3402_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
lean_dec(v_h__1_3398_);
v___x_3404_ = lean_apply_2(v_h__2_3399_, v_k_3401_, lean_box(0));
return v___x_3404_;
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
lean_dec(v_k_3401_);
lean_dec(v_h__2_3399_);
v___x_3405_ = lean_box(0);
v___x_3406_ = lean_apply_1(v_h__1_3398_, v___x_3405_);
return v___x_3406_;
}
}
else
{
lean_object* v_k_3407_; lean_object* v_v_3408_; lean_object* v_p_3409_; lean_object* v___x_3410_; 
lean_dec(v_h__2_3399_);
lean_dec(v_h__1_3398_);
v_k_3407_ = lean_ctor_get(v_p_3397_, 0);
lean_inc(v_k_3407_);
v_v_3408_ = lean_ctor_get(v_p_3397_, 1);
lean_inc(v_v_3408_);
v_p_3409_ = lean_ctor_get(v_p_3397_, 2);
lean_inc_ref(v_p_3409_);
lean_dec_ref(v_p_3397_);
v___x_3410_ = lean_apply_3(v_h__3_3400_, v_k_3407_, v_v_3408_, v_p_3409_);
return v___x_3410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object* v_k_3411_, lean_object* v_h__1_3412_, lean_object* v_h__2_3413_, lean_object* v_h__3_3414_){
_start:
{
lean_object* v_zero_3415_; uint8_t v_isZero_3416_; 
v_zero_3415_ = lean_unsigned_to_nat(0u);
v_isZero_3416_ = lean_nat_dec_eq(v_k_3411_, v_zero_3415_);
if (v_isZero_3416_ == 1)
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec(v_h__3_3414_);
lean_dec(v_h__2_3413_);
v___x_3417_ = lean_box(0);
v___x_3418_ = lean_apply_1(v_h__1_3412_, v___x_3417_);
return v___x_3418_;
}
else
{
lean_object* v_one_3419_; lean_object* v_n_3420_; uint8_t v___x_3421_; 
lean_dec(v_h__1_3412_);
v_one_3419_ = lean_unsigned_to_nat(1u);
v_n_3420_ = lean_nat_sub(v_k_3411_, v_one_3419_);
v___x_3421_ = lean_nat_dec_eq(v_n_3420_, v_zero_3415_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; 
lean_dec(v_h__2_3413_);
v___x_3422_ = lean_apply_2(v_h__3_3414_, v_n_3420_, lean_box(0));
return v___x_3422_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
lean_dec(v_n_3420_);
lean_dec(v_h__3_3414_);
v___x_3423_ = lean_box(0);
v___x_3424_ = lean_apply_1(v_h__2_3413_, v___x_3423_);
return v___x_3424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object* v_k_3425_, lean_object* v_h__1_3426_, lean_object* v_h__2_3427_, lean_object* v_h__3_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(v_k_3425_, v_h__1_3426_, v_h__2_3427_, v_h__3_3428_);
lean_dec(v_k_3425_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object* v_motive_3430_, lean_object* v_k_3431_, lean_object* v_h__1_3432_, lean_object* v_h__2_3433_, lean_object* v_h__3_3434_){
_start:
{
lean_object* v_zero_3435_; uint8_t v_isZero_3436_; 
v_zero_3435_ = lean_unsigned_to_nat(0u);
v_isZero_3436_ = lean_nat_dec_eq(v_k_3431_, v_zero_3435_);
if (v_isZero_3436_ == 1)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_dec(v_h__3_3434_);
lean_dec(v_h__2_3433_);
v___x_3437_ = lean_box(0);
v___x_3438_ = lean_apply_1(v_h__1_3432_, v___x_3437_);
return v___x_3438_;
}
else
{
lean_object* v_one_3439_; lean_object* v_n_3440_; uint8_t v___x_3441_; 
lean_dec(v_h__1_3432_);
v_one_3439_ = lean_unsigned_to_nat(1u);
v_n_3440_ = lean_nat_sub(v_k_3431_, v_one_3439_);
v___x_3441_ = lean_nat_dec_eq(v_n_3440_, v_zero_3435_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; 
lean_dec(v_h__2_3433_);
v___x_3442_ = lean_apply_2(v_h__3_3434_, v_n_3440_, lean_box(0));
return v___x_3442_;
}
else
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_dec(v_n_3440_);
lean_dec(v_h__3_3434_);
v___x_3443_ = lean_box(0);
v___x_3444_ = lean_apply_1(v_h__2_3433_, v___x_3443_);
return v___x_3444_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object* v_motive_3445_, lean_object* v_k_3446_, lean_object* v_h__1_3447_, lean_object* v_h__2_3448_, lean_object* v_h__3_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(v_motive_3445_, v_k_3446_, v_h__1_3447_, v_h__2_3448_, v_h__3_3449_);
lean_dec(v_k_3446_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(lean_object* v_x_3451_, lean_object* v_h__1_3452_, lean_object* v_h__2_3453_, lean_object* v_h__3_3454_, lean_object* v_h__4_3455_, lean_object* v_h__5_3456_, lean_object* v_h__6_3457_, lean_object* v_h__7_3458_, lean_object* v_h__8_3459_, lean_object* v_h__9_3460_){
_start:
{
switch(lean_obj_tag(v_x_3451_))
{
case 0:
{
lean_object* v_k_3461_; lean_object* v___x_3462_; 
lean_dec(v_h__9_3460_);
lean_dec(v_h__8_3459_);
lean_dec(v_h__7_3458_);
lean_dec(v_h__6_3457_);
lean_dec(v_h__5_3456_);
lean_dec(v_h__4_3455_);
lean_dec(v_h__3_3454_);
lean_dec(v_h__2_3453_);
v_k_3461_ = lean_ctor_get(v_x_3451_, 0);
lean_inc(v_k_3461_);
lean_dec_ref(v_x_3451_);
v___x_3462_ = lean_apply_1(v_h__1_3452_, v_k_3461_);
return v___x_3462_;
}
case 1:
{
lean_object* v_k_3463_; lean_object* v___x_3464_; 
lean_dec(v_h__9_3460_);
lean_dec(v_h__8_3459_);
lean_dec(v_h__7_3458_);
lean_dec(v_h__6_3457_);
lean_dec(v_h__5_3456_);
lean_dec(v_h__4_3455_);
lean_dec(v_h__3_3454_);
lean_dec(v_h__1_3452_);
v_k_3463_ = lean_ctor_get(v_x_3451_, 0);
lean_inc(v_k_3463_);
lean_dec_ref(v_x_3451_);
v___x_3464_ = lean_apply_1(v_h__2_3453_, v_k_3463_);
return v___x_3464_;
}
case 2:
{
lean_object* v_k_3465_; lean_object* v___x_3466_; 
lean_dec(v_h__9_3460_);
lean_dec(v_h__8_3459_);
lean_dec(v_h__7_3458_);
lean_dec(v_h__6_3457_);
lean_dec(v_h__5_3456_);
lean_dec(v_h__4_3455_);
lean_dec(v_h__2_3453_);
lean_dec(v_h__1_3452_);
v_k_3465_ = lean_ctor_get(v_x_3451_, 0);
lean_inc(v_k_3465_);
lean_dec_ref(v_x_3451_);
v___x_3466_ = lean_apply_1(v_h__3_3454_, v_k_3465_);
return v___x_3466_;
}
case 3:
{
lean_object* v_i_3467_; lean_object* v___x_3468_; 
lean_dec(v_h__9_3460_);
lean_dec(v_h__8_3459_);
lean_dec(v_h__7_3458_);
lean_dec(v_h__6_3457_);
lean_dec(v_h__5_3456_);
lean_dec(v_h__3_3454_);
lean_dec(v_h__2_3453_);
lean_dec(v_h__1_3452_);
v_i_3467_ = lean_ctor_get(v_x_3451_, 0);
lean_inc(v_i_3467_);
lean_dec_ref(v_x_3451_);
v___x_3468_ = lean_apply_1(v_h__4_3455_, v_i_3467_);
return v___x_3468_;
}
case 4:
{
lean_object* v_a_3469_; lean_object* v___x_3470_; 
lean_dec(v_h__9_3460_);
lean_dec(v_h__8_3459_);
lean_dec(v_h__6_3457_);
lean_dec(v_h__5_3456_);
lean_dec(v_h__4_3455_);
lean_dec(v_h__3_3454_);
lean_dec(v_h__2_3453_);
lean_dec(v_h__1_3452_);
v_a_3469_ = lean_ctor_get(v_x_3451_, 0);
lean_inc_ref(v_a_3469_);
lean_dec_ref(v_x_3451_);
v___x_3470_ = lean_apply_1(v_h__7_3458_, v_a_3469_);
return v___x_3470_;
}
case 5:
{
lean_object* v_a_3471_; lean_object* v_b_3472_; lean_object* v___x_3473_; 
lean_dec(v_h__9_3460_);
lean_dec(v_h__8_3459_);
lean_dec(v_h__7_3458_);
lean_dec(v_h__6_3457_);
lean_dec(v_h__4_3455_);
lean_dec(v_h__3_3454_);
lean_dec(v_h__2_3453_);
lean_dec(v_h__1_3452_);
v_a_3471_ = lean_ctor_get(v_x_3451_, 0);
lean_inc_ref(v_a_3471_);
v_b_3472_ = lean_ctor_get(v_x_3451_, 1);
lean_inc_ref(v_b_3472_);
lean_dec_ref(v_x_3451_);
v___x_3473_ = lean_apply_2(v_h__5_3456_, v_a_3471_, v_b_3472_);
return v___x_3473_;
}
case 6:
{
lean_object* v_a_3474_; lean_object* v_b_3475_; lean_object* v___x_3476_; 
lean_dec(v_h__9_3460_);
lean_dec(v_h__7_3458_);
lean_dec(v_h__6_3457_);
lean_dec(v_h__5_3456_);
lean_dec(v_h__4_3455_);
lean_dec(v_h__3_3454_);
lean_dec(v_h__2_3453_);
lean_dec(v_h__1_3452_);
v_a_3474_ = lean_ctor_get(v_x_3451_, 0);
lean_inc_ref(v_a_3474_);
v_b_3475_ = lean_ctor_get(v_x_3451_, 1);
lean_inc_ref(v_b_3475_);
lean_dec_ref(v_x_3451_);
v___x_3476_ = lean_apply_2(v_h__8_3459_, v_a_3474_, v_b_3475_);
return v___x_3476_;
}
case 7:
{
lean_object* v_a_3477_; lean_object* v_b_3478_; lean_object* v___x_3479_; 
lean_dec(v_h__9_3460_);
lean_dec(v_h__8_3459_);
lean_dec(v_h__7_3458_);
lean_dec(v_h__5_3456_);
lean_dec(v_h__4_3455_);
lean_dec(v_h__3_3454_);
lean_dec(v_h__2_3453_);
lean_dec(v_h__1_3452_);
v_a_3477_ = lean_ctor_get(v_x_3451_, 0);
lean_inc_ref(v_a_3477_);
v_b_3478_ = lean_ctor_get(v_x_3451_, 1);
lean_inc_ref(v_b_3478_);
lean_dec_ref(v_x_3451_);
v___x_3479_ = lean_apply_2(v_h__6_3457_, v_a_3477_, v_b_3478_);
return v___x_3479_;
}
default: 
{
lean_object* v_a_3480_; lean_object* v_k_3481_; lean_object* v___x_3482_; 
lean_dec(v_h__8_3459_);
lean_dec(v_h__7_3458_);
lean_dec(v_h__6_3457_);
lean_dec(v_h__5_3456_);
lean_dec(v_h__4_3455_);
lean_dec(v_h__3_3454_);
lean_dec(v_h__2_3453_);
lean_dec(v_h__1_3452_);
v_a_3480_ = lean_ctor_get(v_x_3451_, 0);
lean_inc_ref(v_a_3480_);
v_k_3481_ = lean_ctor_get(v_x_3451_, 1);
lean_inc(v_k_3481_);
lean_dec_ref(v_x_3451_);
v___x_3482_ = lean_apply_2(v_h__9_3460_, v_a_3480_, v_k_3481_);
return v___x_3482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter(lean_object* v_motive_3483_, lean_object* v_x_3484_, lean_object* v_h__1_3485_, lean_object* v_h__2_3486_, lean_object* v_h__3_3487_, lean_object* v_h__4_3488_, lean_object* v_h__5_3489_, lean_object* v_h__6_3490_, lean_object* v_h__7_3491_, lean_object* v_h__8_3492_, lean_object* v_h__9_3493_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(v_x_3484_, v_h__1_3485_, v_h__2_3486_, v_h__3_3487_, v_h__4_3488_, v_h__5_3489_, v_h__6_3490_, v_h__7_3491_, v_h__8_3492_, v_h__9_3493_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter___redArg(lean_object* v_a_3495_, lean_object* v_h__1_3496_, lean_object* v_h__2_3497_, lean_object* v_h__3_3498_){
_start:
{
switch(lean_obj_tag(v_a_3495_))
{
case 0:
{
lean_object* v_k_3499_; lean_object* v___x_3500_; 
lean_dec(v_h__3_3498_);
lean_dec(v_h__2_3497_);
v_k_3499_ = lean_ctor_get(v_a_3495_, 0);
lean_inc(v_k_3499_);
lean_dec_ref(v_a_3495_);
v___x_3500_ = lean_apply_1(v_h__1_3496_, v_k_3499_);
return v___x_3500_;
}
case 3:
{
lean_object* v_i_3501_; lean_object* v___x_3502_; 
lean_dec(v_h__3_3498_);
lean_dec(v_h__1_3496_);
v_i_3501_ = lean_ctor_get(v_a_3495_, 0);
lean_inc(v_i_3501_);
lean_dec_ref(v_a_3495_);
v___x_3502_ = lean_apply_1(v_h__2_3497_, v_i_3501_);
return v___x_3502_;
}
default: 
{
lean_object* v___x_3503_; 
lean_dec(v_h__2_3497_);
lean_dec(v_h__1_3496_);
v___x_3503_ = lean_apply_3(v_h__3_3498_, v_a_3495_, lean_box(0), lean_box(0));
return v___x_3503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter(lean_object* v_motive_3504_, lean_object* v_a_3505_, lean_object* v_h__1_3506_, lean_object* v_h__2_3507_, lean_object* v_h__3_3508_){
_start:
{
switch(lean_obj_tag(v_a_3505_))
{
case 0:
{
lean_object* v_k_3509_; lean_object* v___x_3510_; 
lean_dec(v_h__3_3508_);
lean_dec(v_h__2_3507_);
v_k_3509_ = lean_ctor_get(v_a_3505_, 0);
lean_inc(v_k_3509_);
lean_dec_ref(v_a_3505_);
v___x_3510_ = lean_apply_1(v_h__1_3506_, v_k_3509_);
return v___x_3510_;
}
case 3:
{
lean_object* v_i_3511_; lean_object* v___x_3512_; 
lean_dec(v_h__3_3508_);
lean_dec(v_h__1_3506_);
v_i_3511_ = lean_ctor_get(v_a_3505_, 0);
lean_inc(v_i_3511_);
lean_dec_ref(v_a_3505_);
v___x_3512_ = lean_apply_1(v_h__2_3507_, v_i_3511_);
return v___x_3512_;
}
default: 
{
lean_object* v___x_3513_; 
lean_dec(v_h__2_3507_);
lean_dec(v_h__1_3506_);
v___x_3513_ = lean_apply_3(v_h__3_3508_, v_a_3505_, lean_box(0), lean_box(0));
return v___x_3513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(lean_object* v_inst_3514_, lean_object* v_ctx_3515_, lean_object* v_m_3516_, lean_object* v_acc_3517_){
_start:
{
if (lean_obj_tag(v_m_3516_) == 0)
{
lean_dec_ref(v_inst_3514_);
return v_acc_3517_;
}
else
{
lean_object* v_toSemiring_3518_; lean_object* v_toMul_3519_; lean_object* v_ofNat_3520_; lean_object* v_npow_3521_; lean_object* v_p_3522_; lean_object* v_m_3523_; lean_object* v___y_3525_; lean_object* v_x_3528_; lean_object* v_k_3529_; lean_object* v___x_3530_; uint8_t v___x_3531_; 
v_toSemiring_3518_ = lean_ctor_get(v_inst_3514_, 0);
v_toMul_3519_ = lean_ctor_get(v_toSemiring_3518_, 1);
v_ofNat_3520_ = lean_ctor_get(v_toSemiring_3518_, 3);
v_npow_3521_ = lean_ctor_get(v_toSemiring_3518_, 5);
v_p_3522_ = lean_ctor_get(v_m_3516_, 0);
lean_inc_ref(v_p_3522_);
v_m_3523_ = lean_ctor_get(v_m_3516_, 1);
lean_inc(v_m_3523_);
lean_dec_ref(v_m_3516_);
v_x_3528_ = lean_ctor_get(v_p_3522_, 0);
lean_inc(v_x_3528_);
v_k_3529_ = lean_ctor_get(v_p_3522_, 1);
lean_inc(v_k_3529_);
lean_dec_ref(v_p_3522_);
v___x_3530_ = lean_unsigned_to_nat(0u);
v___x_3531_ = lean_nat_dec_eq(v_k_3529_, v___x_3530_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; uint8_t v___x_3533_; 
v___x_3532_ = lean_unsigned_to_nat(1u);
v___x_3533_ = lean_nat_dec_eq(v_k_3529_, v___x_3532_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = l_Lean_RArray_getImpl___redArg(v_ctx_3515_, v_x_3528_);
lean_dec(v_x_3528_);
lean_inc(v_npow_3521_);
v___x_3535_ = lean_apply_2(v_npow_3521_, v___x_3534_, v_k_3529_);
v___y_3525_ = v___x_3535_;
goto v___jp_3524_;
}
else
{
lean_object* v___x_3536_; 
lean_dec(v_k_3529_);
v___x_3536_ = l_Lean_RArray_getImpl___redArg(v_ctx_3515_, v_x_3528_);
lean_dec(v_x_3528_);
v___y_3525_ = v___x_3536_;
goto v___jp_3524_;
}
}
else
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
lean_dec(v_k_3529_);
lean_dec(v_x_3528_);
v___x_3537_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3520_);
v___x_3538_ = lean_apply_1(v_ofNat_3520_, v___x_3537_);
v___y_3525_ = v___x_3538_;
goto v___jp_3524_;
}
v___jp_3524_:
{
lean_object* v___x_3526_; 
lean_inc(v_toMul_3519_);
v___x_3526_ = lean_apply_2(v_toMul_3519_, v_acc_3517_, v___y_3525_);
v_m_3516_ = v_m_3523_;
v_acc_3517_ = v___x_3526_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg___boxed(lean_object* v_inst_3539_, lean_object* v_ctx_3540_, lean_object* v_m_3541_, lean_object* v_acc_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3539_, v_ctx_3540_, v_m_3541_, v_acc_3542_);
lean_dec_ref(v_ctx_3540_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(lean_object* v_00_u03b1_3544_, lean_object* v_inst_3545_, lean_object* v_ctx_3546_, lean_object* v_m_3547_, lean_object* v_acc_3548_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3545_, v_ctx_3546_, v_m_3547_, v_acc_3548_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___boxed(lean_object* v_00_u03b1_3550_, lean_object* v_inst_3551_, lean_object* v_ctx_3552_, lean_object* v_m_3553_, lean_object* v_acc_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(v_00_u03b1_3550_, v_inst_3551_, v_ctx_3552_, v_m_3553_, v_acc_3554_);
lean_dec_ref(v_ctx_3552_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(lean_object* v_inst_3556_, lean_object* v_ctx_3557_, lean_object* v_m_3558_){
_start:
{
if (lean_obj_tag(v_m_3558_) == 0)
{
lean_object* v_toSemiring_3559_; lean_object* v_ofNat_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v_toSemiring_3559_ = lean_ctor_get(v_inst_3556_, 0);
lean_inc_ref(v_toSemiring_3559_);
lean_dec_ref(v_inst_3556_);
v_ofNat_3560_ = lean_ctor_get(v_toSemiring_3559_, 3);
lean_inc(v_ofNat_3560_);
lean_dec_ref(v_toSemiring_3559_);
v___x_3561_ = lean_unsigned_to_nat(1u);
v___x_3562_ = lean_apply_1(v_ofNat_3560_, v___x_3561_);
return v___x_3562_;
}
else
{
lean_object* v_toSemiring_3563_; lean_object* v_p_3564_; lean_object* v_m_3565_; lean_object* v_ofNat_3566_; lean_object* v_npow_3567_; lean_object* v_x_3568_; lean_object* v_k_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v_toSemiring_3563_ = lean_ctor_get(v_inst_3556_, 0);
v_p_3564_ = lean_ctor_get(v_m_3558_, 0);
lean_inc_ref(v_p_3564_);
v_m_3565_ = lean_ctor_get(v_m_3558_, 1);
lean_inc(v_m_3565_);
lean_dec_ref(v_m_3558_);
v_ofNat_3566_ = lean_ctor_get(v_toSemiring_3563_, 3);
v_npow_3567_ = lean_ctor_get(v_toSemiring_3563_, 5);
v_x_3568_ = lean_ctor_get(v_p_3564_, 0);
lean_inc(v_x_3568_);
v_k_3569_ = lean_ctor_get(v_p_3564_, 1);
lean_inc(v_k_3569_);
lean_dec_ref(v_p_3564_);
v___x_3570_ = lean_unsigned_to_nat(0u);
v___x_3571_ = lean_nat_dec_eq(v_k_3569_, v___x_3570_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; uint8_t v___x_3573_; 
v___x_3572_ = lean_unsigned_to_nat(1u);
v___x_3573_ = lean_nat_dec_eq(v_k_3569_, v___x_3572_);
if (v___x_3573_ == 0)
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3574_ = l_Lean_RArray_getImpl___redArg(v_ctx_3557_, v_x_3568_);
lean_dec(v_x_3568_);
lean_inc(v_npow_3567_);
v___x_3575_ = lean_apply_2(v_npow_3567_, v___x_3574_, v_k_3569_);
v___x_3576_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3556_, v_ctx_3557_, v_m_3565_, v___x_3575_);
return v___x_3576_;
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
lean_dec(v_k_3569_);
v___x_3577_ = l_Lean_RArray_getImpl___redArg(v_ctx_3557_, v_x_3568_);
lean_dec(v_x_3568_);
v___x_3578_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3556_, v_ctx_3557_, v_m_3565_, v___x_3577_);
return v___x_3578_;
}
}
else
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
lean_dec(v_k_3569_);
lean_dec(v_x_3568_);
v___x_3579_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3566_);
v___x_3580_ = lean_apply_1(v_ofNat_3566_, v___x_3579_);
v___x_3581_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3556_, v_ctx_3557_, v_m_3565_, v___x_3580_);
return v___x_3581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3582_, lean_object* v_ctx_3583_, lean_object* v_m_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3582_, v_ctx_3583_, v_m_3584_);
lean_dec_ref(v_ctx_3583_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule(lean_object* v_00_u03b1_3586_, lean_object* v_inst_3587_, lean_object* v_ctx_3588_, lean_object* v_m_3589_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3587_, v_ctx_3588_, v_m_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3591_, lean_object* v_inst_3592_, lean_object* v_ctx_3593_, lean_object* v_m_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule(v_00_u03b1_3591_, v_inst_3592_, v_ctx_3593_, v_m_3594_);
lean_dec_ref(v_ctx_3593_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(lean_object* v_inst_3596_, lean_object* v_ctx_3597_, lean_object* v_p_3598_){
_start:
{
lean_object* v___x_3599_; 
lean_inc_ref(v_inst_3596_);
v___x_3599_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_3596_);
if (lean_obj_tag(v_p_3598_) == 0)
{
lean_object* v_toSemiring_3600_; lean_object* v_zsmul_3601_; lean_object* v_ofNat_3602_; lean_object* v_k_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v_toSemiring_3600_ = lean_ctor_get(v_inst_3596_, 0);
lean_inc_ref(v_toSemiring_3600_);
lean_dec_ref(v_inst_3596_);
v_zsmul_3601_ = lean_ctor_get(v___x_3599_, 2);
lean_inc(v_zsmul_3601_);
lean_dec_ref(v___x_3599_);
v_ofNat_3602_ = lean_ctor_get(v_toSemiring_3600_, 3);
lean_inc(v_ofNat_3602_);
lean_dec_ref(v_toSemiring_3600_);
v_k_3603_ = lean_ctor_get(v_p_3598_, 0);
lean_inc(v_k_3603_);
lean_dec_ref(v_p_3598_);
v___x_3604_ = lean_unsigned_to_nat(1u);
v___x_3605_ = lean_apply_1(v_ofNat_3602_, v___x_3604_);
v___x_3606_ = lean_apply_2(v_zsmul_3601_, v_k_3603_, v___x_3605_);
return v___x_3606_;
}
else
{
lean_object* v_toSemiring_3607_; lean_object* v_zsmul_3608_; lean_object* v_toAdd_3609_; lean_object* v_k_3610_; lean_object* v_v_3611_; lean_object* v_p_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v_toSemiring_3607_ = lean_ctor_get(v_inst_3596_, 0);
v_zsmul_3608_ = lean_ctor_get(v___x_3599_, 2);
lean_inc(v_zsmul_3608_);
lean_dec_ref(v___x_3599_);
v_toAdd_3609_ = lean_ctor_get(v_toSemiring_3607_, 0);
lean_inc(v_toAdd_3609_);
v_k_3610_ = lean_ctor_get(v_p_3598_, 0);
lean_inc(v_k_3610_);
v_v_3611_ = lean_ctor_get(v_p_3598_, 1);
lean_inc(v_v_3611_);
v_p_3612_ = lean_ctor_get(v_p_3598_, 2);
lean_inc_ref(v_p_3612_);
lean_dec_ref(v_p_3598_);
lean_inc_ref(v_inst_3596_);
v___x_3613_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3596_, v_ctx_3597_, v_v_3611_);
v___x_3614_ = lean_apply_2(v_zsmul_3608_, v_k_3610_, v___x_3613_);
v___x_3615_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3596_, v_ctx_3597_, v_p_3612_);
v___x_3616_ = lean_apply_2(v_toAdd_3609_, v___x_3614_, v___x_3615_);
return v___x_3616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3617_, lean_object* v_ctx_3618_, lean_object* v_p_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3617_, v_ctx_3618_, v_p_3619_);
lean_dec_ref(v_ctx_3618_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule(lean_object* v_00_u03b1_3621_, lean_object* v_inst_3622_, lean_object* v_ctx_3623_, lean_object* v_p_3624_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3622_, v_ctx_3623_, v_p_3624_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3626_, lean_object* v_inst_3627_, lean_object* v_ctx_3628_, lean_object* v_p_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule(v_00_u03b1_3626_, v_inst_3627_, v_ctx_3628_, v_p_3629_);
lean_dec_ref(v_ctx_3628_);
return v_res_3630_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__gcd__cert(lean_object* v_a_3631_, lean_object* v_b_3632_, lean_object* v_p_u2081_3633_, lean_object* v_p_u2082_3634_, lean_object* v_p_3635_){
_start:
{
if (lean_obj_tag(v_p_u2081_3633_) == 0)
{
if (lean_obj_tag(v_p_u2082_3634_) == 0)
{
if (lean_obj_tag(v_p_3635_) == 0)
{
lean_object* v_k_3636_; lean_object* v_k_3637_; lean_object* v_k_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; 
v_k_3636_ = lean_ctor_get(v_p_u2081_3633_, 0);
v_k_3637_ = lean_ctor_get(v_p_u2082_3634_, 0);
v_k_3638_ = lean_ctor_get(v_p_3635_, 0);
v___x_3639_ = lean_int_mul(v_a_3631_, v_k_3636_);
v___x_3640_ = lean_int_mul(v_b_3632_, v_k_3637_);
v___x_3641_ = lean_int_add(v___x_3639_, v___x_3640_);
lean_dec(v___x_3640_);
lean_dec(v___x_3639_);
v___x_3642_ = lean_int_dec_eq(v_k_3638_, v___x_3641_);
lean_dec(v___x_3641_);
return v___x_3642_;
}
else
{
uint8_t v___x_3643_; 
v___x_3643_ = 0;
return v___x_3643_;
}
}
else
{
uint8_t v___x_3644_; 
v___x_3644_ = 0;
return v___x_3644_;
}
}
else
{
uint8_t v___x_3645_; 
v___x_3645_ = 0;
return v___x_3645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__gcd__cert___boxed(lean_object* v_a_3646_, lean_object* v_b_3647_, lean_object* v_p_u2081_3648_, lean_object* v_p_u2082_3649_, lean_object* v_p_3650_){
_start:
{
uint8_t v_res_3651_; lean_object* v_r_3652_; 
v_res_3651_ = l_Lean_Grind_CommRing_eq__gcd__cert(v_a_3646_, v_b_3647_, v_p_u2081_3648_, v_p_u2082_3649_, v_p_3650_);
lean_dec_ref(v_p_3650_);
lean_dec_ref(v_p_u2082_3649_);
lean_dec_ref(v_p_u2081_3648_);
lean_dec(v_b_3647_);
lean_dec(v_a_3646_);
v_r_3652_ = lean_box(v_res_3651_);
return v_r_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(lean_object* v_p_3653_, lean_object* v_h__1_3654_, lean_object* v_h__2_3655_){
_start:
{
if (lean_obj_tag(v_p_3653_) == 0)
{
lean_object* v_k_3656_; lean_object* v___x_3657_; 
lean_dec(v_h__1_3654_);
v_k_3656_ = lean_ctor_get(v_p_3653_, 0);
lean_inc(v_k_3656_);
lean_dec_ref(v_p_3653_);
v___x_3657_ = lean_apply_1(v_h__2_3655_, v_k_3656_);
return v___x_3657_;
}
else
{
lean_object* v_k_3658_; lean_object* v_v_3659_; lean_object* v_p_3660_; lean_object* v___x_3661_; 
lean_dec(v_h__2_3655_);
v_k_3658_ = lean_ctor_get(v_p_3653_, 0);
lean_inc(v_k_3658_);
v_v_3659_ = lean_ctor_get(v_p_3653_, 1);
lean_inc(v_v_3659_);
v_p_3660_ = lean_ctor_get(v_p_3653_, 2);
lean_inc_ref(v_p_3660_);
lean_dec_ref(v_p_3653_);
v___x_3661_ = lean_apply_3(v_h__1_3654_, v_k_3658_, v_v_3659_, v_p_3660_);
return v___x_3661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter(lean_object* v_motive_3662_, lean_object* v_p_3663_, lean_object* v_h__1_3664_, lean_object* v_h__2_3665_){
_start:
{
lean_object* v___x_3666_; 
v___x_3666_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(v_p_3663_, v_h__1_3664_, v_h__2_3665_);
return v___x_3666_;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_Field(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* runtime_initialize_Init_GrindInstances_Ring_Int(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Ring_CommSolver(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Field(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ordered_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_Ring_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
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
l_Lean_Grind_CommRing_instInhabitedExpr_default = _init_l_Lean_Grind_CommRing_instInhabitedExpr_default();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedExpr_default);
l_Lean_Grind_CommRing_instInhabitedExpr = _init_l_Lean_Grind_CommRing_instInhabitedExpr();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedExpr);
l_Lean_Grind_CommRing_instInhabitedMon_default = _init_l_Lean_Grind_CommRing_instInhabitedMon_default();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedMon_default);
l_Lean_Grind_CommRing_instInhabitedMon = _init_l_Lean_Grind_CommRing_instInhabitedMon();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedMon);
l_Lean_Grind_CommRing_hugeFuel = _init_l_Lean_Grind_CommRing_hugeFuel();
lean_mark_persistent(l_Lean_Grind_CommRing_hugeFuel);
l_Lean_Grind_CommRing_instInhabitedPoly_default = _init_l_Lean_Grind_CommRing_instInhabitedPoly_default();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPoly_default);
l_Lean_Grind_CommRing_instInhabitedPoly = _init_l_Lean_Grind_CommRing_instInhabitedPoly();
lean_mark_persistent(l_Lean_Grind_CommRing_instInhabitedPoly);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Ring_CommSolver(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_Field(uint8_t builtin);
lean_object* initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* initialize_Init_GrindInstances_Ring_Int(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_RArray(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Grind_Ordered_Order(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Repr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Ring_CommSolver(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
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
res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Ring_CommSolver(builtin);
}
#ifdef __cplusplus
}
#endif
