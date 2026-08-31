// Lean compiler output
// Module: Init.Grind.Ring.CommSolver
// Imports: public import Init.Data.Ord.Basic public import Init.Grind.Ring.Field public import Init.Grind.Ordered.Ring public import Init.GrindInstances.Ring.Int import all Init.Data.Ord.Basic import Init.LawfulBEqTactics public import Init.Classical public import Init.Data.Bool public import Init.Data.Int.DivMod.Lemmas public import Init.Data.RArray public import Init.Ext import Init.Data.Hashable import Init.Data.Int.LemmasAux import Init.Data.Nat.Internal.Linear import Init.Grind.Ordered.Order import Init.Omega import Init.WFTactics import Init.Data.Int.Repr
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
lean_object* l_Ordering_ctorIdx(uint8_t);
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
static lean_once_cell_t l_Lean_Grind_CommRing_Poly_isSorted___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Poly_isSorted___closed__0;
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
lean_dec_ref_known(v_t_13_, 1);
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
lean_dec_ref_known(v_t_13_, 2);
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
lean_dec_ref_known(v_t_13_, 2);
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
lean_dec_ref_known(v_t_13_, 2);
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
lean_dec_ref_known(v_t_13_, 2);
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
v___y_328_ = v___x_342_;
v___y_329_ = v___y_341_;
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
v___y_328_ = v___x_342_;
v___y_329_ = v___y_341_;
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
lean_inc(v___y_365_);
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
v___y_319_ = v___x_387_;
v___y_320_ = v___y_386_;
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
v___y_319_ = v___x_387_;
v___y_320_ = v___y_386_;
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
lean_inc(v___y_410_);
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
lean_dec_ref_known(v_x_316_, 1);
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
lean_inc(v___y_429_);
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
lean_inc(v___y_447_);
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
lean_inc(v___y_472_);
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
lean_inc(v___y_497_);
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
lean_inc(v___y_522_);
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
lean_inc(v___y_319_);
v___x_322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_322_, 0, v___y_319_);
lean_ctor_set(v___x_322_, 1, v___y_321_);
lean_inc(v___y_320_);
v___x_323_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_323_, 0, v___y_320_);
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
lean_inc(v___y_328_);
v___x_331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_331_, 0, v___y_328_);
lean_ctor_set(v___x_331_, 1, v___y_330_);
lean_inc(v___y_329_);
v___x_332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_332_, 0, v___y_329_);
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
lean_dec_ref_known(v_t_748_, 2);
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
lean_dec_ref_known(v_x_798_, 2);
v_p_808_ = lean_ctor_get(v_x_799_, 0);
lean_inc_ref(v_p_808_);
v_m_809_ = lean_ctor_get(v_x_799_, 1);
lean_inc(v_m_809_);
lean_dec_ref_known(v_x_799_, 2);
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
lean_dec_ref_known(v_x_813_, 2);
v_p_823_ = lean_ctor_get(v_x_814_, 0);
lean_inc_ref(v_p_823_);
v_m_824_ = lean_ctor_get(v_x_814_, 1);
lean_inc(v_m_824_);
lean_dec_ref_known(v_x_814_, 2);
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
lean_inc(v___y_856_);
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
lean_inc(v___y_839_);
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
lean_dec_ref_known(v_x_897_, 2);
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
lean_dec_ref_known(v_m_937_, 2);
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
lean_dec_ref_known(v_m_978_, 2);
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
lean_dec_ref_known(v_m_1007_, 2);
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
lean_object* v_zero_1206_; uint8_t v_isZero_1207_; 
v_zero_1206_ = lean_unsigned_to_nat(0u);
v_isZero_1207_ = lean_nat_dec_eq(v_fuel_1203_, v_zero_1206_);
if (v_isZero_1207_ == 1)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_h__2_1205_);
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_apply_1(v_h__1_1204_, v___x_1208_);
return v___x_1209_;
}
else
{
lean_object* v_one_1210_; lean_object* v_n_1211_; lean_object* v___x_1212_; 
lean_dec(v_h__1_1204_);
v_one_1210_ = lean_unsigned_to_nat(1u);
v_n_1211_ = lean_nat_sub(v_fuel_1203_, v_one_1210_);
v___x_1212_ = lean_apply_1(v_h__2_1205_, v_n_1211_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object* v_motive_1213_, lean_object* v_fuel_1214_, lean_object* v_h__1_1215_, lean_object* v_h__2_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(v_motive_1213_, v_fuel_1214_, v_h__1_1215_, v_h__2_1216_);
lean_dec(v_fuel_1214_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter___redArg(lean_object* v_m_u2081_1218_, lean_object* v_m_u2082_1219_, lean_object* v_h__1_1220_, lean_object* v_h__2_1221_, lean_object* v_h__3_1222_){
_start:
{
if (lean_obj_tag(v_m_u2082_1219_) == 0)
{
lean_object* v___x_1223_; 
lean_dec(v_h__3_1222_);
lean_dec(v_h__2_1221_);
v___x_1223_ = lean_apply_1(v_h__1_1220_, v_m_u2081_1218_);
return v___x_1223_;
}
else
{
lean_dec(v_h__1_1220_);
if (lean_obj_tag(v_m_u2081_1218_) == 0)
{
lean_object* v___x_1224_; 
lean_dec(v_h__3_1222_);
v___x_1224_ = lean_apply_2(v_h__2_1221_, v_m_u2082_1219_, lean_box(0));
return v___x_1224_;
}
else
{
lean_object* v_p_1225_; lean_object* v_m_1226_; lean_object* v_p_1227_; lean_object* v_m_1228_; lean_object* v___x_1229_; 
lean_dec(v_h__2_1221_);
v_p_1225_ = lean_ctor_get(v_m_u2082_1219_, 0);
lean_inc_ref(v_p_1225_);
v_m_1226_ = lean_ctor_get(v_m_u2082_1219_, 1);
lean_inc(v_m_1226_);
lean_dec_ref_known(v_m_u2082_1219_, 2);
v_p_1227_ = lean_ctor_get(v_m_u2081_1218_, 0);
lean_inc_ref(v_p_1227_);
v_m_1228_ = lean_ctor_get(v_m_u2081_1218_, 1);
lean_inc(v_m_1228_);
lean_dec_ref_known(v_m_u2081_1218_, 2);
v___x_1229_ = lean_apply_4(v_h__3_1222_, v_p_1227_, v_m_1228_, v_p_1225_, v_m_1226_);
return v___x_1229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter(lean_object* v_motive_1230_, lean_object* v_m_u2081_1231_, lean_object* v_m_u2082_1232_, lean_object* v_h__1_1233_, lean_object* v_h__2_1234_, lean_object* v_h__3_1235_){
_start:
{
if (lean_obj_tag(v_m_u2082_1232_) == 0)
{
lean_object* v___x_1236_; 
lean_dec(v_h__3_1235_);
lean_dec(v_h__2_1234_);
v___x_1236_ = lean_apply_1(v_h__1_1233_, v_m_u2081_1231_);
return v___x_1236_;
}
else
{
lean_dec(v_h__1_1233_);
if (lean_obj_tag(v_m_u2081_1231_) == 0)
{
lean_object* v___x_1237_; 
lean_dec(v_h__3_1235_);
v___x_1237_ = lean_apply_2(v_h__2_1234_, v_m_u2082_1232_, lean_box(0));
return v___x_1237_;
}
else
{
lean_object* v_p_1238_; lean_object* v_m_1239_; lean_object* v_p_1240_; lean_object* v_m_1241_; lean_object* v___x_1242_; 
lean_dec(v_h__2_1234_);
v_p_1238_ = lean_ctor_get(v_m_u2082_1232_, 0);
lean_inc_ref(v_p_1238_);
v_m_1239_ = lean_ctor_get(v_m_u2082_1232_, 1);
lean_inc(v_m_1239_);
lean_dec_ref_known(v_m_u2082_1232_, 2);
v_p_1240_ = lean_ctor_get(v_m_u2081_1231_, 0);
lean_inc_ref(v_p_1240_);
v_m_1241_ = lean_ctor_get(v_m_u2081_1231_, 1);
lean_inc(v_m_1241_);
lean_dec_ref_known(v_m_u2081_1231_, 2);
v___x_1242_ = lean_apply_4(v_h__3_1235_, v_p_1240_, v_m_1241_, v_p_1238_, v_m_1239_);
return v___x_1242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul__nc(lean_object* v_m_u2081_1243_, lean_object* v_m_u2082_1244_){
_start:
{
if (lean_obj_tag(v_m_u2081_1243_) == 0)
{
return v_m_u2082_1244_;
}
else
{
lean_object* v_m_1245_; 
v_m_1245_ = lean_ctor_get(v_m_u2081_1243_, 1);
if (lean_obj_tag(v_m_1245_) == 0)
{
lean_object* v_p_1246_; lean_object* v___x_1247_; 
v_p_1246_ = lean_ctor_get(v_m_u2081_1243_, 0);
lean_inc_ref(v_p_1246_);
lean_dec_ref_known(v_m_u2081_1243_, 2);
v___x_1247_ = l_Lean_Grind_CommRing_Mon_mulPow__nc(v_p_1246_, v_m_u2082_1244_);
return v___x_1247_;
}
else
{
lean_object* v_p_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1256_; 
lean_inc(v_m_1245_);
v_p_1248_ = lean_ctor_get(v_m_u2081_1243_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_m_u2081_1243_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v_m_u2081_1243_, 1);
lean_dec(v_unused_1257_);
v___x_1250_ = v_m_u2081_1243_;
v_isShared_1251_ = v_isSharedCheck_1256_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_p_1248_);
lean_dec(v_m_u2081_1243_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1256_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_1245_, v_m_u2082_1244_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v___x_1252_);
v___x_1254_ = v___x_1250_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_p_1248_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_unsigned_to_nat(0u);
return v___x_1259_;
}
else
{
lean_object* v_p_1260_; lean_object* v_m_1261_; lean_object* v_k_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_p_1260_ = lean_ctor_get(v_x_1258_, 0);
v_m_1261_ = lean_ctor_get(v_x_1258_, 1);
v_k_1262_ = lean_ctor_get(v_p_1260_, 1);
v___x_1263_ = l_Lean_Grind_CommRing_Mon_degree(v_m_1261_);
v___x_1264_ = lean_nat_add(v_k_1262_, v___x_1263_);
lean_dec(v___x_1263_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree___boxed(lean_object* v_x_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Grind_CommRing_Mon_degree(v_x_1265_);
lean_dec(v_x_1265_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object* v_x_1267_, lean_object* v_h__1_1268_, lean_object* v_h__2_1269_){
_start:
{
if (lean_obj_tag(v_x_1267_) == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v_h__2_1269_);
v___x_1270_ = lean_box(0);
v___x_1271_ = lean_apply_1(v_h__1_1268_, v___x_1270_);
return v___x_1271_;
}
else
{
lean_object* v_p_1272_; lean_object* v_m_1273_; lean_object* v___x_1274_; 
lean_dec(v_h__1_1268_);
v_p_1272_ = lean_ctor_get(v_x_1267_, 0);
lean_inc_ref(v_p_1272_);
v_m_1273_ = lean_ctor_get(v_x_1267_, 1);
lean_inc(v_m_1273_);
lean_dec_ref_known(v_x_1267_, 2);
v___x_1274_ = lean_apply_2(v_h__2_1269_, v_p_1272_, v_m_1273_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object* v_motive_1275_, lean_object* v_x_1276_, lean_object* v_h__1_1277_, lean_object* v_h__2_1278_){
_start:
{
if (lean_obj_tag(v_x_1276_) == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec(v_h__2_1278_);
v___x_1279_ = lean_box(0);
v___x_1280_ = lean_apply_1(v_h__1_1277_, v___x_1279_);
return v___x_1280_;
}
else
{
lean_object* v_p_1281_; lean_object* v_m_1282_; lean_object* v___x_1283_; 
lean_dec(v_h__1_1277_);
v_p_1281_ = lean_ctor_get(v_x_1276_, 0);
lean_inc_ref(v_p_1281_);
v_m_1282_ = lean_ctor_get(v_x_1276_, 1);
lean_inc(v_m_1282_);
lean_dec_ref_known(v_x_1276_, 2);
v___x_1283_ = lean_apply_2(v_h__2_1278_, v_p_1281_, v_m_1282_);
return v___x_1283_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Var_revlex(lean_object* v_x_1284_, lean_object* v_y_1285_){
_start:
{
uint8_t v___x_1286_; 
v___x_1286_ = l_Nat_blt(v_x_1284_, v_y_1285_);
if (v___x_1286_ == 0)
{
uint8_t v___x_1287_; 
v___x_1287_ = l_Nat_blt(v_y_1285_, v_x_1284_);
if (v___x_1287_ == 0)
{
uint8_t v___x_1288_; 
v___x_1288_ = 1;
return v___x_1288_;
}
else
{
uint8_t v___x_1289_; 
v___x_1289_ = 0;
return v___x_1289_;
}
}
else
{
uint8_t v___x_1290_; 
v___x_1290_ = 2;
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_revlex___boxed(lean_object* v_x_1291_, lean_object* v_y_1292_){
_start:
{
uint8_t v_res_1293_; lean_object* v_r_1294_; 
v_res_1293_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1291_, v_y_1292_);
lean_dec(v_y_1292_);
lean_dec(v_x_1291_);
v_r_1294_ = lean_box(v_res_1293_);
return v_r_1294_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_powerRevlex(lean_object* v_k_u2081_1295_, lean_object* v_k_u2082_1296_){
_start:
{
uint8_t v___x_1297_; 
v___x_1297_ = l_Nat_blt(v_k_u2081_1295_, v_k_u2082_1296_);
if (v___x_1297_ == 0)
{
uint8_t v___x_1298_; 
v___x_1298_ = l_Nat_blt(v_k_u2082_1296_, v_k_u2081_1295_);
if (v___x_1298_ == 0)
{
uint8_t v___x_1299_; 
v___x_1299_ = 1;
return v___x_1299_;
}
else
{
uint8_t v___x_1300_; 
v___x_1300_ = 0;
return v___x_1300_;
}
}
else
{
uint8_t v___x_1301_; 
v___x_1301_ = 2;
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_powerRevlex___boxed(lean_object* v_k_u2081_1302_, lean_object* v_k_u2082_1303_){
_start:
{
uint8_t v_res_1304_; lean_object* v_r_1305_; 
v_res_1304_ = l_Lean_Grind_CommRing_powerRevlex(v_k_u2081_1302_, v_k_u2082_1303_);
lean_dec(v_k_u2082_1303_);
lean_dec(v_k_u2081_1302_);
v_r_1305_ = lean_box(v_res_1304_);
return v_r_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(uint8_t v_c_1306_, lean_object* v_h__1_1307_, lean_object* v_h__2_1308_){
_start:
{
if (v_c_1306_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec(v_h__1_1307_);
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_apply_1(v_h__2_1308_, v___x_1309_);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_dec(v_h__2_1308_);
v___x_1311_ = lean_box(0);
v___x_1312_ = lean_apply_1(v_h__1_1307_, v___x_1311_);
return v___x_1312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg___boxed(lean_object* v_c_1313_, lean_object* v_h__1_1314_, lean_object* v_h__2_1315_){
_start:
{
uint8_t v_c_24__boxed_1316_; lean_object* v_res_1317_; 
v_c_24__boxed_1316_ = lean_unbox(v_c_1313_);
v_res_1317_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(v_c_24__boxed_1316_, v_h__1_1314_, v_h__2_1315_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(lean_object* v_motive_1318_, uint8_t v_c_1319_, lean_object* v_h__1_1320_, lean_object* v_h__2_1321_){
_start:
{
if (v_c_1319_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec(v_h__1_1320_);
v___x_1322_ = lean_box(0);
v___x_1323_ = lean_apply_1(v_h__2_1321_, v___x_1322_);
return v___x_1323_;
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec(v_h__2_1321_);
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_apply_1(v_h__1_1320_, v___x_1324_);
return v___x_1325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___boxed(lean_object* v_motive_1326_, lean_object* v_c_1327_, lean_object* v_h__1_1328_, lean_object* v_h__2_1329_){
_start:
{
uint8_t v_c_35__boxed_1330_; lean_object* v_res_1331_; 
v_c_35__boxed_1330_ = lean_unbox(v_c_1327_);
v_res_1331_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(v_motive_1326_, v_c_35__boxed_1330_, v_h__1_1328_, v_h__2_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_revlex(lean_object* v_p_u2081_1332_, lean_object* v_p_u2082_1333_){
_start:
{
lean_object* v_x_1334_; lean_object* v_k_1335_; lean_object* v_x_1336_; lean_object* v_k_1337_; uint8_t v___x_1338_; 
v_x_1334_ = lean_ctor_get(v_p_u2081_1332_, 0);
v_k_1335_ = lean_ctor_get(v_p_u2081_1332_, 1);
v_x_1336_ = lean_ctor_get(v_p_u2082_1333_, 0);
v_k_1337_ = lean_ctor_get(v_p_u2082_1333_, 1);
v___x_1338_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1334_, v_x_1336_);
if (v___x_1338_ == 1)
{
uint8_t v___x_1339_; 
v___x_1339_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1335_, v_k_1337_);
return v___x_1339_;
}
else
{
return v___x_1338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_revlex___boxed(lean_object* v_p_u2081_1340_, lean_object* v_p_u2082_1341_){
_start:
{
uint8_t v_res_1342_; lean_object* v_r_1343_; 
v_res_1342_ = l_Lean_Grind_CommRing_Power_revlex(v_p_u2081_1340_, v_p_u2082_1341_);
lean_dec_ref(v_p_u2082_1341_);
lean_dec_ref(v_p_u2081_1340_);
v_r_1343_ = lean_box(v_res_1342_);
return v_r_1343_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexWF(lean_object* v_m_u2081_1344_, lean_object* v_m_u2082_1345_){
_start:
{
if (lean_obj_tag(v_m_u2081_1344_) == 0)
{
if (lean_obj_tag(v_m_u2082_1345_) == 0)
{
uint8_t v___x_1346_; 
v___x_1346_ = 1;
return v___x_1346_;
}
else
{
uint8_t v___x_1347_; 
v___x_1347_ = 2;
return v___x_1347_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1345_) == 0)
{
uint8_t v___x_1348_; 
v___x_1348_ = 0;
return v___x_1348_;
}
else
{
lean_object* v_p_1349_; lean_object* v_p_1350_; lean_object* v_m_1351_; lean_object* v_m_1352_; lean_object* v_x_1353_; lean_object* v_k_1354_; lean_object* v_x_1355_; lean_object* v_k_1356_; uint8_t v___x_1357_; 
v_p_1349_ = lean_ctor_get(v_m_u2081_1344_, 0);
v_p_1350_ = lean_ctor_get(v_m_u2082_1345_, 0);
v_m_1351_ = lean_ctor_get(v_m_u2081_1344_, 1);
v_m_1352_ = lean_ctor_get(v_m_u2082_1345_, 1);
v_x_1353_ = lean_ctor_get(v_p_1349_, 0);
v_k_1354_ = lean_ctor_get(v_p_1349_, 1);
v_x_1355_ = lean_ctor_get(v_p_1350_, 0);
v_k_1356_ = lean_ctor_get(v_p_1350_, 1);
v___x_1357_ = lean_nat_dec_eq(v_x_1353_, v_x_1355_);
if (v___x_1357_ == 0)
{
uint8_t v___x_1358_; 
v___x_1358_ = l_Nat_blt(v_x_1353_, v_x_1355_);
if (v___x_1358_ == 0)
{
uint8_t v___x_1359_; 
v___x_1359_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1344_, v_m_1352_);
if (v___x_1359_ == 1)
{
uint8_t v___x_1360_; 
v___x_1360_ = 2;
return v___x_1360_;
}
else
{
return v___x_1359_;
}
}
else
{
uint8_t v___x_1361_; 
v___x_1361_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1351_, v_m_u2082_1345_);
if (v___x_1361_ == 1)
{
uint8_t v___x_1362_; 
v___x_1362_ = 0;
return v___x_1362_;
}
else
{
return v___x_1361_;
}
}
}
else
{
uint8_t v___x_1363_; 
v___x_1363_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1351_, v_m_1352_);
if (v___x_1363_ == 1)
{
uint8_t v___x_1364_; 
v___x_1364_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1354_, v_k_1356_);
return v___x_1364_;
}
else
{
return v___x_1363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexWF___boxed(lean_object* v_m_u2081_1365_, lean_object* v_m_u2082_1366_){
_start:
{
uint8_t v_res_1367_; lean_object* v_r_1368_; 
v_res_1367_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1365_, v_m_u2082_1366_);
lean_dec(v_m_u2082_1366_);
lean_dec(v_m_u2081_1365_);
v_r_1368_ = lean_box(v_res_1367_);
return v_r_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(lean_object* v_m_u2081_1369_, lean_object* v_m_u2082_1370_, lean_object* v_h__1_1371_, lean_object* v_h__2_1372_, lean_object* v_h__3_1373_, lean_object* v_h__4_1374_){
_start:
{
if (lean_obj_tag(v_m_u2081_1369_) == 0)
{
lean_dec(v_h__4_1374_);
lean_dec(v_h__3_1373_);
if (lean_obj_tag(v_m_u2082_1370_) == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec(v_h__2_1372_);
v___x_1375_ = lean_box(0);
v___x_1376_ = lean_apply_1(v_h__1_1371_, v___x_1375_);
return v___x_1376_;
}
else
{
lean_object* v_p_1377_; lean_object* v_m_1378_; lean_object* v___x_1379_; 
lean_dec(v_h__1_1371_);
v_p_1377_ = lean_ctor_get(v_m_u2082_1370_, 0);
lean_inc_ref(v_p_1377_);
v_m_1378_ = lean_ctor_get(v_m_u2082_1370_, 1);
lean_inc(v_m_1378_);
lean_dec_ref_known(v_m_u2082_1370_, 2);
v___x_1379_ = lean_apply_2(v_h__2_1372_, v_p_1377_, v_m_1378_);
return v___x_1379_;
}
}
else
{
lean_dec(v_h__2_1372_);
lean_dec(v_h__1_1371_);
if (lean_obj_tag(v_m_u2082_1370_) == 0)
{
lean_object* v_p_1380_; lean_object* v_m_1381_; lean_object* v___x_1382_; 
lean_dec(v_h__4_1374_);
v_p_1380_ = lean_ctor_get(v_m_u2081_1369_, 0);
lean_inc_ref(v_p_1380_);
v_m_1381_ = lean_ctor_get(v_m_u2081_1369_, 1);
lean_inc(v_m_1381_);
lean_dec_ref_known(v_m_u2081_1369_, 2);
v___x_1382_ = lean_apply_2(v_h__3_1373_, v_p_1380_, v_m_1381_);
return v___x_1382_;
}
else
{
lean_object* v_p_1383_; lean_object* v_m_1384_; lean_object* v_p_1385_; lean_object* v_m_1386_; lean_object* v___x_1387_; 
lean_dec(v_h__3_1373_);
v_p_1383_ = lean_ctor_get(v_m_u2081_1369_, 0);
lean_inc_ref(v_p_1383_);
v_m_1384_ = lean_ctor_get(v_m_u2081_1369_, 1);
lean_inc(v_m_1384_);
lean_dec_ref_known(v_m_u2081_1369_, 2);
v_p_1385_ = lean_ctor_get(v_m_u2082_1370_, 0);
lean_inc_ref(v_p_1385_);
v_m_1386_ = lean_ctor_get(v_m_u2082_1370_, 1);
lean_inc(v_m_1386_);
lean_dec_ref_known(v_m_u2082_1370_, 2);
v___x_1387_ = lean_apply_4(v_h__4_1374_, v_p_1383_, v_m_1384_, v_p_1385_, v_m_1386_);
return v___x_1387_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter(lean_object* v_motive_1388_, lean_object* v_m_u2081_1389_, lean_object* v_m_u2082_1390_, lean_object* v_h__1_1391_, lean_object* v_h__2_1392_, lean_object* v_h__3_1393_, lean_object* v_h__4_1394_){
_start:
{
if (lean_obj_tag(v_m_u2081_1389_) == 0)
{
lean_dec(v_h__4_1394_);
lean_dec(v_h__3_1393_);
if (lean_obj_tag(v_m_u2082_1390_) == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec(v_h__2_1392_);
v___x_1395_ = lean_box(0);
v___x_1396_ = lean_apply_1(v_h__1_1391_, v___x_1395_);
return v___x_1396_;
}
else
{
lean_object* v_p_1397_; lean_object* v_m_1398_; lean_object* v___x_1399_; 
lean_dec(v_h__1_1391_);
v_p_1397_ = lean_ctor_get(v_m_u2082_1390_, 0);
lean_inc_ref(v_p_1397_);
v_m_1398_ = lean_ctor_get(v_m_u2082_1390_, 1);
lean_inc(v_m_1398_);
lean_dec_ref_known(v_m_u2082_1390_, 2);
v___x_1399_ = lean_apply_2(v_h__2_1392_, v_p_1397_, v_m_1398_);
return v___x_1399_;
}
}
else
{
lean_dec(v_h__2_1392_);
lean_dec(v_h__1_1391_);
if (lean_obj_tag(v_m_u2082_1390_) == 0)
{
lean_object* v_p_1400_; lean_object* v_m_1401_; lean_object* v___x_1402_; 
lean_dec(v_h__4_1394_);
v_p_1400_ = lean_ctor_get(v_m_u2081_1389_, 0);
lean_inc_ref(v_p_1400_);
v_m_1401_ = lean_ctor_get(v_m_u2081_1389_, 1);
lean_inc(v_m_1401_);
lean_dec_ref_known(v_m_u2081_1389_, 2);
v___x_1402_ = lean_apply_2(v_h__3_1393_, v_p_1400_, v_m_1401_);
return v___x_1402_;
}
else
{
lean_object* v_p_1403_; lean_object* v_m_1404_; lean_object* v_p_1405_; lean_object* v_m_1406_; lean_object* v___x_1407_; 
lean_dec(v_h__3_1393_);
v_p_1403_ = lean_ctor_get(v_m_u2081_1389_, 0);
lean_inc_ref(v_p_1403_);
v_m_1404_ = lean_ctor_get(v_m_u2081_1389_, 1);
lean_inc(v_m_1404_);
lean_dec_ref_known(v_m_u2081_1389_, 2);
v_p_1405_ = lean_ctor_get(v_m_u2082_1390_, 0);
lean_inc_ref(v_p_1405_);
v_m_1406_ = lean_ctor_get(v_m_u2082_1390_, 1);
lean_inc(v_m_1406_);
lean_dec_ref_known(v_m_u2082_1390_, 2);
v___x_1407_ = lean_apply_4(v_h__4_1394_, v_p_1403_, v_m_1404_, v_p_1405_, v_m_1406_);
return v___x_1407_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexFuel(lean_object* v_fuel_1408_, lean_object* v_m_u2081_1409_, lean_object* v_m_u2082_1410_){
_start:
{
lean_object* v_zero_1411_; uint8_t v_isZero_1412_; 
v_zero_1411_ = lean_unsigned_to_nat(0u);
v_isZero_1412_ = lean_nat_dec_eq(v_fuel_1408_, v_zero_1411_);
if (v_isZero_1412_ == 1)
{
uint8_t v___x_1413_; 
v___x_1413_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1409_, v_m_u2082_1410_);
return v___x_1413_;
}
else
{
if (lean_obj_tag(v_m_u2081_1409_) == 0)
{
if (lean_obj_tag(v_m_u2082_1410_) == 0)
{
uint8_t v___x_1414_; 
v___x_1414_ = 1;
return v___x_1414_;
}
else
{
uint8_t v___x_1415_; 
v___x_1415_ = 2;
return v___x_1415_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1410_) == 0)
{
uint8_t v___x_1416_; 
v___x_1416_ = 0;
return v___x_1416_;
}
else
{
lean_object* v_p_1417_; lean_object* v_p_1418_; lean_object* v_m_1419_; lean_object* v_m_1420_; lean_object* v_x_1421_; lean_object* v_k_1422_; lean_object* v_x_1423_; lean_object* v_k_1424_; lean_object* v_one_1425_; lean_object* v_n_1426_; uint8_t v___x_1427_; 
v_p_1417_ = lean_ctor_get(v_m_u2081_1409_, 0);
v_p_1418_ = lean_ctor_get(v_m_u2082_1410_, 0);
v_m_1419_ = lean_ctor_get(v_m_u2081_1409_, 1);
v_m_1420_ = lean_ctor_get(v_m_u2082_1410_, 1);
v_x_1421_ = lean_ctor_get(v_p_1417_, 0);
v_k_1422_ = lean_ctor_get(v_p_1417_, 1);
v_x_1423_ = lean_ctor_get(v_p_1418_, 0);
v_k_1424_ = lean_ctor_get(v_p_1418_, 1);
v_one_1425_ = lean_unsigned_to_nat(1u);
v_n_1426_ = lean_nat_sub(v_fuel_1408_, v_one_1425_);
v___x_1427_ = lean_nat_dec_eq(v_x_1421_, v_x_1423_);
if (v___x_1427_ == 0)
{
uint8_t v___x_1428_; 
v___x_1428_ = l_Nat_blt(v_x_1421_, v_x_1423_);
if (v___x_1428_ == 0)
{
uint8_t v___x_1429_; 
v___x_1429_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1426_, v_m_u2081_1409_, v_m_1420_);
lean_dec(v_n_1426_);
if (v___x_1429_ == 1)
{
uint8_t v___x_1430_; 
v___x_1430_ = 2;
return v___x_1430_;
}
else
{
return v___x_1429_;
}
}
else
{
uint8_t v___x_1431_; 
v___x_1431_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1426_, v_m_1419_, v_m_u2082_1410_);
lean_dec(v_n_1426_);
if (v___x_1431_ == 1)
{
uint8_t v___x_1432_; 
v___x_1432_ = 0;
return v___x_1432_;
}
else
{
return v___x_1431_;
}
}
}
else
{
uint8_t v___x_1433_; 
v___x_1433_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1426_, v_m_1419_, v_m_1420_);
lean_dec(v_n_1426_);
if (v___x_1433_ == 1)
{
uint8_t v___x_1434_; 
v___x_1434_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1422_, v_k_1424_);
return v___x_1434_;
}
else
{
return v___x_1433_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexFuel___boxed(lean_object* v_fuel_1435_, lean_object* v_m_u2081_1436_, lean_object* v_m_u2082_1437_){
_start:
{
uint8_t v_res_1438_; lean_object* v_r_1439_; 
v_res_1438_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_fuel_1435_, v_m_u2081_1436_, v_m_u2082_1437_);
lean_dec(v_m_u2082_1437_);
lean_dec(v_m_u2081_1436_);
lean_dec(v_fuel_1435_);
v_r_1439_ = lean_box(v_res_1438_);
return v_r_1439_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlex(lean_object* v_m_u2081_1440_, lean_object* v_m_u2082_1441_){
_start:
{
lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1442_ = lean_unsigned_to_nat(1000000u);
v___x_1443_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v___x_1442_, v_m_u2081_1440_, v_m_u2082_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlex___boxed(lean_object* v_m_u2081_1444_, lean_object* v_m_u2082_1445_){
_start:
{
uint8_t v_res_1446_; lean_object* v_r_1447_; 
v_res_1446_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1444_, v_m_u2082_1445_);
lean_dec(v_m_u2082_1445_);
lean_dec(v_m_u2081_1444_);
v_r_1447_ = lean_box(v_res_1446_);
return v_r_1447_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object* v_m_u2081_1448_, lean_object* v_m_u2082_1449_){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1450_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2081_1448_);
v___x_1451_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2082_1449_);
v___x_1452_ = lean_nat_dec_lt(v___x_1450_, v___x_1451_);
if (v___x_1452_ == 0)
{
uint8_t v___x_1453_; 
v___x_1453_ = lean_nat_dec_eq(v___x_1450_, v___x_1451_);
lean_dec(v___x_1451_);
lean_dec(v___x_1450_);
if (v___x_1453_ == 0)
{
uint8_t v___x_1454_; 
v___x_1454_ = 2;
return v___x_1454_;
}
else
{
uint8_t v___x_1455_; 
v___x_1455_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1448_, v_m_u2082_1449_);
return v___x_1455_;
}
}
else
{
uint8_t v___x_1456_; 
lean_dec(v___x_1451_);
lean_dec(v___x_1450_);
v___x_1456_ = 0;
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_grevlex___boxed(lean_object* v_m_u2081_1457_, lean_object* v_m_u2082_1458_){
_start:
{
uint8_t v_res_1459_; lean_object* v_r_1460_; 
v_res_1459_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_u2081_1457_, v_m_u2082_1458_);
lean_dec(v_m_u2082_1458_);
lean_dec(v_m_u2081_1457_);
v_r_1460_ = lean_box(v_res_1459_);
return v_r_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx(lean_object* v_x_1461_){
_start:
{
if (lean_obj_tag(v_x_1461_) == 0)
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_unsigned_to_nat(0u);
return v___x_1462_;
}
else
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_unsigned_to_nat(1u);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___boxed(lean_object* v_x_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_Grind_CommRing_Poly_ctorIdx(v_x_1464_);
lean_dec_ref(v_x_1464_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___redArg(lean_object* v_t_1466_, lean_object* v_k_1467_){
_start:
{
if (lean_obj_tag(v_t_1466_) == 0)
{
lean_object* v_k_1468_; lean_object* v___x_1469_; 
v_k_1468_ = lean_ctor_get(v_t_1466_, 0);
lean_inc(v_k_1468_);
lean_dec_ref_known(v_t_1466_, 1);
v___x_1469_ = lean_apply_1(v_k_1467_, v_k_1468_);
return v___x_1469_;
}
else
{
lean_object* v_k_1470_; lean_object* v_v_1471_; lean_object* v_p_1472_; lean_object* v___x_1473_; 
v_k_1470_ = lean_ctor_get(v_t_1466_, 0);
lean_inc(v_k_1470_);
v_v_1471_ = lean_ctor_get(v_t_1466_, 1);
lean_inc(v_v_1471_);
v_p_1472_ = lean_ctor_get(v_t_1466_, 2);
lean_inc_ref(v_p_1472_);
lean_dec_ref_known(v_t_1466_, 3);
v___x_1473_ = lean_apply_3(v_k_1467_, v_k_1470_, v_v_1471_, v_p_1472_);
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim(lean_object* v_motive_1474_, lean_object* v_ctorIdx_1475_, lean_object* v_t_1476_, lean_object* v_h_1477_, lean_object* v_k_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1476_, v_k_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___boxed(lean_object* v_motive_1480_, lean_object* v_ctorIdx_1481_, lean_object* v_t_1482_, lean_object* v_h_1483_, lean_object* v_k_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_Grind_CommRing_Poly_ctorElim(v_motive_1480_, v_ctorIdx_1481_, v_t_1482_, v_h_1483_, v_k_1484_);
lean_dec(v_ctorIdx_1481_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim___redArg(lean_object* v_t_1486_, lean_object* v_num_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1486_, v_num_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim(lean_object* v_motive_1489_, lean_object* v_t_1490_, lean_object* v_h_1491_, lean_object* v_num_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1490_, v_num_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim___redArg(lean_object* v_t_1494_, lean_object* v_add_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1494_, v_add_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim(lean_object* v_motive_1497_, lean_object* v_t_1498_, lean_object* v_h_1499_, lean_object* v_add_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1498_, v_add_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPoly_beq(lean_object* v_x_1502_, lean_object* v_x_1503_){
_start:
{
if (lean_obj_tag(v_x_1502_) == 0)
{
if (lean_obj_tag(v_x_1503_) == 0)
{
lean_object* v_k_1504_; lean_object* v_k_1505_; uint8_t v___x_1506_; 
v_k_1504_ = lean_ctor_get(v_x_1502_, 0);
v_k_1505_ = lean_ctor_get(v_x_1503_, 0);
v___x_1506_ = lean_int_dec_eq(v_k_1504_, v_k_1505_);
return v___x_1506_;
}
else
{
uint8_t v___x_1507_; 
v___x_1507_ = 0;
return v___x_1507_;
}
}
else
{
if (lean_obj_tag(v_x_1503_) == 1)
{
lean_object* v_k_1508_; lean_object* v_v_1509_; lean_object* v_p_1510_; lean_object* v_k_1511_; lean_object* v_v_1512_; lean_object* v_p_1513_; uint8_t v___x_1514_; 
v_k_1508_ = lean_ctor_get(v_x_1502_, 0);
v_v_1509_ = lean_ctor_get(v_x_1502_, 1);
v_p_1510_ = lean_ctor_get(v_x_1502_, 2);
v_k_1511_ = lean_ctor_get(v_x_1503_, 0);
v_v_1512_ = lean_ctor_get(v_x_1503_, 1);
v_p_1513_ = lean_ctor_get(v_x_1503_, 2);
v___x_1514_ = lean_int_dec_eq(v_k_1508_, v_k_1511_);
if (v___x_1514_ == 0)
{
return v___x_1514_;
}
else
{
uint8_t v___x_1515_; 
v___x_1515_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_v_1509_, v_v_1512_);
if (v___x_1515_ == 0)
{
return v___x_1515_;
}
else
{
v_x_1502_ = v_p_1510_;
v_x_1503_ = v_p_1513_;
goto _start;
}
}
}
else
{
uint8_t v___x_1517_; 
v___x_1517_ = 0;
return v___x_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPoly_beq___boxed(lean_object* v_x_1518_, lean_object* v_x_1519_){
_start:
{
uint8_t v_res_1520_; lean_object* v_r_1521_; 
v_res_1520_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_x_1518_, v_x_1519_);
lean_dec_ref(v_x_1519_);
lean_dec_ref(v_x_1518_);
v_r_1521_ = lean_box(v_res_1520_);
return v_r_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_1524_, lean_object* v_x_1525_, lean_object* v_h__1_1526_, lean_object* v_h__2_1527_, lean_object* v_h__3_1528_){
_start:
{
if (lean_obj_tag(v_x_1524_) == 0)
{
lean_dec(v_h__2_1527_);
if (lean_obj_tag(v_x_1525_) == 0)
{
lean_object* v_k_1529_; lean_object* v_k_1530_; lean_object* v___x_1531_; 
lean_dec(v_h__3_1528_);
v_k_1529_ = lean_ctor_get(v_x_1524_, 0);
lean_inc(v_k_1529_);
lean_dec_ref_known(v_x_1524_, 1);
v_k_1530_ = lean_ctor_get(v_x_1525_, 0);
lean_inc(v_k_1530_);
lean_dec_ref_known(v_x_1525_, 1);
v___x_1531_ = lean_apply_2(v_h__1_1526_, v_k_1529_, v_k_1530_);
return v___x_1531_;
}
else
{
lean_object* v___x_1532_; 
lean_dec(v_h__1_1526_);
v___x_1532_ = lean_apply_4(v_h__3_1528_, v_x_1524_, v_x_1525_, lean_box(0), lean_box(0));
return v___x_1532_;
}
}
else
{
lean_dec(v_h__1_1526_);
if (lean_obj_tag(v_x_1525_) == 1)
{
lean_object* v_k_1533_; lean_object* v_v_1534_; lean_object* v_p_1535_; lean_object* v_k_1536_; lean_object* v_v_1537_; lean_object* v_p_1538_; lean_object* v___x_1539_; 
lean_dec(v_h__3_1528_);
v_k_1533_ = lean_ctor_get(v_x_1524_, 0);
lean_inc(v_k_1533_);
v_v_1534_ = lean_ctor_get(v_x_1524_, 1);
lean_inc(v_v_1534_);
v_p_1535_ = lean_ctor_get(v_x_1524_, 2);
lean_inc_ref(v_p_1535_);
lean_dec_ref_known(v_x_1524_, 3);
v_k_1536_ = lean_ctor_get(v_x_1525_, 0);
lean_inc(v_k_1536_);
v_v_1537_ = lean_ctor_get(v_x_1525_, 1);
lean_inc(v_v_1537_);
v_p_1538_ = lean_ctor_get(v_x_1525_, 2);
lean_inc_ref(v_p_1538_);
lean_dec_ref_known(v_x_1525_, 3);
v___x_1539_ = lean_apply_6(v_h__2_1527_, v_k_1533_, v_v_1534_, v_p_1535_, v_k_1536_, v_v_1537_, v_p_1538_);
return v___x_1539_;
}
else
{
lean_object* v___x_1540_; 
lean_dec(v_h__2_1527_);
v___x_1540_ = lean_apply_4(v_h__3_1528_, v_x_1524_, v_x_1525_, lean_box(0), lean_box(0));
return v___x_1540_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_1541_, lean_object* v_x_1542_, lean_object* v_x_1543_, lean_object* v_h__1_1544_, lean_object* v_h__2_1545_, lean_object* v_h__3_1546_){
_start:
{
if (lean_obj_tag(v_x_1542_) == 0)
{
lean_dec(v_h__2_1545_);
if (lean_obj_tag(v_x_1543_) == 0)
{
lean_object* v_k_1547_; lean_object* v_k_1548_; lean_object* v___x_1549_; 
lean_dec(v_h__3_1546_);
v_k_1547_ = lean_ctor_get(v_x_1542_, 0);
lean_inc(v_k_1547_);
lean_dec_ref_known(v_x_1542_, 1);
v_k_1548_ = lean_ctor_get(v_x_1543_, 0);
lean_inc(v_k_1548_);
lean_dec_ref_known(v_x_1543_, 1);
v___x_1549_ = lean_apply_2(v_h__1_1544_, v_k_1547_, v_k_1548_);
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; 
lean_dec(v_h__1_1544_);
v___x_1550_ = lean_apply_4(v_h__3_1546_, v_x_1542_, v_x_1543_, lean_box(0), lean_box(0));
return v___x_1550_;
}
}
else
{
lean_dec(v_h__1_1544_);
if (lean_obj_tag(v_x_1543_) == 1)
{
lean_object* v_k_1551_; lean_object* v_v_1552_; lean_object* v_p_1553_; lean_object* v_k_1554_; lean_object* v_v_1555_; lean_object* v_p_1556_; lean_object* v___x_1557_; 
lean_dec(v_h__3_1546_);
v_k_1551_ = lean_ctor_get(v_x_1542_, 0);
lean_inc(v_k_1551_);
v_v_1552_ = lean_ctor_get(v_x_1542_, 1);
lean_inc(v_v_1552_);
v_p_1553_ = lean_ctor_get(v_x_1542_, 2);
lean_inc_ref(v_p_1553_);
lean_dec_ref_known(v_x_1542_, 3);
v_k_1554_ = lean_ctor_get(v_x_1543_, 0);
lean_inc(v_k_1554_);
v_v_1555_ = lean_ctor_get(v_x_1543_, 1);
lean_inc(v_v_1555_);
v_p_1556_ = lean_ctor_get(v_x_1543_, 2);
lean_inc_ref(v_p_1556_);
lean_dec_ref_known(v_x_1543_, 3);
v___x_1557_ = lean_apply_6(v_h__2_1545_, v_k_1551_, v_v_1552_, v_p_1553_, v_k_1554_, v_v_1555_, v_p_1556_);
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; 
lean_dec(v_h__2_1545_);
v___x_1558_ = lean_apply_4(v_h__3_1546_, v_x_1542_, v_x_1543_, lean_box(0), lean_box(0));
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr(lean_object* v_x_1571_, lean_object* v_prec_1572_){
_start:
{
lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; 
if (lean_obj_tag(v_x_1571_) == 0)
{
lean_object* v_k_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1605_; 
v_k_1582_ = lean_ctor_get(v_x_1571_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_x_1571_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1584_ = v_x_1571_;
v_isShared_1585_ = v_isSharedCheck_1605_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_k_1582_);
lean_dec(v_x_1571_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1605_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___y_1587_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = lean_unsigned_to_nat(1024u);
v___x_1602_ = lean_nat_dec_le(v___x_1601_, v_prec_1572_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1587_ = v___x_1603_;
goto v___jp_1586_;
}
else
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1587_ = v___x_1604_;
goto v___jp_1586_;
}
v___jp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1588_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__2));
v___x_1589_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1590_ = lean_int_dec_lt(v_k_1582_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1591_ = l_Int_repr(v_k_1582_);
lean_dec(v_k_1582_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 3);
lean_ctor_set(v___x_1584_, 0, v___x_1591_);
v___x_1593_ = v___x_1584_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
v___y_1574_ = v___x_1588_;
v___y_1575_ = v___y_1587_;
v___y_1576_ = v___x_1593_;
goto v___jp_1573_;
}
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1595_ = lean_unsigned_to_nat(1024u);
v___x_1596_ = l_Int_repr(v_k_1582_);
lean_dec(v_k_1582_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 3);
lean_ctor_set(v___x_1584_, 0, v___x_1596_);
v___x_1598_ = v___x_1584_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Repr_addAppParen(v___x_1598_, v___x_1595_);
v___y_1574_ = v___x_1588_;
v___y_1575_ = v___y_1587_;
v___y_1576_ = v___x_1599_;
goto v___jp_1573_;
}
}
}
}
}
else
{
lean_object* v_k_1606_; lean_object* v_v_1607_; lean_object* v_p_1608_; lean_object* v___x_1609_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1627_; uint8_t v___x_1637_; 
v_k_1606_ = lean_ctor_get(v_x_1571_, 0);
lean_inc(v_k_1606_);
v_v_1607_ = lean_ctor_get(v_x_1571_, 1);
lean_inc(v_v_1607_);
v_p_1608_ = lean_ctor_get(v_x_1571_, 2);
lean_inc_ref(v_p_1608_);
lean_dec_ref_known(v_x_1571_, 3);
v___x_1609_ = lean_unsigned_to_nat(1024u);
v___x_1637_ = lean_nat_dec_le(v___x_1609_, v_prec_1572_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1627_ = v___x_1638_;
goto v___jp_1626_;
}
else
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1627_ = v___x_1639_;
goto v___jp_1626_;
}
v___jp_1610_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_inc(v___y_1612_);
v___x_1615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___y_1612_);
lean_ctor_set(v___x_1615_, 1, v___y_1614_);
lean_inc_n(v___y_1613_, 2);
v___x_1616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
lean_ctor_set(v___x_1616_, 1, v___y_1613_);
v___x_1617_ = l_Lean_Grind_CommRing_instReprMon_repr(v_v_1607_, v___x_1609_);
v___x_1618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v___y_1613_);
v___x_1620_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_p_1608_, v___x_1609_);
v___x_1621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
lean_inc(v___y_1611_);
v___x_1622_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___y_1611_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = 0;
v___x_1624_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set_uint8(v___x_1624_, sizeof(void*)*1, v___x_1623_);
v___x_1625_ = l_Repr_addAppParen(v___x_1624_, v_prec_1572_);
return v___x_1625_;
}
v___jp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1628_ = lean_box(1);
v___x_1629_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__5));
v___x_1630_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1631_ = lean_int_dec_lt(v_k_1606_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = l_Int_repr(v_k_1606_);
lean_dec(v_k_1606_);
v___x_1633_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
v___y_1611_ = v___y_1627_;
v___y_1612_ = v___x_1629_;
v___y_1613_ = v___x_1628_;
v___y_1614_ = v___x_1633_;
goto v___jp_1610_;
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = l_Int_repr(v_k_1606_);
lean_dec(v_k_1606_);
v___x_1635_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
v___x_1636_ = l_Repr_addAppParen(v___x_1635_, v___x_1609_);
v___y_1611_ = v___y_1627_;
v___y_1612_ = v___x_1629_;
v___y_1613_ = v___x_1628_;
v___y_1614_ = v___x_1636_;
goto v___jp_1610_;
}
}
}
v___jp_1573_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_inc(v___y_1574_);
v___x_1577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___y_1574_);
lean_ctor_set(v___x_1577_, 1, v___y_1576_);
lean_inc(v___y_1575_);
v___x_1578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___y_1575_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = 0;
v___x_1580_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*1, v___x_1579_);
v___x_1581_ = l_Repr_addAppParen(v___x_1580_, v_prec_1572_);
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___boxed(lean_object* v_x_1640_, lean_object* v_prec_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_x_1640_, v_prec_1641_);
lean_dec(v_prec_1641_);
return v_res_1642_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default(void){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_1647_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly(void){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
return v___x_1648_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePoly_hash(lean_object* v_x_1649_){
_start:
{
if (lean_obj_tag(v_x_1649_) == 0)
{
lean_object* v_k_1650_; uint64_t v___x_1651_; lean_object* v_intZero_1652_; uint8_t v_isNeg_1653_; 
v_k_1650_ = lean_ctor_get(v_x_1649_, 0);
v___x_1651_ = 0ULL;
v_intZero_1652_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1653_ = lean_int_dec_lt(v_k_1650_, v_intZero_1652_);
if (v_isNeg_1653_ == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; uint64_t v___x_1657_; uint64_t v___x_1658_; 
v_a_1654_ = lean_nat_abs(v_k_1650_);
v___x_1655_ = lean_unsigned_to_nat(2u);
v___x_1656_ = lean_nat_mul(v___x_1655_, v_a_1654_);
lean_dec(v_a_1654_);
v___x_1657_ = lean_uint64_of_nat(v___x_1656_);
lean_dec(v___x_1656_);
v___x_1658_ = lean_uint64_mix_hash(v___x_1651_, v___x_1657_);
return v___x_1658_;
}
else
{
lean_object* v_abs_1659_; lean_object* v_one_1660_; lean_object* v_a_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint64_t v___x_1665_; uint64_t v___x_1666_; 
v_abs_1659_ = lean_nat_abs(v_k_1650_);
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
v___x_1666_ = lean_uint64_mix_hash(v___x_1651_, v___x_1665_);
return v___x_1666_;
}
}
else
{
lean_object* v_k_1667_; lean_object* v_v_1668_; lean_object* v_p_1669_; uint64_t v___x_1670_; uint64_t v___y_1672_; lean_object* v_intZero_1678_; uint8_t v_isNeg_1679_; 
v_k_1667_ = lean_ctor_get(v_x_1649_, 0);
v_v_1668_ = lean_ctor_get(v_x_1649_, 1);
v_p_1669_ = lean_ctor_get(v_x_1649_, 2);
v___x_1670_ = 1ULL;
v_intZero_1678_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1679_ = lean_int_dec_lt(v_k_1667_, v_intZero_1678_);
if (v_isNeg_1679_ == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint64_t v___x_1683_; 
v_a_1680_ = lean_nat_abs(v_k_1667_);
v___x_1681_ = lean_unsigned_to_nat(2u);
v___x_1682_ = lean_nat_mul(v___x_1681_, v_a_1680_);
lean_dec(v_a_1680_);
v___x_1683_ = lean_uint64_of_nat(v___x_1682_);
lean_dec(v___x_1682_);
v___y_1672_ = v___x_1683_;
goto v___jp_1671_;
}
else
{
lean_object* v_abs_1684_; lean_object* v_one_1685_; lean_object* v_a_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; uint64_t v___x_1690_; 
v_abs_1684_ = lean_nat_abs(v_k_1667_);
v_one_1685_ = lean_unsigned_to_nat(1u);
v_a_1686_ = lean_nat_sub(v_abs_1684_, v_one_1685_);
lean_dec(v_abs_1684_);
v___x_1687_ = lean_unsigned_to_nat(2u);
v___x_1688_ = lean_nat_mul(v___x_1687_, v_a_1686_);
lean_dec(v_a_1686_);
v___x_1689_ = lean_nat_add(v___x_1688_, v_one_1685_);
lean_dec(v___x_1688_);
v___x_1690_ = lean_uint64_of_nat(v___x_1689_);
lean_dec(v___x_1689_);
v___y_1672_ = v___x_1690_;
goto v___jp_1671_;
}
v___jp_1671_:
{
uint64_t v___x_1673_; uint64_t v___x_1674_; uint64_t v___x_1675_; uint64_t v___x_1676_; uint64_t v___x_1677_; 
v___x_1673_ = lean_uint64_mix_hash(v___x_1670_, v___y_1672_);
v___x_1674_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_v_1668_);
v___x_1675_ = lean_uint64_mix_hash(v___x_1673_, v___x_1674_);
v___x_1676_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_p_1669_);
v___x_1677_ = lean_uint64_mix_hash(v___x_1675_, v___x_1676_);
return v___x_1677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePoly_hash___boxed(lean_object* v_x_1691_){
_start:
{
uint64_t v_res_1692_; lean_object* v_r_1693_; 
v_res_1692_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_x_1691_);
lean_dec_ref(v_x_1691_);
v_r_1693_ = lean_box_uint64(v_res_1692_);
return v_r_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg(lean_object* v_inst_1696_, lean_object* v_ctx_1697_, lean_object* v_p_1698_){
_start:
{
lean_object* v_toSemiring_1699_; lean_object* v_intCast_1700_; lean_object* v_toAdd_1701_; lean_object* v___x_1702_; 
v_toSemiring_1699_ = lean_ctor_get(v_inst_1696_, 0);
v_intCast_1700_ = lean_ctor_get(v_inst_1696_, 3);
v_toAdd_1701_ = lean_ctor_get(v_toSemiring_1699_, 0);
lean_inc(v_toAdd_1701_);
lean_inc_ref(v_inst_1696_);
v___x_1702_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1696_);
if (lean_obj_tag(v_p_1698_) == 0)
{
lean_object* v_k_1703_; lean_object* v___x_1704_; 
lean_inc(v_intCast_1700_);
lean_dec_ref(v___x_1702_);
lean_dec(v_toAdd_1701_);
lean_dec_ref(v_inst_1696_);
v_k_1703_ = lean_ctor_get(v_p_1698_, 0);
lean_inc(v_k_1703_);
lean_dec_ref_known(v_p_1698_, 1);
v___x_1704_ = lean_apply_1(v_intCast_1700_, v_k_1703_);
return v___x_1704_;
}
else
{
lean_object* v_zsmul_1705_; lean_object* v_k_1706_; lean_object* v_v_1707_; lean_object* v_p_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_zsmul_1705_ = lean_ctor_get(v___x_1702_, 2);
lean_inc(v_zsmul_1705_);
lean_dec_ref(v___x_1702_);
v_k_1706_ = lean_ctor_get(v_p_1698_, 0);
lean_inc(v_k_1706_);
v_v_1707_ = lean_ctor_get(v_p_1698_, 1);
lean_inc(v_v_1707_);
v_p_1708_ = lean_ctor_get(v_p_1698_, 2);
lean_inc_ref(v_p_1708_);
lean_dec_ref_known(v_p_1698_, 3);
lean_inc_ref(v_toSemiring_1699_);
v___x_1709_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_toSemiring_1699_, v_ctx_1697_, v_v_1707_);
v___x_1710_ = lean_apply_2(v_zsmul_1705_, v_k_1706_, v___x_1709_);
v___x_1711_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1696_, v_ctx_1697_, v_p_1708_);
v___x_1712_ = lean_apply_2(v_toAdd_1701_, v___x_1710_, v___x_1711_);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg___boxed(lean_object* v_inst_1713_, lean_object* v_ctx_1714_, lean_object* v_p_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1713_, v_ctx_1714_, v_p_1715_);
lean_dec_ref(v_ctx_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote(lean_object* v_00_u03b1_1717_, lean_object* v_inst_1718_, lean_object* v_ctx_1719_, lean_object* v_p_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1718_, v_ctx_1719_, v_p_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_inst_1723_, lean_object* v_ctx_1724_, lean_object* v_p_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Grind_CommRing_Poly_denote(v_00_u03b1_1722_, v_inst_1723_, v_ctx_1724_, v_p_1725_);
lean_dec_ref(v_ctx_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg(lean_object* v_inst_1727_, lean_object* v_ctx_1728_, lean_object* v_k_1729_, lean_object* v_m_1730_){
_start:
{
lean_object* v_toSemiring_1731_; lean_object* v___x_1732_; lean_object* v_zsmul_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v_toSemiring_1731_ = lean_ctor_get(v_inst_1727_, 0);
lean_inc_ref(v_toSemiring_1731_);
v___x_1732_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1727_);
v_zsmul_1733_ = lean_ctor_get(v___x_1732_, 2);
lean_inc(v_zsmul_1733_);
lean_dec_ref(v___x_1732_);
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1736_ = lean_int_dec_eq(v_k_1729_, v___x_1735_);
if (v___x_1736_ == 0)
{
if (lean_obj_tag(v_m_1730_) == 0)
{
lean_object* v_ofNat_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_ofNat_1737_ = lean_ctor_get(v_toSemiring_1731_, 3);
lean_inc(v_ofNat_1737_);
lean_dec_ref(v_toSemiring_1731_);
v___x_1738_ = lean_apply_1(v_ofNat_1737_, v___x_1734_);
v___x_1739_ = lean_apply_2(v_zsmul_1733_, v_k_1729_, v___x_1738_);
return v___x_1739_;
}
else
{
lean_object* v_p_1740_; lean_object* v_m_1741_; lean_object* v_ofNat_1742_; lean_object* v_npow_1743_; lean_object* v_x_1744_; lean_object* v_k_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v_p_1740_ = lean_ctor_get(v_m_1730_, 0);
lean_inc_ref(v_p_1740_);
v_m_1741_ = lean_ctor_get(v_m_1730_, 1);
lean_inc(v_m_1741_);
lean_dec_ref_known(v_m_1730_, 2);
v_ofNat_1742_ = lean_ctor_get(v_toSemiring_1731_, 3);
v_npow_1743_ = lean_ctor_get(v_toSemiring_1731_, 5);
v_x_1744_ = lean_ctor_get(v_p_1740_, 0);
lean_inc(v_x_1744_);
v_k_1745_ = lean_ctor_get(v_p_1740_, 1);
lean_inc(v_k_1745_);
lean_dec_ref(v_p_1740_);
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = lean_nat_dec_eq(v_k_1745_, v___x_1746_);
if (v___x_1747_ == 0)
{
uint8_t v___x_1748_; 
v___x_1748_ = lean_nat_dec_eq(v_k_1745_, v___x_1734_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1749_ = l_Lean_RArray_getImpl___redArg(v_ctx_1728_, v_x_1744_);
lean_dec(v_x_1744_);
lean_inc(v_npow_1743_);
v___x_1750_ = lean_apply_2(v_npow_1743_, v___x_1749_, v_k_1745_);
v___x_1751_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1731_, v_ctx_1728_, v_m_1741_, v___x_1750_);
v___x_1752_ = lean_apply_2(v_zsmul_1733_, v_k_1729_, v___x_1751_);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec(v_k_1745_);
v___x_1753_ = l_Lean_RArray_getImpl___redArg(v_ctx_1728_, v_x_1744_);
lean_dec(v_x_1744_);
v___x_1754_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1731_, v_ctx_1728_, v_m_1741_, v___x_1753_);
v___x_1755_ = lean_apply_2(v_zsmul_1733_, v_k_1729_, v___x_1754_);
return v___x_1755_;
}
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec(v_k_1745_);
lean_dec(v_x_1744_);
lean_inc(v_ofNat_1742_);
v___x_1756_ = lean_apply_1(v_ofNat_1742_, v___x_1734_);
v___x_1757_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1731_, v_ctx_1728_, v_m_1741_, v___x_1756_);
v___x_1758_ = lean_apply_2(v_zsmul_1733_, v_k_1729_, v___x_1757_);
return v___x_1758_;
}
}
}
else
{
lean_dec(v_zsmul_1733_);
lean_dec(v_k_1729_);
if (lean_obj_tag(v_m_1730_) == 0)
{
lean_object* v_ofNat_1759_; lean_object* v___x_1760_; 
v_ofNat_1759_ = lean_ctor_get(v_toSemiring_1731_, 3);
lean_inc(v_ofNat_1759_);
lean_dec_ref(v_toSemiring_1731_);
v___x_1760_ = lean_apply_1(v_ofNat_1759_, v___x_1734_);
return v___x_1760_;
}
else
{
lean_object* v_p_1761_; lean_object* v_m_1762_; lean_object* v_ofNat_1763_; lean_object* v_npow_1764_; lean_object* v_x_1765_; lean_object* v_k_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_p_1761_ = lean_ctor_get(v_m_1730_, 0);
lean_inc_ref(v_p_1761_);
v_m_1762_ = lean_ctor_get(v_m_1730_, 1);
lean_inc(v_m_1762_);
lean_dec_ref_known(v_m_1730_, 2);
v_ofNat_1763_ = lean_ctor_get(v_toSemiring_1731_, 3);
v_npow_1764_ = lean_ctor_get(v_toSemiring_1731_, 5);
v_x_1765_ = lean_ctor_get(v_p_1761_, 0);
lean_inc(v_x_1765_);
v_k_1766_ = lean_ctor_get(v_p_1761_, 1);
lean_inc(v_k_1766_);
lean_dec_ref(v_p_1761_);
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = lean_nat_dec_eq(v_k_1766_, v___x_1767_);
if (v___x_1768_ == 0)
{
uint8_t v___x_1769_; 
v___x_1769_ = lean_nat_dec_eq(v_k_1766_, v___x_1734_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = l_Lean_RArray_getImpl___redArg(v_ctx_1728_, v_x_1765_);
lean_dec(v_x_1765_);
lean_inc(v_npow_1764_);
v___x_1771_ = lean_apply_2(v_npow_1764_, v___x_1770_, v_k_1766_);
v___x_1772_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1731_, v_ctx_1728_, v_m_1762_, v___x_1771_);
return v___x_1772_;
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_dec(v_k_1766_);
v___x_1773_ = l_Lean_RArray_getImpl___redArg(v_ctx_1728_, v_x_1765_);
lean_dec(v_x_1765_);
v___x_1774_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1731_, v_ctx_1728_, v_m_1762_, v___x_1773_);
return v___x_1774_;
}
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec(v_k_1766_);
lean_dec(v_x_1765_);
lean_inc(v_ofNat_1763_);
v___x_1775_ = lean_apply_1(v_ofNat_1763_, v___x_1734_);
v___x_1776_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1731_, v_ctx_1728_, v_m_1762_, v___x_1775_);
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg___boxed(lean_object* v_inst_1777_, lean_object* v_ctx_1778_, lean_object* v_k_1779_, lean_object* v_m_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Grind_CommRing_denoteTerm___redArg(v_inst_1777_, v_ctx_1778_, v_k_1779_, v_m_1780_);
lean_dec_ref(v_ctx_1778_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm(lean_object* v_00_u03b1_1782_, lean_object* v_inst_1783_, lean_object* v_ctx_1784_, lean_object* v_k_1785_, lean_object* v_m_1786_){
_start:
{
lean_object* v_toSemiring_1787_; lean_object* v___x_1788_; lean_object* v_zsmul_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v_toSemiring_1787_ = lean_ctor_get(v_inst_1783_, 0);
lean_inc_ref(v_toSemiring_1787_);
v___x_1788_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1783_);
v_zsmul_1789_ = lean_ctor_get(v___x_1788_, 2);
lean_inc(v_zsmul_1789_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = lean_unsigned_to_nat(1u);
v___x_1791_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1792_ = lean_int_dec_eq(v_k_1785_, v___x_1791_);
if (v___x_1792_ == 0)
{
if (lean_obj_tag(v_m_1786_) == 0)
{
lean_object* v_ofNat_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_ofNat_1793_ = lean_ctor_get(v_toSemiring_1787_, 3);
lean_inc(v_ofNat_1793_);
lean_dec_ref(v_toSemiring_1787_);
v___x_1794_ = lean_apply_1(v_ofNat_1793_, v___x_1790_);
v___x_1795_ = lean_apply_2(v_zsmul_1789_, v_k_1785_, v___x_1794_);
return v___x_1795_;
}
else
{
lean_object* v_p_1796_; lean_object* v_m_1797_; lean_object* v_ofNat_1798_; lean_object* v_npow_1799_; lean_object* v_x_1800_; lean_object* v_k_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v_p_1796_ = lean_ctor_get(v_m_1786_, 0);
lean_inc_ref(v_p_1796_);
v_m_1797_ = lean_ctor_get(v_m_1786_, 1);
lean_inc(v_m_1797_);
lean_dec_ref_known(v_m_1786_, 2);
v_ofNat_1798_ = lean_ctor_get(v_toSemiring_1787_, 3);
v_npow_1799_ = lean_ctor_get(v_toSemiring_1787_, 5);
v_x_1800_ = lean_ctor_get(v_p_1796_, 0);
lean_inc(v_x_1800_);
v_k_1801_ = lean_ctor_get(v_p_1796_, 1);
lean_inc(v_k_1801_);
lean_dec_ref(v_p_1796_);
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_nat_dec_eq(v_k_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
uint8_t v___x_1804_; 
v___x_1804_ = lean_nat_dec_eq(v_k_1801_, v___x_1790_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = l_Lean_RArray_getImpl___redArg(v_ctx_1784_, v_x_1800_);
lean_dec(v_x_1800_);
lean_inc(v_npow_1799_);
v___x_1806_ = lean_apply_2(v_npow_1799_, v___x_1805_, v_k_1801_);
v___x_1807_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1787_, v_ctx_1784_, v_m_1797_, v___x_1806_);
v___x_1808_ = lean_apply_2(v_zsmul_1789_, v_k_1785_, v___x_1807_);
return v___x_1808_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec(v_k_1801_);
v___x_1809_ = l_Lean_RArray_getImpl___redArg(v_ctx_1784_, v_x_1800_);
lean_dec(v_x_1800_);
v___x_1810_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1787_, v_ctx_1784_, v_m_1797_, v___x_1809_);
v___x_1811_ = lean_apply_2(v_zsmul_1789_, v_k_1785_, v___x_1810_);
return v___x_1811_;
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec(v_k_1801_);
lean_dec(v_x_1800_);
lean_inc(v_ofNat_1798_);
v___x_1812_ = lean_apply_1(v_ofNat_1798_, v___x_1790_);
v___x_1813_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1787_, v_ctx_1784_, v_m_1797_, v___x_1812_);
v___x_1814_ = lean_apply_2(v_zsmul_1789_, v_k_1785_, v___x_1813_);
return v___x_1814_;
}
}
}
else
{
lean_dec(v_zsmul_1789_);
lean_dec(v_k_1785_);
if (lean_obj_tag(v_m_1786_) == 0)
{
lean_object* v_ofNat_1815_; lean_object* v___x_1816_; 
v_ofNat_1815_ = lean_ctor_get(v_toSemiring_1787_, 3);
lean_inc(v_ofNat_1815_);
lean_dec_ref(v_toSemiring_1787_);
v___x_1816_ = lean_apply_1(v_ofNat_1815_, v___x_1790_);
return v___x_1816_;
}
else
{
lean_object* v_p_1817_; lean_object* v_m_1818_; lean_object* v_ofNat_1819_; lean_object* v_npow_1820_; lean_object* v_x_1821_; lean_object* v_k_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
v_p_1817_ = lean_ctor_get(v_m_1786_, 0);
lean_inc_ref(v_p_1817_);
v_m_1818_ = lean_ctor_get(v_m_1786_, 1);
lean_inc(v_m_1818_);
lean_dec_ref_known(v_m_1786_, 2);
v_ofNat_1819_ = lean_ctor_get(v_toSemiring_1787_, 3);
v_npow_1820_ = lean_ctor_get(v_toSemiring_1787_, 5);
v_x_1821_ = lean_ctor_get(v_p_1817_, 0);
lean_inc(v_x_1821_);
v_k_1822_ = lean_ctor_get(v_p_1817_, 1);
lean_inc(v_k_1822_);
lean_dec_ref(v_p_1817_);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = lean_nat_dec_eq(v_k_1822_, v___x_1823_);
if (v___x_1824_ == 0)
{
uint8_t v___x_1825_; 
v___x_1825_ = lean_nat_dec_eq(v_k_1822_, v___x_1790_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = l_Lean_RArray_getImpl___redArg(v_ctx_1784_, v_x_1821_);
lean_dec(v_x_1821_);
lean_inc(v_npow_1820_);
v___x_1827_ = lean_apply_2(v_npow_1820_, v___x_1826_, v_k_1822_);
v___x_1828_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1787_, v_ctx_1784_, v_m_1818_, v___x_1827_);
return v___x_1828_;
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec(v_k_1822_);
v___x_1829_ = l_Lean_RArray_getImpl___redArg(v_ctx_1784_, v_x_1821_);
lean_dec(v_x_1821_);
v___x_1830_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1787_, v_ctx_1784_, v_m_1818_, v___x_1829_);
return v___x_1830_;
}
}
else
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec(v_k_1822_);
lean_dec(v_x_1821_);
lean_inc(v_ofNat_1819_);
v___x_1831_ = lean_apply_1(v_ofNat_1819_, v___x_1790_);
v___x_1832_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1787_, v_ctx_1784_, v_m_1818_, v___x_1831_);
return v___x_1832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___boxed(lean_object* v_00_u03b1_1833_, lean_object* v_inst_1834_, lean_object* v_ctx_1835_, lean_object* v_k_1836_, lean_object* v_m_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Grind_CommRing_denoteTerm(v_00_u03b1_1833_, v_inst_1834_, v_ctx_1835_, v_k_1836_, v_m_1837_);
lean_dec_ref(v_ctx_1835_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(lean_object* v_inst_1839_, lean_object* v_ctx_1840_, lean_object* v_p_1841_, lean_object* v_acc_1842_){
_start:
{
if (lean_obj_tag(v_p_1841_) == 0)
{
lean_object* v_toSemiring_1843_; lean_object* v_intCast_1844_; lean_object* v_toAdd_1845_; lean_object* v_k_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v_toSemiring_1843_ = lean_ctor_get(v_inst_1839_, 0);
lean_inc_ref(v_toSemiring_1843_);
v_intCast_1844_ = lean_ctor_get(v_inst_1839_, 3);
lean_inc(v_intCast_1844_);
lean_dec_ref(v_inst_1839_);
v_toAdd_1845_ = lean_ctor_get(v_toSemiring_1843_, 0);
lean_inc(v_toAdd_1845_);
lean_dec_ref(v_toSemiring_1843_);
v_k_1846_ = lean_ctor_get(v_p_1841_, 0);
lean_inc(v_k_1846_);
lean_dec_ref_known(v_p_1841_, 1);
v___x_1847_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1848_ = lean_int_dec_eq(v_k_1846_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_apply_1(v_intCast_1844_, v_k_1846_);
v___x_1850_ = lean_apply_2(v_toAdd_1845_, v_acc_1842_, v___x_1849_);
return v___x_1850_;
}
else
{
lean_dec(v_k_1846_);
lean_dec(v_toAdd_1845_);
lean_dec(v_intCast_1844_);
return v_acc_1842_;
}
}
else
{
lean_object* v_toSemiring_1851_; lean_object* v_toAdd_1852_; lean_object* v_ofNat_1853_; lean_object* v_npow_1854_; lean_object* v_k_1855_; lean_object* v_v_1856_; lean_object* v_p_1857_; lean_object* v___y_1859_; lean_object* v___x_1862_; lean_object* v_zsmul_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v_toSemiring_1851_ = lean_ctor_get(v_inst_1839_, 0);
v_toAdd_1852_ = lean_ctor_get(v_toSemiring_1851_, 0);
v_ofNat_1853_ = lean_ctor_get(v_toSemiring_1851_, 3);
v_npow_1854_ = lean_ctor_get(v_toSemiring_1851_, 5);
v_k_1855_ = lean_ctor_get(v_p_1841_, 0);
lean_inc(v_k_1855_);
v_v_1856_ = lean_ctor_get(v_p_1841_, 1);
lean_inc(v_v_1856_);
v_p_1857_ = lean_ctor_get(v_p_1841_, 2);
lean_inc_ref(v_p_1857_);
lean_dec_ref_known(v_p_1841_, 3);
lean_inc_ref(v_inst_1839_);
v___x_1862_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1839_);
v_zsmul_1863_ = lean_ctor_get(v___x_1862_, 2);
lean_inc(v_zsmul_1863_);
lean_dec_ref(v___x_1862_);
v___x_1864_ = lean_unsigned_to_nat(1u);
v___x_1865_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1866_ = lean_int_dec_eq(v_k_1855_, v___x_1865_);
if (v___x_1866_ == 0)
{
if (lean_obj_tag(v_v_1856_) == 0)
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_inc(v_ofNat_1853_);
v___x_1867_ = lean_apply_1(v_ofNat_1853_, v___x_1864_);
v___x_1868_ = lean_apply_2(v_zsmul_1863_, v_k_1855_, v___x_1867_);
v___y_1859_ = v___x_1868_;
goto v___jp_1858_;
}
else
{
lean_object* v_p_1869_; lean_object* v_m_1870_; lean_object* v_x_1871_; lean_object* v_k_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v_p_1869_ = lean_ctor_get(v_v_1856_, 0);
lean_inc_ref(v_p_1869_);
v_m_1870_ = lean_ctor_get(v_v_1856_, 1);
lean_inc(v_m_1870_);
lean_dec_ref_known(v_v_1856_, 2);
v_x_1871_ = lean_ctor_get(v_p_1869_, 0);
lean_inc(v_x_1871_);
v_k_1872_ = lean_ctor_get(v_p_1869_, 1);
lean_inc(v_k_1872_);
lean_dec_ref(v_p_1869_);
v___x_1873_ = lean_unsigned_to_nat(0u);
v___x_1874_ = lean_nat_dec_eq(v_k_1872_, v___x_1873_);
if (v___x_1874_ == 0)
{
uint8_t v___x_1875_; 
v___x_1875_ = lean_nat_dec_eq(v_k_1872_, v___x_1864_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1876_ = l_Lean_RArray_getImpl___redArg(v_ctx_1840_, v_x_1871_);
lean_dec(v_x_1871_);
lean_inc(v_npow_1854_);
v___x_1877_ = lean_apply_2(v_npow_1854_, v___x_1876_, v_k_1872_);
lean_inc_ref(v_toSemiring_1851_);
v___x_1878_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1851_, v_ctx_1840_, v_m_1870_, v___x_1877_);
v___x_1879_ = lean_apply_2(v_zsmul_1863_, v_k_1855_, v___x_1878_);
v___y_1859_ = v___x_1879_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec(v_k_1872_);
v___x_1880_ = l_Lean_RArray_getImpl___redArg(v_ctx_1840_, v_x_1871_);
lean_dec(v_x_1871_);
lean_inc_ref(v_toSemiring_1851_);
v___x_1881_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1851_, v_ctx_1840_, v_m_1870_, v___x_1880_);
v___x_1882_ = lean_apply_2(v_zsmul_1863_, v_k_1855_, v___x_1881_);
v___y_1859_ = v___x_1882_;
goto v___jp_1858_;
}
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec(v_k_1872_);
lean_dec(v_x_1871_);
lean_inc(v_ofNat_1853_);
v___x_1883_ = lean_apply_1(v_ofNat_1853_, v___x_1864_);
lean_inc_ref(v_toSemiring_1851_);
v___x_1884_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1851_, v_ctx_1840_, v_m_1870_, v___x_1883_);
v___x_1885_ = lean_apply_2(v_zsmul_1863_, v_k_1855_, v___x_1884_);
v___y_1859_ = v___x_1885_;
goto v___jp_1858_;
}
}
}
else
{
lean_dec(v_zsmul_1863_);
lean_dec(v_k_1855_);
if (lean_obj_tag(v_v_1856_) == 0)
{
lean_object* v___x_1886_; 
lean_inc(v_ofNat_1853_);
v___x_1886_ = lean_apply_1(v_ofNat_1853_, v___x_1864_);
v___y_1859_ = v___x_1886_;
goto v___jp_1858_;
}
else
{
lean_object* v_p_1887_; lean_object* v_m_1888_; lean_object* v_x_1889_; lean_object* v_k_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v_p_1887_ = lean_ctor_get(v_v_1856_, 0);
lean_inc_ref(v_p_1887_);
v_m_1888_ = lean_ctor_get(v_v_1856_, 1);
lean_inc(v_m_1888_);
lean_dec_ref_known(v_v_1856_, 2);
v_x_1889_ = lean_ctor_get(v_p_1887_, 0);
lean_inc(v_x_1889_);
v_k_1890_ = lean_ctor_get(v_p_1887_, 1);
lean_inc(v_k_1890_);
lean_dec_ref(v_p_1887_);
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = lean_nat_dec_eq(v_k_1890_, v___x_1891_);
if (v___x_1892_ == 0)
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_nat_dec_eq(v_k_1890_, v___x_1864_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = l_Lean_RArray_getImpl___redArg(v_ctx_1840_, v_x_1889_);
lean_dec(v_x_1889_);
lean_inc(v_npow_1854_);
v___x_1895_ = lean_apply_2(v_npow_1854_, v___x_1894_, v_k_1890_);
lean_inc_ref(v_toSemiring_1851_);
v___x_1896_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1851_, v_ctx_1840_, v_m_1888_, v___x_1895_);
v___y_1859_ = v___x_1896_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec(v_k_1890_);
v___x_1897_ = l_Lean_RArray_getImpl___redArg(v_ctx_1840_, v_x_1889_);
lean_dec(v_x_1889_);
lean_inc_ref(v_toSemiring_1851_);
v___x_1898_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1851_, v_ctx_1840_, v_m_1888_, v___x_1897_);
v___y_1859_ = v___x_1898_;
goto v___jp_1858_;
}
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
lean_dec(v_k_1890_);
lean_dec(v_x_1889_);
lean_inc(v_ofNat_1853_);
v___x_1899_ = lean_apply_1(v_ofNat_1853_, v___x_1864_);
lean_inc_ref(v_toSemiring_1851_);
v___x_1900_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1851_, v_ctx_1840_, v_m_1888_, v___x_1899_);
v___y_1859_ = v___x_1900_;
goto v___jp_1858_;
}
}
}
v___jp_1858_:
{
lean_object* v___x_1860_; 
lean_inc(v_toAdd_1852_);
v___x_1860_ = lean_apply_2(v_toAdd_1852_, v_acc_1842_, v___y_1859_);
v_p_1841_ = v_p_1857_;
v_acc_1842_ = v___x_1860_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg___boxed(lean_object* v_inst_1901_, lean_object* v_ctx_1902_, lean_object* v_p_1903_, lean_object* v_acc_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1901_, v_ctx_1902_, v_p_1903_, v_acc_1904_);
lean_dec_ref(v_ctx_1902_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go(lean_object* v_00_u03b1_1906_, lean_object* v_inst_1907_, lean_object* v_ctx_1908_, lean_object* v_p_1909_, lean_object* v_acc_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1907_, v_ctx_1908_, v_p_1909_, v_acc_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___boxed(lean_object* v_00_u03b1_1912_, lean_object* v_inst_1913_, lean_object* v_ctx_1914_, lean_object* v_p_1915_, lean_object* v_acc_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_Grind_CommRing_Poly_denote_x27_go(v_00_u03b1_1912_, v_inst_1913_, v_ctx_1914_, v_p_1915_, v_acc_1916_);
lean_dec_ref(v_ctx_1914_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg(lean_object* v_inst_1918_, lean_object* v_ctx_1919_, lean_object* v_p_1920_){
_start:
{
if (lean_obj_tag(v_p_1920_) == 0)
{
lean_object* v_intCast_1921_; lean_object* v_k_1922_; lean_object* v___x_1923_; 
v_intCast_1921_ = lean_ctor_get(v_inst_1918_, 3);
lean_inc(v_intCast_1921_);
lean_dec_ref(v_inst_1918_);
v_k_1922_ = lean_ctor_get(v_p_1920_, 0);
lean_inc(v_k_1922_);
lean_dec_ref_known(v_p_1920_, 1);
v___x_1923_ = lean_apply_1(v_intCast_1921_, v_k_1922_);
return v___x_1923_;
}
else
{
lean_object* v_toSemiring_1924_; lean_object* v_k_1925_; lean_object* v_v_1926_; lean_object* v_p_1927_; lean_object* v___x_1928_; lean_object* v_zsmul_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v_toSemiring_1924_ = lean_ctor_get(v_inst_1918_, 0);
v_k_1925_ = lean_ctor_get(v_p_1920_, 0);
lean_inc(v_k_1925_);
v_v_1926_ = lean_ctor_get(v_p_1920_, 1);
lean_inc(v_v_1926_);
v_p_1927_ = lean_ctor_get(v_p_1920_, 2);
lean_inc_ref(v_p_1927_);
lean_dec_ref_known(v_p_1920_, 3);
lean_inc_ref(v_inst_1918_);
v___x_1928_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1918_);
v_zsmul_1929_ = lean_ctor_get(v___x_1928_, 2);
lean_inc(v_zsmul_1929_);
lean_dec_ref(v___x_1928_);
v___x_1930_ = lean_unsigned_to_nat(1u);
v___x_1931_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1932_ = lean_int_dec_eq(v_k_1925_, v___x_1931_);
if (v___x_1932_ == 0)
{
if (lean_obj_tag(v_v_1926_) == 0)
{
lean_object* v_ofNat_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_ofNat_1933_ = lean_ctor_get(v_toSemiring_1924_, 3);
lean_inc(v_ofNat_1933_);
v___x_1934_ = lean_apply_1(v_ofNat_1933_, v___x_1930_);
v___x_1935_ = lean_apply_2(v_zsmul_1929_, v_k_1925_, v___x_1934_);
v___x_1936_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1918_, v_ctx_1919_, v_p_1927_, v___x_1935_);
return v___x_1936_;
}
else
{
lean_object* v_p_1937_; lean_object* v_m_1938_; lean_object* v_ofNat_1939_; lean_object* v_npow_1940_; lean_object* v_x_1941_; lean_object* v_k_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v_p_1937_ = lean_ctor_get(v_v_1926_, 0);
lean_inc_ref(v_p_1937_);
v_m_1938_ = lean_ctor_get(v_v_1926_, 1);
lean_inc(v_m_1938_);
lean_dec_ref_known(v_v_1926_, 2);
v_ofNat_1939_ = lean_ctor_get(v_toSemiring_1924_, 3);
v_npow_1940_ = lean_ctor_get(v_toSemiring_1924_, 5);
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
v___x_1945_ = lean_nat_dec_eq(v_k_1942_, v___x_1930_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1946_ = l_Lean_RArray_getImpl___redArg(v_ctx_1919_, v_x_1941_);
lean_dec(v_x_1941_);
lean_inc(v_npow_1940_);
v___x_1947_ = lean_apply_2(v_npow_1940_, v___x_1946_, v_k_1942_);
lean_inc_ref(v_toSemiring_1924_);
v___x_1948_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1924_, v_ctx_1919_, v_m_1938_, v___x_1947_);
v___x_1949_ = lean_apply_2(v_zsmul_1929_, v_k_1925_, v___x_1948_);
v___x_1950_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1918_, v_ctx_1919_, v_p_1927_, v___x_1949_);
return v___x_1950_;
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_dec(v_k_1942_);
v___x_1951_ = l_Lean_RArray_getImpl___redArg(v_ctx_1919_, v_x_1941_);
lean_dec(v_x_1941_);
lean_inc_ref(v_toSemiring_1924_);
v___x_1952_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1924_, v_ctx_1919_, v_m_1938_, v___x_1951_);
v___x_1953_ = lean_apply_2(v_zsmul_1929_, v_k_1925_, v___x_1952_);
v___x_1954_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1918_, v_ctx_1919_, v_p_1927_, v___x_1953_);
return v___x_1954_;
}
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec(v_k_1942_);
lean_dec(v_x_1941_);
lean_inc(v_ofNat_1939_);
v___x_1955_ = lean_apply_1(v_ofNat_1939_, v___x_1930_);
lean_inc_ref(v_toSemiring_1924_);
v___x_1956_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1924_, v_ctx_1919_, v_m_1938_, v___x_1955_);
v___x_1957_ = lean_apply_2(v_zsmul_1929_, v_k_1925_, v___x_1956_);
v___x_1958_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1918_, v_ctx_1919_, v_p_1927_, v___x_1957_);
return v___x_1958_;
}
}
}
else
{
lean_dec(v_zsmul_1929_);
lean_dec(v_k_1925_);
if (lean_obj_tag(v_v_1926_) == 0)
{
lean_object* v_ofNat_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v_ofNat_1959_ = lean_ctor_get(v_toSemiring_1924_, 3);
lean_inc(v_ofNat_1959_);
v___x_1960_ = lean_apply_1(v_ofNat_1959_, v___x_1930_);
v___x_1961_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1918_, v_ctx_1919_, v_p_1927_, v___x_1960_);
return v___x_1961_;
}
else
{
lean_object* v_p_1962_; lean_object* v_m_1963_; lean_object* v_ofNat_1964_; lean_object* v_npow_1965_; lean_object* v_x_1966_; lean_object* v_k_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v_p_1962_ = lean_ctor_get(v_v_1926_, 0);
lean_inc_ref(v_p_1962_);
v_m_1963_ = lean_ctor_get(v_v_1926_, 1);
lean_inc(v_m_1963_);
lean_dec_ref_known(v_v_1926_, 2);
v_ofNat_1964_ = lean_ctor_get(v_toSemiring_1924_, 3);
v_npow_1965_ = lean_ctor_get(v_toSemiring_1924_, 5);
v_x_1966_ = lean_ctor_get(v_p_1962_, 0);
lean_inc(v_x_1966_);
v_k_1967_ = lean_ctor_get(v_p_1962_, 1);
lean_inc(v_k_1967_);
lean_dec_ref(v_p_1962_);
v___x_1968_ = lean_unsigned_to_nat(0u);
v___x_1969_ = lean_nat_dec_eq(v_k_1967_, v___x_1968_);
if (v___x_1969_ == 0)
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_nat_dec_eq(v_k_1967_, v___x_1930_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1971_ = l_Lean_RArray_getImpl___redArg(v_ctx_1919_, v_x_1966_);
lean_dec(v_x_1966_);
lean_inc(v_npow_1965_);
v___x_1972_ = lean_apply_2(v_npow_1965_, v___x_1971_, v_k_1967_);
lean_inc_ref(v_toSemiring_1924_);
v___x_1973_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1924_, v_ctx_1919_, v_m_1963_, v___x_1972_);
v___x_1974_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1918_, v_ctx_1919_, v_p_1927_, v___x_1973_);
return v___x_1974_;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_dec(v_k_1967_);
v___x_1975_ = l_Lean_RArray_getImpl___redArg(v_ctx_1919_, v_x_1966_);
lean_dec(v_x_1966_);
lean_inc_ref(v_toSemiring_1924_);
v___x_1976_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1924_, v_ctx_1919_, v_m_1963_, v___x_1975_);
v___x_1977_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1918_, v_ctx_1919_, v_p_1927_, v___x_1976_);
return v___x_1977_;
}
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec(v_k_1967_);
lean_dec(v_x_1966_);
lean_inc(v_ofNat_1964_);
v___x_1978_ = lean_apply_1(v_ofNat_1964_, v___x_1930_);
lean_inc_ref(v_toSemiring_1924_);
v___x_1979_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1924_, v_ctx_1919_, v_m_1963_, v___x_1978_);
v___x_1980_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1918_, v_ctx_1919_, v_p_1927_, v___x_1979_);
return v___x_1980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg___boxed(lean_object* v_inst_1981_, lean_object* v_ctx_1982_, lean_object* v_p_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Grind_CommRing_Poly_denote_x27___redArg(v_inst_1981_, v_ctx_1982_, v_p_1983_);
lean_dec_ref(v_ctx_1982_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27(lean_object* v_00_u03b1_1985_, lean_object* v_inst_1986_, lean_object* v_ctx_1987_, lean_object* v_p_1988_){
_start:
{
if (lean_obj_tag(v_p_1988_) == 0)
{
lean_object* v_intCast_1989_; lean_object* v_k_1990_; lean_object* v___x_1991_; 
v_intCast_1989_ = lean_ctor_get(v_inst_1986_, 3);
lean_inc(v_intCast_1989_);
lean_dec_ref(v_inst_1986_);
v_k_1990_ = lean_ctor_get(v_p_1988_, 0);
lean_inc(v_k_1990_);
lean_dec_ref_known(v_p_1988_, 1);
v___x_1991_ = lean_apply_1(v_intCast_1989_, v_k_1990_);
return v___x_1991_;
}
else
{
lean_object* v_toSemiring_1992_; lean_object* v_k_1993_; lean_object* v_v_1994_; lean_object* v_p_1995_; lean_object* v___x_1996_; lean_object* v_zsmul_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v_toSemiring_1992_ = lean_ctor_get(v_inst_1986_, 0);
v_k_1993_ = lean_ctor_get(v_p_1988_, 0);
lean_inc(v_k_1993_);
v_v_1994_ = lean_ctor_get(v_p_1988_, 1);
lean_inc(v_v_1994_);
v_p_1995_ = lean_ctor_get(v_p_1988_, 2);
lean_inc_ref(v_p_1995_);
lean_dec_ref_known(v_p_1988_, 3);
lean_inc_ref(v_inst_1986_);
v___x_1996_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1986_);
v_zsmul_1997_ = lean_ctor_get(v___x_1996_, 2);
lean_inc(v_zsmul_1997_);
lean_dec_ref(v___x_1996_);
v___x_1998_ = lean_unsigned_to_nat(1u);
v___x_1999_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2000_ = lean_int_dec_eq(v_k_1993_, v___x_1999_);
if (v___x_2000_ == 0)
{
if (lean_obj_tag(v_v_1994_) == 0)
{
lean_object* v_ofNat_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_ofNat_2001_ = lean_ctor_get(v_toSemiring_1992_, 3);
lean_inc(v_ofNat_2001_);
v___x_2002_ = lean_apply_1(v_ofNat_2001_, v___x_1998_);
v___x_2003_ = lean_apply_2(v_zsmul_1997_, v_k_1993_, v___x_2002_);
v___x_2004_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1986_, v_ctx_1987_, v_p_1995_, v___x_2003_);
return v___x_2004_;
}
else
{
lean_object* v_p_2005_; lean_object* v_m_2006_; lean_object* v_ofNat_2007_; lean_object* v_npow_2008_; lean_object* v_x_2009_; lean_object* v_k_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v_p_2005_ = lean_ctor_get(v_v_1994_, 0);
lean_inc_ref(v_p_2005_);
v_m_2006_ = lean_ctor_get(v_v_1994_, 1);
lean_inc(v_m_2006_);
lean_dec_ref_known(v_v_1994_, 2);
v_ofNat_2007_ = lean_ctor_get(v_toSemiring_1992_, 3);
v_npow_2008_ = lean_ctor_get(v_toSemiring_1992_, 5);
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
v___x_2013_ = lean_nat_dec_eq(v_k_2010_, v___x_1998_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2014_ = l_Lean_RArray_getImpl___redArg(v_ctx_1987_, v_x_2009_);
lean_dec(v_x_2009_);
lean_inc(v_npow_2008_);
v___x_2015_ = lean_apply_2(v_npow_2008_, v___x_2014_, v_k_2010_);
lean_inc_ref(v_toSemiring_1992_);
v___x_2016_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1992_, v_ctx_1987_, v_m_2006_, v___x_2015_);
v___x_2017_ = lean_apply_2(v_zsmul_1997_, v_k_1993_, v___x_2016_);
v___x_2018_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1986_, v_ctx_1987_, v_p_1995_, v___x_2017_);
return v___x_2018_;
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec(v_k_2010_);
v___x_2019_ = l_Lean_RArray_getImpl___redArg(v_ctx_1987_, v_x_2009_);
lean_dec(v_x_2009_);
lean_inc_ref(v_toSemiring_1992_);
v___x_2020_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1992_, v_ctx_1987_, v_m_2006_, v___x_2019_);
v___x_2021_ = lean_apply_2(v_zsmul_1997_, v_k_1993_, v___x_2020_);
v___x_2022_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1986_, v_ctx_1987_, v_p_1995_, v___x_2021_);
return v___x_2022_;
}
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
lean_dec(v_k_2010_);
lean_dec(v_x_2009_);
lean_inc(v_ofNat_2007_);
v___x_2023_ = lean_apply_1(v_ofNat_2007_, v___x_1998_);
lean_inc_ref(v_toSemiring_1992_);
v___x_2024_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1992_, v_ctx_1987_, v_m_2006_, v___x_2023_);
v___x_2025_ = lean_apply_2(v_zsmul_1997_, v_k_1993_, v___x_2024_);
v___x_2026_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1986_, v_ctx_1987_, v_p_1995_, v___x_2025_);
return v___x_2026_;
}
}
}
else
{
lean_dec(v_zsmul_1997_);
lean_dec(v_k_1993_);
if (lean_obj_tag(v_v_1994_) == 0)
{
lean_object* v_ofNat_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_ofNat_2027_ = lean_ctor_get(v_toSemiring_1992_, 3);
lean_inc(v_ofNat_2027_);
v___x_2028_ = lean_apply_1(v_ofNat_2027_, v___x_1998_);
v___x_2029_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1986_, v_ctx_1987_, v_p_1995_, v___x_2028_);
return v___x_2029_;
}
else
{
lean_object* v_p_2030_; lean_object* v_m_2031_; lean_object* v_ofNat_2032_; lean_object* v_npow_2033_; lean_object* v_x_2034_; lean_object* v_k_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v_p_2030_ = lean_ctor_get(v_v_1994_, 0);
lean_inc_ref(v_p_2030_);
v_m_2031_ = lean_ctor_get(v_v_1994_, 1);
lean_inc(v_m_2031_);
lean_dec_ref_known(v_v_1994_, 2);
v_ofNat_2032_ = lean_ctor_get(v_toSemiring_1992_, 3);
v_npow_2033_ = lean_ctor_get(v_toSemiring_1992_, 5);
v_x_2034_ = lean_ctor_get(v_p_2030_, 0);
lean_inc(v_x_2034_);
v_k_2035_ = lean_ctor_get(v_p_2030_, 1);
lean_inc(v_k_2035_);
lean_dec_ref(v_p_2030_);
v___x_2036_ = lean_unsigned_to_nat(0u);
v___x_2037_ = lean_nat_dec_eq(v_k_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
uint8_t v___x_2038_; 
v___x_2038_ = lean_nat_dec_eq(v_k_2035_, v___x_1998_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2039_ = l_Lean_RArray_getImpl___redArg(v_ctx_1987_, v_x_2034_);
lean_dec(v_x_2034_);
lean_inc(v_npow_2033_);
v___x_2040_ = lean_apply_2(v_npow_2033_, v___x_2039_, v_k_2035_);
lean_inc_ref(v_toSemiring_1992_);
v___x_2041_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1992_, v_ctx_1987_, v_m_2031_, v___x_2040_);
v___x_2042_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1986_, v_ctx_1987_, v_p_1995_, v___x_2041_);
return v___x_2042_;
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec(v_k_2035_);
v___x_2043_ = l_Lean_RArray_getImpl___redArg(v_ctx_1987_, v_x_2034_);
lean_dec(v_x_2034_);
lean_inc_ref(v_toSemiring_1992_);
v___x_2044_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1992_, v_ctx_1987_, v_m_2031_, v___x_2043_);
v___x_2045_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1986_, v_ctx_1987_, v_p_1995_, v___x_2044_);
return v___x_2045_;
}
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec(v_k_2035_);
lean_dec(v_x_2034_);
lean_inc(v_ofNat_2032_);
v___x_2046_ = lean_apply_1(v_ofNat_2032_, v___x_1998_);
lean_inc_ref(v_toSemiring_1992_);
v___x_2047_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1992_, v_ctx_1987_, v_m_2031_, v___x_2046_);
v___x_2048_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1986_, v_ctx_1987_, v_p_1995_, v___x_2047_);
return v___x_2048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___boxed(lean_object* v_00_u03b1_2049_, lean_object* v_inst_2050_, lean_object* v_ctx_2051_, lean_object* v_p_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Grind_CommRing_Poly_denote_x27(v_00_u03b1_2049_, v_inst_2050_, v_ctx_2051_, v_p_2052_);
lean_dec_ref(v_ctx_2051_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object* v_m_2054_){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2056_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2055_);
lean_ctor_set(v___x_2057_, 1, v_m_2054_);
lean_ctor_set(v___x_2057_, 2, v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object* v_x_2058_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = l_Lean_Grind_CommRing_Mon_ofVar(v_x_2058_);
v___x_2060_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2059_);
return v___x_2060_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_isSorted___closed__0(void){
_start:
{
uint8_t v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = 2;
v___x_2062_ = l_Ordering_ctorIdx(v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_isSorted(lean_object* v_x_2063_){
_start:
{
if (lean_obj_tag(v_x_2063_) == 0)
{
uint8_t v___x_2064_; 
v___x_2064_ = 1;
return v___x_2064_;
}
else
{
lean_object* v_p_2065_; 
v_p_2065_ = lean_ctor_get(v_x_2063_, 2);
if (lean_obj_tag(v_p_2065_) == 0)
{
uint8_t v___x_2066_; 
v___x_2066_ = 1;
return v___x_2066_;
}
else
{
lean_object* v_v_2067_; lean_object* v_v_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v_v_2067_ = lean_ctor_get(v_x_2063_, 1);
v_v_2068_ = lean_ctor_get(v_p_2065_, 1);
v___x_2069_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2067_, v_v_2068_);
v___x_2070_ = l_Ordering_ctorIdx(v___x_2069_);
v___x_2071_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_isSorted___closed__0, &l_Lean_Grind_CommRing_Poly_isSorted___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_isSorted___closed__0);
v___x_2072_ = lean_nat_dec_eq(v___x_2070_, v___x_2071_);
lean_dec(v___x_2070_);
if (v___x_2072_ == 0)
{
return v___x_2072_;
}
else
{
v_x_2063_ = v_p_2065_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isSorted___boxed(lean_object* v_x_2074_){
_start:
{
uint8_t v_res_2075_; lean_object* v_r_2076_; 
v_res_2075_ = l_Lean_Grind_CommRing_Poly_isSorted(v_x_2074_);
lean_dec_ref(v_x_2074_);
v_r_2076_ = lean_box(v_res_2075_);
return v_r_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go(lean_object* v_k_2077_, lean_object* v_a_2078_){
_start:
{
if (lean_obj_tag(v_a_2078_) == 0)
{
lean_object* v_k_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2087_; 
v_k_2079_ = lean_ctor_get(v_a_2078_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_a_2078_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2081_ = v_a_2078_;
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_k_2079_);
lean_dec(v_a_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = lean_int_add(v_k_2079_, v_k_2077_);
lean_dec(v_k_2079_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2083_);
v___x_2085_ = v___x_2081_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_object* v_k_2088_; lean_object* v_v_2089_; lean_object* v_p_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2098_; 
v_k_2088_ = lean_ctor_get(v_a_2078_, 0);
v_v_2089_ = lean_ctor_get(v_a_2078_, 1);
v_p_2090_ = lean_ctor_get(v_a_2078_, 2);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_a_2078_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2092_ = v_a_2078_;
v_isShared_2093_ = v_isSharedCheck_2098_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_p_2090_);
lean_inc(v_v_2089_);
lean_inc(v_k_2088_);
lean_dec(v_a_2078_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2098_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2094_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2077_, v_p_2090_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 2, v___x_2094_);
v___x_2096_ = v___x_2092_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go___boxed(lean_object* v_k_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2099_, v_a_2100_);
lean_dec(v_k_2099_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object* v_p_2102_, lean_object* v_k_2103_){
_start:
{
lean_object* v___x_2104_; uint8_t v___x_2105_; 
v___x_2104_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2105_ = lean_int_dec_eq(v_k_2103_, v___x_2104_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2103_, v_p_2102_);
return v___x_2106_;
}
else
{
return v_p_2102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst___boxed(lean_object* v_p_2107_, lean_object* v_k_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2107_, v_k_2108_);
lean_dec(v_k_2108_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object* v_p_2110_, lean_object* v_h__1_2111_, lean_object* v_h__2_2112_){
_start:
{
if (lean_obj_tag(v_p_2110_) == 0)
{
lean_object* v_k_2113_; lean_object* v___x_2114_; 
lean_dec(v_h__2_2112_);
v_k_2113_ = lean_ctor_get(v_p_2110_, 0);
lean_inc(v_k_2113_);
lean_dec_ref_known(v_p_2110_, 1);
v___x_2114_ = lean_apply_1(v_h__1_2111_, v_k_2113_);
return v___x_2114_;
}
else
{
lean_object* v_k_2115_; lean_object* v_v_2116_; lean_object* v_p_2117_; lean_object* v___x_2118_; 
lean_dec(v_h__1_2111_);
v_k_2115_ = lean_ctor_get(v_p_2110_, 0);
lean_inc(v_k_2115_);
v_v_2116_ = lean_ctor_get(v_p_2110_, 1);
lean_inc(v_v_2116_);
v_p_2117_ = lean_ctor_get(v_p_2110_, 2);
lean_inc_ref(v_p_2117_);
lean_dec_ref_known(v_p_2110_, 3);
v___x_2118_ = lean_apply_3(v_h__2_2112_, v_k_2115_, v_v_2116_, v_p_2117_);
return v___x_2118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object* v_motive_2119_, lean_object* v_p_2120_, lean_object* v_h__1_2121_, lean_object* v_h__2_2122_){
_start:
{
if (lean_obj_tag(v_p_2120_) == 0)
{
lean_object* v_k_2123_; lean_object* v___x_2124_; 
lean_dec(v_h__2_2122_);
v_k_2123_ = lean_ctor_get(v_p_2120_, 0);
lean_inc(v_k_2123_);
lean_dec_ref_known(v_p_2120_, 1);
v___x_2124_ = lean_apply_1(v_h__1_2121_, v_k_2123_);
return v___x_2124_;
}
else
{
lean_object* v_k_2125_; lean_object* v_v_2126_; lean_object* v_p_2127_; lean_object* v___x_2128_; 
lean_dec(v_h__1_2121_);
v_k_2125_ = lean_ctor_get(v_p_2120_, 0);
lean_inc(v_k_2125_);
v_v_2126_ = lean_ctor_get(v_p_2120_, 1);
lean_inc(v_v_2126_);
v_p_2127_ = lean_ctor_get(v_p_2120_, 2);
lean_inc_ref(v_p_2127_);
lean_dec_ref_known(v_p_2120_, 3);
v___x_2128_ = lean_apply_3(v_h__2_2122_, v_k_2125_, v_v_2126_, v_p_2127_);
return v___x_2128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert_go(lean_object* v_k_2129_, lean_object* v_m_2130_, lean_object* v_a_2131_){
_start:
{
if (lean_obj_tag(v_a_2131_) == 0)
{
lean_object* v___x_2132_; 
v___x_2132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2132_, 0, v_k_2129_);
lean_ctor_set(v___x_2132_, 1, v_m_2130_);
lean_ctor_set(v___x_2132_, 2, v_a_2131_);
return v___x_2132_;
}
else
{
lean_object* v_k_2133_; lean_object* v_v_2134_; lean_object* v_p_2135_; uint8_t v___x_2136_; 
v_k_2133_ = lean_ctor_get(v_a_2131_, 0);
v_v_2134_ = lean_ctor_get(v_a_2131_, 1);
v_p_2135_ = lean_ctor_get(v_a_2131_, 2);
v___x_2136_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2130_, v_v_2134_);
switch(v___x_2136_)
{
case 0:
{
lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2144_; 
lean_inc_ref(v_p_2135_);
lean_inc(v_v_2134_);
lean_inc(v_k_2133_);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_a_2131_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; lean_object* v_unused_2146_; lean_object* v_unused_2147_; 
v_unused_2145_ = lean_ctor_get(v_a_2131_, 2);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_a_2131_, 1);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v_a_2131_, 0);
lean_dec(v_unused_2147_);
v___x_2138_ = v_a_2131_;
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
else
{
lean_dec(v_a_2131_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2129_, v_m_2130_, v_p_2135_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 2, v___x_2140_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_k_2133_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_v_2134_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
case 1:
{
lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2157_; 
lean_inc_ref(v_p_2135_);
lean_inc(v_k_2133_);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_a_2131_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; lean_object* v_unused_2159_; lean_object* v_unused_2160_; 
v_unused_2158_ = lean_ctor_get(v_a_2131_, 2);
lean_dec(v_unused_2158_);
v_unused_2159_ = lean_ctor_get(v_a_2131_, 1);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_a_2131_, 0);
lean_dec(v_unused_2160_);
v___x_2149_ = v_a_2131_;
v_isShared_2150_ = v_isSharedCheck_2157_;
goto v_resetjp_2148_;
}
else
{
lean_dec(v_a_2131_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2157_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v_k_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; 
v_k_2151_ = lean_int_add(v_k_2129_, v_k_2133_);
lean_dec(v_k_2133_);
lean_dec(v_k_2129_);
v___x_2152_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2153_ = lean_int_dec_eq(v_k_2151_, v___x_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2155_; 
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 1, v_m_2130_);
lean_ctor_set(v___x_2149_, 0, v_k_2151_);
v___x_2155_ = v___x_2149_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_k_2151_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_m_2130_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_p_2135_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
else
{
lean_dec(v_k_2151_);
lean_del_object(v___x_2149_);
lean_dec(v_m_2130_);
return v_p_2135_;
}
}
}
default: 
{
lean_object* v___x_2161_; 
v___x_2161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2161_, 0, v_k_2129_);
lean_ctor_set(v___x_2161_, 1, v_m_2130_);
lean_ctor_set(v___x_2161_, 2, v_a_2131_);
return v___x_2161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert(lean_object* v_k_2162_, lean_object* v_m_2163_, lean_object* v_p_2164_){
_start:
{
lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2166_ = lean_int_dec_eq(v_k_2162_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = lean_box(0);
v___x_2168_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2163_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2162_, v_m_2163_, v_p_2164_);
return v___x_2169_;
}
else
{
lean_object* v___x_2170_; 
lean_dec(v_m_2163_);
v___x_2170_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2164_, v_k_2162_);
lean_dec(v_k_2162_);
return v___x_2170_;
}
}
else
{
lean_dec(v_m_2163_);
lean_dec(v_k_2162_);
return v_p_2164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_concat(lean_object* v_p_u2081_2171_, lean_object* v_p_u2082_2172_){
_start:
{
if (lean_obj_tag(v_p_u2081_2171_) == 0)
{
lean_object* v_k_2173_; lean_object* v___x_2174_; 
v_k_2173_ = lean_ctor_get(v_p_u2081_2171_, 0);
lean_inc(v_k_2173_);
lean_dec_ref_known(v_p_u2081_2171_, 1);
v___x_2174_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2172_, v_k_2173_);
lean_dec(v_k_2173_);
return v___x_2174_;
}
else
{
lean_object* v_k_2175_; lean_object* v_v_2176_; lean_object* v_p_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2185_; 
v_k_2175_ = lean_ctor_get(v_p_u2081_2171_, 0);
v_v_2176_ = lean_ctor_get(v_p_u2081_2171_, 1);
v_p_2177_ = lean_ctor_get(v_p_u2081_2171_, 2);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_p_u2081_2171_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2179_ = v_p_u2081_2171_;
v_isShared_2180_ = v_isSharedCheck_2185_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_p_2177_);
lean_inc(v_v_2176_);
lean_inc(v_k_2175_);
lean_dec(v_p_u2081_2171_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2185_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2181_ = l_Lean_Grind_CommRing_Poly_concat(v_p_2177_, v_p_u2082_2172_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 2, v___x_2181_);
v___x_2183_ = v___x_2179_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2184_, 2, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go(lean_object* v_k_2186_, lean_object* v_a_2187_){
_start:
{
if (lean_obj_tag(v_a_2187_) == 0)
{
lean_object* v_k_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2196_; 
v_k_2188_ = lean_ctor_get(v_a_2187_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_a_2187_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2190_ = v_a_2187_;
v_isShared_2191_ = v_isSharedCheck_2196_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_k_2188_);
lean_dec(v_a_2187_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2196_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2192_ = lean_int_mul(v_k_2186_, v_k_2188_);
lean_dec(v_k_2188_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2192_);
v___x_2194_ = v___x_2190_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
else
{
lean_object* v_k_2197_; lean_object* v_v_2198_; lean_object* v_p_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2208_; 
v_k_2197_ = lean_ctor_get(v_a_2187_, 0);
v_v_2198_ = lean_ctor_get(v_a_2187_, 1);
v_p_2199_ = lean_ctor_get(v_a_2187_, 2);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_a_2187_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2201_ = v_a_2187_;
v_isShared_2202_ = v_isSharedCheck_2208_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_p_2199_);
lean_inc(v_v_2198_);
lean_inc(v_k_2197_);
lean_dec(v_a_2187_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2208_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2203_ = lean_int_mul(v_k_2186_, v_k_2197_);
lean_dec(v_k_2197_);
v___x_2204_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2186_, v_p_2199_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 2, v___x_2204_);
lean_ctor_set(v___x_2201_, 0, v___x_2203_);
v___x_2206_ = v___x_2201_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_v_2198_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go___boxed(lean_object* v_k_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2209_, v_a_2210_);
lean_dec(v_k_2209_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object* v_k_2212_, lean_object* v_p_2213_){
_start:
{
lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___x_2214_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2215_ = lean_int_dec_eq(v_k_2212_, v___x_2214_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2217_ = lean_int_dec_eq(v_k_2212_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2212_, v_p_2213_);
return v___x_2218_;
}
else
{
return v_p_2213_;
}
}
else
{
lean_object* v___x_2219_; 
lean_dec_ref(v_p_2213_);
v___x_2219_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst___boxed(lean_object* v_k_2220_, lean_object* v_p_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2220_, v_p_2221_);
lean_dec(v_k_2220_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go(lean_object* v_k_2223_, lean_object* v_m_2224_, lean_object* v_a_2225_){
_start:
{
if (lean_obj_tag(v_a_2225_) == 0)
{
lean_object* v_k_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v_k_2226_ = lean_ctor_get(v_a_2225_, 0);
lean_inc(v_k_2226_);
lean_dec_ref_known(v_a_2225_, 1);
v___x_2227_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2228_ = lean_int_dec_eq(v_k_2226_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = lean_int_mul(v_k_2223_, v_k_2226_);
lean_dec(v_k_2226_);
v___x_2230_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2231_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2229_);
lean_ctor_set(v___x_2231_, 1, v_m_2224_);
lean_ctor_set(v___x_2231_, 2, v___x_2230_);
return v___x_2231_;
}
else
{
lean_object* v___x_2232_; 
lean_dec(v_k_2226_);
lean_dec(v_m_2224_);
v___x_2232_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2232_;
}
}
else
{
lean_object* v_k_2233_; lean_object* v_v_2234_; lean_object* v_p_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2245_; 
v_k_2233_ = lean_ctor_get(v_a_2225_, 0);
v_v_2234_ = lean_ctor_get(v_a_2225_, 1);
v_p_2235_ = lean_ctor_get(v_a_2225_, 2);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_a_2225_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2237_ = v_a_2225_;
v_isShared_2238_ = v_isSharedCheck_2245_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_p_2235_);
lean_inc(v_v_2234_);
lean_inc(v_k_2233_);
lean_dec(v_a_2225_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2245_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2239_ = lean_int_mul(v_k_2223_, v_k_2233_);
lean_dec(v_k_2233_);
lean_inc(v_m_2224_);
v___x_2240_ = l_Lean_Grind_CommRing_Mon_mul(v_m_2224_, v_v_2234_);
v___x_2241_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2223_, v_m_2224_, v_p_2235_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 2, v___x_2241_);
lean_ctor_set(v___x_2237_, 1, v___x_2240_);
lean_ctor_set(v___x_2237_, 0, v___x_2239_);
v___x_2243_ = v___x_2237_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2239_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2244_, 2, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go___boxed(lean_object* v_k_2246_, lean_object* v_m_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2246_, v_m_2247_, v_a_2248_);
lean_dec(v_k_2246_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object* v_k_2250_, lean_object* v_m_2251_, lean_object* v_p_2252_){
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
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2250_, v_m_2251_, v_p_2252_);
return v___x_2257_;
}
else
{
lean_object* v___x_2258_; 
lean_dec(v_m_2251_);
v___x_2258_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2250_, v_p_2252_);
return v___x_2258_;
}
}
else
{
lean_object* v___x_2259_; 
lean_dec_ref(v_p_2252_);
lean_dec(v_m_2251_);
v___x_2259_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon___boxed(lean_object* v_k_2260_, lean_object* v_m_2261_, lean_object* v_p_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2260_, v_m_2261_, v_p_2262_);
lean_dec(v_k_2260_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go(lean_object* v_k_2264_, lean_object* v_m_2265_, lean_object* v_p_2266_, lean_object* v_acc_2267_){
_start:
{
if (lean_obj_tag(v_p_2266_) == 0)
{
lean_object* v_k_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v_k_2268_ = lean_ctor_get(v_p_2266_, 0);
lean_inc(v_k_2268_);
lean_dec_ref_known(v_p_2266_, 1);
v___x_2269_ = lean_int_mul(v_k_2264_, v_k_2268_);
lean_dec(v_k_2268_);
v___x_2270_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2269_, v_m_2265_, v_acc_2267_);
return v___x_2270_;
}
else
{
lean_object* v_k_2271_; lean_object* v_v_2272_; lean_object* v_p_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v_k_2271_ = lean_ctor_get(v_p_2266_, 0);
lean_inc(v_k_2271_);
v_v_2272_ = lean_ctor_get(v_p_2266_, 1);
lean_inc(v_v_2272_);
v_p_2273_ = lean_ctor_get(v_p_2266_, 2);
lean_inc_ref(v_p_2273_);
lean_dec_ref_known(v_p_2266_, 3);
v___x_2274_ = lean_int_mul(v_k_2264_, v_k_2271_);
lean_dec(v_k_2271_);
lean_inc(v_m_2265_);
v___x_2275_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_2265_, v_v_2272_);
v___x_2276_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2274_, v___x_2275_, v_acc_2267_);
v_p_2266_ = v_p_2273_;
v_acc_2267_ = v___x_2276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go___boxed(lean_object* v_k_2278_, lean_object* v_m_2279_, lean_object* v_p_2280_, lean_object* v_acc_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2278_, v_m_2279_, v_p_2280_, v_acc_2281_);
lean_dec(v_k_2278_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc(lean_object* v_k_2283_, lean_object* v_m_2284_, lean_object* v_p_2285_){
_start:
{
lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2286_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2287_ = lean_int_dec_eq(v_k_2283_, v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2288_ = lean_box(0);
v___x_2289_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2284_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2291_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2283_, v_m_2284_, v_p_2285_, v___x_2290_);
return v___x_2291_;
}
else
{
lean_object* v___x_2292_; 
lean_dec(v_m_2284_);
v___x_2292_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2283_, v_p_2285_);
return v___x_2292_;
}
}
else
{
lean_object* v___x_2293_; 
lean_dec_ref(v_p_2285_);
lean_dec(v_m_2284_);
v___x_2293_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc___boxed(lean_object* v_k_2294_, lean_object* v_m_2295_, lean_object* v_p_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2294_, v_m_2295_, v_p_2296_);
lean_dec(v_k_2294_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_go(lean_object* v_fuel_2298_, lean_object* v_p_u2081_2299_, lean_object* v_p_u2082_2300_){
_start:
{
lean_object* v_zero_2301_; uint8_t v_isZero_2302_; 
v_zero_2301_ = lean_unsigned_to_nat(0u);
v_isZero_2302_ = lean_nat_dec_eq(v_fuel_2298_, v_zero_2301_);
if (v_isZero_2302_ == 1)
{
lean_object* v___x_2303_; 
lean_dec(v_fuel_2298_);
v___x_2303_ = l_Lean_Grind_CommRing_Poly_concat(v_p_u2081_2299_, v_p_u2082_2300_);
return v___x_2303_;
}
else
{
if (lean_obj_tag(v_p_u2081_2299_) == 0)
{
lean_dec(v_fuel_2298_);
if (lean_obj_tag(v_p_u2082_2300_) == 0)
{
lean_object* v_k_2304_; lean_object* v_k_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2313_; 
v_k_2304_ = lean_ctor_get(v_p_u2081_2299_, 0);
lean_inc(v_k_2304_);
lean_dec_ref_known(v_p_u2081_2299_, 1);
v_k_2305_ = lean_ctor_get(v_p_u2082_2300_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_p_u2082_2300_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2307_ = v_p_u2082_2300_;
v_isShared_2308_ = v_isSharedCheck_2313_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_k_2305_);
lean_dec(v_p_u2082_2300_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2313_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
v___x_2309_ = lean_int_add(v_k_2304_, v_k_2305_);
lean_dec(v_k_2305_);
lean_dec(v_k_2304_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2309_);
v___x_2311_ = v___x_2307_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
else
{
lean_object* v_k_2314_; lean_object* v___x_2315_; 
v_k_2314_ = lean_ctor_get(v_p_u2081_2299_, 0);
lean_inc(v_k_2314_);
lean_dec_ref_known(v_p_u2081_2299_, 1);
v___x_2315_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2300_, v_k_2314_);
lean_dec(v_k_2314_);
return v___x_2315_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_2300_) == 0)
{
lean_object* v_k_2316_; lean_object* v___x_2317_; 
lean_dec(v_fuel_2298_);
v_k_2316_ = lean_ctor_get(v_p_u2082_2300_, 0);
lean_inc(v_k_2316_);
lean_dec_ref_known(v_p_u2082_2300_, 1);
v___x_2317_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2081_2299_, v_k_2316_);
lean_dec(v_k_2316_);
return v___x_2317_;
}
else
{
lean_object* v_k_2318_; lean_object* v_v_2319_; lean_object* v_p_2320_; lean_object* v_k_2321_; lean_object* v_v_2322_; lean_object* v_p_2323_; lean_object* v_one_2324_; lean_object* v_n_2325_; uint8_t v___x_2326_; 
v_k_2318_ = lean_ctor_get(v_p_u2081_2299_, 0);
v_v_2319_ = lean_ctor_get(v_p_u2081_2299_, 1);
v_p_2320_ = lean_ctor_get(v_p_u2081_2299_, 2);
v_k_2321_ = lean_ctor_get(v_p_u2082_2300_, 0);
v_v_2322_ = lean_ctor_get(v_p_u2082_2300_, 1);
v_p_2323_ = lean_ctor_get(v_p_u2082_2300_, 2);
v_one_2324_ = lean_unsigned_to_nat(1u);
v_n_2325_ = lean_nat_sub(v_fuel_2298_, v_one_2324_);
lean_dec(v_fuel_2298_);
v___x_2326_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2319_, v_v_2322_);
switch(v___x_2326_)
{
case 0:
{
lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2334_; 
lean_inc_ref(v_p_2323_);
lean_inc(v_v_2322_);
lean_inc(v_k_2321_);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_p_u2082_2300_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; lean_object* v_unused_2336_; lean_object* v_unused_2337_; 
v_unused_2335_ = lean_ctor_get(v_p_u2082_2300_, 2);
lean_dec(v_unused_2335_);
v_unused_2336_ = lean_ctor_get(v_p_u2082_2300_, 1);
lean_dec(v_unused_2336_);
v_unused_2337_ = lean_ctor_get(v_p_u2082_2300_, 0);
lean_dec(v_unused_2337_);
v___x_2328_ = v_p_u2082_2300_;
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
else
{
lean_dec(v_p_u2082_2300_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2330_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2325_, v_p_u2081_2299_, v_p_2323_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 2, v___x_2330_);
v___x_2332_ = v___x_2328_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_k_2321_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_v_2322_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
case 1:
{
lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2349_; 
lean_inc_ref(v_p_2323_);
lean_inc(v_k_2321_);
lean_inc_ref(v_p_2320_);
lean_inc(v_v_2319_);
lean_inc(v_k_2318_);
lean_dec_ref_known(v_p_u2081_2299_, 3);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_p_u2082_2300_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; lean_object* v_unused_2351_; lean_object* v_unused_2352_; 
v_unused_2350_ = lean_ctor_get(v_p_u2082_2300_, 2);
lean_dec(v_unused_2350_);
v_unused_2351_ = lean_ctor_get(v_p_u2082_2300_, 1);
lean_dec(v_unused_2351_);
v_unused_2352_ = lean_ctor_get(v_p_u2082_2300_, 0);
lean_dec(v_unused_2352_);
v___x_2339_ = v_p_u2082_2300_;
v_isShared_2340_ = v_isSharedCheck_2349_;
goto v_resetjp_2338_;
}
else
{
lean_dec(v_p_u2082_2300_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2349_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_k_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v_k_2341_ = lean_int_add(v_k_2318_, v_k_2321_);
lean_dec(v_k_2321_);
lean_dec(v_k_2318_);
v___x_2342_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2343_ = lean_int_dec_eq(v_k_2341_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2346_; 
v___x_2344_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2325_, v_p_2320_, v_p_2323_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 2, v___x_2344_);
lean_ctor_set(v___x_2339_, 1, v_v_2319_);
lean_ctor_set(v___x_2339_, 0, v_k_2341_);
v___x_2346_ = v___x_2339_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_k_2341_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_v_2319_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v___x_2344_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
else
{
lean_dec(v_k_2341_);
lean_del_object(v___x_2339_);
lean_dec(v_v_2319_);
v_fuel_2298_ = v_n_2325_;
v_p_u2081_2299_ = v_p_2320_;
v_p_u2082_2300_ = v_p_2323_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2360_; 
lean_inc_ref(v_p_2320_);
lean_inc(v_v_2319_);
lean_inc(v_k_2318_);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_p_u2081_2299_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; lean_object* v_unused_2362_; lean_object* v_unused_2363_; 
v_unused_2361_ = lean_ctor_get(v_p_u2081_2299_, 2);
lean_dec(v_unused_2361_);
v_unused_2362_ = lean_ctor_get(v_p_u2081_2299_, 1);
lean_dec(v_unused_2362_);
v_unused_2363_ = lean_ctor_get(v_p_u2081_2299_, 0);
lean_dec(v_unused_2363_);
v___x_2354_ = v_p_u2081_2299_;
v_isShared_2355_ = v_isSharedCheck_2360_;
goto v_resetjp_2353_;
}
else
{
lean_dec(v_p_u2081_2299_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2360_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2356_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2325_, v_p_2320_, v_p_u2082_2300_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 2, v___x_2356_);
v___x_2358_ = v___x_2354_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_k_2318_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_v_2319_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object* v_p_u2081_2364_, lean_object* v_p_u2082_2365_){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_unsigned_to_nat(1000000u);
v___x_2367_ = l_Lean_Grind_CommRing_Poly_combine_go(v___x_2366_, v_p_u2081_2364_, v_p_u2082_2365_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object* v_p_u2081_2368_, lean_object* v_p_u2082_2369_, lean_object* v_h__1_2370_, lean_object* v_h__2_2371_, lean_object* v_h__3_2372_, lean_object* v_h__4_2373_){
_start:
{
if (lean_obj_tag(v_p_u2081_2368_) == 0)
{
lean_dec(v_h__4_2373_);
lean_dec(v_h__3_2372_);
if (lean_obj_tag(v_p_u2082_2369_) == 0)
{
lean_object* v_k_2374_; lean_object* v_k_2375_; lean_object* v___x_2376_; 
lean_dec(v_h__2_2371_);
v_k_2374_ = lean_ctor_get(v_p_u2081_2368_, 0);
lean_inc(v_k_2374_);
lean_dec_ref_known(v_p_u2081_2368_, 1);
v_k_2375_ = lean_ctor_get(v_p_u2082_2369_, 0);
lean_inc(v_k_2375_);
lean_dec_ref_known(v_p_u2082_2369_, 1);
v___x_2376_ = lean_apply_2(v_h__1_2370_, v_k_2374_, v_k_2375_);
return v___x_2376_;
}
else
{
lean_object* v_k_2377_; lean_object* v_k_2378_; lean_object* v_v_2379_; lean_object* v_p_2380_; lean_object* v___x_2381_; 
lean_dec(v_h__1_2370_);
v_k_2377_ = lean_ctor_get(v_p_u2081_2368_, 0);
lean_inc(v_k_2377_);
lean_dec_ref_known(v_p_u2081_2368_, 1);
v_k_2378_ = lean_ctor_get(v_p_u2082_2369_, 0);
lean_inc(v_k_2378_);
v_v_2379_ = lean_ctor_get(v_p_u2082_2369_, 1);
lean_inc(v_v_2379_);
v_p_2380_ = lean_ctor_get(v_p_u2082_2369_, 2);
lean_inc_ref(v_p_2380_);
lean_dec_ref_known(v_p_u2082_2369_, 3);
v___x_2381_ = lean_apply_4(v_h__2_2371_, v_k_2377_, v_k_2378_, v_v_2379_, v_p_2380_);
return v___x_2381_;
}
}
else
{
lean_dec(v_h__2_2371_);
lean_dec(v_h__1_2370_);
if (lean_obj_tag(v_p_u2082_2369_) == 0)
{
lean_object* v_k_2382_; lean_object* v_v_2383_; lean_object* v_p_2384_; lean_object* v_k_2385_; lean_object* v___x_2386_; 
lean_dec(v_h__4_2373_);
v_k_2382_ = lean_ctor_get(v_p_u2081_2368_, 0);
lean_inc(v_k_2382_);
v_v_2383_ = lean_ctor_get(v_p_u2081_2368_, 1);
lean_inc(v_v_2383_);
v_p_2384_ = lean_ctor_get(v_p_u2081_2368_, 2);
lean_inc_ref(v_p_2384_);
lean_dec_ref_known(v_p_u2081_2368_, 3);
v_k_2385_ = lean_ctor_get(v_p_u2082_2369_, 0);
lean_inc(v_k_2385_);
lean_dec_ref_known(v_p_u2082_2369_, 1);
v___x_2386_ = lean_apply_4(v_h__3_2372_, v_k_2382_, v_v_2383_, v_p_2384_, v_k_2385_);
return v___x_2386_;
}
else
{
lean_object* v_k_2387_; lean_object* v_v_2388_; lean_object* v_p_2389_; lean_object* v_k_2390_; lean_object* v_v_2391_; lean_object* v_p_2392_; lean_object* v___x_2393_; 
lean_dec(v_h__3_2372_);
v_k_2387_ = lean_ctor_get(v_p_u2081_2368_, 0);
lean_inc(v_k_2387_);
v_v_2388_ = lean_ctor_get(v_p_u2081_2368_, 1);
lean_inc(v_v_2388_);
v_p_2389_ = lean_ctor_get(v_p_u2081_2368_, 2);
lean_inc_ref(v_p_2389_);
lean_dec_ref_known(v_p_u2081_2368_, 3);
v_k_2390_ = lean_ctor_get(v_p_u2082_2369_, 0);
lean_inc(v_k_2390_);
v_v_2391_ = lean_ctor_get(v_p_u2082_2369_, 1);
lean_inc(v_v_2391_);
v_p_2392_ = lean_ctor_get(v_p_u2082_2369_, 2);
lean_inc_ref(v_p_2392_);
lean_dec_ref_known(v_p_u2082_2369_, 3);
v___x_2393_ = lean_apply_6(v_h__4_2373_, v_k_2387_, v_v_2388_, v_p_2389_, v_k_2390_, v_v_2391_, v_p_2392_);
return v___x_2393_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object* v_motive_2394_, lean_object* v_p_u2081_2395_, lean_object* v_p_u2082_2396_, lean_object* v_h__1_2397_, lean_object* v_h__2_2398_, lean_object* v_h__3_2399_, lean_object* v_h__4_2400_){
_start:
{
if (lean_obj_tag(v_p_u2081_2395_) == 0)
{
lean_dec(v_h__4_2400_);
lean_dec(v_h__3_2399_);
if (lean_obj_tag(v_p_u2082_2396_) == 0)
{
lean_object* v_k_2401_; lean_object* v_k_2402_; lean_object* v___x_2403_; 
lean_dec(v_h__2_2398_);
v_k_2401_ = lean_ctor_get(v_p_u2081_2395_, 0);
lean_inc(v_k_2401_);
lean_dec_ref_known(v_p_u2081_2395_, 1);
v_k_2402_ = lean_ctor_get(v_p_u2082_2396_, 0);
lean_inc(v_k_2402_);
lean_dec_ref_known(v_p_u2082_2396_, 1);
v___x_2403_ = lean_apply_2(v_h__1_2397_, v_k_2401_, v_k_2402_);
return v___x_2403_;
}
else
{
lean_object* v_k_2404_; lean_object* v_k_2405_; lean_object* v_v_2406_; lean_object* v_p_2407_; lean_object* v___x_2408_; 
lean_dec(v_h__1_2397_);
v_k_2404_ = lean_ctor_get(v_p_u2081_2395_, 0);
lean_inc(v_k_2404_);
lean_dec_ref_known(v_p_u2081_2395_, 1);
v_k_2405_ = lean_ctor_get(v_p_u2082_2396_, 0);
lean_inc(v_k_2405_);
v_v_2406_ = lean_ctor_get(v_p_u2082_2396_, 1);
lean_inc(v_v_2406_);
v_p_2407_ = lean_ctor_get(v_p_u2082_2396_, 2);
lean_inc_ref(v_p_2407_);
lean_dec_ref_known(v_p_u2082_2396_, 3);
v___x_2408_ = lean_apply_4(v_h__2_2398_, v_k_2404_, v_k_2405_, v_v_2406_, v_p_2407_);
return v___x_2408_;
}
}
else
{
lean_dec(v_h__2_2398_);
lean_dec(v_h__1_2397_);
if (lean_obj_tag(v_p_u2082_2396_) == 0)
{
lean_object* v_k_2409_; lean_object* v_v_2410_; lean_object* v_p_2411_; lean_object* v_k_2412_; lean_object* v___x_2413_; 
lean_dec(v_h__4_2400_);
v_k_2409_ = lean_ctor_get(v_p_u2081_2395_, 0);
lean_inc(v_k_2409_);
v_v_2410_ = lean_ctor_get(v_p_u2081_2395_, 1);
lean_inc(v_v_2410_);
v_p_2411_ = lean_ctor_get(v_p_u2081_2395_, 2);
lean_inc_ref(v_p_2411_);
lean_dec_ref_known(v_p_u2081_2395_, 3);
v_k_2412_ = lean_ctor_get(v_p_u2082_2396_, 0);
lean_inc(v_k_2412_);
lean_dec_ref_known(v_p_u2082_2396_, 1);
v___x_2413_ = lean_apply_4(v_h__3_2399_, v_k_2409_, v_v_2410_, v_p_2411_, v_k_2412_);
return v___x_2413_;
}
else
{
lean_object* v_k_2414_; lean_object* v_v_2415_; lean_object* v_p_2416_; lean_object* v_k_2417_; lean_object* v_v_2418_; lean_object* v_p_2419_; lean_object* v___x_2420_; 
lean_dec(v_h__3_2399_);
v_k_2414_ = lean_ctor_get(v_p_u2081_2395_, 0);
lean_inc(v_k_2414_);
v_v_2415_ = lean_ctor_get(v_p_u2081_2395_, 1);
lean_inc(v_v_2415_);
v_p_2416_ = lean_ctor_get(v_p_u2081_2395_, 2);
lean_inc_ref(v_p_2416_);
lean_dec_ref_known(v_p_u2081_2395_, 3);
v_k_2417_ = lean_ctor_get(v_p_u2082_2396_, 0);
lean_inc(v_k_2417_);
v_v_2418_ = lean_ctor_get(v_p_u2082_2396_, 1);
lean_inc(v_v_2418_);
v_p_2419_ = lean_ctor_get(v_p_u2082_2396_, 2);
lean_inc_ref(v_p_2419_);
lean_dec_ref_known(v_p_u2082_2396_, 3);
v___x_2420_ = lean_apply_6(v_h__4_2400_, v_k_2414_, v_v_2415_, v_p_2416_, v_k_2417_, v_v_2418_, v_p_2419_);
return v___x_2420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t v_x_2421_, lean_object* v_h__1_2422_, lean_object* v_h__2_2423_, lean_object* v_h__3_2424_){
_start:
{
switch(v_x_2421_)
{
case 0:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_dec(v_h__2_2423_);
lean_dec(v_h__1_2422_);
v___x_2425_ = lean_box(0);
v___x_2426_ = lean_apply_1(v_h__3_2424_, v___x_2425_);
return v___x_2426_;
}
case 1:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_dec(v_h__3_2424_);
lean_dec(v_h__2_2423_);
v___x_2427_ = lean_box(0);
v___x_2428_ = lean_apply_1(v_h__1_2422_, v___x_2427_);
return v___x_2428_;
}
default: 
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_dec(v_h__3_2424_);
lean_dec(v_h__1_2422_);
v___x_2429_ = lean_box(0);
v___x_2430_ = lean_apply_1(v_h__2_2423_, v___x_2429_);
return v___x_2430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object* v_x_2431_, lean_object* v_h__1_2432_, lean_object* v_h__2_2433_, lean_object* v_h__3_2434_){
_start:
{
uint8_t v_x_33__boxed_2435_; lean_object* v_res_2436_; 
v_x_33__boxed_2435_ = lean_unbox(v_x_2431_);
v_res_2436_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(v_x_33__boxed_2435_, v_h__1_2432_, v_h__2_2433_, v_h__3_2434_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object* v_motive_2437_, uint8_t v_x_2438_, lean_object* v_h__1_2439_, lean_object* v_h__2_2440_, lean_object* v_h__3_2441_){
_start:
{
switch(v_x_2438_)
{
case 0:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
lean_dec(v_h__2_2440_);
lean_dec(v_h__1_2439_);
v___x_2442_ = lean_box(0);
v___x_2443_ = lean_apply_1(v_h__3_2441_, v___x_2442_);
return v___x_2443_;
}
case 1:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
lean_dec(v_h__3_2441_);
lean_dec(v_h__2_2440_);
v___x_2444_ = lean_box(0);
v___x_2445_ = lean_apply_1(v_h__1_2439_, v___x_2444_);
return v___x_2445_;
}
default: 
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_dec(v_h__3_2441_);
lean_dec(v_h__1_2439_);
v___x_2446_ = lean_box(0);
v___x_2447_ = lean_apply_1(v_h__2_2440_, v___x_2446_);
return v___x_2447_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object* v_motive_2448_, lean_object* v_x_2449_, lean_object* v_h__1_2450_, lean_object* v_h__2_2451_, lean_object* v_h__3_2452_){
_start:
{
uint8_t v_x_48__boxed_2453_; lean_object* v_res_2454_; 
v_x_48__boxed_2453_ = lean_unbox(v_x_2449_);
v_res_2454_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(v_motive_2448_, v_x_48__boxed_2453_, v_h__1_2450_, v_h__2_2451_, v_h__3_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul_go(lean_object* v_p_u2082_2455_, lean_object* v_p_u2081_2456_, lean_object* v_acc_2457_){
_start:
{
if (lean_obj_tag(v_p_u2081_2456_) == 0)
{
lean_object* v_k_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_k_2458_ = lean_ctor_get(v_p_u2081_2456_, 0);
lean_inc(v_k_2458_);
lean_dec_ref_known(v_p_u2081_2456_, 1);
v___x_2459_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2458_, v_p_u2082_2455_);
lean_dec(v_k_2458_);
v___x_2460_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2457_, v___x_2459_);
return v___x_2460_;
}
else
{
lean_object* v_k_2461_; lean_object* v_v_2462_; lean_object* v_p_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_k_2461_ = lean_ctor_get(v_p_u2081_2456_, 0);
lean_inc(v_k_2461_);
v_v_2462_ = lean_ctor_get(v_p_u2081_2456_, 1);
lean_inc(v_v_2462_);
v_p_2463_ = lean_ctor_get(v_p_u2081_2456_, 2);
lean_inc_ref(v_p_2463_);
lean_dec_ref_known(v_p_u2081_2456_, 3);
lean_inc_ref(v_p_u2082_2455_);
v___x_2464_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2461_, v_v_2462_, v_p_u2082_2455_);
lean_dec(v_k_2461_);
v___x_2465_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2457_, v___x_2464_);
v_p_u2081_2456_ = v_p_2463_;
v_acc_2457_ = v___x_2465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul(lean_object* v_p_u2081_2467_, lean_object* v_p_u2082_2468_){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2470_ = l_Lean_Grind_CommRing_Poly_mul_go(v_p_u2082_2468_, v_p_u2081_2467_, v___x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc_go(lean_object* v_p_u2082_2471_, lean_object* v_p_u2081_2472_, lean_object* v_acc_2473_){
_start:
{
if (lean_obj_tag(v_p_u2081_2472_) == 0)
{
lean_object* v_k_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_k_2474_ = lean_ctor_get(v_p_u2081_2472_, 0);
lean_inc(v_k_2474_);
lean_dec_ref_known(v_p_u2081_2472_, 1);
v___x_2475_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2474_, v_p_u2082_2471_);
lean_dec(v_k_2474_);
v___x_2476_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2473_, v___x_2475_);
return v___x_2476_;
}
else
{
lean_object* v_k_2477_; lean_object* v_v_2478_; lean_object* v_p_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_k_2477_ = lean_ctor_get(v_p_u2081_2472_, 0);
lean_inc(v_k_2477_);
v_v_2478_ = lean_ctor_get(v_p_u2081_2472_, 1);
lean_inc(v_v_2478_);
v_p_2479_ = lean_ctor_get(v_p_u2081_2472_, 2);
lean_inc_ref(v_p_2479_);
lean_dec_ref_known(v_p_u2081_2472_, 3);
lean_inc_ref(v_p_u2082_2471_);
v___x_2480_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2477_, v_v_2478_, v_p_u2082_2471_);
lean_dec(v_k_2477_);
v___x_2481_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2473_, v___x_2480_);
v_p_u2081_2472_ = v_p_2479_;
v_acc_2473_ = v___x_2481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object* v_p_u2081_2483_, lean_object* v_p_u2082_2484_){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2486_ = l_Lean_Grind_CommRing_Poly_mul__nc_go(v_p_u2082_2484_, v_p_u2081_2483_, v___x_2485_);
return v___x_2486_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_pow___closed__0(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow(lean_object* v_p_2489_, lean_object* v_k_2490_){
_start:
{
lean_object* v_zero_2491_; uint8_t v_isZero_2492_; 
v_zero_2491_ = lean_unsigned_to_nat(0u);
v_isZero_2492_ = lean_nat_dec_eq(v_k_2490_, v_zero_2491_);
if (v_isZero_2492_ == 1)
{
lean_object* v___x_2493_; 
lean_dec_ref(v_p_2489_);
v___x_2493_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2493_;
}
else
{
lean_object* v_one_2494_; lean_object* v_n_2495_; uint8_t v___x_2496_; 
v_one_2494_ = lean_unsigned_to_nat(1u);
v_n_2495_ = lean_nat_sub(v_k_2490_, v_one_2494_);
v___x_2496_ = lean_nat_dec_eq(v_n_2495_, v_zero_2491_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
lean_inc_ref(v_p_2489_);
v___x_2497_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2489_, v_n_2495_);
lean_dec(v_n_2495_);
v___x_2498_ = l_Lean_Grind_CommRing_Poly_mul(v_p_2489_, v___x_2497_);
return v___x_2498_;
}
else
{
lean_dec(v_n_2495_);
return v_p_2489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow___boxed(lean_object* v_p_2499_, lean_object* v_k_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2499_, v_k_2500_);
lean_dec(v_k_2500_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc(lean_object* v_p_2502_, lean_object* v_k_2503_){
_start:
{
lean_object* v_zero_2504_; uint8_t v_isZero_2505_; 
v_zero_2504_ = lean_unsigned_to_nat(0u);
v_isZero_2505_ = lean_nat_dec_eq(v_k_2503_, v_zero_2504_);
if (v_isZero_2505_ == 1)
{
lean_object* v___x_2506_; 
lean_dec_ref(v_p_2502_);
v___x_2506_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2506_;
}
else
{
lean_object* v_one_2507_; lean_object* v_n_2508_; uint8_t v___x_2509_; 
v_one_2507_ = lean_unsigned_to_nat(1u);
v_n_2508_ = lean_nat_sub(v_k_2503_, v_one_2507_);
v___x_2509_ = lean_nat_dec_eq(v_n_2508_, v_zero_2504_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_inc_ref(v_p_2502_);
v___x_2510_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2502_, v_n_2508_);
lean_dec(v_n_2508_);
v___x_2511_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2510_, v_p_2502_);
return v___x_2511_;
}
else
{
lean_dec(v_n_2508_);
return v_p_2502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc___boxed(lean_object* v_p_2512_, lean_object* v_k_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2512_, v_k_2513_);
lean_dec(v_k_2513_);
return v_res_2514_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2516_ = lean_int_neg(v___x_2515_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object* v_x_2517_){
_start:
{
switch(lean_obj_tag(v_x_2517_))
{
case 0:
{
lean_object* v_k_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
v_k_2518_ = lean_ctor_get(v_x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v_x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_k_2518_);
lean_dec(v_x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_k_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
case 1:
{
lean_object* v_k_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2534_; 
v_k_2526_ = lean_ctor_get(v_x_2517_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_x_2517_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2528_ = v_x_2517_;
v_isShared_2529_ = v_isSharedCheck_2534_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_k_2526_);
lean_dec(v_x_2517_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2534_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2530_ = lean_nat_to_int(v_k_2526_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set_tag(v___x_2528_, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2530_);
v___x_2532_ = v___x_2528_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
case 2:
{
lean_object* v_k_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
v_k_2535_ = lean_ctor_get(v_x_2517_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_x_2517_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v_x_2517_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_k_2535_);
lean_dec(v_x_2517_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
lean_ctor_set_tag(v___x_2537_, 0);
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_k_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
case 3:
{
lean_object* v_i_2543_; lean_object* v___x_2544_; 
v_i_2543_ = lean_ctor_get(v_x_2517_, 0);
lean_inc(v_i_2543_);
lean_dec_ref_known(v_x_2517_, 1);
v___x_2544_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2543_);
return v___x_2544_;
}
case 4:
{
lean_object* v_a_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v_a_2545_ = lean_ctor_get(v_x_2517_, 0);
lean_inc_ref(v_a_2545_);
lean_dec_ref_known(v_x_2517_, 1);
v___x_2546_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2547_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2545_);
v___x_2548_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2546_, v___x_2547_);
return v___x_2548_;
}
case 5:
{
lean_object* v_a_2549_; lean_object* v_b_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v_a_2549_ = lean_ctor_get(v_x_2517_, 0);
lean_inc_ref(v_a_2549_);
v_b_2550_ = lean_ctor_get(v_x_2517_, 1);
lean_inc_ref(v_b_2550_);
lean_dec_ref_known(v_x_2517_, 2);
v___x_2551_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2549_);
v___x_2552_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2550_);
v___x_2553_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2551_, v___x_2552_);
return v___x_2553_;
}
case 6:
{
lean_object* v_a_2554_; lean_object* v_b_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v_a_2554_ = lean_ctor_get(v_x_2517_, 0);
lean_inc_ref(v_a_2554_);
v_b_2555_ = lean_ctor_get(v_x_2517_, 1);
lean_inc_ref(v_b_2555_);
lean_dec_ref_known(v_x_2517_, 2);
v___x_2556_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2554_);
v___x_2557_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2558_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2555_);
v___x_2559_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2557_, v___x_2558_);
v___x_2560_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2556_, v___x_2559_);
return v___x_2560_;
}
case 7:
{
lean_object* v_a_2561_; lean_object* v_b_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v_a_2561_ = lean_ctor_get(v_x_2517_, 0);
lean_inc_ref(v_a_2561_);
v_b_2562_ = lean_ctor_get(v_x_2517_, 1);
lean_inc_ref(v_b_2562_);
lean_dec_ref_known(v_x_2517_, 2);
v___x_2563_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2561_);
v___x_2564_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2562_);
v___x_2565_ = l_Lean_Grind_CommRing_Poly_mul(v___x_2563_, v___x_2564_);
return v___x_2565_;
}
default: 
{
lean_object* v_a_2566_; lean_object* v_k_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2599_; 
v_a_2566_ = lean_ctor_get(v_x_2517_, 0);
v_k_2567_ = lean_ctor_get(v_x_2517_, 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_x_2517_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2569_ = v_x_2517_;
v_isShared_2570_ = v_isSharedCheck_2599_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_k_2567_);
lean_inc(v_a_2566_);
lean_dec(v_x_2517_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2599_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v_n_2572_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v___x_2575_ = lean_unsigned_to_nat(0u);
v___x_2576_ = lean_nat_dec_eq(v_k_2567_, v___x_2575_);
if (v___x_2576_ == 0)
{
switch(lean_obj_tag(v_a_2566_))
{
case 0:
{
lean_object* v_k_2577_; 
lean_del_object(v___x_2569_);
v_k_2577_ = lean_ctor_get(v_a_2566_, 0);
lean_inc(v_k_2577_);
lean_dec_ref_known(v_a_2566_, 1);
v_n_2572_ = v_k_2577_;
goto v___jp_2571_;
}
case 2:
{
lean_object* v_k_2578_; 
lean_del_object(v___x_2569_);
v_k_2578_ = lean_ctor_get(v_a_2566_, 0);
lean_inc(v_k_2578_);
lean_dec_ref_known(v_a_2566_, 1);
v_n_2572_ = v_k_2578_;
goto v___jp_2571_;
}
case 1:
{
lean_object* v_k_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2588_; 
lean_del_object(v___x_2569_);
v_k_2579_ = lean_ctor_get(v_a_2566_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_a_2566_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2581_ = v_a_2566_;
v_isShared_2582_ = v_isSharedCheck_2588_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_k_2579_);
lean_dec(v_a_2566_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2588_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2583_ = lean_nat_to_int(v_k_2579_);
v___x_2584_ = l_Int_pow(v___x_2583_, v_k_2567_);
lean_dec(v_k_2567_);
lean_dec(v___x_2583_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2584_);
v___x_2586_ = v___x_2581_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
case 3:
{
lean_object* v_i_2589_; lean_object* v___x_2591_; 
v_i_2589_ = lean_ctor_get(v_a_2566_, 0);
lean_inc(v_i_2589_);
lean_dec_ref_known(v_a_2566_, 1);
if (v_isShared_2570_ == 0)
{
lean_ctor_set_tag(v___x_2569_, 0);
lean_ctor_set(v___x_2569_, 0, v_i_2589_);
v___x_2591_ = v___x_2569_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_i_2589_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_k_2567_);
v___x_2591_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = lean_box(0);
v___x_2593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2591_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2593_);
return v___x_2594_;
}
}
default: 
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_del_object(v___x_2569_);
v___x_2596_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2566_);
v___x_2597_ = l_Lean_Grind_CommRing_Poly_pow(v___x_2596_, v_k_2567_);
lean_dec(v_k_2567_);
return v___x_2597_;
}
}
}
else
{
lean_object* v___x_2598_; 
lean_del_object(v___x_2569_);
lean_dec(v_k_2567_);
lean_dec_ref(v_a_2566_);
v___x_2598_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2598_;
}
v___jp_2571_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = l_Int_pow(v_n_2572_, v_k_2567_);
lean_dec(v_k_2567_);
lean_dec(v_n_2572_);
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
return v___x_2574_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf(lean_object* v_m_2600_, lean_object* v_x_2601_){
_start:
{
if (lean_obj_tag(v_m_2600_) == 0)
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_unsigned_to_nat(0u);
return v___x_2602_;
}
else
{
lean_object* v_p_2603_; lean_object* v_m_2604_; lean_object* v_x_2605_; lean_object* v_k_2606_; uint8_t v___x_2607_; 
v_p_2603_ = lean_ctor_get(v_m_2600_, 0);
v_m_2604_ = lean_ctor_get(v_m_2600_, 1);
v_x_2605_ = lean_ctor_get(v_p_2603_, 0);
v_k_2606_ = lean_ctor_get(v_p_2603_, 1);
v___x_2607_ = lean_nat_dec_eq(v_x_2605_, v_x_2601_);
if (v___x_2607_ == 0)
{
v_m_2600_ = v_m_2604_;
goto _start;
}
else
{
lean_inc(v_k_2606_);
return v_k_2606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf___boxed(lean_object* v_m_2609_, lean_object* v_x_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_2609_, v_x_2610_);
lean_dec(v_x_2610_);
lean_dec(v_m_2609_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar(lean_object* v_m_2612_, lean_object* v_x_2613_){
_start:
{
if (lean_obj_tag(v_m_2612_) == 0)
{
return v_m_2612_;
}
else
{
lean_object* v_p_2614_; lean_object* v_m_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2625_; 
v_p_2614_ = lean_ctor_get(v_m_2612_, 0);
v_m_2615_ = lean_ctor_get(v_m_2612_, 1);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_m_2612_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2617_ = v_m_2612_;
v_isShared_2618_ = v_isSharedCheck_2625_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_m_2615_);
lean_inc(v_p_2614_);
lean_dec(v_m_2612_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2625_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v_x_2619_; uint8_t v___x_2620_; 
v_x_2619_ = lean_ctor_get(v_p_2614_, 0);
v___x_2620_ = lean_nat_dec_eq(v_x_2619_, v_x_2613_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2621_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2615_, v_x_2613_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 1, v___x_2621_);
v___x_2623_ = v___x_2617_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_p_2614_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
else
{
lean_del_object(v___x_2617_);
lean_dec_ref(v_p_2614_);
return v_m_2615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar___boxed(lean_object* v_m_2626_, lean_object* v_x_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2626_, v_x_2627_);
lean_dec(v_x_2627_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27(lean_object* v_c_2629_, lean_object* v_x_2630_, lean_object* v_p_2631_, lean_object* v_acc_2632_){
_start:
{
if (lean_obj_tag(v_p_2631_) == 0)
{
lean_object* v_k_2633_; lean_object* v___x_2634_; 
v_k_2633_ = lean_ctor_get(v_p_2631_, 0);
lean_inc(v_k_2633_);
lean_dec_ref_known(v_p_2631_, 1);
v___x_2634_ = l_Lean_Grind_CommRing_Poly_addConst(v_acc_2632_, v_k_2633_);
lean_dec(v_k_2633_);
return v___x_2634_;
}
else
{
lean_object* v_k_2635_; lean_object* v_v_2636_; lean_object* v_p_2637_; lean_object* v_n_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v_k_2635_ = lean_ctor_get(v_p_2631_, 0);
lean_inc(v_k_2635_);
v_v_2636_ = lean_ctor_get(v_p_2631_, 1);
lean_inc(v_v_2636_);
v_p_2637_ = lean_ctor_get(v_p_2631_, 2);
lean_inc_ref(v_p_2637_);
lean_dec_ref_known(v_p_2631_, 3);
v_n_2641_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_2636_, v_x_2630_);
v___x_2642_ = lean_unsigned_to_nat(0u);
v___x_2643_ = lean_nat_dec_lt(v___x_2642_, v_n_2641_);
if (v___x_2643_ == 0)
{
lean_dec(v_n_2641_);
goto v___jp_2638_;
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2644_ = l_Int_pow(v_c_2629_, v_n_2641_);
lean_dec(v_n_2641_);
v___x_2645_ = lean_int_emod(v_k_2635_, v___x_2644_);
v___x_2646_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2647_ = lean_int_dec_eq(v___x_2645_, v___x_2646_);
lean_dec(v___x_2645_);
if (v___x_2647_ == 0)
{
lean_dec(v___x_2644_);
goto v___jp_2638_;
}
else
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2648_ = lean_int_ediv(v_k_2635_, v___x_2644_);
lean_dec(v___x_2644_);
lean_dec(v_k_2635_);
v___x_2649_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_v_2636_, v_x_2630_);
v___x_2650_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2648_, v___x_2649_, v_acc_2632_);
v_p_2631_ = v_p_2637_;
v_acc_2632_ = v___x_2650_;
goto _start;
}
}
v___jp_2638_:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_Grind_CommRing_Poly_insert(v_k_2635_, v_v_2636_, v_acc_2632_);
v_p_2631_ = v_p_2637_;
v_acc_2632_ = v___x_2639_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27___boxed(lean_object* v_c_2652_, lean_object* v_x_2653_, lean_object* v_p_2654_, lean_object* v_acc_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2652_, v_x_2653_, v_p_2654_, v_acc_2655_);
lean_dec(v_x_2653_);
lean_dec(v_c_2652_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar(lean_object* v_c_2657_, lean_object* v_x_2658_, lean_object* v_p_2659_){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2661_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2657_, v_x_2658_, v_p_2659_, v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar___boxed(lean_object* v_c_2662_, lean_object* v_x_2663_, lean_object* v_p_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_Grind_CommRing_Poly_cancelVar(v_c_2662_, v_x_2663_, v_p_2664_);
lean_dec(v_x_2663_);
lean_dec(v_c_2662_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(lean_object* v_x_2666_, lean_object* v_h__1_2667_, lean_object* v_h__2_2668_, lean_object* v_h__3_2669_, lean_object* v_h__4_2670_, lean_object* v_h__5_2671_, lean_object* v_h__6_2672_, lean_object* v_h__7_2673_, lean_object* v_h__8_2674_, lean_object* v_h__9_2675_){
_start:
{
switch(lean_obj_tag(v_x_2666_))
{
case 0:
{
lean_object* v_k_2676_; lean_object* v___x_2677_; 
lean_dec(v_h__9_2675_);
lean_dec(v_h__8_2674_);
lean_dec(v_h__7_2673_);
lean_dec(v_h__6_2672_);
lean_dec(v_h__5_2671_);
lean_dec(v_h__4_2670_);
lean_dec(v_h__3_2669_);
lean_dec(v_h__2_2668_);
v_k_2676_ = lean_ctor_get(v_x_2666_, 0);
lean_inc(v_k_2676_);
lean_dec_ref_known(v_x_2666_, 1);
v___x_2677_ = lean_apply_1(v_h__1_2667_, v_k_2676_);
return v___x_2677_;
}
case 1:
{
lean_object* v_k_2678_; lean_object* v___x_2679_; 
lean_dec(v_h__9_2675_);
lean_dec(v_h__8_2674_);
lean_dec(v_h__7_2673_);
lean_dec(v_h__6_2672_);
lean_dec(v_h__5_2671_);
lean_dec(v_h__4_2670_);
lean_dec(v_h__2_2668_);
lean_dec(v_h__1_2667_);
v_k_2678_ = lean_ctor_get(v_x_2666_, 0);
lean_inc(v_k_2678_);
lean_dec_ref_known(v_x_2666_, 1);
v___x_2679_ = lean_apply_1(v_h__3_2669_, v_k_2678_);
return v___x_2679_;
}
case 2:
{
lean_object* v_k_2680_; lean_object* v___x_2681_; 
lean_dec(v_h__9_2675_);
lean_dec(v_h__8_2674_);
lean_dec(v_h__7_2673_);
lean_dec(v_h__6_2672_);
lean_dec(v_h__5_2671_);
lean_dec(v_h__4_2670_);
lean_dec(v_h__3_2669_);
lean_dec(v_h__1_2667_);
v_k_2680_ = lean_ctor_get(v_x_2666_, 0);
lean_inc(v_k_2680_);
lean_dec_ref_known(v_x_2666_, 1);
v___x_2681_ = lean_apply_1(v_h__2_2668_, v_k_2680_);
return v___x_2681_;
}
case 3:
{
lean_object* v_i_2682_; lean_object* v___x_2683_; 
lean_dec(v_h__9_2675_);
lean_dec(v_h__8_2674_);
lean_dec(v_h__7_2673_);
lean_dec(v_h__6_2672_);
lean_dec(v_h__5_2671_);
lean_dec(v_h__3_2669_);
lean_dec(v_h__2_2668_);
lean_dec(v_h__1_2667_);
v_i_2682_ = lean_ctor_get(v_x_2666_, 0);
lean_inc(v_i_2682_);
lean_dec_ref_known(v_x_2666_, 1);
v___x_2683_ = lean_apply_1(v_h__4_2670_, v_i_2682_);
return v___x_2683_;
}
case 4:
{
lean_object* v_a_2684_; lean_object* v___x_2685_; 
lean_dec(v_h__9_2675_);
lean_dec(v_h__8_2674_);
lean_dec(v_h__6_2672_);
lean_dec(v_h__5_2671_);
lean_dec(v_h__4_2670_);
lean_dec(v_h__3_2669_);
lean_dec(v_h__2_2668_);
lean_dec(v_h__1_2667_);
v_a_2684_ = lean_ctor_get(v_x_2666_, 0);
lean_inc_ref(v_a_2684_);
lean_dec_ref_known(v_x_2666_, 1);
v___x_2685_ = lean_apply_1(v_h__7_2673_, v_a_2684_);
return v___x_2685_;
}
case 5:
{
lean_object* v_a_2686_; lean_object* v_b_2687_; lean_object* v___x_2688_; 
lean_dec(v_h__9_2675_);
lean_dec(v_h__8_2674_);
lean_dec(v_h__7_2673_);
lean_dec(v_h__6_2672_);
lean_dec(v_h__4_2670_);
lean_dec(v_h__3_2669_);
lean_dec(v_h__2_2668_);
lean_dec(v_h__1_2667_);
v_a_2686_ = lean_ctor_get(v_x_2666_, 0);
lean_inc_ref(v_a_2686_);
v_b_2687_ = lean_ctor_get(v_x_2666_, 1);
lean_inc_ref(v_b_2687_);
lean_dec_ref_known(v_x_2666_, 2);
v___x_2688_ = lean_apply_2(v_h__5_2671_, v_a_2686_, v_b_2687_);
return v___x_2688_;
}
case 6:
{
lean_object* v_a_2689_; lean_object* v_b_2690_; lean_object* v___x_2691_; 
lean_dec(v_h__9_2675_);
lean_dec(v_h__7_2673_);
lean_dec(v_h__6_2672_);
lean_dec(v_h__5_2671_);
lean_dec(v_h__4_2670_);
lean_dec(v_h__3_2669_);
lean_dec(v_h__2_2668_);
lean_dec(v_h__1_2667_);
v_a_2689_ = lean_ctor_get(v_x_2666_, 0);
lean_inc_ref(v_a_2689_);
v_b_2690_ = lean_ctor_get(v_x_2666_, 1);
lean_inc_ref(v_b_2690_);
lean_dec_ref_known(v_x_2666_, 2);
v___x_2691_ = lean_apply_2(v_h__8_2674_, v_a_2689_, v_b_2690_);
return v___x_2691_;
}
case 7:
{
lean_object* v_a_2692_; lean_object* v_b_2693_; lean_object* v___x_2694_; 
lean_dec(v_h__9_2675_);
lean_dec(v_h__8_2674_);
lean_dec(v_h__7_2673_);
lean_dec(v_h__5_2671_);
lean_dec(v_h__4_2670_);
lean_dec(v_h__3_2669_);
lean_dec(v_h__2_2668_);
lean_dec(v_h__1_2667_);
v_a_2692_ = lean_ctor_get(v_x_2666_, 0);
lean_inc_ref(v_a_2692_);
v_b_2693_ = lean_ctor_get(v_x_2666_, 1);
lean_inc_ref(v_b_2693_);
lean_dec_ref_known(v_x_2666_, 2);
v___x_2694_ = lean_apply_2(v_h__6_2672_, v_a_2692_, v_b_2693_);
return v___x_2694_;
}
default: 
{
lean_object* v_a_2695_; lean_object* v_k_2696_; lean_object* v___x_2697_; 
lean_dec(v_h__8_2674_);
lean_dec(v_h__7_2673_);
lean_dec(v_h__6_2672_);
lean_dec(v_h__5_2671_);
lean_dec(v_h__4_2670_);
lean_dec(v_h__3_2669_);
lean_dec(v_h__2_2668_);
lean_dec(v_h__1_2667_);
v_a_2695_ = lean_ctor_get(v_x_2666_, 0);
lean_inc_ref(v_a_2695_);
v_k_2696_ = lean_ctor_get(v_x_2666_, 1);
lean_inc(v_k_2696_);
lean_dec_ref_known(v_x_2666_, 2);
v___x_2697_ = lean_apply_2(v_h__9_2675_, v_a_2695_, v_k_2696_);
return v___x_2697_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter(lean_object* v_motive_2698_, lean_object* v_x_2699_, lean_object* v_h__1_2700_, lean_object* v_h__2_2701_, lean_object* v_h__3_2702_, lean_object* v_h__4_2703_, lean_object* v_h__5_2704_, lean_object* v_h__6_2705_, lean_object* v_h__7_2706_, lean_object* v_h__8_2707_, lean_object* v_h__9_2708_){
_start:
{
switch(lean_obj_tag(v_x_2699_))
{
case 0:
{
lean_object* v_k_2709_; lean_object* v___x_2710_; 
lean_dec(v_h__9_2708_);
lean_dec(v_h__8_2707_);
lean_dec(v_h__7_2706_);
lean_dec(v_h__6_2705_);
lean_dec(v_h__5_2704_);
lean_dec(v_h__4_2703_);
lean_dec(v_h__3_2702_);
lean_dec(v_h__2_2701_);
v_k_2709_ = lean_ctor_get(v_x_2699_, 0);
lean_inc(v_k_2709_);
lean_dec_ref_known(v_x_2699_, 1);
v___x_2710_ = lean_apply_1(v_h__1_2700_, v_k_2709_);
return v___x_2710_;
}
case 1:
{
lean_object* v_k_2711_; lean_object* v___x_2712_; 
lean_dec(v_h__9_2708_);
lean_dec(v_h__8_2707_);
lean_dec(v_h__7_2706_);
lean_dec(v_h__6_2705_);
lean_dec(v_h__5_2704_);
lean_dec(v_h__4_2703_);
lean_dec(v_h__2_2701_);
lean_dec(v_h__1_2700_);
v_k_2711_ = lean_ctor_get(v_x_2699_, 0);
lean_inc(v_k_2711_);
lean_dec_ref_known(v_x_2699_, 1);
v___x_2712_ = lean_apply_1(v_h__3_2702_, v_k_2711_);
return v___x_2712_;
}
case 2:
{
lean_object* v_k_2713_; lean_object* v___x_2714_; 
lean_dec(v_h__9_2708_);
lean_dec(v_h__8_2707_);
lean_dec(v_h__7_2706_);
lean_dec(v_h__6_2705_);
lean_dec(v_h__5_2704_);
lean_dec(v_h__4_2703_);
lean_dec(v_h__3_2702_);
lean_dec(v_h__1_2700_);
v_k_2713_ = lean_ctor_get(v_x_2699_, 0);
lean_inc(v_k_2713_);
lean_dec_ref_known(v_x_2699_, 1);
v___x_2714_ = lean_apply_1(v_h__2_2701_, v_k_2713_);
return v___x_2714_;
}
case 3:
{
lean_object* v_i_2715_; lean_object* v___x_2716_; 
lean_dec(v_h__9_2708_);
lean_dec(v_h__8_2707_);
lean_dec(v_h__7_2706_);
lean_dec(v_h__6_2705_);
lean_dec(v_h__5_2704_);
lean_dec(v_h__3_2702_);
lean_dec(v_h__2_2701_);
lean_dec(v_h__1_2700_);
v_i_2715_ = lean_ctor_get(v_x_2699_, 0);
lean_inc(v_i_2715_);
lean_dec_ref_known(v_x_2699_, 1);
v___x_2716_ = lean_apply_1(v_h__4_2703_, v_i_2715_);
return v___x_2716_;
}
case 4:
{
lean_object* v_a_2717_; lean_object* v___x_2718_; 
lean_dec(v_h__9_2708_);
lean_dec(v_h__8_2707_);
lean_dec(v_h__6_2705_);
lean_dec(v_h__5_2704_);
lean_dec(v_h__4_2703_);
lean_dec(v_h__3_2702_);
lean_dec(v_h__2_2701_);
lean_dec(v_h__1_2700_);
v_a_2717_ = lean_ctor_get(v_x_2699_, 0);
lean_inc_ref(v_a_2717_);
lean_dec_ref_known(v_x_2699_, 1);
v___x_2718_ = lean_apply_1(v_h__7_2706_, v_a_2717_);
return v___x_2718_;
}
case 5:
{
lean_object* v_a_2719_; lean_object* v_b_2720_; lean_object* v___x_2721_; 
lean_dec(v_h__9_2708_);
lean_dec(v_h__8_2707_);
lean_dec(v_h__7_2706_);
lean_dec(v_h__6_2705_);
lean_dec(v_h__4_2703_);
lean_dec(v_h__3_2702_);
lean_dec(v_h__2_2701_);
lean_dec(v_h__1_2700_);
v_a_2719_ = lean_ctor_get(v_x_2699_, 0);
lean_inc_ref(v_a_2719_);
v_b_2720_ = lean_ctor_get(v_x_2699_, 1);
lean_inc_ref(v_b_2720_);
lean_dec_ref_known(v_x_2699_, 2);
v___x_2721_ = lean_apply_2(v_h__5_2704_, v_a_2719_, v_b_2720_);
return v___x_2721_;
}
case 6:
{
lean_object* v_a_2722_; lean_object* v_b_2723_; lean_object* v___x_2724_; 
lean_dec(v_h__9_2708_);
lean_dec(v_h__7_2706_);
lean_dec(v_h__6_2705_);
lean_dec(v_h__5_2704_);
lean_dec(v_h__4_2703_);
lean_dec(v_h__3_2702_);
lean_dec(v_h__2_2701_);
lean_dec(v_h__1_2700_);
v_a_2722_ = lean_ctor_get(v_x_2699_, 0);
lean_inc_ref(v_a_2722_);
v_b_2723_ = lean_ctor_get(v_x_2699_, 1);
lean_inc_ref(v_b_2723_);
lean_dec_ref_known(v_x_2699_, 2);
v___x_2724_ = lean_apply_2(v_h__8_2707_, v_a_2722_, v_b_2723_);
return v___x_2724_;
}
case 7:
{
lean_object* v_a_2725_; lean_object* v_b_2726_; lean_object* v___x_2727_; 
lean_dec(v_h__9_2708_);
lean_dec(v_h__8_2707_);
lean_dec(v_h__7_2706_);
lean_dec(v_h__5_2704_);
lean_dec(v_h__4_2703_);
lean_dec(v_h__3_2702_);
lean_dec(v_h__2_2701_);
lean_dec(v_h__1_2700_);
v_a_2725_ = lean_ctor_get(v_x_2699_, 0);
lean_inc_ref(v_a_2725_);
v_b_2726_ = lean_ctor_get(v_x_2699_, 1);
lean_inc_ref(v_b_2726_);
lean_dec_ref_known(v_x_2699_, 2);
v___x_2727_ = lean_apply_2(v_h__6_2705_, v_a_2725_, v_b_2726_);
return v___x_2727_;
}
default: 
{
lean_object* v_a_2728_; lean_object* v_k_2729_; lean_object* v___x_2730_; 
lean_dec(v_h__8_2707_);
lean_dec(v_h__7_2706_);
lean_dec(v_h__6_2705_);
lean_dec(v_h__5_2704_);
lean_dec(v_h__4_2703_);
lean_dec(v_h__3_2702_);
lean_dec(v_h__2_2701_);
lean_dec(v_h__1_2700_);
v_a_2728_ = lean_ctor_get(v_x_2699_, 0);
lean_inc_ref(v_a_2728_);
v_k_2729_ = lean_ctor_get(v_x_2699_, 1);
lean_inc(v_k_2729_);
lean_dec_ref_known(v_x_2699_, 2);
v___x_2730_ = lean_apply_2(v_h__9_2708_, v_a_2728_, v_k_2729_);
return v___x_2730_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter___redArg(lean_object* v_a_2731_, lean_object* v_h__1_2732_, lean_object* v_h__2_2733_, lean_object* v_h__3_2734_, lean_object* v_h__4_2735_, lean_object* v_h__5_2736_){
_start:
{
switch(lean_obj_tag(v_a_2731_))
{
case 0:
{
lean_object* v_k_2737_; lean_object* v___x_2738_; 
lean_dec(v_h__5_2736_);
lean_dec(v_h__4_2735_);
lean_dec(v_h__3_2734_);
lean_dec(v_h__2_2733_);
v_k_2737_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_k_2737_);
lean_dec_ref_known(v_a_2731_, 1);
v___x_2738_ = lean_apply_1(v_h__1_2732_, v_k_2737_);
return v___x_2738_;
}
case 2:
{
lean_object* v_k_2739_; lean_object* v___x_2740_; 
lean_dec(v_h__5_2736_);
lean_dec(v_h__4_2735_);
lean_dec(v_h__3_2734_);
lean_dec(v_h__1_2732_);
v_k_2739_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_k_2739_);
lean_dec_ref_known(v_a_2731_, 1);
v___x_2740_ = lean_apply_1(v_h__2_2733_, v_k_2739_);
return v___x_2740_;
}
case 1:
{
lean_object* v_k_2741_; lean_object* v___x_2742_; 
lean_dec(v_h__5_2736_);
lean_dec(v_h__4_2735_);
lean_dec(v_h__2_2733_);
lean_dec(v_h__1_2732_);
v_k_2741_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_k_2741_);
lean_dec_ref_known(v_a_2731_, 1);
v___x_2742_ = lean_apply_1(v_h__3_2734_, v_k_2741_);
return v___x_2742_;
}
case 3:
{
lean_object* v_i_2743_; lean_object* v___x_2744_; 
lean_dec(v_h__5_2736_);
lean_dec(v_h__3_2734_);
lean_dec(v_h__2_2733_);
lean_dec(v_h__1_2732_);
v_i_2743_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_i_2743_);
lean_dec_ref_known(v_a_2731_, 1);
v___x_2744_ = lean_apply_1(v_h__4_2735_, v_i_2743_);
return v___x_2744_;
}
default: 
{
lean_object* v___x_2745_; 
lean_dec(v_h__4_2735_);
lean_dec(v_h__3_2734_);
lean_dec(v_h__2_2733_);
lean_dec(v_h__1_2732_);
v___x_2745_ = lean_apply_5(v_h__5_2736_, v_a_2731_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2745_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter(lean_object* v_motive_2746_, lean_object* v_a_2747_, lean_object* v_h__1_2748_, lean_object* v_h__2_2749_, lean_object* v_h__3_2750_, lean_object* v_h__4_2751_, lean_object* v_h__5_2752_){
_start:
{
switch(lean_obj_tag(v_a_2747_))
{
case 0:
{
lean_object* v_k_2753_; lean_object* v___x_2754_; 
lean_dec(v_h__5_2752_);
lean_dec(v_h__4_2751_);
lean_dec(v_h__3_2750_);
lean_dec(v_h__2_2749_);
v_k_2753_ = lean_ctor_get(v_a_2747_, 0);
lean_inc(v_k_2753_);
lean_dec_ref_known(v_a_2747_, 1);
v___x_2754_ = lean_apply_1(v_h__1_2748_, v_k_2753_);
return v___x_2754_;
}
case 2:
{
lean_object* v_k_2755_; lean_object* v___x_2756_; 
lean_dec(v_h__5_2752_);
lean_dec(v_h__4_2751_);
lean_dec(v_h__3_2750_);
lean_dec(v_h__1_2748_);
v_k_2755_ = lean_ctor_get(v_a_2747_, 0);
lean_inc(v_k_2755_);
lean_dec_ref_known(v_a_2747_, 1);
v___x_2756_ = lean_apply_1(v_h__2_2749_, v_k_2755_);
return v___x_2756_;
}
case 1:
{
lean_object* v_k_2757_; lean_object* v___x_2758_; 
lean_dec(v_h__5_2752_);
lean_dec(v_h__4_2751_);
lean_dec(v_h__2_2749_);
lean_dec(v_h__1_2748_);
v_k_2757_ = lean_ctor_get(v_a_2747_, 0);
lean_inc(v_k_2757_);
lean_dec_ref_known(v_a_2747_, 1);
v___x_2758_ = lean_apply_1(v_h__3_2750_, v_k_2757_);
return v___x_2758_;
}
case 3:
{
lean_object* v_i_2759_; lean_object* v___x_2760_; 
lean_dec(v_h__5_2752_);
lean_dec(v_h__3_2750_);
lean_dec(v_h__2_2749_);
lean_dec(v_h__1_2748_);
v_i_2759_ = lean_ctor_get(v_a_2747_, 0);
lean_inc(v_i_2759_);
lean_dec_ref_known(v_a_2747_, 1);
v___x_2760_ = lean_apply_1(v_h__4_2751_, v_i_2759_);
return v___x_2760_;
}
default: 
{
lean_object* v___x_2761_; 
lean_dec(v_h__4_2751_);
lean_dec(v_h__3_2750_);
lean_dec(v_h__2_2749_);
lean_dec(v_h__1_2748_);
v___x_2761_ = lean_apply_5(v_h__5_2752_, v_a_2747_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly__nc(lean_object* v_x_2762_){
_start:
{
switch(lean_obj_tag(v_x_2762_))
{
case 0:
{
lean_object* v_k_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
v_k_2763_ = lean_ctor_get(v_x_2762_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_x_2762_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v_x_2762_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_k_2763_);
lean_dec(v_x_2762_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_k_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
case 1:
{
lean_object* v_k_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2779_; 
v_k_2771_ = lean_ctor_get(v_x_2762_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_x_2762_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2773_ = v_x_2762_;
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_k_2771_);
lean_dec(v_x_2762_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2775_ = lean_nat_to_int(v_k_2771_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set_tag(v___x_2773_, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2775_);
v___x_2777_ = v___x_2773_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
case 2:
{
lean_object* v_k_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
v_k_2780_ = lean_ctor_get(v_x_2762_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v_x_2762_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v_x_2762_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_k_2780_);
lean_dec(v_x_2762_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 0);
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_k_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
case 3:
{
lean_object* v_i_2788_; lean_object* v___x_2789_; 
v_i_2788_ = lean_ctor_get(v_x_2762_, 0);
lean_inc(v_i_2788_);
lean_dec_ref_known(v_x_2762_, 1);
v___x_2789_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2788_);
return v___x_2789_;
}
case 4:
{
lean_object* v_a_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_a_2790_ = lean_ctor_get(v_x_2762_, 0);
lean_inc_ref(v_a_2790_);
lean_dec_ref_known(v_x_2762_, 1);
v___x_2791_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2792_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2790_);
v___x_2793_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2791_, v___x_2792_);
return v___x_2793_;
}
case 5:
{
lean_object* v_a_2794_; lean_object* v_b_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_a_2794_ = lean_ctor_get(v_x_2762_, 0);
lean_inc_ref(v_a_2794_);
v_b_2795_ = lean_ctor_get(v_x_2762_, 1);
lean_inc_ref(v_b_2795_);
lean_dec_ref_known(v_x_2762_, 2);
v___x_2796_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2794_);
v___x_2797_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2795_);
v___x_2798_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2796_, v___x_2797_);
return v___x_2798_;
}
case 6:
{
lean_object* v_a_2799_; lean_object* v_b_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_a_2799_ = lean_ctor_get(v_x_2762_, 0);
lean_inc_ref(v_a_2799_);
v_b_2800_ = lean_ctor_get(v_x_2762_, 1);
lean_inc_ref(v_b_2800_);
lean_dec_ref_known(v_x_2762_, 2);
v___x_2801_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2799_);
v___x_2802_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2803_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2800_);
v___x_2804_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2802_, v___x_2803_);
v___x_2805_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2801_, v___x_2804_);
return v___x_2805_;
}
case 7:
{
lean_object* v_a_2806_; lean_object* v_b_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v_a_2806_ = lean_ctor_get(v_x_2762_, 0);
lean_inc_ref(v_a_2806_);
v_b_2807_ = lean_ctor_get(v_x_2762_, 1);
lean_inc_ref(v_b_2807_);
lean_dec_ref_known(v_x_2762_, 2);
v___x_2808_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2806_);
v___x_2809_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2807_);
v___x_2810_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2808_, v___x_2809_);
return v___x_2810_;
}
default: 
{
lean_object* v_a_2811_; lean_object* v_k_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2844_; 
v_a_2811_ = lean_ctor_get(v_x_2762_, 0);
v_k_2812_ = lean_ctor_get(v_x_2762_, 1);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_x_2762_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2814_ = v_x_2762_;
v_isShared_2815_ = v_isSharedCheck_2844_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_k_2812_);
lean_inc(v_a_2811_);
lean_dec(v_x_2762_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2844_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v_n_2817_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2820_ = lean_unsigned_to_nat(0u);
v___x_2821_ = lean_nat_dec_eq(v_k_2812_, v___x_2820_);
if (v___x_2821_ == 0)
{
switch(lean_obj_tag(v_a_2811_))
{
case 0:
{
lean_object* v_k_2822_; 
lean_del_object(v___x_2814_);
v_k_2822_ = lean_ctor_get(v_a_2811_, 0);
lean_inc(v_k_2822_);
lean_dec_ref_known(v_a_2811_, 1);
v_n_2817_ = v_k_2822_;
goto v___jp_2816_;
}
case 2:
{
lean_object* v_k_2823_; 
lean_del_object(v___x_2814_);
v_k_2823_ = lean_ctor_get(v_a_2811_, 0);
lean_inc(v_k_2823_);
lean_dec_ref_known(v_a_2811_, 1);
v_n_2817_ = v_k_2823_;
goto v___jp_2816_;
}
case 1:
{
lean_object* v_k_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2833_; 
lean_del_object(v___x_2814_);
v_k_2824_ = lean_ctor_get(v_a_2811_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_a_2811_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2826_ = v_a_2811_;
v_isShared_2827_ = v_isSharedCheck_2833_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_k_2824_);
lean_dec(v_a_2811_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2833_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
v___x_2828_ = lean_nat_to_int(v_k_2824_);
v___x_2829_ = l_Int_pow(v___x_2828_, v_k_2812_);
lean_dec(v_k_2812_);
lean_dec(v___x_2828_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set_tag(v___x_2826_, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2829_);
v___x_2831_ = v___x_2826_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2829_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
case 3:
{
lean_object* v_i_2834_; lean_object* v___x_2836_; 
v_i_2834_ = lean_ctor_get(v_a_2811_, 0);
lean_inc(v_i_2834_);
lean_dec_ref_known(v_a_2811_, 1);
if (v_isShared_2815_ == 0)
{
lean_ctor_set_tag(v___x_2814_, 0);
lean_ctor_set(v___x_2814_, 0, v_i_2834_);
v___x_2836_ = v___x_2814_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_i_2834_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_k_2812_);
v___x_2836_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2837_ = lean_box(0);
v___x_2838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2838_);
return v___x_2839_;
}
}
default: 
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
lean_del_object(v___x_2814_);
v___x_2841_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2811_);
v___x_2842_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_2841_, v_k_2812_);
lean_dec(v_k_2812_);
return v___x_2842_;
}
}
}
else
{
lean_object* v___x_2843_; 
lean_del_object(v___x_2814_);
lean_dec(v_k_2812_);
lean_dec_ref(v_a_2811_);
v___x_2843_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2843_;
}
v___jp_2816_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = l_Int_pow(v_n_2817_, v_k_2812_);
lean_dec(v_k_2812_);
lean_dec(v_n_2817_);
v___x_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
return v___x_2819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_normEq0(lean_object* v_p_2845_, lean_object* v_c_2846_){
_start:
{
if (lean_obj_tag(v_p_2845_) == 0)
{
lean_object* v_k_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v_k_2847_ = lean_ctor_get(v_p_2845_, 0);
v___x_2848_ = lean_nat_to_int(v_c_2846_);
v___x_2849_ = lean_int_emod(v_k_2847_, v___x_2848_);
lean_dec(v___x_2848_);
v___x_2850_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2851_ = lean_int_dec_eq(v___x_2849_, v___x_2850_);
lean_dec(v___x_2849_);
if (v___x_2851_ == 0)
{
return v_p_2845_;
}
else
{
lean_object* v___x_2852_; 
lean_dec_ref_known(v_p_2845_, 1);
v___x_2852_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2852_;
}
}
else
{
lean_object* v_k_2853_; lean_object* v_v_2854_; lean_object* v_p_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2868_; 
v_k_2853_ = lean_ctor_get(v_p_2845_, 0);
v_v_2854_ = lean_ctor_get(v_p_2845_, 1);
v_p_2855_ = lean_ctor_get(v_p_2845_, 2);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_p_2845_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2857_ = v_p_2845_;
v_isShared_2858_ = v_isSharedCheck_2868_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_p_2855_);
lean_inc(v_v_2854_);
lean_inc(v_k_2853_);
lean_dec(v_p_2845_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2868_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
lean_inc(v_c_2846_);
v___x_2859_ = lean_nat_to_int(v_c_2846_);
v___x_2860_ = lean_int_emod(v_k_2853_, v___x_2859_);
lean_dec(v___x_2859_);
v___x_2861_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2862_ = lean_int_dec_eq(v___x_2860_, v___x_2861_);
lean_dec(v___x_2860_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; lean_object* v___x_2865_; 
v___x_2863_ = l_Lean_Grind_CommRing_Poly_normEq0(v_p_2855_, v_c_2846_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 2, v___x_2863_);
v___x_2865_ = v___x_2857_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_k_2853_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_v_2854_);
lean_ctor_set(v_reuseFailAlloc_2866_, 2, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
else
{
lean_del_object(v___x_2857_);
lean_dec(v_v_2854_);
lean_dec(v_k_2853_);
v_p_2845_ = v_p_2855_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object* v_p_2869_, lean_object* v_k_2870_, lean_object* v_c_2871_){
_start:
{
if (lean_obj_tag(v_p_2869_) == 0)
{
lean_object* v_k_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2882_; 
v_k_2872_ = lean_ctor_get(v_p_2869_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_p_2869_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2874_ = v_p_2869_;
v_isShared_2875_ = v_isSharedCheck_2882_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_k_2872_);
lean_dec(v_p_2869_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2882_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2876_ = lean_int_add(v_k_2872_, v_k_2870_);
lean_dec(v_k_2872_);
v___x_2877_ = lean_nat_to_int(v_c_2871_);
v___x_2878_ = lean_int_emod(v___x_2876_, v___x_2877_);
lean_dec(v___x_2877_);
lean_dec(v___x_2876_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2878_);
v___x_2880_ = v___x_2874_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
else
{
lean_object* v_k_2883_; lean_object* v_v_2884_; lean_object* v_p_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2893_; 
v_k_2883_ = lean_ctor_get(v_p_2869_, 0);
v_v_2884_ = lean_ctor_get(v_p_2869_, 1);
v_p_2885_ = lean_ctor_get(v_p_2869_, 2);
v_isSharedCheck_2893_ = !lean_is_exclusive(v_p_2869_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2887_ = v_p_2869_;
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_p_2885_);
lean_inc(v_v_2884_);
lean_inc(v_k_2883_);
lean_dec(v_p_2869_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2889_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2885_, v_k_2870_, v_c_2871_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 2, v___x_2889_);
v___x_2891_ = v___x_2887_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_k_2883_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_v_2884_);
lean_ctor_set(v_reuseFailAlloc_2892_, 2, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC___boxed(lean_object* v_p_2894_, lean_object* v_k_2895_, lean_object* v_c_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2894_, v_k_2895_, v_c_2896_);
lean_dec(v_k_2895_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC_go(lean_object* v_m_2898_, lean_object* v_c_2899_, lean_object* v_k_2900_, lean_object* v_a_2901_){
_start:
{
if (lean_obj_tag(v_a_2901_) == 0)
{
lean_object* v___x_2902_; 
lean_dec(v_c_2899_);
v___x_2902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2902_, 0, v_k_2900_);
lean_ctor_set(v___x_2902_, 1, v_m_2898_);
lean_ctor_set(v___x_2902_, 2, v_a_2901_);
return v___x_2902_;
}
else
{
lean_object* v_k_2903_; lean_object* v_v_2904_; lean_object* v_p_2905_; uint8_t v___x_2906_; 
v_k_2903_ = lean_ctor_get(v_a_2901_, 0);
v_v_2904_ = lean_ctor_get(v_a_2901_, 1);
v_p_2905_ = lean_ctor_get(v_a_2901_, 2);
v___x_2906_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2898_, v_v_2904_);
switch(v___x_2906_)
{
case 0:
{
lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2914_; 
lean_inc_ref(v_p_2905_);
lean_inc(v_v_2904_);
lean_inc(v_k_2903_);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_a_2901_);
if (v_isSharedCheck_2914_ == 0)
{
lean_object* v_unused_2915_; lean_object* v_unused_2916_; lean_object* v_unused_2917_; 
v_unused_2915_ = lean_ctor_get(v_a_2901_, 2);
lean_dec(v_unused_2915_);
v_unused_2916_ = lean_ctor_get(v_a_2901_, 1);
lean_dec(v_unused_2916_);
v_unused_2917_ = lean_ctor_get(v_a_2901_, 0);
lean_dec(v_unused_2917_);
v___x_2908_ = v_a_2901_;
v_isShared_2909_ = v_isSharedCheck_2914_;
goto v_resetjp_2907_;
}
else
{
lean_dec(v_a_2901_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2914_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2910_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_2898_, v_c_2899_, v_k_2900_, v_p_2905_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 2, v___x_2910_);
v___x_2912_ = v___x_2908_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_k_2903_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_v_2904_);
lean_ctor_set(v_reuseFailAlloc_2913_, 2, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
case 1:
{
lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2929_; 
lean_inc_ref(v_p_2905_);
lean_inc(v_k_2903_);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_a_2901_);
if (v_isSharedCheck_2929_ == 0)
{
lean_object* v_unused_2930_; lean_object* v_unused_2931_; lean_object* v_unused_2932_; 
v_unused_2930_ = lean_ctor_get(v_a_2901_, 2);
lean_dec(v_unused_2930_);
v_unused_2931_ = lean_ctor_get(v_a_2901_, 1);
lean_dec(v_unused_2931_);
v_unused_2932_ = lean_ctor_get(v_a_2901_, 0);
lean_dec(v_unused_2932_);
v___x_2919_ = v_a_2901_;
v_isShared_2920_ = v_isSharedCheck_2929_;
goto v_resetjp_2918_;
}
else
{
lean_dec(v_a_2901_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2929_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v_k_x27_x27_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2921_ = lean_int_add(v_k_2900_, v_k_2903_);
lean_dec(v_k_2903_);
lean_dec(v_k_2900_);
v___x_2922_ = lean_nat_to_int(v_c_2899_);
v_k_x27_x27_2923_ = lean_int_emod(v___x_2921_, v___x_2922_);
lean_dec(v___x_2922_);
lean_dec(v___x_2921_);
v___x_2924_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2925_ = lean_int_dec_eq(v_k_x27_x27_2923_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2927_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 1, v_m_2898_);
lean_ctor_set(v___x_2919_, 0, v_k_x27_x27_2923_);
v___x_2927_ = v___x_2919_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_k_x27_x27_2923_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_m_2898_);
lean_ctor_set(v_reuseFailAlloc_2928_, 2, v_p_2905_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
else
{
lean_dec(v_k_x27_x27_2923_);
lean_del_object(v___x_2919_);
lean_dec(v_m_2898_);
return v_p_2905_;
}
}
}
default: 
{
lean_object* v___x_2933_; 
lean_dec(v_c_2899_);
v___x_2933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2933_, 0, v_k_2900_);
lean_ctor_set(v___x_2933_, 1, v_m_2898_);
lean_ctor_set(v___x_2933_, 2, v_a_2901_);
return v___x_2933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC(lean_object* v_k_2934_, lean_object* v_m_2935_, lean_object* v_p_2936_, lean_object* v_c_2937_){
_start:
{
lean_object* v___x_2938_; lean_object* v_k_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
lean_inc(v_c_2937_);
v___x_2938_ = lean_nat_to_int(v_c_2937_);
v_k_2939_ = lean_int_emod(v_k_2934_, v___x_2938_);
lean_dec(v___x_2938_);
v___x_2940_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2941_ = lean_int_dec_eq(v_k_2939_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_2935_, v_c_2937_, v_k_2939_, v_p_2936_);
return v___x_2942_;
}
else
{
lean_dec(v_k_2939_);
lean_dec(v_c_2937_);
lean_dec(v_m_2935_);
return v_p_2936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC___boxed(lean_object* v_k_2943_, lean_object* v_m_2944_, lean_object* v_p_2945_, lean_object* v_c_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_Grind_CommRing_Poly_insertC(v_k_2943_, v_m_2944_, v_p_2945_, v_c_2946_);
lean_dec(v_k_2943_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go(lean_object* v_k_2948_, lean_object* v_c_2949_, lean_object* v_a_2950_){
_start:
{
if (lean_obj_tag(v_a_2950_) == 0)
{
lean_object* v_k_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2961_; 
v_k_2951_ = lean_ctor_get(v_a_2950_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_a_2950_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2953_ = v_a_2950_;
v_isShared_2954_ = v_isSharedCheck_2961_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_k_2951_);
lean_dec(v_a_2950_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2961_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2955_ = lean_int_mul(v_k_2948_, v_k_2951_);
lean_dec(v_k_2951_);
v___x_2956_ = lean_nat_to_int(v_c_2949_);
v___x_2957_ = lean_int_emod(v___x_2955_, v___x_2956_);
lean_dec(v___x_2956_);
lean_dec(v___x_2955_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 0, v___x_2957_);
v___x_2959_ = v___x_2953_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___x_2957_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
else
{
lean_object* v_k_2962_; lean_object* v_v_2963_; lean_object* v_p_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2978_; 
v_k_2962_ = lean_ctor_get(v_a_2950_, 0);
v_v_2963_ = lean_ctor_get(v_a_2950_, 1);
v_p_2964_ = lean_ctor_get(v_a_2950_, 2);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_a_2950_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2966_ = v_a_2950_;
v_isShared_2967_ = v_isSharedCheck_2978_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_p_2964_);
lean_inc(v_v_2963_);
lean_inc(v_k_2962_);
lean_dec(v_a_2950_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2978_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v_k_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2968_ = lean_int_mul(v_k_2948_, v_k_2962_);
lean_dec(v_k_2962_);
lean_inc(v_c_2949_);
v___x_2969_ = lean_nat_to_int(v_c_2949_);
v_k_2970_ = lean_int_emod(v___x_2968_, v___x_2969_);
lean_dec(v___x_2969_);
lean_dec(v___x_2968_);
v___x_2971_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2972_ = lean_int_dec_eq(v_k_2970_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2973_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_2948_, v_c_2949_, v_p_2964_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 2, v___x_2973_);
lean_ctor_set(v___x_2966_, 0, v_k_2970_);
v___x_2975_ = v___x_2966_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_k_2970_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_v_2963_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
else
{
lean_dec(v_k_2970_);
lean_del_object(v___x_2966_);
lean_dec(v_v_2963_);
v_a_2950_ = v_p_2964_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go___boxed(lean_object* v_k_2979_, lean_object* v_c_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_2979_, v_c_2980_, v_a_2981_);
lean_dec(v_k_2979_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object* v_k_2983_, lean_object* v_p_2984_, lean_object* v_c_2985_){
_start:
{
lean_object* v___x_2986_; lean_object* v_k_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; 
lean_inc(v_c_2985_);
v___x_2986_ = lean_nat_to_int(v_c_2985_);
v_k_2987_ = lean_int_emod(v_k_2983_, v___x_2986_);
lean_dec(v___x_2986_);
v___x_2988_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2989_ = lean_int_dec_eq(v_k_2987_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; uint8_t v___x_2991_; 
v___x_2990_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2991_ = lean_int_dec_eq(v_k_2987_, v___x_2990_);
lean_dec(v_k_2987_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; 
v___x_2992_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_2983_, v_c_2985_, v_p_2984_);
return v___x_2992_;
}
else
{
lean_dec(v_c_2985_);
return v_p_2984_;
}
}
else
{
lean_object* v___x_2993_; 
lean_dec(v_k_2987_);
lean_dec(v_c_2985_);
lean_dec_ref(v_p_2984_);
v___x_2993_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC___boxed(lean_object* v_k_2994_, lean_object* v_p_2995_, lean_object* v_c_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_2994_, v_p_2995_, v_c_2996_);
lean_dec(v_k_2994_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go(lean_object* v_k_2998_, lean_object* v_m_2999_, lean_object* v_c_3000_, lean_object* v_a_3001_){
_start:
{
if (lean_obj_tag(v_a_3001_) == 0)
{
lean_object* v_k_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v_k_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v_k_3002_ = lean_ctor_get(v_a_3001_, 0);
lean_inc(v_k_3002_);
lean_dec_ref_known(v_a_3001_, 1);
v___x_3003_ = lean_int_mul(v_k_2998_, v_k_3002_);
lean_dec(v_k_3002_);
v___x_3004_ = lean_nat_to_int(v_c_3000_);
v_k_3005_ = lean_int_emod(v___x_3003_, v___x_3004_);
lean_dec(v___x_3004_);
lean_dec(v___x_3003_);
v___x_3006_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3007_ = lean_int_dec_eq(v_k_3005_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3009_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3009_, 0, v_k_3005_);
lean_ctor_set(v___x_3009_, 1, v_m_2999_);
lean_ctor_set(v___x_3009_, 2, v___x_3008_);
return v___x_3009_;
}
else
{
lean_object* v___x_3010_; 
lean_dec(v_k_3005_);
lean_dec(v_m_2999_);
v___x_3010_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3010_;
}
}
else
{
lean_object* v_k_3011_; lean_object* v_v_3012_; lean_object* v_p_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3028_; 
v_k_3011_ = lean_ctor_get(v_a_3001_, 0);
v_v_3012_ = lean_ctor_get(v_a_3001_, 1);
v_p_3013_ = lean_ctor_get(v_a_3001_, 2);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_a_3001_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3015_ = v_a_3001_;
v_isShared_3016_ = v_isSharedCheck_3028_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_p_3013_);
lean_inc(v_v_3012_);
lean_inc(v_k_3011_);
lean_dec(v_a_3001_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3028_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v_k_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3017_ = lean_int_mul(v_k_2998_, v_k_3011_);
lean_dec(v_k_3011_);
lean_inc(v_c_3000_);
v___x_3018_ = lean_nat_to_int(v_c_3000_);
v_k_3019_ = lean_int_emod(v___x_3017_, v___x_3018_);
lean_dec(v___x_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3021_ = lean_int_dec_eq(v_k_3019_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
lean_inc(v_m_2999_);
v___x_3022_ = l_Lean_Grind_CommRing_Mon_mul(v_m_2999_, v_v_3012_);
v___x_3023_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_2998_, v_m_2999_, v_c_3000_, v_p_3013_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 2, v___x_3023_);
lean_ctor_set(v___x_3015_, 1, v___x_3022_);
lean_ctor_set(v___x_3015_, 0, v_k_3019_);
v___x_3025_ = v___x_3015_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_k_3019_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3026_, 2, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
else
{
lean_dec(v_k_3019_);
lean_del_object(v___x_3015_);
lean_dec(v_v_3012_);
v_a_3001_ = v_p_3013_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go___boxed(lean_object* v_k_3029_, lean_object* v_m_3030_, lean_object* v_c_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3029_, v_m_3030_, v_c_3031_, v_a_3032_);
lean_dec(v_k_3029_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object* v_k_3034_, lean_object* v_m_3035_, lean_object* v_p_3036_, lean_object* v_c_3037_){
_start:
{
lean_object* v___x_3038_; lean_object* v_k_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; 
lean_inc(v_c_3037_);
v___x_3038_ = lean_nat_to_int(v_c_3037_);
v_k_3039_ = lean_int_emod(v_k_3034_, v___x_3038_);
lean_dec(v___x_3038_);
v___x_3040_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3041_ = lean_int_dec_eq(v_k_3039_, v___x_3040_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = lean_box(0);
v___x_3043_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_3035_, v___x_3042_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; 
lean_dec(v_k_3039_);
v___x_3044_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3034_, v_m_3035_, v_c_3037_, v_p_3036_);
return v___x_3044_;
}
else
{
lean_object* v___x_3045_; 
lean_dec(v_m_3035_);
v___x_3045_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3039_, v_p_3036_, v_c_3037_);
lean_dec(v_k_3039_);
return v___x_3045_;
}
}
else
{
lean_object* v___x_3046_; 
lean_dec(v_k_3039_);
lean_dec(v_c_3037_);
lean_dec_ref(v_p_3036_);
lean_dec(v_m_3035_);
v___x_3046_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC___boxed(lean_object* v_k_3047_, lean_object* v_m_3048_, lean_object* v_p_3049_, lean_object* v_c_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_3047_, v_m_3048_, v_p_3049_, v_c_3050_);
lean_dec(v_k_3047_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(lean_object* v_k_3052_, lean_object* v_m_3053_, lean_object* v_c_3054_, lean_object* v_p_3055_, lean_object* v_acc_3056_){
_start:
{
if (lean_obj_tag(v_p_3055_) == 0)
{
lean_object* v_k_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v_k_3057_ = lean_ctor_get(v_p_3055_, 0);
lean_inc(v_k_3057_);
lean_dec_ref_known(v_p_3055_, 1);
v___x_3058_ = lean_int_mul(v_k_3052_, v_k_3057_);
lean_dec(v_k_3057_);
v___x_3059_ = lean_nat_to_int(v_c_3054_);
v___x_3060_ = lean_int_emod(v___x_3058_, v___x_3059_);
lean_dec(v___x_3059_);
lean_dec(v___x_3058_);
v___x_3061_ = l_Lean_Grind_CommRing_Poly_insert(v___x_3060_, v_m_3053_, v_acc_3056_);
return v___x_3061_;
}
else
{
lean_object* v_k_3062_; lean_object* v_v_3063_; lean_object* v_p_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_k_3062_ = lean_ctor_get(v_p_3055_, 0);
lean_inc(v_k_3062_);
v_v_3063_ = lean_ctor_get(v_p_3055_, 1);
lean_inc(v_v_3063_);
v_p_3064_ = lean_ctor_get(v_p_3055_, 2);
lean_inc_ref(v_p_3064_);
lean_dec_ref_known(v_p_3055_, 3);
v___x_3065_ = lean_int_mul(v_k_3052_, v_k_3062_);
lean_dec(v_k_3062_);
lean_inc(v_c_3054_);
v___x_3066_ = lean_nat_to_int(v_c_3054_);
v___x_3067_ = lean_int_emod(v___x_3065_, v___x_3066_);
lean_dec(v___x_3066_);
lean_dec(v___x_3065_);
lean_inc(v_m_3053_);
v___x_3068_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_3053_, v_v_3063_);
v___x_3069_ = l_Lean_Grind_CommRing_Poly_insert(v___x_3067_, v___x_3068_, v_acc_3056_);
v_p_3055_ = v_p_3064_;
v_acc_3056_ = v___x_3069_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go___boxed(lean_object* v_k_3071_, lean_object* v_m_3072_, lean_object* v_c_3073_, lean_object* v_p_3074_, lean_object* v_acc_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_3071_, v_m_3072_, v_c_3073_, v_p_3074_, v_acc_3075_);
lean_dec(v_k_3071_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc(lean_object* v_k_3077_, lean_object* v_m_3078_, lean_object* v_p_3079_, lean_object* v_c_3080_){
_start:
{
lean_object* v___x_3081_; lean_object* v_k_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; 
lean_inc(v_c_3080_);
v___x_3081_ = lean_nat_to_int(v_c_3080_);
v_k_3082_ = lean_int_emod(v_k_3077_, v___x_3081_);
lean_dec(v___x_3081_);
v___x_3083_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3084_ = lean_int_dec_eq(v_k_3082_, v___x_3083_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = lean_box(0);
v___x_3086_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_3078_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
lean_dec(v_k_3082_);
v___x_3087_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3088_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_3077_, v_m_3078_, v_c_3080_, v_p_3079_, v___x_3087_);
return v___x_3088_;
}
else
{
lean_object* v___x_3089_; 
lean_dec(v_m_3078_);
v___x_3089_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3082_, v_p_3079_, v_c_3080_);
lean_dec(v_k_3082_);
return v___x_3089_;
}
}
else
{
lean_object* v___x_3090_; 
lean_dec(v_k_3082_);
lean_dec(v_c_3080_);
lean_dec_ref(v_p_3079_);
lean_dec(v_m_3078_);
v___x_3090_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc___boxed(lean_object* v_k_3091_, lean_object* v_m_3092_, lean_object* v_p_3093_, lean_object* v_c_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3091_, v_m_3092_, v_p_3093_, v_c_3094_);
lean_dec(v_k_3091_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineC(lean_object* v_p_u2081_3096_, lean_object* v_p_u2082_3097_, lean_object* v_c_3098_){
_start:
{
if (lean_obj_tag(v_p_u2081_3096_) == 0)
{
if (lean_obj_tag(v_p_u2082_3097_) == 0)
{
lean_object* v_k_3099_; lean_object* v_k_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3110_; 
v_k_3099_ = lean_ctor_get(v_p_u2081_3096_, 0);
lean_inc(v_k_3099_);
lean_dec_ref_known(v_p_u2081_3096_, 1);
v_k_3100_ = lean_ctor_get(v_p_u2082_3097_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_p_u2082_3097_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3102_ = v_p_u2082_3097_;
v_isShared_3103_ = v_isSharedCheck_3110_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_k_3100_);
lean_dec(v_p_u2082_3097_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3110_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3104_ = lean_int_add(v_k_3099_, v_k_3100_);
lean_dec(v_k_3100_);
lean_dec(v_k_3099_);
v___x_3105_ = lean_nat_to_int(v_c_3098_);
v___x_3106_ = lean_int_emod(v___x_3104_, v___x_3105_);
lean_dec(v___x_3105_);
lean_dec(v___x_3104_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3106_);
v___x_3108_ = v___x_3102_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
else
{
lean_object* v_k_3111_; lean_object* v___x_3112_; 
v_k_3111_ = lean_ctor_get(v_p_u2081_3096_, 0);
lean_inc(v_k_3111_);
lean_dec_ref_known(v_p_u2081_3096_, 1);
v___x_3112_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2082_3097_, v_k_3111_, v_c_3098_);
lean_dec(v_k_3111_);
return v___x_3112_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_3097_) == 0)
{
lean_object* v_k_3113_; lean_object* v___x_3114_; 
v_k_3113_ = lean_ctor_get(v_p_u2082_3097_, 0);
lean_inc(v_k_3113_);
lean_dec_ref_known(v_p_u2082_3097_, 1);
v___x_3114_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2081_3096_, v_k_3113_, v_c_3098_);
lean_dec(v_k_3113_);
return v___x_3114_;
}
else
{
lean_object* v_k_3115_; lean_object* v_v_3116_; lean_object* v_p_3117_; lean_object* v_k_3118_; lean_object* v_v_3119_; lean_object* v_p_3120_; uint8_t v___x_3121_; 
v_k_3115_ = lean_ctor_get(v_p_u2081_3096_, 0);
v_v_3116_ = lean_ctor_get(v_p_u2081_3096_, 1);
v_p_3117_ = lean_ctor_get(v_p_u2081_3096_, 2);
v_k_3118_ = lean_ctor_get(v_p_u2082_3097_, 0);
v_v_3119_ = lean_ctor_get(v_p_u2082_3097_, 1);
v_p_3120_ = lean_ctor_get(v_p_u2082_3097_, 2);
v___x_3121_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_3116_, v_v_3119_);
switch(v___x_3121_)
{
case 0:
{
lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3129_; 
lean_inc_ref(v_p_3120_);
lean_inc(v_v_3119_);
lean_inc(v_k_3118_);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_p_u2082_3097_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; lean_object* v_unused_3131_; lean_object* v_unused_3132_; 
v_unused_3130_ = lean_ctor_get(v_p_u2082_3097_, 2);
lean_dec(v_unused_3130_);
v_unused_3131_ = lean_ctor_get(v_p_u2082_3097_, 1);
lean_dec(v_unused_3131_);
v_unused_3132_ = lean_ctor_get(v_p_u2082_3097_, 0);
lean_dec(v_unused_3132_);
v___x_3123_ = v_p_u2082_3097_;
v_isShared_3124_ = v_isSharedCheck_3129_;
goto v_resetjp_3122_;
}
else
{
lean_dec(v_p_u2082_3097_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3129_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v___x_3127_; 
v___x_3125_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_u2081_3096_, v_p_3120_, v_c_3098_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 2, v___x_3125_);
v___x_3127_ = v___x_3123_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_k_3118_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_v_3119_);
lean_ctor_set(v_reuseFailAlloc_3128_, 2, v___x_3125_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
case 1:
{
lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3146_; 
lean_inc_ref(v_p_3120_);
lean_inc(v_k_3118_);
lean_inc_ref(v_p_3117_);
lean_inc(v_v_3116_);
lean_inc(v_k_3115_);
lean_dec_ref_known(v_p_u2081_3096_, 3);
v_isSharedCheck_3146_ = !lean_is_exclusive(v_p_u2082_3097_);
if (v_isSharedCheck_3146_ == 0)
{
lean_object* v_unused_3147_; lean_object* v_unused_3148_; lean_object* v_unused_3149_; 
v_unused_3147_ = lean_ctor_get(v_p_u2082_3097_, 2);
lean_dec(v_unused_3147_);
v_unused_3148_ = lean_ctor_get(v_p_u2082_3097_, 1);
lean_dec(v_unused_3148_);
v_unused_3149_ = lean_ctor_get(v_p_u2082_3097_, 0);
lean_dec(v_unused_3149_);
v___x_3134_ = v_p_u2082_3097_;
v_isShared_3135_ = v_isSharedCheck_3146_;
goto v_resetjp_3133_;
}
else
{
lean_dec(v_p_u2082_3097_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3146_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v_k_3138_; lean_object* v___x_3139_; uint8_t v___x_3140_; 
v___x_3136_ = lean_int_add(v_k_3115_, v_k_3118_);
lean_dec(v_k_3118_);
lean_dec(v_k_3115_);
lean_inc(v_c_3098_);
v___x_3137_ = lean_nat_to_int(v_c_3098_);
v_k_3138_ = lean_int_emod(v___x_3136_, v___x_3137_);
lean_dec(v___x_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3140_ = lean_int_dec_eq(v_k_3138_, v___x_3139_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3141_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3117_, v_p_3120_, v_c_3098_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 2, v___x_3141_);
lean_ctor_set(v___x_3134_, 1, v_v_3116_);
lean_ctor_set(v___x_3134_, 0, v_k_3138_);
v___x_3143_ = v___x_3134_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_k_3138_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_v_3116_);
lean_ctor_set(v_reuseFailAlloc_3144_, 2, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
else
{
lean_dec(v_k_3138_);
lean_del_object(v___x_3134_);
lean_dec(v_v_3116_);
v_p_u2081_3096_ = v_p_3117_;
v_p_u2082_3097_ = v_p_3120_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3157_; 
lean_inc_ref(v_p_3117_);
lean_inc(v_v_3116_);
lean_inc(v_k_3115_);
v_isSharedCheck_3157_ = !lean_is_exclusive(v_p_u2081_3096_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; lean_object* v_unused_3159_; lean_object* v_unused_3160_; 
v_unused_3158_ = lean_ctor_get(v_p_u2081_3096_, 2);
lean_dec(v_unused_3158_);
v_unused_3159_ = lean_ctor_get(v_p_u2081_3096_, 1);
lean_dec(v_unused_3159_);
v_unused_3160_ = lean_ctor_get(v_p_u2081_3096_, 0);
lean_dec(v_unused_3160_);
v___x_3151_ = v_p_u2081_3096_;
v_isShared_3152_ = v_isSharedCheck_3157_;
goto v_resetjp_3150_;
}
else
{
lean_dec(v_p_u2081_3096_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3157_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3153_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3117_, v_p_u2082_3097_, v_c_3098_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 2, v___x_3153_);
v___x_3155_ = v___x_3151_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_k_3115_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v_v_3116_);
lean_ctor_set(v_reuseFailAlloc_3156_, 2, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC_go(lean_object* v_p_u2082_3161_, lean_object* v_c_3162_, lean_object* v_p_u2081_3163_, lean_object* v_acc_3164_){
_start:
{
if (lean_obj_tag(v_p_u2081_3163_) == 0)
{
lean_object* v_k_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v_k_3165_ = lean_ctor_get(v_p_u2081_3163_, 0);
lean_inc(v_k_3165_);
lean_dec_ref_known(v_p_u2081_3163_, 1);
lean_inc(v_c_3162_);
v___x_3166_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3165_, v_p_u2082_3161_, v_c_3162_);
lean_dec(v_k_3165_);
v___x_3167_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3164_, v___x_3166_, v_c_3162_);
return v___x_3167_;
}
else
{
lean_object* v_k_3168_; lean_object* v_v_3169_; lean_object* v_p_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_k_3168_ = lean_ctor_get(v_p_u2081_3163_, 0);
lean_inc(v_k_3168_);
v_v_3169_ = lean_ctor_get(v_p_u2081_3163_, 1);
lean_inc(v_v_3169_);
v_p_3170_ = lean_ctor_get(v_p_u2081_3163_, 2);
lean_inc_ref(v_p_3170_);
lean_dec_ref_known(v_p_u2081_3163_, 3);
lean_inc_n(v_c_3162_, 2);
lean_inc_ref(v_p_u2082_3161_);
v___x_3171_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_3168_, v_v_3169_, v_p_u2082_3161_, v_c_3162_);
lean_dec(v_k_3168_);
v___x_3172_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3164_, v___x_3171_, v_c_3162_);
v_p_u2081_3163_ = v_p_3170_;
v_acc_3164_ = v___x_3172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC(lean_object* v_p_u2081_3174_, lean_object* v_p_u2082_3175_, lean_object* v_c_3176_){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3178_ = l_Lean_Grind_CommRing_Poly_mulC_go(v_p_u2082_3175_, v_c_3176_, v_p_u2081_3174_, v___x_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc_go(lean_object* v_p_u2082_3179_, lean_object* v_c_3180_, lean_object* v_p_u2081_3181_, lean_object* v_acc_3182_){
_start:
{
if (lean_obj_tag(v_p_u2081_3181_) == 0)
{
lean_object* v_k_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v_k_3183_ = lean_ctor_get(v_p_u2081_3181_, 0);
lean_inc(v_k_3183_);
lean_dec_ref_known(v_p_u2081_3181_, 1);
lean_inc(v_c_3180_);
v___x_3184_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3183_, v_p_u2082_3179_, v_c_3180_);
lean_dec(v_k_3183_);
v___x_3185_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3182_, v___x_3184_, v_c_3180_);
return v___x_3185_;
}
else
{
lean_object* v_k_3186_; lean_object* v_v_3187_; lean_object* v_p_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_k_3186_ = lean_ctor_get(v_p_u2081_3181_, 0);
lean_inc(v_k_3186_);
v_v_3187_ = lean_ctor_get(v_p_u2081_3181_, 1);
lean_inc(v_v_3187_);
v_p_3188_ = lean_ctor_get(v_p_u2081_3181_, 2);
lean_inc_ref(v_p_3188_);
lean_dec_ref_known(v_p_u2081_3181_, 3);
lean_inc_n(v_c_3180_, 2);
lean_inc_ref(v_p_u2082_3179_);
v___x_3189_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3186_, v_v_3187_, v_p_u2082_3179_, v_c_3180_);
lean_dec(v_k_3186_);
v___x_3190_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3182_, v___x_3189_, v_c_3180_);
v_p_u2081_3181_ = v_p_3188_;
v_acc_3182_ = v___x_3190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc(lean_object* v_p_u2081_3192_, lean_object* v_p_u2082_3193_, lean_object* v_c_3194_){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3196_ = l_Lean_Grind_CommRing_Poly_mulC__nc_go(v_p_u2082_3193_, v_c_3194_, v_p_u2081_3192_, v___x_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC(lean_object* v_p_3197_, lean_object* v_k_3198_, lean_object* v_c_3199_){
_start:
{
lean_object* v_zero_3200_; uint8_t v_isZero_3201_; 
v_zero_3200_ = lean_unsigned_to_nat(0u);
v_isZero_3201_ = lean_nat_dec_eq(v_k_3198_, v_zero_3200_);
if (v_isZero_3201_ == 1)
{
lean_object* v___x_3202_; 
lean_dec(v_c_3199_);
lean_dec_ref(v_p_3197_);
v___x_3202_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3202_;
}
else
{
lean_object* v_one_3203_; lean_object* v_n_3204_; uint8_t v___x_3205_; 
v_one_3203_ = lean_unsigned_to_nat(1u);
v_n_3204_ = lean_nat_sub(v_k_3198_, v_one_3203_);
v___x_3205_ = lean_nat_dec_eq(v_n_3204_, v_zero_3200_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
lean_inc(v_c_3199_);
lean_inc_ref(v_p_3197_);
v___x_3206_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3197_, v_n_3204_, v_c_3199_);
lean_dec(v_n_3204_);
v___x_3207_ = l_Lean_Grind_CommRing_Poly_mulC(v_p_3197_, v___x_3206_, v_c_3199_);
return v___x_3207_;
}
else
{
lean_dec(v_n_3204_);
lean_dec(v_c_3199_);
return v_p_3197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC___boxed(lean_object* v_p_3208_, lean_object* v_k_3209_, lean_object* v_c_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3208_, v_k_3209_, v_c_3210_);
lean_dec(v_k_3209_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc(lean_object* v_p_3212_, lean_object* v_k_3213_, lean_object* v_c_3214_){
_start:
{
lean_object* v_zero_3215_; uint8_t v_isZero_3216_; 
v_zero_3215_ = lean_unsigned_to_nat(0u);
v_isZero_3216_ = lean_nat_dec_eq(v_k_3213_, v_zero_3215_);
if (v_isZero_3216_ == 1)
{
lean_object* v___x_3217_; 
lean_dec(v_c_3214_);
lean_dec_ref(v_p_3212_);
v___x_3217_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3217_;
}
else
{
lean_object* v_one_3218_; lean_object* v_n_3219_; uint8_t v___x_3220_; 
v_one_3218_ = lean_unsigned_to_nat(1u);
v_n_3219_ = lean_nat_sub(v_k_3213_, v_one_3218_);
v___x_3220_ = lean_nat_dec_eq(v_n_3219_, v_zero_3215_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_inc(v_c_3214_);
lean_inc_ref(v_p_3212_);
v___x_3221_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3212_, v_n_3219_, v_c_3214_);
lean_dec(v_n_3219_);
v___x_3222_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3221_, v_p_3212_, v_c_3214_);
return v___x_3222_;
}
else
{
lean_dec(v_n_3219_);
lean_dec(v_c_3214_);
return v_p_3212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc___boxed(lean_object* v_p_3223_, lean_object* v_k_3224_, lean_object* v_c_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3223_, v_k_3224_, v_c_3225_);
lean_dec(v_k_3224_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC_go(lean_object* v_c_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v_k_3230_; 
switch(lean_obj_tag(v_a_3228_))
{
case 1:
{
lean_object* v_k_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3244_; 
v_k_3234_ = lean_ctor_get(v_a_3228_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_a_3228_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3236_ = v_a_3228_;
v_isShared_3237_ = v_isSharedCheck_3244_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_k_3234_);
lean_dec(v_a_3228_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3244_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3238_ = lean_nat_to_int(v_k_3234_);
v___x_3239_ = lean_nat_to_int(v_c_3227_);
v___x_3240_ = lean_int_emod(v___x_3238_, v___x_3239_);
lean_dec(v___x_3239_);
lean_dec(v___x_3238_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set_tag(v___x_3236_, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3240_);
v___x_3242_ = v___x_3236_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
case 3:
{
lean_object* v_i_3245_; lean_object* v___x_3246_; 
lean_dec(v_c_3227_);
v_i_3245_ = lean_ctor_get(v_a_3228_, 0);
lean_inc(v_i_3245_);
lean_dec_ref_known(v_a_3228_, 1);
v___x_3246_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3245_);
return v___x_3246_;
}
case 4:
{
lean_object* v_a_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v_a_3247_ = lean_ctor_get(v_a_3228_, 0);
lean_inc_ref(v_a_3247_);
lean_dec_ref_known(v_a_3228_, 1);
v___x_3248_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3227_);
v___x_3249_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3227_, v_a_3247_);
v___x_3250_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3248_, v___x_3249_, v_c_3227_);
return v___x_3250_;
}
case 5:
{
lean_object* v_a_3251_; lean_object* v_b_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v_a_3251_ = lean_ctor_get(v_a_3228_, 0);
lean_inc_ref(v_a_3251_);
v_b_3252_ = lean_ctor_get(v_a_3228_, 1);
lean_inc_ref(v_b_3252_);
lean_dec_ref_known(v_a_3228_, 2);
lean_inc_n(v_c_3227_, 2);
v___x_3253_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3227_, v_a_3251_);
v___x_3254_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3227_, v_b_3252_);
v___x_3255_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3253_, v___x_3254_, v_c_3227_);
return v___x_3255_;
}
case 6:
{
lean_object* v_a_3256_; lean_object* v_b_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_a_3256_ = lean_ctor_get(v_a_3228_, 0);
lean_inc_ref(v_a_3256_);
v_b_3257_ = lean_ctor_get(v_a_3228_, 1);
lean_inc_ref(v_b_3257_);
lean_dec_ref_known(v_a_3228_, 2);
lean_inc_n(v_c_3227_, 3);
v___x_3258_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3227_, v_a_3256_);
v___x_3259_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_3260_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3227_, v_b_3257_);
v___x_3261_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3259_, v___x_3260_, v_c_3227_);
v___x_3262_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3258_, v___x_3261_, v_c_3227_);
return v___x_3262_;
}
case 7:
{
lean_object* v_a_3263_; lean_object* v_b_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v_a_3263_ = lean_ctor_get(v_a_3228_, 0);
lean_inc_ref(v_a_3263_);
v_b_3264_ = lean_ctor_get(v_a_3228_, 1);
lean_inc_ref(v_b_3264_);
lean_dec_ref_known(v_a_3228_, 2);
lean_inc_n(v_c_3227_, 2);
v___x_3265_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3227_, v_a_3263_);
v___x_3266_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3227_, v_b_3264_);
v___x_3267_ = l_Lean_Grind_CommRing_Poly_mulC(v___x_3265_, v___x_3266_, v_c_3227_);
return v___x_3267_;
}
case 8:
{
lean_object* v_a_3268_; lean_object* v_k_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3296_; 
v_a_3268_ = lean_ctor_get(v_a_3228_, 0);
v_k_3269_ = lean_ctor_get(v_a_3228_, 1);
v_isSharedCheck_3296_ = !lean_is_exclusive(v_a_3228_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3271_ = v_a_3228_;
v_isShared_3272_ = v_isSharedCheck_3296_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_k_3269_);
lean_inc(v_a_3268_);
lean_dec(v_a_3228_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3296_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = lean_unsigned_to_nat(0u);
v___x_3274_ = lean_nat_dec_eq(v_k_3269_, v___x_3273_);
if (v___x_3274_ == 0)
{
switch(lean_obj_tag(v_a_3268_))
{
case 0:
{
lean_object* v_k_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3285_; 
lean_del_object(v___x_3271_);
v_k_3275_ = lean_ctor_get(v_a_3268_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v_a_3268_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3277_ = v_a_3268_;
v_isShared_3278_ = v_isSharedCheck_3285_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_k_3275_);
lean_dec(v_a_3268_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3285_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
v___x_3279_ = l_Int_pow(v_k_3275_, v_k_3269_);
lean_dec(v_k_3269_);
lean_dec(v_k_3275_);
v___x_3280_ = lean_nat_to_int(v_c_3227_);
v___x_3281_ = lean_int_emod(v___x_3279_, v___x_3280_);
lean_dec(v___x_3280_);
lean_dec(v___x_3279_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v___x_3281_);
v___x_3283_ = v___x_3277_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
case 3:
{
lean_object* v_i_3286_; lean_object* v___x_3288_; 
lean_dec(v_c_3227_);
v_i_3286_ = lean_ctor_get(v_a_3268_, 0);
lean_inc(v_i_3286_);
lean_dec_ref_known(v_a_3268_, 1);
if (v_isShared_3272_ == 0)
{
lean_ctor_set_tag(v___x_3271_, 0);
lean_ctor_set(v___x_3271_, 0, v_i_3286_);
v___x_3288_ = v___x_3271_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_i_3286_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v_k_3269_);
v___x_3288_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3289_ = lean_box(0);
v___x_3290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3290_);
return v___x_3291_;
}
}
default: 
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_del_object(v___x_3271_);
lean_inc(v_c_3227_);
v___x_3293_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3227_, v_a_3268_);
v___x_3294_ = l_Lean_Grind_CommRing_Poly_powC(v___x_3293_, v_k_3269_, v_c_3227_);
lean_dec(v_k_3269_);
return v___x_3294_;
}
}
}
else
{
lean_object* v___x_3295_; 
lean_del_object(v___x_3271_);
lean_dec(v_k_3269_);
lean_dec_ref(v_a_3268_);
lean_dec(v_c_3227_);
v___x_3295_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3295_;
}
}
}
default: 
{
lean_object* v_k_3297_; 
v_k_3297_ = lean_ctor_get(v_a_3228_, 0);
lean_inc(v_k_3297_);
lean_dec_ref(v_a_3228_);
v_k_3230_ = v_k_3297_;
goto v___jp_3229_;
}
}
v___jp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3231_ = lean_nat_to_int(v_c_3227_);
v___x_3232_ = lean_int_emod(v_k_3230_, v___x_3231_);
lean_dec(v___x_3231_);
lean_dec(v_k_3230_);
v___x_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
return v___x_3233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC(lean_object* v_e_3298_, lean_object* v_c_3299_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3299_, v_e_3298_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(lean_object* v_c_3301_, lean_object* v_a_3302_){
_start:
{
lean_object* v_k_3304_; 
switch(lean_obj_tag(v_a_3302_))
{
case 1:
{
lean_object* v_k_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3318_; 
v_k_3308_ = lean_ctor_get(v_a_3302_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_a_3302_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3310_ = v_a_3302_;
v_isShared_3311_ = v_isSharedCheck_3318_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_k_3308_);
lean_dec(v_a_3302_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3318_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3316_; 
v___x_3312_ = lean_nat_to_int(v_k_3308_);
v___x_3313_ = lean_nat_to_int(v_c_3301_);
v___x_3314_ = lean_int_emod(v___x_3312_, v___x_3313_);
lean_dec(v___x_3313_);
lean_dec(v___x_3312_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set_tag(v___x_3310_, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3314_);
v___x_3316_ = v___x_3310_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
case 3:
{
lean_object* v_i_3319_; lean_object* v___x_3320_; 
lean_dec(v_c_3301_);
v_i_3319_ = lean_ctor_get(v_a_3302_, 0);
lean_inc(v_i_3319_);
lean_dec_ref_known(v_a_3302_, 1);
v___x_3320_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3319_);
return v___x_3320_;
}
case 4:
{
lean_object* v_a_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v_a_3321_ = lean_ctor_get(v_a_3302_, 0);
lean_inc_ref(v_a_3321_);
lean_dec_ref_known(v_a_3302_, 1);
v___x_3322_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3301_);
v___x_3323_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3301_, v_a_3321_);
v___x_3324_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3322_, v___x_3323_, v_c_3301_);
return v___x_3324_;
}
case 5:
{
lean_object* v_a_3325_; lean_object* v_b_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v_a_3325_ = lean_ctor_get(v_a_3302_, 0);
lean_inc_ref(v_a_3325_);
v_b_3326_ = lean_ctor_get(v_a_3302_, 1);
lean_inc_ref(v_b_3326_);
lean_dec_ref_known(v_a_3302_, 2);
lean_inc_n(v_c_3301_, 2);
v___x_3327_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3301_, v_a_3325_);
v___x_3328_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3301_, v_b_3326_);
v___x_3329_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3327_, v___x_3328_, v_c_3301_);
return v___x_3329_;
}
case 6:
{
lean_object* v_a_3330_; lean_object* v_b_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v_a_3330_ = lean_ctor_get(v_a_3302_, 0);
lean_inc_ref(v_a_3330_);
v_b_3331_ = lean_ctor_get(v_a_3302_, 1);
lean_inc_ref(v_b_3331_);
lean_dec_ref_known(v_a_3302_, 2);
lean_inc_n(v_c_3301_, 3);
v___x_3332_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3301_, v_a_3330_);
v___x_3333_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_3334_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3301_, v_b_3331_);
v___x_3335_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3333_, v___x_3334_, v_c_3301_);
v___x_3336_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3332_, v___x_3335_, v_c_3301_);
return v___x_3336_;
}
case 7:
{
lean_object* v_a_3337_; lean_object* v_b_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v_a_3337_ = lean_ctor_get(v_a_3302_, 0);
lean_inc_ref(v_a_3337_);
v_b_3338_ = lean_ctor_get(v_a_3302_, 1);
lean_inc_ref(v_b_3338_);
lean_dec_ref_known(v_a_3302_, 2);
lean_inc_n(v_c_3301_, 2);
v___x_3339_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3301_, v_a_3337_);
v___x_3340_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3301_, v_b_3338_);
v___x_3341_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3339_, v___x_3340_, v_c_3301_);
return v___x_3341_;
}
case 8:
{
lean_object* v_a_3342_; lean_object* v_k_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3370_; 
v_a_3342_ = lean_ctor_get(v_a_3302_, 0);
v_k_3343_ = lean_ctor_get(v_a_3302_, 1);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_a_3302_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3345_ = v_a_3302_;
v_isShared_3346_ = v_isSharedCheck_3370_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_k_3343_);
lean_inc(v_a_3342_);
lean_dec(v_a_3302_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3370_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; uint8_t v___x_3348_; 
v___x_3347_ = lean_unsigned_to_nat(0u);
v___x_3348_ = lean_nat_dec_eq(v_k_3343_, v___x_3347_);
if (v___x_3348_ == 0)
{
switch(lean_obj_tag(v_a_3342_))
{
case 0:
{
lean_object* v_k_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3359_; 
lean_del_object(v___x_3345_);
v_k_3349_ = lean_ctor_get(v_a_3342_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v_a_3342_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3351_ = v_a_3342_;
v_isShared_3352_ = v_isSharedCheck_3359_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_k_3349_);
lean_dec(v_a_3342_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3359_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3357_; 
v___x_3353_ = l_Int_pow(v_k_3349_, v_k_3343_);
lean_dec(v_k_3343_);
lean_dec(v_k_3349_);
v___x_3354_ = lean_nat_to_int(v_c_3301_);
v___x_3355_ = lean_int_emod(v___x_3353_, v___x_3354_);
lean_dec(v___x_3354_);
lean_dec(v___x_3353_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v___x_3355_);
v___x_3357_ = v___x_3351_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3355_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
case 3:
{
lean_object* v_i_3360_; lean_object* v___x_3362_; 
lean_dec(v_c_3301_);
v_i_3360_ = lean_ctor_get(v_a_3342_, 0);
lean_inc(v_i_3360_);
lean_dec_ref_known(v_a_3342_, 1);
if (v_isShared_3346_ == 0)
{
lean_ctor_set_tag(v___x_3345_, 0);
lean_ctor_set(v___x_3345_, 0, v_i_3360_);
v___x_3362_ = v___x_3345_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_i_3360_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_k_3343_);
v___x_3362_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = lean_box(0);
v___x_3364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3362_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3364_);
return v___x_3365_;
}
}
default: 
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_del_object(v___x_3345_);
lean_inc(v_c_3301_);
v___x_3367_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3301_, v_a_3342_);
v___x_3368_ = l_Lean_Grind_CommRing_Poly_powC__nc(v___x_3367_, v_k_3343_, v_c_3301_);
lean_dec(v_k_3343_);
return v___x_3368_;
}
}
}
else
{
lean_object* v___x_3369_; 
lean_del_object(v___x_3345_);
lean_dec(v_k_3343_);
lean_dec_ref(v_a_3342_);
lean_dec(v_c_3301_);
v___x_3369_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3369_;
}
}
}
default: 
{
lean_object* v_k_3371_; 
v_k_3371_ = lean_ctor_get(v_a_3302_, 0);
lean_inc(v_k_3371_);
lean_dec_ref(v_a_3302_);
v_k_3304_ = v_k_3371_;
goto v___jp_3303_;
}
}
v___jp_3303_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = lean_nat_to_int(v_c_3301_);
v___x_3306_ = lean_int_emod(v_k_3304_, v___x_3305_);
lean_dec(v___x_3305_);
lean_dec(v_k_3304_);
v___x_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
return v___x_3307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc(lean_object* v_e_3372_, lean_object* v_c_3373_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3373_, v_e_3372_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter___redArg(lean_object* v_x_3375_, lean_object* v_h__1_3376_){
_start:
{
lean_object* v_x_3377_; lean_object* v_k_3378_; lean_object* v___x_3379_; 
v_x_3377_ = lean_ctor_get(v_x_3375_, 0);
lean_inc(v_x_3377_);
v_k_3378_ = lean_ctor_get(v_x_3375_, 1);
lean_inc(v_k_3378_);
lean_dec_ref(v_x_3375_);
v___x_3379_ = lean_apply_2(v_h__1_3376_, v_x_3377_, v_k_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter(lean_object* v_motive_3380_, lean_object* v_x_3381_, lean_object* v_h__1_3382_){
_start:
{
lean_object* v_x_3383_; lean_object* v_k_3384_; lean_object* v___x_3385_; 
v_x_3383_ = lean_ctor_get(v_x_3381_, 0);
lean_inc(v_x_3383_);
v_k_3384_ = lean_ctor_get(v_x_3381_, 1);
lean_inc(v_k_3384_);
lean_dec_ref(v_x_3381_);
v___x_3385_ = lean_apply_2(v_h__1_3382_, v_x_3383_, v_k_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(lean_object* v_k_3386_, lean_object* v_h__1_3387_, lean_object* v_h__2_3388_, lean_object* v_h__3_3389_){
_start:
{
lean_object* v___x_3390_; uint8_t v___x_3391_; 
v___x_3390_ = lean_unsigned_to_nat(0u);
v___x_3391_ = lean_nat_dec_eq(v_k_3386_, v___x_3390_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; uint8_t v___x_3393_; 
lean_dec(v_h__1_3387_);
v___x_3392_ = lean_unsigned_to_nat(1u);
v___x_3393_ = lean_nat_dec_eq(v_k_3386_, v___x_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; 
lean_dec(v_h__2_3388_);
v___x_3394_ = lean_apply_3(v_h__3_3389_, v_k_3386_, lean_box(0), lean_box(0));
return v___x_3394_;
}
else
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
lean_dec(v_h__3_3389_);
lean_dec(v_k_3386_);
v___x_3395_ = lean_box(0);
v___x_3396_ = lean_apply_1(v_h__2_3388_, v___x_3395_);
return v___x_3396_;
}
}
else
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
lean_dec(v_h__3_3389_);
lean_dec(v_h__2_3388_);
lean_dec(v_k_3386_);
v___x_3397_ = lean_box(0);
v___x_3398_ = lean_apply_1(v_h__1_3387_, v___x_3397_);
return v___x_3398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(lean_object* v_motive_3399_, lean_object* v_k_3400_, lean_object* v_h__1_3401_, lean_object* v_h__2_3402_, lean_object* v_h__3_3403_){
_start:
{
lean_object* v___x_3404_; uint8_t v___x_3405_; 
v___x_3404_ = lean_unsigned_to_nat(0u);
v___x_3405_ = lean_nat_dec_eq(v_k_3400_, v___x_3404_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; uint8_t v___x_3407_; 
lean_dec(v_h__1_3401_);
v___x_3406_ = lean_unsigned_to_nat(1u);
v___x_3407_ = lean_nat_dec_eq(v_k_3400_, v___x_3406_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; 
lean_dec(v_h__2_3402_);
v___x_3408_ = lean_apply_3(v_h__3_3403_, v_k_3400_, lean_box(0), lean_box(0));
return v___x_3408_;
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
lean_dec(v_h__3_3403_);
lean_dec(v_k_3400_);
v___x_3409_ = lean_box(0);
v___x_3410_ = lean_apply_1(v_h__2_3402_, v___x_3409_);
return v___x_3410_;
}
}
else
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
lean_dec(v_h__3_3403_);
lean_dec(v_h__2_3402_);
lean_dec(v_k_3400_);
v___x_3411_ = lean_box(0);
v___x_3412_ = lean_apply_1(v_h__1_3401_, v___x_3411_);
return v___x_3412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(lean_object* v_m_u2081_3413_, lean_object* v_h__1_3414_, lean_object* v_h__2_3415_, lean_object* v_h__3_3416_){
_start:
{
if (lean_obj_tag(v_m_u2081_3413_) == 0)
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec(v_h__3_3416_);
lean_dec(v_h__2_3415_);
v___x_3417_ = lean_box(0);
v___x_3418_ = lean_apply_1(v_h__1_3414_, v___x_3417_);
return v___x_3418_;
}
else
{
lean_object* v_m_3419_; 
lean_dec(v_h__1_3414_);
v_m_3419_ = lean_ctor_get(v_m_u2081_3413_, 1);
if (lean_obj_tag(v_m_3419_) == 0)
{
lean_object* v_p_3420_; lean_object* v___x_3421_; 
lean_dec(v_h__3_3416_);
v_p_3420_ = lean_ctor_get(v_m_u2081_3413_, 0);
lean_inc_ref(v_p_3420_);
lean_dec_ref_known(v_m_u2081_3413_, 2);
v___x_3421_ = lean_apply_1(v_h__2_3415_, v_p_3420_);
return v___x_3421_;
}
else
{
lean_object* v_p_3422_; lean_object* v___x_3423_; 
lean_inc(v_m_3419_);
lean_dec(v_h__2_3415_);
v_p_3422_ = lean_ctor_get(v_m_u2081_3413_, 0);
lean_inc_ref(v_p_3422_);
lean_dec_ref_known(v_m_u2081_3413_, 2);
v___x_3423_ = lean_apply_3(v_h__3_3416_, v_p_3422_, v_m_3419_, lean_box(0));
return v___x_3423_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(lean_object* v_motive_3424_, lean_object* v_m_u2081_3425_, lean_object* v_h__1_3426_, lean_object* v_h__2_3427_, lean_object* v_h__3_3428_){
_start:
{
if (lean_obj_tag(v_m_u2081_3425_) == 0)
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
lean_dec(v_h__3_3428_);
lean_dec(v_h__2_3427_);
v___x_3429_ = lean_box(0);
v___x_3430_ = lean_apply_1(v_h__1_3426_, v___x_3429_);
return v___x_3430_;
}
else
{
lean_object* v_m_3431_; 
lean_dec(v_h__1_3426_);
v_m_3431_ = lean_ctor_get(v_m_u2081_3425_, 1);
if (lean_obj_tag(v_m_3431_) == 0)
{
lean_object* v_p_3432_; lean_object* v___x_3433_; 
lean_dec(v_h__3_3428_);
v_p_3432_ = lean_ctor_get(v_m_u2081_3425_, 0);
lean_inc_ref(v_p_3432_);
lean_dec_ref_known(v_m_u2081_3425_, 2);
v___x_3433_ = lean_apply_1(v_h__2_3427_, v_p_3432_);
return v___x_3433_;
}
else
{
lean_object* v_p_3434_; lean_object* v___x_3435_; 
lean_inc(v_m_3431_);
lean_dec(v_h__2_3427_);
v_p_3434_ = lean_ctor_get(v_m_u2081_3425_, 0);
lean_inc_ref(v_p_3434_);
lean_dec_ref_known(v_m_u2081_3425_, 2);
v___x_3435_ = lean_apply_3(v_h__3_3428_, v_p_3434_, v_m_3431_, lean_box(0));
return v___x_3435_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(uint8_t v_a_3436_, lean_object* v_h__1_3437_, lean_object* v_h__2_3438_){
_start:
{
if (v_a_3436_ == 1)
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
lean_dec(v_h__2_3438_);
v___x_3439_ = lean_box(0);
v___x_3440_ = lean_apply_1(v_h__1_3437_, v___x_3439_);
return v___x_3440_;
}
else
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
lean_dec(v_h__1_3437_);
v___x_3441_ = lean_box(v_a_3436_);
v___x_3442_ = lean_apply_2(v_h__2_3438_, v___x_3441_, lean_box(0));
return v___x_3442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object* v_a_3443_, lean_object* v_h__1_3444_, lean_object* v_h__2_3445_){
_start:
{
uint8_t v_a_13__boxed_3446_; lean_object* v_res_3447_; 
v_a_13__boxed_3446_ = lean_unbox(v_a_3443_);
v_res_3447_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(v_a_13__boxed_3446_, v_h__1_3444_, v_h__2_3445_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(lean_object* v_motive_3448_, uint8_t v_a_3449_, lean_object* v_h__1_3450_, lean_object* v_h__2_3451_){
_start:
{
if (v_a_3449_ == 1)
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_dec(v_h__2_3451_);
v___x_3452_ = lean_box(0);
v___x_3453_ = lean_apply_1(v_h__1_3450_, v___x_3452_);
return v___x_3453_;
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
lean_dec(v_h__1_3450_);
v___x_3454_ = lean_box(v_a_3449_);
v___x_3455_ = lean_apply_2(v_h__2_3451_, v___x_3454_, lean_box(0));
return v___x_3455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___boxed(lean_object* v_motive_3456_, lean_object* v_a_3457_, lean_object* v_h__1_3458_, lean_object* v_h__2_3459_){
_start:
{
uint8_t v_a_24__boxed_3460_; lean_object* v_res_3461_; 
v_a_24__boxed_3460_ = lean_unbox(v_a_3457_);
v_res_3461_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(v_motive_3456_, v_a_24__boxed_3460_, v_h__1_3458_, v_h__2_3459_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(lean_object* v_p_3462_, lean_object* v_h__1_3463_, lean_object* v_h__2_3464_, lean_object* v_h__3_3465_){
_start:
{
if (lean_obj_tag(v_p_3462_) == 0)
{
lean_object* v_k_3466_; lean_object* v___x_3467_; uint8_t v___x_3468_; 
lean_dec(v_h__3_3465_);
v_k_3466_ = lean_ctor_get(v_p_3462_, 0);
lean_inc(v_k_3466_);
lean_dec_ref_known(v_p_3462_, 1);
v___x_3467_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3468_ = lean_int_dec_eq(v_k_3466_, v___x_3467_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; 
lean_dec(v_h__1_3463_);
v___x_3469_ = lean_apply_2(v_h__2_3464_, v_k_3466_, lean_box(0));
return v___x_3469_;
}
else
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_dec(v_k_3466_);
lean_dec(v_h__2_3464_);
v___x_3470_ = lean_box(0);
v___x_3471_ = lean_apply_1(v_h__1_3463_, v___x_3470_);
return v___x_3471_;
}
}
else
{
lean_object* v_k_3472_; lean_object* v_v_3473_; lean_object* v_p_3474_; lean_object* v___x_3475_; 
lean_dec(v_h__2_3464_);
lean_dec(v_h__1_3463_);
v_k_3472_ = lean_ctor_get(v_p_3462_, 0);
lean_inc(v_k_3472_);
v_v_3473_ = lean_ctor_get(v_p_3462_, 1);
lean_inc(v_v_3473_);
v_p_3474_ = lean_ctor_get(v_p_3462_, 2);
lean_inc_ref(v_p_3474_);
lean_dec_ref_known(v_p_3462_, 3);
v___x_3475_ = lean_apply_3(v_h__3_3465_, v_k_3472_, v_v_3473_, v_p_3474_);
return v___x_3475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(lean_object* v_motive_3476_, lean_object* v_p_3477_, lean_object* v_h__1_3478_, lean_object* v_h__2_3479_, lean_object* v_h__3_3480_){
_start:
{
if (lean_obj_tag(v_p_3477_) == 0)
{
lean_object* v_k_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; 
lean_dec(v_h__3_3480_);
v_k_3481_ = lean_ctor_get(v_p_3477_, 0);
lean_inc(v_k_3481_);
lean_dec_ref_known(v_p_3477_, 1);
v___x_3482_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3483_ = lean_int_dec_eq(v_k_3481_, v___x_3482_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3484_; 
lean_dec(v_h__1_3478_);
v___x_3484_ = lean_apply_2(v_h__2_3479_, v_k_3481_, lean_box(0));
return v___x_3484_;
}
else
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
lean_dec(v_k_3481_);
lean_dec(v_h__2_3479_);
v___x_3485_ = lean_box(0);
v___x_3486_ = lean_apply_1(v_h__1_3478_, v___x_3485_);
return v___x_3486_;
}
}
else
{
lean_object* v_k_3487_; lean_object* v_v_3488_; lean_object* v_p_3489_; lean_object* v___x_3490_; 
lean_dec(v_h__2_3479_);
lean_dec(v_h__1_3478_);
v_k_3487_ = lean_ctor_get(v_p_3477_, 0);
lean_inc(v_k_3487_);
v_v_3488_ = lean_ctor_get(v_p_3477_, 1);
lean_inc(v_v_3488_);
v_p_3489_ = lean_ctor_get(v_p_3477_, 2);
lean_inc_ref(v_p_3489_);
lean_dec_ref_known(v_p_3477_, 3);
v___x_3490_ = lean_apply_3(v_h__3_3480_, v_k_3487_, v_v_3488_, v_p_3489_);
return v___x_3490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object* v_k_3491_, lean_object* v_h__1_3492_, lean_object* v_h__2_3493_, lean_object* v_h__3_3494_){
_start:
{
lean_object* v_zero_3495_; uint8_t v_isZero_3496_; 
v_zero_3495_ = lean_unsigned_to_nat(0u);
v_isZero_3496_ = lean_nat_dec_eq(v_k_3491_, v_zero_3495_);
if (v_isZero_3496_ == 1)
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
lean_dec(v_h__3_3494_);
lean_dec(v_h__2_3493_);
v___x_3497_ = lean_box(0);
v___x_3498_ = lean_apply_1(v_h__1_3492_, v___x_3497_);
return v___x_3498_;
}
else
{
lean_object* v_one_3499_; lean_object* v_n_3500_; uint8_t v___x_3501_; 
lean_dec(v_h__1_3492_);
v_one_3499_ = lean_unsigned_to_nat(1u);
v_n_3500_ = lean_nat_sub(v_k_3491_, v_one_3499_);
v___x_3501_ = lean_nat_dec_eq(v_n_3500_, v_zero_3495_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3502_; 
lean_dec(v_h__2_3493_);
v___x_3502_ = lean_apply_2(v_h__3_3494_, v_n_3500_, lean_box(0));
return v___x_3502_;
}
else
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
lean_dec(v_n_3500_);
lean_dec(v_h__3_3494_);
v___x_3503_ = lean_box(0);
v___x_3504_ = lean_apply_1(v_h__2_3493_, v___x_3503_);
return v___x_3504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object* v_k_3505_, lean_object* v_h__1_3506_, lean_object* v_h__2_3507_, lean_object* v_h__3_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(v_k_3505_, v_h__1_3506_, v_h__2_3507_, v_h__3_3508_);
lean_dec(v_k_3505_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object* v_motive_3510_, lean_object* v_k_3511_, lean_object* v_h__1_3512_, lean_object* v_h__2_3513_, lean_object* v_h__3_3514_){
_start:
{
lean_object* v_zero_3515_; uint8_t v_isZero_3516_; 
v_zero_3515_ = lean_unsigned_to_nat(0u);
v_isZero_3516_ = lean_nat_dec_eq(v_k_3511_, v_zero_3515_);
if (v_isZero_3516_ == 1)
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
lean_dec(v_h__3_3514_);
lean_dec(v_h__2_3513_);
v___x_3517_ = lean_box(0);
v___x_3518_ = lean_apply_1(v_h__1_3512_, v___x_3517_);
return v___x_3518_;
}
else
{
lean_object* v_one_3519_; lean_object* v_n_3520_; uint8_t v___x_3521_; 
lean_dec(v_h__1_3512_);
v_one_3519_ = lean_unsigned_to_nat(1u);
v_n_3520_ = lean_nat_sub(v_k_3511_, v_one_3519_);
v___x_3521_ = lean_nat_dec_eq(v_n_3520_, v_zero_3515_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; 
lean_dec(v_h__2_3513_);
v___x_3522_ = lean_apply_2(v_h__3_3514_, v_n_3520_, lean_box(0));
return v___x_3522_;
}
else
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
lean_dec(v_n_3520_);
lean_dec(v_h__3_3514_);
v___x_3523_ = lean_box(0);
v___x_3524_ = lean_apply_1(v_h__2_3513_, v___x_3523_);
return v___x_3524_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object* v_motive_3525_, lean_object* v_k_3526_, lean_object* v_h__1_3527_, lean_object* v_h__2_3528_, lean_object* v_h__3_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(v_motive_3525_, v_k_3526_, v_h__1_3527_, v_h__2_3528_, v_h__3_3529_);
lean_dec(v_k_3526_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(lean_object* v_x_3531_, lean_object* v_h__1_3532_, lean_object* v_h__2_3533_, lean_object* v_h__3_3534_, lean_object* v_h__4_3535_, lean_object* v_h__5_3536_, lean_object* v_h__6_3537_, lean_object* v_h__7_3538_, lean_object* v_h__8_3539_, lean_object* v_h__9_3540_){
_start:
{
switch(lean_obj_tag(v_x_3531_))
{
case 0:
{
lean_object* v_k_3541_; lean_object* v___x_3542_; 
lean_dec(v_h__9_3540_);
lean_dec(v_h__8_3539_);
lean_dec(v_h__7_3538_);
lean_dec(v_h__6_3537_);
lean_dec(v_h__5_3536_);
lean_dec(v_h__4_3535_);
lean_dec(v_h__3_3534_);
lean_dec(v_h__2_3533_);
v_k_3541_ = lean_ctor_get(v_x_3531_, 0);
lean_inc(v_k_3541_);
lean_dec_ref_known(v_x_3531_, 1);
v___x_3542_ = lean_apply_1(v_h__1_3532_, v_k_3541_);
return v___x_3542_;
}
case 1:
{
lean_object* v_k_3543_; lean_object* v___x_3544_; 
lean_dec(v_h__9_3540_);
lean_dec(v_h__8_3539_);
lean_dec(v_h__7_3538_);
lean_dec(v_h__6_3537_);
lean_dec(v_h__5_3536_);
lean_dec(v_h__4_3535_);
lean_dec(v_h__3_3534_);
lean_dec(v_h__1_3532_);
v_k_3543_ = lean_ctor_get(v_x_3531_, 0);
lean_inc(v_k_3543_);
lean_dec_ref_known(v_x_3531_, 1);
v___x_3544_ = lean_apply_1(v_h__2_3533_, v_k_3543_);
return v___x_3544_;
}
case 2:
{
lean_object* v_k_3545_; lean_object* v___x_3546_; 
lean_dec(v_h__9_3540_);
lean_dec(v_h__8_3539_);
lean_dec(v_h__7_3538_);
lean_dec(v_h__6_3537_);
lean_dec(v_h__5_3536_);
lean_dec(v_h__4_3535_);
lean_dec(v_h__2_3533_);
lean_dec(v_h__1_3532_);
v_k_3545_ = lean_ctor_get(v_x_3531_, 0);
lean_inc(v_k_3545_);
lean_dec_ref_known(v_x_3531_, 1);
v___x_3546_ = lean_apply_1(v_h__3_3534_, v_k_3545_);
return v___x_3546_;
}
case 3:
{
lean_object* v_i_3547_; lean_object* v___x_3548_; 
lean_dec(v_h__9_3540_);
lean_dec(v_h__8_3539_);
lean_dec(v_h__7_3538_);
lean_dec(v_h__6_3537_);
lean_dec(v_h__5_3536_);
lean_dec(v_h__3_3534_);
lean_dec(v_h__2_3533_);
lean_dec(v_h__1_3532_);
v_i_3547_ = lean_ctor_get(v_x_3531_, 0);
lean_inc(v_i_3547_);
lean_dec_ref_known(v_x_3531_, 1);
v___x_3548_ = lean_apply_1(v_h__4_3535_, v_i_3547_);
return v___x_3548_;
}
case 4:
{
lean_object* v_a_3549_; lean_object* v___x_3550_; 
lean_dec(v_h__9_3540_);
lean_dec(v_h__8_3539_);
lean_dec(v_h__6_3537_);
lean_dec(v_h__5_3536_);
lean_dec(v_h__4_3535_);
lean_dec(v_h__3_3534_);
lean_dec(v_h__2_3533_);
lean_dec(v_h__1_3532_);
v_a_3549_ = lean_ctor_get(v_x_3531_, 0);
lean_inc_ref(v_a_3549_);
lean_dec_ref_known(v_x_3531_, 1);
v___x_3550_ = lean_apply_1(v_h__7_3538_, v_a_3549_);
return v___x_3550_;
}
case 5:
{
lean_object* v_a_3551_; lean_object* v_b_3552_; lean_object* v___x_3553_; 
lean_dec(v_h__9_3540_);
lean_dec(v_h__8_3539_);
lean_dec(v_h__7_3538_);
lean_dec(v_h__6_3537_);
lean_dec(v_h__4_3535_);
lean_dec(v_h__3_3534_);
lean_dec(v_h__2_3533_);
lean_dec(v_h__1_3532_);
v_a_3551_ = lean_ctor_get(v_x_3531_, 0);
lean_inc_ref(v_a_3551_);
v_b_3552_ = lean_ctor_get(v_x_3531_, 1);
lean_inc_ref(v_b_3552_);
lean_dec_ref_known(v_x_3531_, 2);
v___x_3553_ = lean_apply_2(v_h__5_3536_, v_a_3551_, v_b_3552_);
return v___x_3553_;
}
case 6:
{
lean_object* v_a_3554_; lean_object* v_b_3555_; lean_object* v___x_3556_; 
lean_dec(v_h__9_3540_);
lean_dec(v_h__7_3538_);
lean_dec(v_h__6_3537_);
lean_dec(v_h__5_3536_);
lean_dec(v_h__4_3535_);
lean_dec(v_h__3_3534_);
lean_dec(v_h__2_3533_);
lean_dec(v_h__1_3532_);
v_a_3554_ = lean_ctor_get(v_x_3531_, 0);
lean_inc_ref(v_a_3554_);
v_b_3555_ = lean_ctor_get(v_x_3531_, 1);
lean_inc_ref(v_b_3555_);
lean_dec_ref_known(v_x_3531_, 2);
v___x_3556_ = lean_apply_2(v_h__8_3539_, v_a_3554_, v_b_3555_);
return v___x_3556_;
}
case 7:
{
lean_object* v_a_3557_; lean_object* v_b_3558_; lean_object* v___x_3559_; 
lean_dec(v_h__9_3540_);
lean_dec(v_h__8_3539_);
lean_dec(v_h__7_3538_);
lean_dec(v_h__5_3536_);
lean_dec(v_h__4_3535_);
lean_dec(v_h__3_3534_);
lean_dec(v_h__2_3533_);
lean_dec(v_h__1_3532_);
v_a_3557_ = lean_ctor_get(v_x_3531_, 0);
lean_inc_ref(v_a_3557_);
v_b_3558_ = lean_ctor_get(v_x_3531_, 1);
lean_inc_ref(v_b_3558_);
lean_dec_ref_known(v_x_3531_, 2);
v___x_3559_ = lean_apply_2(v_h__6_3537_, v_a_3557_, v_b_3558_);
return v___x_3559_;
}
default: 
{
lean_object* v_a_3560_; lean_object* v_k_3561_; lean_object* v___x_3562_; 
lean_dec(v_h__8_3539_);
lean_dec(v_h__7_3538_);
lean_dec(v_h__6_3537_);
lean_dec(v_h__5_3536_);
lean_dec(v_h__4_3535_);
lean_dec(v_h__3_3534_);
lean_dec(v_h__2_3533_);
lean_dec(v_h__1_3532_);
v_a_3560_ = lean_ctor_get(v_x_3531_, 0);
lean_inc_ref(v_a_3560_);
v_k_3561_ = lean_ctor_get(v_x_3531_, 1);
lean_inc(v_k_3561_);
lean_dec_ref_known(v_x_3531_, 2);
v___x_3562_ = lean_apply_2(v_h__9_3540_, v_a_3560_, v_k_3561_);
return v___x_3562_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter(lean_object* v_motive_3563_, lean_object* v_x_3564_, lean_object* v_h__1_3565_, lean_object* v_h__2_3566_, lean_object* v_h__3_3567_, lean_object* v_h__4_3568_, lean_object* v_h__5_3569_, lean_object* v_h__6_3570_, lean_object* v_h__7_3571_, lean_object* v_h__8_3572_, lean_object* v_h__9_3573_){
_start:
{
switch(lean_obj_tag(v_x_3564_))
{
case 0:
{
lean_object* v_k_3574_; lean_object* v___x_3575_; 
lean_dec(v_h__9_3573_);
lean_dec(v_h__8_3572_);
lean_dec(v_h__7_3571_);
lean_dec(v_h__6_3570_);
lean_dec(v_h__5_3569_);
lean_dec(v_h__4_3568_);
lean_dec(v_h__3_3567_);
lean_dec(v_h__2_3566_);
v_k_3574_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_k_3574_);
lean_dec_ref_known(v_x_3564_, 1);
v___x_3575_ = lean_apply_1(v_h__1_3565_, v_k_3574_);
return v___x_3575_;
}
case 1:
{
lean_object* v_k_3576_; lean_object* v___x_3577_; 
lean_dec(v_h__9_3573_);
lean_dec(v_h__8_3572_);
lean_dec(v_h__7_3571_);
lean_dec(v_h__6_3570_);
lean_dec(v_h__5_3569_);
lean_dec(v_h__4_3568_);
lean_dec(v_h__3_3567_);
lean_dec(v_h__1_3565_);
v_k_3576_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_k_3576_);
lean_dec_ref_known(v_x_3564_, 1);
v___x_3577_ = lean_apply_1(v_h__2_3566_, v_k_3576_);
return v___x_3577_;
}
case 2:
{
lean_object* v_k_3578_; lean_object* v___x_3579_; 
lean_dec(v_h__9_3573_);
lean_dec(v_h__8_3572_);
lean_dec(v_h__7_3571_);
lean_dec(v_h__6_3570_);
lean_dec(v_h__5_3569_);
lean_dec(v_h__4_3568_);
lean_dec(v_h__2_3566_);
lean_dec(v_h__1_3565_);
v_k_3578_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_k_3578_);
lean_dec_ref_known(v_x_3564_, 1);
v___x_3579_ = lean_apply_1(v_h__3_3567_, v_k_3578_);
return v___x_3579_;
}
case 3:
{
lean_object* v_i_3580_; lean_object* v___x_3581_; 
lean_dec(v_h__9_3573_);
lean_dec(v_h__8_3572_);
lean_dec(v_h__7_3571_);
lean_dec(v_h__6_3570_);
lean_dec(v_h__5_3569_);
lean_dec(v_h__3_3567_);
lean_dec(v_h__2_3566_);
lean_dec(v_h__1_3565_);
v_i_3580_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_i_3580_);
lean_dec_ref_known(v_x_3564_, 1);
v___x_3581_ = lean_apply_1(v_h__4_3568_, v_i_3580_);
return v___x_3581_;
}
case 4:
{
lean_object* v_a_3582_; lean_object* v___x_3583_; 
lean_dec(v_h__9_3573_);
lean_dec(v_h__8_3572_);
lean_dec(v_h__6_3570_);
lean_dec(v_h__5_3569_);
lean_dec(v_h__4_3568_);
lean_dec(v_h__3_3567_);
lean_dec(v_h__2_3566_);
lean_dec(v_h__1_3565_);
v_a_3582_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_a_3582_);
lean_dec_ref_known(v_x_3564_, 1);
v___x_3583_ = lean_apply_1(v_h__7_3571_, v_a_3582_);
return v___x_3583_;
}
case 5:
{
lean_object* v_a_3584_; lean_object* v_b_3585_; lean_object* v___x_3586_; 
lean_dec(v_h__9_3573_);
lean_dec(v_h__8_3572_);
lean_dec(v_h__7_3571_);
lean_dec(v_h__6_3570_);
lean_dec(v_h__4_3568_);
lean_dec(v_h__3_3567_);
lean_dec(v_h__2_3566_);
lean_dec(v_h__1_3565_);
v_a_3584_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_a_3584_);
v_b_3585_ = lean_ctor_get(v_x_3564_, 1);
lean_inc_ref(v_b_3585_);
lean_dec_ref_known(v_x_3564_, 2);
v___x_3586_ = lean_apply_2(v_h__5_3569_, v_a_3584_, v_b_3585_);
return v___x_3586_;
}
case 6:
{
lean_object* v_a_3587_; lean_object* v_b_3588_; lean_object* v___x_3589_; 
lean_dec(v_h__9_3573_);
lean_dec(v_h__7_3571_);
lean_dec(v_h__6_3570_);
lean_dec(v_h__5_3569_);
lean_dec(v_h__4_3568_);
lean_dec(v_h__3_3567_);
lean_dec(v_h__2_3566_);
lean_dec(v_h__1_3565_);
v_a_3587_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_a_3587_);
v_b_3588_ = lean_ctor_get(v_x_3564_, 1);
lean_inc_ref(v_b_3588_);
lean_dec_ref_known(v_x_3564_, 2);
v___x_3589_ = lean_apply_2(v_h__8_3572_, v_a_3587_, v_b_3588_);
return v___x_3589_;
}
case 7:
{
lean_object* v_a_3590_; lean_object* v_b_3591_; lean_object* v___x_3592_; 
lean_dec(v_h__9_3573_);
lean_dec(v_h__8_3572_);
lean_dec(v_h__7_3571_);
lean_dec(v_h__5_3569_);
lean_dec(v_h__4_3568_);
lean_dec(v_h__3_3567_);
lean_dec(v_h__2_3566_);
lean_dec(v_h__1_3565_);
v_a_3590_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_a_3590_);
v_b_3591_ = lean_ctor_get(v_x_3564_, 1);
lean_inc_ref(v_b_3591_);
lean_dec_ref_known(v_x_3564_, 2);
v___x_3592_ = lean_apply_2(v_h__6_3570_, v_a_3590_, v_b_3591_);
return v___x_3592_;
}
default: 
{
lean_object* v_a_3593_; lean_object* v_k_3594_; lean_object* v___x_3595_; 
lean_dec(v_h__8_3572_);
lean_dec(v_h__7_3571_);
lean_dec(v_h__6_3570_);
lean_dec(v_h__5_3569_);
lean_dec(v_h__4_3568_);
lean_dec(v_h__3_3567_);
lean_dec(v_h__2_3566_);
lean_dec(v_h__1_3565_);
v_a_3593_ = lean_ctor_get(v_x_3564_, 0);
lean_inc_ref(v_a_3593_);
v_k_3594_ = lean_ctor_get(v_x_3564_, 1);
lean_inc(v_k_3594_);
lean_dec_ref_known(v_x_3564_, 2);
v___x_3595_ = lean_apply_2(v_h__9_3573_, v_a_3593_, v_k_3594_);
return v___x_3595_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter___redArg(lean_object* v_a_3596_, lean_object* v_h__1_3597_, lean_object* v_h__2_3598_, lean_object* v_h__3_3599_){
_start:
{
switch(lean_obj_tag(v_a_3596_))
{
case 0:
{
lean_object* v_k_3600_; lean_object* v___x_3601_; 
lean_dec(v_h__3_3599_);
lean_dec(v_h__2_3598_);
v_k_3600_ = lean_ctor_get(v_a_3596_, 0);
lean_inc(v_k_3600_);
lean_dec_ref_known(v_a_3596_, 1);
v___x_3601_ = lean_apply_1(v_h__1_3597_, v_k_3600_);
return v___x_3601_;
}
case 3:
{
lean_object* v_i_3602_; lean_object* v___x_3603_; 
lean_dec(v_h__3_3599_);
lean_dec(v_h__1_3597_);
v_i_3602_ = lean_ctor_get(v_a_3596_, 0);
lean_inc(v_i_3602_);
lean_dec_ref_known(v_a_3596_, 1);
v___x_3603_ = lean_apply_1(v_h__2_3598_, v_i_3602_);
return v___x_3603_;
}
default: 
{
lean_object* v___x_3604_; 
lean_dec(v_h__2_3598_);
lean_dec(v_h__1_3597_);
v___x_3604_ = lean_apply_3(v_h__3_3599_, v_a_3596_, lean_box(0), lean_box(0));
return v___x_3604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter(lean_object* v_motive_3605_, lean_object* v_a_3606_, lean_object* v_h__1_3607_, lean_object* v_h__2_3608_, lean_object* v_h__3_3609_){
_start:
{
switch(lean_obj_tag(v_a_3606_))
{
case 0:
{
lean_object* v_k_3610_; lean_object* v___x_3611_; 
lean_dec(v_h__3_3609_);
lean_dec(v_h__2_3608_);
v_k_3610_ = lean_ctor_get(v_a_3606_, 0);
lean_inc(v_k_3610_);
lean_dec_ref_known(v_a_3606_, 1);
v___x_3611_ = lean_apply_1(v_h__1_3607_, v_k_3610_);
return v___x_3611_;
}
case 3:
{
lean_object* v_i_3612_; lean_object* v___x_3613_; 
lean_dec(v_h__3_3609_);
lean_dec(v_h__1_3607_);
v_i_3612_ = lean_ctor_get(v_a_3606_, 0);
lean_inc(v_i_3612_);
lean_dec_ref_known(v_a_3606_, 1);
v___x_3613_ = lean_apply_1(v_h__2_3608_, v_i_3612_);
return v___x_3613_;
}
default: 
{
lean_object* v___x_3614_; 
lean_dec(v_h__2_3608_);
lean_dec(v_h__1_3607_);
v___x_3614_ = lean_apply_3(v_h__3_3609_, v_a_3606_, lean_box(0), lean_box(0));
return v___x_3614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(lean_object* v_inst_3615_, lean_object* v_ctx_3616_, lean_object* v_m_3617_, lean_object* v_acc_3618_){
_start:
{
if (lean_obj_tag(v_m_3617_) == 0)
{
lean_dec_ref(v_inst_3615_);
return v_acc_3618_;
}
else
{
lean_object* v_toSemiring_3619_; lean_object* v_toMul_3620_; lean_object* v_ofNat_3621_; lean_object* v_npow_3622_; lean_object* v_p_3623_; lean_object* v_m_3624_; lean_object* v___y_3626_; lean_object* v_x_3629_; lean_object* v_k_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; 
v_toSemiring_3619_ = lean_ctor_get(v_inst_3615_, 0);
v_toMul_3620_ = lean_ctor_get(v_toSemiring_3619_, 1);
v_ofNat_3621_ = lean_ctor_get(v_toSemiring_3619_, 3);
v_npow_3622_ = lean_ctor_get(v_toSemiring_3619_, 5);
v_p_3623_ = lean_ctor_get(v_m_3617_, 0);
lean_inc_ref(v_p_3623_);
v_m_3624_ = lean_ctor_get(v_m_3617_, 1);
lean_inc(v_m_3624_);
lean_dec_ref_known(v_m_3617_, 2);
v_x_3629_ = lean_ctor_get(v_p_3623_, 0);
lean_inc(v_x_3629_);
v_k_3630_ = lean_ctor_get(v_p_3623_, 1);
lean_inc(v_k_3630_);
lean_dec_ref(v_p_3623_);
v___x_3631_ = lean_unsigned_to_nat(0u);
v___x_3632_ = lean_nat_dec_eq(v_k_3630_, v___x_3631_);
if (v___x_3632_ == 0)
{
lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3633_ = lean_unsigned_to_nat(1u);
v___x_3634_ = lean_nat_dec_eq(v_k_3630_, v___x_3633_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = l_Lean_RArray_getImpl___redArg(v_ctx_3616_, v_x_3629_);
lean_dec(v_x_3629_);
lean_inc(v_npow_3622_);
v___x_3636_ = lean_apply_2(v_npow_3622_, v___x_3635_, v_k_3630_);
v___y_3626_ = v___x_3636_;
goto v___jp_3625_;
}
else
{
lean_object* v___x_3637_; 
lean_dec(v_k_3630_);
v___x_3637_ = l_Lean_RArray_getImpl___redArg(v_ctx_3616_, v_x_3629_);
lean_dec(v_x_3629_);
v___y_3626_ = v___x_3637_;
goto v___jp_3625_;
}
}
else
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
lean_dec(v_k_3630_);
lean_dec(v_x_3629_);
v___x_3638_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3621_);
v___x_3639_ = lean_apply_1(v_ofNat_3621_, v___x_3638_);
v___y_3626_ = v___x_3639_;
goto v___jp_3625_;
}
v___jp_3625_:
{
lean_object* v___x_3627_; 
lean_inc(v_toMul_3620_);
v___x_3627_ = lean_apply_2(v_toMul_3620_, v_acc_3618_, v___y_3626_);
v_m_3617_ = v_m_3624_;
v_acc_3618_ = v___x_3627_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg___boxed(lean_object* v_inst_3640_, lean_object* v_ctx_3641_, lean_object* v_m_3642_, lean_object* v_acc_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3640_, v_ctx_3641_, v_m_3642_, v_acc_3643_);
lean_dec_ref(v_ctx_3641_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(lean_object* v_00_u03b1_3645_, lean_object* v_inst_3646_, lean_object* v_ctx_3647_, lean_object* v_m_3648_, lean_object* v_acc_3649_){
_start:
{
lean_object* v___x_3650_; 
v___x_3650_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3646_, v_ctx_3647_, v_m_3648_, v_acc_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___boxed(lean_object* v_00_u03b1_3651_, lean_object* v_inst_3652_, lean_object* v_ctx_3653_, lean_object* v_m_3654_, lean_object* v_acc_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(v_00_u03b1_3651_, v_inst_3652_, v_ctx_3653_, v_m_3654_, v_acc_3655_);
lean_dec_ref(v_ctx_3653_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(lean_object* v_inst_3657_, lean_object* v_ctx_3658_, lean_object* v_m_3659_){
_start:
{
if (lean_obj_tag(v_m_3659_) == 0)
{
lean_object* v_toSemiring_3660_; lean_object* v_ofNat_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_toSemiring_3660_ = lean_ctor_get(v_inst_3657_, 0);
lean_inc_ref(v_toSemiring_3660_);
lean_dec_ref(v_inst_3657_);
v_ofNat_3661_ = lean_ctor_get(v_toSemiring_3660_, 3);
lean_inc(v_ofNat_3661_);
lean_dec_ref(v_toSemiring_3660_);
v___x_3662_ = lean_unsigned_to_nat(1u);
v___x_3663_ = lean_apply_1(v_ofNat_3661_, v___x_3662_);
return v___x_3663_;
}
else
{
lean_object* v_toSemiring_3664_; lean_object* v_p_3665_; lean_object* v_m_3666_; lean_object* v_ofNat_3667_; lean_object* v_npow_3668_; lean_object* v_x_3669_; lean_object* v_k_3670_; lean_object* v___x_3671_; uint8_t v___x_3672_; 
v_toSemiring_3664_ = lean_ctor_get(v_inst_3657_, 0);
v_p_3665_ = lean_ctor_get(v_m_3659_, 0);
lean_inc_ref(v_p_3665_);
v_m_3666_ = lean_ctor_get(v_m_3659_, 1);
lean_inc(v_m_3666_);
lean_dec_ref_known(v_m_3659_, 2);
v_ofNat_3667_ = lean_ctor_get(v_toSemiring_3664_, 3);
v_npow_3668_ = lean_ctor_get(v_toSemiring_3664_, 5);
v_x_3669_ = lean_ctor_get(v_p_3665_, 0);
lean_inc(v_x_3669_);
v_k_3670_ = lean_ctor_get(v_p_3665_, 1);
lean_inc(v_k_3670_);
lean_dec_ref(v_p_3665_);
v___x_3671_ = lean_unsigned_to_nat(0u);
v___x_3672_ = lean_nat_dec_eq(v_k_3670_, v___x_3671_);
if (v___x_3672_ == 0)
{
lean_object* v___x_3673_; uint8_t v___x_3674_; 
v___x_3673_ = lean_unsigned_to_nat(1u);
v___x_3674_ = lean_nat_dec_eq(v_k_3670_, v___x_3673_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3675_ = l_Lean_RArray_getImpl___redArg(v_ctx_3658_, v_x_3669_);
lean_dec(v_x_3669_);
lean_inc(v_npow_3668_);
v___x_3676_ = lean_apply_2(v_npow_3668_, v___x_3675_, v_k_3670_);
v___x_3677_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3657_, v_ctx_3658_, v_m_3666_, v___x_3676_);
return v___x_3677_;
}
else
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
lean_dec(v_k_3670_);
v___x_3678_ = l_Lean_RArray_getImpl___redArg(v_ctx_3658_, v_x_3669_);
lean_dec(v_x_3669_);
v___x_3679_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3657_, v_ctx_3658_, v_m_3666_, v___x_3678_);
return v___x_3679_;
}
}
else
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_dec(v_k_3670_);
lean_dec(v_x_3669_);
v___x_3680_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3667_);
v___x_3681_ = lean_apply_1(v_ofNat_3667_, v___x_3680_);
v___x_3682_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3657_, v_ctx_3658_, v_m_3666_, v___x_3681_);
return v___x_3682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3683_, lean_object* v_ctx_3684_, lean_object* v_m_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3683_, v_ctx_3684_, v_m_3685_);
lean_dec_ref(v_ctx_3684_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule(lean_object* v_00_u03b1_3687_, lean_object* v_inst_3688_, lean_object* v_ctx_3689_, lean_object* v_m_3690_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3688_, v_ctx_3689_, v_m_3690_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3692_, lean_object* v_inst_3693_, lean_object* v_ctx_3694_, lean_object* v_m_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule(v_00_u03b1_3692_, v_inst_3693_, v_ctx_3694_, v_m_3695_);
lean_dec_ref(v_ctx_3694_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(lean_object* v_inst_3697_, lean_object* v_ctx_3698_, lean_object* v_p_3699_){
_start:
{
lean_object* v___x_3700_; 
lean_inc_ref(v_inst_3697_);
v___x_3700_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_3697_);
if (lean_obj_tag(v_p_3699_) == 0)
{
lean_object* v_toSemiring_3701_; lean_object* v_zsmul_3702_; lean_object* v_ofNat_3703_; lean_object* v_k_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_toSemiring_3701_ = lean_ctor_get(v_inst_3697_, 0);
lean_inc_ref(v_toSemiring_3701_);
lean_dec_ref(v_inst_3697_);
v_zsmul_3702_ = lean_ctor_get(v___x_3700_, 2);
lean_inc(v_zsmul_3702_);
lean_dec_ref(v___x_3700_);
v_ofNat_3703_ = lean_ctor_get(v_toSemiring_3701_, 3);
lean_inc(v_ofNat_3703_);
lean_dec_ref(v_toSemiring_3701_);
v_k_3704_ = lean_ctor_get(v_p_3699_, 0);
lean_inc(v_k_3704_);
lean_dec_ref_known(v_p_3699_, 1);
v___x_3705_ = lean_unsigned_to_nat(1u);
v___x_3706_ = lean_apply_1(v_ofNat_3703_, v___x_3705_);
v___x_3707_ = lean_apply_2(v_zsmul_3702_, v_k_3704_, v___x_3706_);
return v___x_3707_;
}
else
{
lean_object* v_toSemiring_3708_; lean_object* v_zsmul_3709_; lean_object* v_toAdd_3710_; lean_object* v_k_3711_; lean_object* v_v_3712_; lean_object* v_p_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v_toSemiring_3708_ = lean_ctor_get(v_inst_3697_, 0);
v_zsmul_3709_ = lean_ctor_get(v___x_3700_, 2);
lean_inc(v_zsmul_3709_);
lean_dec_ref(v___x_3700_);
v_toAdd_3710_ = lean_ctor_get(v_toSemiring_3708_, 0);
lean_inc(v_toAdd_3710_);
v_k_3711_ = lean_ctor_get(v_p_3699_, 0);
lean_inc(v_k_3711_);
v_v_3712_ = lean_ctor_get(v_p_3699_, 1);
lean_inc(v_v_3712_);
v_p_3713_ = lean_ctor_get(v_p_3699_, 2);
lean_inc_ref(v_p_3713_);
lean_dec_ref_known(v_p_3699_, 3);
lean_inc_ref(v_inst_3697_);
v___x_3714_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3697_, v_ctx_3698_, v_v_3712_);
v___x_3715_ = lean_apply_2(v_zsmul_3709_, v_k_3711_, v___x_3714_);
v___x_3716_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3697_, v_ctx_3698_, v_p_3713_);
v___x_3717_ = lean_apply_2(v_toAdd_3710_, v___x_3715_, v___x_3716_);
return v___x_3717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3718_, lean_object* v_ctx_3719_, lean_object* v_p_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3718_, v_ctx_3719_, v_p_3720_);
lean_dec_ref(v_ctx_3719_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule(lean_object* v_00_u03b1_3722_, lean_object* v_inst_3723_, lean_object* v_ctx_3724_, lean_object* v_p_3725_){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3723_, v_ctx_3724_, v_p_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3727_, lean_object* v_inst_3728_, lean_object* v_ctx_3729_, lean_object* v_p_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule(v_00_u03b1_3727_, v_inst_3728_, v_ctx_3729_, v_p_3730_);
lean_dec_ref(v_ctx_3729_);
return v_res_3731_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__gcd__cert(lean_object* v_a_3732_, lean_object* v_b_3733_, lean_object* v_p_u2081_3734_, lean_object* v_p_u2082_3735_, lean_object* v_p_3736_){
_start:
{
if (lean_obj_tag(v_p_u2081_3734_) == 0)
{
if (lean_obj_tag(v_p_u2082_3735_) == 0)
{
if (lean_obj_tag(v_p_3736_) == 0)
{
lean_object* v_k_3737_; lean_object* v_k_3738_; lean_object* v_k_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; uint8_t v___x_3743_; 
v_k_3737_ = lean_ctor_get(v_p_u2081_3734_, 0);
v_k_3738_ = lean_ctor_get(v_p_u2082_3735_, 0);
v_k_3739_ = lean_ctor_get(v_p_3736_, 0);
v___x_3740_ = lean_int_mul(v_a_3732_, v_k_3737_);
v___x_3741_ = lean_int_mul(v_b_3733_, v_k_3738_);
v___x_3742_ = lean_int_add(v___x_3740_, v___x_3741_);
lean_dec(v___x_3741_);
lean_dec(v___x_3740_);
v___x_3743_ = lean_int_dec_eq(v_k_3739_, v___x_3742_);
lean_dec(v___x_3742_);
return v___x_3743_;
}
else
{
uint8_t v___x_3744_; 
v___x_3744_ = 0;
return v___x_3744_;
}
}
else
{
uint8_t v___x_3745_; 
v___x_3745_ = 0;
return v___x_3745_;
}
}
else
{
uint8_t v___x_3746_; 
v___x_3746_ = 0;
return v___x_3746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__gcd__cert___boxed(lean_object* v_a_3747_, lean_object* v_b_3748_, lean_object* v_p_u2081_3749_, lean_object* v_p_u2082_3750_, lean_object* v_p_3751_){
_start:
{
uint8_t v_res_3752_; lean_object* v_r_3753_; 
v_res_3752_ = l_Lean_Grind_CommRing_eq__gcd__cert(v_a_3747_, v_b_3748_, v_p_u2081_3749_, v_p_u2082_3750_, v_p_3751_);
lean_dec_ref(v_p_3751_);
lean_dec_ref(v_p_u2082_3750_);
lean_dec_ref(v_p_u2081_3749_);
lean_dec(v_b_3748_);
lean_dec(v_a_3747_);
v_r_3753_ = lean_box(v_res_3752_);
return v_r_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(lean_object* v_p_3754_, lean_object* v_h__1_3755_, lean_object* v_h__2_3756_){
_start:
{
if (lean_obj_tag(v_p_3754_) == 0)
{
lean_object* v_k_3757_; lean_object* v___x_3758_; 
lean_dec(v_h__1_3755_);
v_k_3757_ = lean_ctor_get(v_p_3754_, 0);
lean_inc(v_k_3757_);
lean_dec_ref_known(v_p_3754_, 1);
v___x_3758_ = lean_apply_1(v_h__2_3756_, v_k_3757_);
return v___x_3758_;
}
else
{
lean_object* v_k_3759_; lean_object* v_v_3760_; lean_object* v_p_3761_; lean_object* v___x_3762_; 
lean_dec(v_h__2_3756_);
v_k_3759_ = lean_ctor_get(v_p_3754_, 0);
lean_inc(v_k_3759_);
v_v_3760_ = lean_ctor_get(v_p_3754_, 1);
lean_inc(v_v_3760_);
v_p_3761_ = lean_ctor_get(v_p_3754_, 2);
lean_inc_ref(v_p_3761_);
lean_dec_ref_known(v_p_3754_, 3);
v___x_3762_ = lean_apply_3(v_h__1_3755_, v_k_3759_, v_v_3760_, v_p_3761_);
return v___x_3762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter(lean_object* v_motive_3763_, lean_object* v_p_3764_, lean_object* v_h__1_3765_, lean_object* v_h__2_3766_){
_start:
{
if (lean_obj_tag(v_p_3764_) == 0)
{
lean_object* v_k_3767_; lean_object* v___x_3768_; 
lean_dec(v_h__1_3765_);
v_k_3767_ = lean_ctor_get(v_p_3764_, 0);
lean_inc(v_k_3767_);
lean_dec_ref_known(v_p_3764_, 1);
v___x_3768_ = lean_apply_1(v_h__2_3766_, v_k_3767_);
return v___x_3768_;
}
else
{
lean_object* v_k_3769_; lean_object* v_v_3770_; lean_object* v_p_3771_; lean_object* v___x_3772_; 
lean_dec(v_h__2_3766_);
v_k_3769_ = lean_ctor_get(v_p_3764_, 0);
lean_inc(v_k_3769_);
v_v_3770_ = lean_ctor_get(v_p_3764_, 1);
lean_inc(v_v_3770_);
v_p_3771_ = lean_ctor_get(v_p_3764_, 2);
lean_inc_ref(v_p_3771_);
lean_dec_ref_known(v_p_3764_, 3);
v___x_3772_ = lean_apply_3(v_h__1_3765_, v_k_3769_, v_v_3770_, v_p_3771_);
return v___x_3772_;
}
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
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Ring_CommSolver(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
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
