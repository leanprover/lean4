// Lean compiler output
// Module: Init.Grind.Ring.CommSolver
// Imports: public import Init.Data.Ord.Basic public import Init.Grind.Ring.Field public import Init.Grind.Ordered.Ring public import Init.GrindInstances.Ring.Int import all Init.Data.Ord.Basic import Init.LawfulBEqTactics public import Init.Classical public import Init.Data.Bool public import Init.Data.Int.DivMod.Lemmas public import Init.Data.RArray public import Init.Ext import Init.Data.Hashable import Init.Data.Int.LemmasAux import Init.Data.Nat.Internal.Linear import Init.Grind.Ordered.Order import Init.Omega import Init.WFTactics import Init.Data.Int.Repr public import Init.Data.Nat.Gcd
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
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Grind_CommRing_Expr_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 4:
{
lean_object* v_a_7_; lean_object* v___x_8_; 
v_a_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_a_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_a_7_);
return v___x_8_;
}
case 5:
{
lean_object* v_a_9_; lean_object* v_b_10_; lean_object* v___x_11_; 
v_a_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_a_9_);
v_b_10_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_b_10_);
lean_dec_ref_known(v_t_5_, 2);
v___x_11_ = lean_apply_2(v_k_6_, v_a_9_, v_b_10_);
return v___x_11_;
}
case 6:
{
lean_object* v_a_12_; lean_object* v_b_13_; lean_object* v___x_14_; 
v_a_12_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_a_12_);
v_b_13_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_b_13_);
lean_dec_ref_known(v_t_5_, 2);
v___x_14_ = lean_apply_2(v_k_6_, v_a_12_, v_b_13_);
return v___x_14_;
}
case 7:
{
lean_object* v_a_15_; lean_object* v_b_16_; lean_object* v___x_17_; 
v_a_15_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_a_15_);
v_b_16_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_b_16_);
lean_dec_ref_known(v_t_5_, 2);
v___x_17_ = lean_apply_2(v_k_6_, v_a_15_, v_b_16_);
return v___x_17_;
}
case 8:
{
lean_object* v_a_18_; lean_object* v_k_19_; lean_object* v___x_20_; 
v_a_18_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_a_18_);
v_k_19_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_k_19_);
lean_dec_ref_known(v_t_5_, 2);
v___x_20_ = lean_apply_2(v_k_6_, v_a_18_, v_k_19_);
return v___x_20_;
}
default: 
{
lean_object* v_k_21_; lean_object* v___x_22_; 
v_k_21_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_k_21_);
lean_dec_ref(v_t_5_);
v___x_22_ = lean_apply_1(v_k_6_, v_k_21_);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_25_, v_k_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_ctorElim___boxed(lean_object* v_motive_29_, lean_object* v_ctorIdx_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_k_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Grind_CommRing_Expr_ctorElim(v_motive_29_, v_ctorIdx_30_, v_t_31_, v_h_32_, v_k_33_);
lean_dec(v_ctorIdx_30_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_num_elim___redArg(lean_object* v_t_35_, lean_object* v_num_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_35_, v_num_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_num_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_num_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_39_, v_num_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_natCast_elim___redArg(lean_object* v_t_43_, lean_object* v_natCast_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_43_, v_natCast_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_natCast_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_natCast_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_47_, v_natCast_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_intCast_elim___redArg(lean_object* v_t_51_, lean_object* v_intCast_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_51_, v_intCast_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_intCast_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_intCast_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_55_, v_intCast_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_var_elim___redArg(lean_object* v_t_59_, lean_object* v_var_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_59_, v_var_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_var_elim(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_var_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_63_, v_var_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_neg_elim___redArg(lean_object* v_t_67_, lean_object* v_neg_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_67_, v_neg_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_neg_elim(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_neg_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_71_, v_neg_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_add_elim___redArg(lean_object* v_t_75_, lean_object* v_add_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_75_, v_add_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_add_elim(lean_object* v_motive_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_add_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_79_, v_add_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_sub_elim___redArg(lean_object* v_t_83_, lean_object* v_sub_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_83_, v_sub_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_sub_elim(lean_object* v_motive_86_, lean_object* v_t_87_, lean_object* v_h_88_, lean_object* v_sub_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_87_, v_sub_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_mul_elim___redArg(lean_object* v_t_91_, lean_object* v_mul_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_91_, v_mul_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_mul_elim(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_mul_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_95_, v_mul_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_pow_elim___redArg(lean_object* v_t_99_, lean_object* v_pow_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_99_, v_pow_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_pow_elim(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_pow_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Grind_CommRing_Expr_ctorElim___redArg(v_t_103_, v_pow_105_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_nat_to_int(v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedExpr_default(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__1);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedExpr(void){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Grind_CommRing_instInhabitedExpr_default;
return v___x_112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqExpr_beq(lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
lean_object* v_a_116_; lean_object* v_a_117_; lean_object* v_b_118_; lean_object* v_b_119_; 
switch(lean_obj_tag(v_x_113_))
{
case 0:
{
if (lean_obj_tag(v_x_114_) == 0)
{
lean_object* v_k_122_; lean_object* v_k_123_; uint8_t v___x_124_; 
v_k_122_ = lean_ctor_get(v_x_113_, 0);
v_k_123_ = lean_ctor_get(v_x_114_, 0);
v___x_124_ = lean_int_dec_eq(v_k_122_, v_k_123_);
return v___x_124_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
}
case 1:
{
if (lean_obj_tag(v_x_114_) == 1)
{
lean_object* v_k_126_; lean_object* v_k_127_; uint8_t v___x_128_; 
v_k_126_ = lean_ctor_get(v_x_113_, 0);
v_k_127_ = lean_ctor_get(v_x_114_, 0);
v___x_128_ = lean_nat_dec_eq(v_k_126_, v_k_127_);
return v___x_128_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 0;
return v___x_129_;
}
}
case 2:
{
if (lean_obj_tag(v_x_114_) == 2)
{
lean_object* v_k_130_; lean_object* v_k_131_; uint8_t v___x_132_; 
v_k_130_ = lean_ctor_get(v_x_113_, 0);
v_k_131_ = lean_ctor_get(v_x_114_, 0);
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
case 3:
{
if (lean_obj_tag(v_x_114_) == 3)
{
lean_object* v_i_134_; lean_object* v_i_135_; uint8_t v___x_136_; 
v_i_134_ = lean_ctor_get(v_x_113_, 0);
v_i_135_ = lean_ctor_get(v_x_114_, 0);
v___x_136_ = lean_nat_dec_eq(v_i_134_, v_i_135_);
return v___x_136_;
}
else
{
uint8_t v___x_137_; 
v___x_137_ = 0;
return v___x_137_;
}
}
case 4:
{
if (lean_obj_tag(v_x_114_) == 4)
{
lean_object* v_a_138_; lean_object* v_a_139_; 
v_a_138_ = lean_ctor_get(v_x_113_, 0);
v_a_139_ = lean_ctor_get(v_x_114_, 0);
v_x_113_ = v_a_138_;
v_x_114_ = v_a_139_;
goto _start;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = 0;
return v___x_141_;
}
}
case 5:
{
if (lean_obj_tag(v_x_114_) == 5)
{
lean_object* v_a_142_; lean_object* v_b_143_; lean_object* v_a_144_; lean_object* v_b_145_; 
v_a_142_ = lean_ctor_get(v_x_113_, 0);
v_b_143_ = lean_ctor_get(v_x_113_, 1);
v_a_144_ = lean_ctor_get(v_x_114_, 0);
v_b_145_ = lean_ctor_get(v_x_114_, 1);
v_a_116_ = v_a_142_;
v_a_117_ = v_b_143_;
v_b_118_ = v_a_144_;
v_b_119_ = v_b_145_;
goto v___jp_115_;
}
else
{
uint8_t v___x_146_; 
v___x_146_ = 0;
return v___x_146_;
}
}
case 6:
{
if (lean_obj_tag(v_x_114_) == 6)
{
lean_object* v_a_147_; lean_object* v_b_148_; lean_object* v_a_149_; lean_object* v_b_150_; 
v_a_147_ = lean_ctor_get(v_x_113_, 0);
v_b_148_ = lean_ctor_get(v_x_113_, 1);
v_a_149_ = lean_ctor_get(v_x_114_, 0);
v_b_150_ = lean_ctor_get(v_x_114_, 1);
v_a_116_ = v_a_147_;
v_a_117_ = v_b_148_;
v_b_118_ = v_a_149_;
v_b_119_ = v_b_150_;
goto v___jp_115_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = 0;
return v___x_151_;
}
}
case 7:
{
if (lean_obj_tag(v_x_114_) == 7)
{
lean_object* v_a_152_; lean_object* v_b_153_; lean_object* v_a_154_; lean_object* v_b_155_; 
v_a_152_ = lean_ctor_get(v_x_113_, 0);
v_b_153_ = lean_ctor_get(v_x_113_, 1);
v_a_154_ = lean_ctor_get(v_x_114_, 0);
v_b_155_ = lean_ctor_get(v_x_114_, 1);
v_a_116_ = v_a_152_;
v_a_117_ = v_b_153_;
v_b_118_ = v_a_154_;
v_b_119_ = v_b_155_;
goto v___jp_115_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = 0;
return v___x_156_;
}
}
default: 
{
if (lean_obj_tag(v_x_114_) == 8)
{
lean_object* v_a_157_; lean_object* v_k_158_; lean_object* v_a_159_; lean_object* v_k_160_; uint8_t v___x_161_; 
v_a_157_ = lean_ctor_get(v_x_113_, 0);
v_k_158_ = lean_ctor_get(v_x_113_, 1);
v_a_159_ = lean_ctor_get(v_x_114_, 0);
v_k_160_ = lean_ctor_get(v_x_114_, 1);
v___x_161_ = l_Lean_Grind_CommRing_instBEqExpr_beq(v_a_157_, v_a_159_);
if (v___x_161_ == 0)
{
return v___x_161_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = lean_nat_dec_eq(v_k_158_, v_k_160_);
return v___x_162_;
}
}
else
{
uint8_t v___x_163_; 
v___x_163_ = 0;
return v___x_163_;
}
}
}
v___jp_115_:
{
uint8_t v___x_120_; 
v___x_120_ = l_Lean_Grind_CommRing_instBEqExpr_beq(v_a_116_, v_b_118_);
if (v___x_120_ == 0)
{
return v___x_120_;
}
else
{
v_x_113_ = v_a_117_;
v_x_114_ = v_b_119_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqExpr_beq___boxed(lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Lean_Grind_CommRing_instBEqExpr_beq(v_x_164_, v_x_165_);
lean_dec_ref(v_x_165_);
lean_dec_ref(v_x_164_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashableExpr_hash(lean_object* v_x_170_){
_start:
{
switch(lean_obj_tag(v_x_170_))
{
case 0:
{
lean_object* v_k_171_; uint64_t v___x_172_; lean_object* v_intZero_173_; uint8_t v_isNeg_174_; 
v_k_171_ = lean_ctor_get(v_x_170_, 0);
v___x_172_ = 0ULL;
v_intZero_173_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_174_ = lean_int_dec_lt(v_k_171_, v_intZero_173_);
if (v_isNeg_174_ == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint64_t v___x_178_; uint64_t v___x_179_; 
v_a_175_ = lean_nat_abs(v_k_171_);
v___x_176_ = lean_unsigned_to_nat(2u);
v___x_177_ = lean_nat_mul(v___x_176_, v_a_175_);
lean_dec(v_a_175_);
v___x_178_ = lean_uint64_of_nat(v___x_177_);
lean_dec(v___x_177_);
v___x_179_ = lean_uint64_mix_hash(v___x_172_, v___x_178_);
return v___x_179_;
}
else
{
lean_object* v_abs_180_; lean_object* v_one_181_; lean_object* v_a_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; 
v_abs_180_ = lean_nat_abs(v_k_171_);
v_one_181_ = lean_unsigned_to_nat(1u);
v_a_182_ = lean_nat_sub(v_abs_180_, v_one_181_);
lean_dec(v_abs_180_);
v___x_183_ = lean_unsigned_to_nat(2u);
v___x_184_ = lean_nat_mul(v___x_183_, v_a_182_);
lean_dec(v_a_182_);
v___x_185_ = lean_nat_add(v___x_184_, v_one_181_);
lean_dec(v___x_184_);
v___x_186_ = lean_uint64_of_nat(v___x_185_);
lean_dec(v___x_185_);
v___x_187_ = lean_uint64_mix_hash(v___x_172_, v___x_186_);
return v___x_187_;
}
}
case 1:
{
lean_object* v_k_188_; uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; 
v_k_188_ = lean_ctor_get(v_x_170_, 0);
v___x_189_ = 1ULL;
v___x_190_ = lean_uint64_of_nat(v_k_188_);
v___x_191_ = lean_uint64_mix_hash(v___x_189_, v___x_190_);
return v___x_191_;
}
case 2:
{
lean_object* v_k_192_; uint64_t v___x_193_; lean_object* v_intZero_194_; uint8_t v_isNeg_195_; 
v_k_192_ = lean_ctor_get(v_x_170_, 0);
v___x_193_ = 2ULL;
v_intZero_194_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_195_ = lean_int_dec_lt(v_k_192_, v_intZero_194_);
if (v_isNeg_195_ == 0)
{
lean_object* v_a_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint64_t v___x_199_; uint64_t v___x_200_; 
v_a_196_ = lean_nat_abs(v_k_192_);
v___x_197_ = lean_unsigned_to_nat(2u);
v___x_198_ = lean_nat_mul(v___x_197_, v_a_196_);
lean_dec(v_a_196_);
v___x_199_ = lean_uint64_of_nat(v___x_198_);
lean_dec(v___x_198_);
v___x_200_ = lean_uint64_mix_hash(v___x_193_, v___x_199_);
return v___x_200_;
}
else
{
lean_object* v_abs_201_; lean_object* v_one_202_; lean_object* v_a_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint64_t v___x_207_; uint64_t v___x_208_; 
v_abs_201_ = lean_nat_abs(v_k_192_);
v_one_202_ = lean_unsigned_to_nat(1u);
v_a_203_ = lean_nat_sub(v_abs_201_, v_one_202_);
lean_dec(v_abs_201_);
v___x_204_ = lean_unsigned_to_nat(2u);
v___x_205_ = lean_nat_mul(v___x_204_, v_a_203_);
lean_dec(v_a_203_);
v___x_206_ = lean_nat_add(v___x_205_, v_one_202_);
lean_dec(v___x_205_);
v___x_207_ = lean_uint64_of_nat(v___x_206_);
lean_dec(v___x_206_);
v___x_208_ = lean_uint64_mix_hash(v___x_193_, v___x_207_);
return v___x_208_;
}
}
case 3:
{
lean_object* v_i_209_; uint64_t v___x_210_; uint64_t v___x_211_; uint64_t v___x_212_; 
v_i_209_ = lean_ctor_get(v_x_170_, 0);
v___x_210_ = 3ULL;
v___x_211_ = lean_uint64_of_nat(v_i_209_);
v___x_212_ = lean_uint64_mix_hash(v___x_210_, v___x_211_);
return v___x_212_;
}
case 4:
{
lean_object* v_a_213_; uint64_t v___x_214_; uint64_t v___x_215_; uint64_t v___x_216_; 
v_a_213_ = lean_ctor_get(v_x_170_, 0);
v___x_214_ = 4ULL;
v___x_215_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_213_);
v___x_216_ = lean_uint64_mix_hash(v___x_214_, v___x_215_);
return v___x_216_;
}
case 5:
{
lean_object* v_a_217_; lean_object* v_b_218_; uint64_t v___x_219_; uint64_t v___x_220_; uint64_t v___x_221_; uint64_t v___x_222_; uint64_t v___x_223_; 
v_a_217_ = lean_ctor_get(v_x_170_, 0);
v_b_218_ = lean_ctor_get(v_x_170_, 1);
v___x_219_ = 5ULL;
v___x_220_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_217_);
v___x_221_ = lean_uint64_mix_hash(v___x_219_, v___x_220_);
v___x_222_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_218_);
v___x_223_ = lean_uint64_mix_hash(v___x_221_, v___x_222_);
return v___x_223_;
}
case 6:
{
lean_object* v_a_224_; lean_object* v_b_225_; uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; 
v_a_224_ = lean_ctor_get(v_x_170_, 0);
v_b_225_ = lean_ctor_get(v_x_170_, 1);
v___x_226_ = 6ULL;
v___x_227_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_224_);
v___x_228_ = lean_uint64_mix_hash(v___x_226_, v___x_227_);
v___x_229_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_225_);
v___x_230_ = lean_uint64_mix_hash(v___x_228_, v___x_229_);
return v___x_230_;
}
case 7:
{
lean_object* v_a_231_; lean_object* v_b_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; 
v_a_231_ = lean_ctor_get(v_x_170_, 0);
v_b_232_ = lean_ctor_get(v_x_170_, 1);
v___x_233_ = 7ULL;
v___x_234_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_231_);
v___x_235_ = lean_uint64_mix_hash(v___x_233_, v___x_234_);
v___x_236_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_232_);
v___x_237_ = lean_uint64_mix_hash(v___x_235_, v___x_236_);
return v___x_237_;
}
default: 
{
lean_object* v_a_238_; lean_object* v_k_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; uint64_t v___x_244_; 
v_a_238_ = lean_ctor_get(v_x_170_, 0);
v_k_239_ = lean_ctor_get(v_x_170_, 1);
v___x_240_ = 8ULL;
v___x_241_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_238_);
v___x_242_ = lean_uint64_mix_hash(v___x_240_, v___x_241_);
v___x_243_ = lean_uint64_of_nat(v_k_239_);
v___x_244_ = lean_uint64_mix_hash(v___x_242_, v___x_243_);
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableExpr_hash___boxed(lean_object* v_x_245_){
_start:
{
uint64_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_x_245_);
lean_dec_ref(v_x_245_);
v_r_247_ = lean_box_uint64(v_res_246_);
return v_r_247_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_unsigned_to_nat(2u);
v___x_257_ = lean_nat_to_int(v___x_256_);
return v___x_257_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_nat_to_int(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprExpr_repr(lean_object* v_x_308_, lean_object* v_prec_309_){
_start:
{
lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; 
switch(lean_obj_tag(v_x_308_))
{
case 0:
{
lean_object* v_k_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_351_; 
v_k_328_ = lean_ctor_get(v_x_308_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_351_ == 0)
{
v___x_330_ = v_x_308_;
v_isShared_331_ = v_isSharedCheck_351_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_k_328_);
lean_dec(v_x_308_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_351_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___y_333_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1024u);
v___x_348_ = lean_nat_dec_le(v___x_347_, v_prec_309_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
v___x_349_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_333_ = v___x_349_;
goto v___jp_332_;
}
else
{
lean_object* v___x_350_; 
v___x_350_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_333_ = v___x_350_;
goto v___jp_332_;
}
v___jp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_334_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__2));
v___x_335_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_336_ = lean_int_dec_lt(v_k_328_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = l_Int_repr(v_k_328_);
lean_dec(v_k_328_);
if (v_isShared_331_ == 0)
{
lean_ctor_set_tag(v___x_330_, 3);
lean_ctor_set(v___x_330_, 0, v___x_337_);
v___x_339_ = v___x_330_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
v___y_320_ = v___x_334_;
v___y_321_ = v___y_333_;
v___y_322_ = v___x_339_;
goto v___jp_319_;
}
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_341_ = lean_unsigned_to_nat(1024u);
v___x_342_ = l_Int_repr(v_k_328_);
lean_dec(v_k_328_);
if (v_isShared_331_ == 0)
{
lean_ctor_set_tag(v___x_330_, 3);
lean_ctor_set(v___x_330_, 0, v___x_342_);
v___x_344_ = v___x_330_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_346_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; 
v___x_345_ = l_Repr_addAppParen(v___x_344_, v___x_341_);
v___y_320_ = v___x_334_;
v___y_321_ = v___y_333_;
v___y_322_ = v___x_345_;
goto v___jp_319_;
}
}
}
}
}
case 1:
{
lean_object* v_k_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_372_; 
v_k_352_ = lean_ctor_get(v_x_308_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_372_ == 0)
{
v___x_354_ = v_x_308_;
v_isShared_355_ = v_isSharedCheck_372_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_k_352_);
lean_dec(v_x_308_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_372_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___y_357_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_unsigned_to_nat(1024u);
v___x_369_ = lean_nat_dec_le(v___x_368_, v_prec_309_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
v___x_370_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_357_ = v___x_370_;
goto v___jp_356_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_357_ = v___x_371_;
goto v___jp_356_;
}
v___jp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_358_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__7));
v___x_359_ = l_Nat_reprFast(v_k_352_);
if (v_isShared_355_ == 0)
{
lean_ctor_set_tag(v___x_354_, 3);
lean_ctor_set(v___x_354_, 0, v___x_359_);
v___x_361_ = v___x_354_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_367_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_358_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
lean_inc(v___y_357_);
v___x_363_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_363_, 0, v___y_357_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = 0;
v___x_365_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*1, v___x_364_);
v___x_366_ = l_Repr_addAppParen(v___x_365_, v_prec_309_);
return v___x_366_;
}
}
}
}
case 2:
{
lean_object* v_k_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_396_; 
v_k_373_ = lean_ctor_get(v_x_308_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_396_ == 0)
{
v___x_375_ = v_x_308_;
v_isShared_376_ = v_isSharedCheck_396_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_k_373_);
lean_dec(v_x_308_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_396_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___y_378_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(1024u);
v___x_393_ = lean_nat_dec_le(v___x_392_, v_prec_309_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
v___x_394_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_378_ = v___x_394_;
goto v___jp_377_;
}
else
{
lean_object* v___x_395_; 
v___x_395_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_378_ = v___x_395_;
goto v___jp_377_;
}
v___jp_377_:
{
lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_379_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__10));
v___x_380_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_381_ = lean_int_dec_lt(v_k_373_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = l_Int_repr(v_k_373_);
lean_dec(v_k_373_);
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 3);
lean_ctor_set(v___x_375_, 0, v___x_382_);
v___x_384_ = v___x_375_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
v___y_311_ = v___x_379_;
v___y_312_ = v___y_378_;
v___y_313_ = v___x_384_;
goto v___jp_310_;
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_386_ = lean_unsigned_to_nat(1024u);
v___x_387_ = l_Int_repr(v_k_373_);
lean_dec(v_k_373_);
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 3);
lean_ctor_set(v___x_375_, 0, v___x_387_);
v___x_389_ = v___x_375_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_391_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; 
v___x_390_ = l_Repr_addAppParen(v___x_389_, v___x_386_);
v___y_311_ = v___x_379_;
v___y_312_ = v___y_378_;
v___y_313_ = v___x_390_;
goto v___jp_310_;
}
}
}
}
}
case 3:
{
lean_object* v_i_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_417_; 
v_i_397_ = lean_ctor_get(v_x_308_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_417_ == 0)
{
v___x_399_ = v_x_308_;
v_isShared_400_ = v_isSharedCheck_417_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_i_397_);
lean_dec(v_x_308_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_417_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___y_402_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_unsigned_to_nat(1024u);
v___x_414_ = lean_nat_dec_le(v___x_413_, v_prec_309_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
v___x_415_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_402_ = v___x_415_;
goto v___jp_401_;
}
else
{
lean_object* v___x_416_; 
v___x_416_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_402_ = v___x_416_;
goto v___jp_401_;
}
v___jp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_403_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__13));
v___x_404_ = l_Nat_reprFast(v_i_397_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_404_);
v___x_406_ = v___x_399_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_412_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_403_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_inc(v___y_402_);
v___x_408_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_408_, 0, v___y_402_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = 0;
v___x_410_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*1, v___x_409_);
v___x_411_ = l_Repr_addAppParen(v___x_410_, v_prec_309_);
return v___x_411_;
}
}
}
}
case 4:
{
lean_object* v_a_418_; lean_object* v___x_419_; lean_object* v___y_421_; uint8_t v___x_429_; 
v_a_418_ = lean_ctor_get(v_x_308_, 0);
lean_inc_ref(v_a_418_);
lean_dec_ref_known(v_x_308_, 1);
v___x_419_ = lean_unsigned_to_nat(1024u);
v___x_429_ = lean_nat_dec_le(v___x_419_, v_prec_309_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
v___x_430_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_421_ = v___x_430_;
goto v___jp_420_;
}
else
{
lean_object* v___x_431_; 
v___x_431_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_421_ = v___x_431_;
goto v___jp_420_;
}
v___jp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_422_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__16));
v___x_423_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_418_, v___x_419_);
v___x_424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
lean_inc(v___y_421_);
v___x_425_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_425_, 0, v___y_421_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = 0;
v___x_427_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set_uint8(v___x_427_, sizeof(void*)*1, v___x_426_);
v___x_428_ = l_Repr_addAppParen(v___x_427_, v_prec_309_);
return v___x_428_;
}
}
case 5:
{
lean_object* v_a_432_; lean_object* v_b_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_456_; 
v_a_432_ = lean_ctor_get(v_x_308_, 0);
v_b_433_ = lean_ctor_get(v_x_308_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_456_ == 0)
{
v___x_435_ = v_x_308_;
v_isShared_436_ = v_isSharedCheck_456_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_b_433_);
lean_inc(v_a_432_);
lean_dec(v_x_308_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_456_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___y_439_; uint8_t v___x_453_; 
v___x_437_ = lean_unsigned_to_nat(1024u);
v___x_453_ = lean_nat_dec_le(v___x_437_, v_prec_309_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
v___x_454_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_439_ = v___x_454_;
goto v___jp_438_;
}
else
{
lean_object* v___x_455_; 
v___x_455_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_439_ = v___x_455_;
goto v___jp_438_;
}
v___jp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_440_ = lean_box(1);
v___x_441_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__19));
v___x_442_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_432_, v___x_437_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_442_);
lean_ctor_set(v___x_435_, 0, v___x_441_);
v___x_444_ = v___x_435_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_442_);
v___x_444_ = v_reuseFailAlloc_452_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_440_);
v___x_446_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_433_, v___x_437_);
v___x_447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
lean_inc(v___y_439_);
v___x_448_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_448_, 0, v___y_439_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = 0;
v___x_450_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*1, v___x_449_);
v___x_451_ = l_Repr_addAppParen(v___x_450_, v_prec_309_);
return v___x_451_;
}
}
}
}
case 6:
{
lean_object* v_a_457_; lean_object* v_b_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_481_; 
v_a_457_ = lean_ctor_get(v_x_308_, 0);
v_b_458_ = lean_ctor_get(v_x_308_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_481_ == 0)
{
v___x_460_ = v_x_308_;
v_isShared_461_ = v_isSharedCheck_481_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_b_458_);
lean_inc(v_a_457_);
lean_dec(v_x_308_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_481_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___y_464_; uint8_t v___x_478_; 
v___x_462_ = lean_unsigned_to_nat(1024u);
v___x_478_ = lean_nat_dec_le(v___x_462_, v_prec_309_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
v___x_479_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_464_ = v___x_479_;
goto v___jp_463_;
}
else
{
lean_object* v___x_480_; 
v___x_480_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_464_ = v___x_480_;
goto v___jp_463_;
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_465_ = lean_box(1);
v___x_466_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__22));
v___x_467_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_457_, v___x_462_);
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 5);
lean_ctor_set(v___x_460_, 1, v___x_467_);
lean_ctor_set(v___x_460_, 0, v___x_466_);
v___x_469_ = v___x_460_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_467_);
v___x_469_ = v_reuseFailAlloc_477_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_465_);
v___x_471_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_458_, v___x_462_);
v___x_472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
lean_inc(v___y_464_);
v___x_473_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_473_, 0, v___y_464_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = 0;
v___x_475_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*1, v___x_474_);
v___x_476_ = l_Repr_addAppParen(v___x_475_, v_prec_309_);
return v___x_476_;
}
}
}
}
case 7:
{
lean_object* v_a_482_; lean_object* v_b_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_506_; 
v_a_482_ = lean_ctor_get(v_x_308_, 0);
v_b_483_ = lean_ctor_get(v_x_308_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_506_ == 0)
{
v___x_485_ = v_x_308_;
v_isShared_486_ = v_isSharedCheck_506_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_b_483_);
lean_inc(v_a_482_);
lean_dec(v_x_308_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_506_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___y_489_; uint8_t v___x_503_; 
v___x_487_ = lean_unsigned_to_nat(1024u);
v___x_503_ = lean_nat_dec_le(v___x_487_, v_prec_309_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_489_ = v___x_504_;
goto v___jp_488_;
}
else
{
lean_object* v___x_505_; 
v___x_505_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_489_ = v___x_505_;
goto v___jp_488_;
}
v___jp_488_:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_490_ = lean_box(1);
v___x_491_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__25));
v___x_492_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_482_, v___x_487_);
if (v_isShared_486_ == 0)
{
lean_ctor_set_tag(v___x_485_, 5);
lean_ctor_set(v___x_485_, 1, v___x_492_);
lean_ctor_set(v___x_485_, 0, v___x_491_);
v___x_494_ = v___x_485_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_492_);
v___x_494_ = v_reuseFailAlloc_502_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_490_);
v___x_496_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_483_, v___x_487_);
v___x_497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_495_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
lean_inc(v___y_489_);
v___x_498_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_498_, 0, v___y_489_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = 0;
v___x_500_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*1, v___x_499_);
v___x_501_ = l_Repr_addAppParen(v___x_500_, v_prec_309_);
return v___x_501_;
}
}
}
}
default: 
{
lean_object* v_a_507_; lean_object* v_k_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_532_; 
v_a_507_ = lean_ctor_get(v_x_308_, 0);
v_k_508_ = lean_ctor_get(v_x_308_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_532_ == 0)
{
v___x_510_ = v_x_308_;
v_isShared_511_ = v_isSharedCheck_532_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_k_508_);
lean_inc(v_a_507_);
lean_dec(v_x_308_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_532_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___y_514_; uint8_t v___x_529_; 
v___x_512_ = lean_unsigned_to_nat(1024u);
v___x_529_ = lean_nat_dec_le(v___x_512_, v_prec_309_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; 
v___x_530_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_514_ = v___x_530_;
goto v___jp_513_;
}
else
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_514_ = v___x_531_;
goto v___jp_513_;
}
v___jp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_515_ = lean_box(1);
v___x_516_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__28));
v___x_517_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_507_, v___x_512_);
if (v_isShared_511_ == 0)
{
lean_ctor_set_tag(v___x_510_, 5);
lean_ctor_set(v___x_510_, 1, v___x_517_);
lean_ctor_set(v___x_510_, 0, v___x_516_);
v___x_519_ = v___x_510_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_517_);
v___x_519_ = v_reuseFailAlloc_528_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v___x_515_);
v___x_521_ = l_Nat_reprFast(v_k_508_);
v___x_522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
v___x_523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_520_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
lean_inc(v___y_514_);
v___x_524_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_524_, 0, v___y_514_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = 0;
v___x_526_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*1, v___x_525_);
v___x_527_ = l_Repr_addAppParen(v___x_526_, v_prec_309_);
return v___x_527_;
}
}
}
}
}
v___jp_310_:
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_inc(v___y_311_);
v___x_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_314_, 0, v___y_311_);
lean_ctor_set(v___x_314_, 1, v___y_313_);
lean_inc(v___y_312_);
v___x_315_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_315_, 0, v___y_312_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = 0;
v___x_317_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*1, v___x_316_);
v___x_318_ = l_Repr_addAppParen(v___x_317_, v_prec_309_);
return v___x_318_;
}
v___jp_319_:
{
lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
lean_inc(v___y_320_);
v___x_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_323_, 0, v___y_320_);
lean_ctor_set(v___x_323_, 1, v___y_322_);
lean_inc(v___y_321_);
v___x_324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_324_, 0, v___y_321_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = 0;
v___x_326_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*1, v___x_325_);
v___x_327_ = l_Repr_addAppParen(v___x_326_, v_prec_309_);
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___boxed(lean_object* v_x_533_, lean_object* v_prec_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_x_533_, v_prec_534_);
lean_dec(v_prec_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___redArg(lean_object* v_ctx_538_, lean_object* v_v_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_RArray_getImpl___redArg(v_ctx_538_, v_v_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___redArg___boxed(lean_object* v_ctx_541_, lean_object* v_v_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Grind_CommRing_Var_denote___redArg(v_ctx_541_, v_v_542_);
lean_dec(v_v_542_);
lean_dec_ref(v_ctx_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote(lean_object* v_00_u03b1_544_, lean_object* v_ctx_545_, lean_object* v_v_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_RArray_getImpl___redArg(v_ctx_545_, v_v_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___boxed(lean_object* v_00_u03b1_548_, lean_object* v_ctx_549_, lean_object* v_v_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Grind_CommRing_Var_denote(v_00_u03b1_548_, v_ctx_549_, v_v_550_);
lean_dec(v_v_550_);
lean_dec_ref(v_ctx_549_);
return v_res_551_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPower_beq(lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v_x_554_; lean_object* v_k_555_; lean_object* v_x_556_; lean_object* v_k_557_; uint8_t v___x_558_; 
v_x_554_ = lean_ctor_get(v_x_552_, 0);
v_k_555_ = lean_ctor_get(v_x_552_, 1);
v_x_556_ = lean_ctor_get(v_x_553_, 0);
v_k_557_ = lean_ctor_get(v_x_553_, 1);
v___x_558_ = lean_nat_dec_eq(v_x_554_, v_x_556_);
if (v___x_558_ == 0)
{
return v___x_558_;
}
else
{
uint8_t v___x_559_; 
v___x_559_ = lean_nat_dec_eq(v_k_555_, v_k_557_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPower_beq___boxed(lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
uint8_t v_res_562_; lean_object* v_r_563_; 
v_res_562_ = l_Lean_Grind_CommRing_instBEqPower_beq(v_x_560_, v_x_561_);
lean_dec_ref(v_x_561_);
lean_dec_ref(v_x_560_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___redArg(lean_object* v_x_566_, lean_object* v_x_567_, lean_object* v_h__1_568_){
_start:
{
lean_object* v_x_569_; lean_object* v_k_570_; lean_object* v_x_571_; lean_object* v_k_572_; lean_object* v___x_573_; 
v_x_569_ = lean_ctor_get(v_x_566_, 0);
lean_inc(v_x_569_);
v_k_570_ = lean_ctor_get(v_x_566_, 1);
lean_inc(v_k_570_);
lean_dec_ref(v_x_566_);
v_x_571_ = lean_ctor_get(v_x_567_, 0);
lean_inc(v_x_571_);
v_k_572_ = lean_ctor_get(v_x_567_, 1);
lean_inc(v_k_572_);
lean_dec_ref(v_x_567_);
v___x_573_ = lean_apply_4(v_h__1_568_, v_x_569_, v_k_570_, v_x_571_, v_k_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter(lean_object* v_motive_574_, lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_h__1_577_, lean_object* v_h__2_578_){
_start:
{
lean_object* v_x_579_; lean_object* v_k_580_; lean_object* v_x_581_; lean_object* v_k_582_; lean_object* v___x_583_; 
v_x_579_ = lean_ctor_get(v_x_575_, 0);
lean_inc(v_x_579_);
v_k_580_ = lean_ctor_get(v_x_575_, 1);
lean_inc(v_k_580_);
lean_dec_ref(v_x_575_);
v_x_581_ = lean_ctor_get(v_x_576_, 0);
lean_inc(v_x_581_);
v_k_582_ = lean_ctor_get(v_x_576_, 1);
lean_inc(v_k_582_);
lean_dec_ref(v_x_576_);
v___x_583_ = lean_apply_4(v_h__1_577_, v_x_579_, v_k_580_, v_x_581_, v_k_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter___boxed(lean_object* v_motive_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_h__1_587_, lean_object* v_h__2_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPower_beq_match__1_splitter(v_motive_584_, v_x_585_, v_x_586_, v_h__1_587_, v_h__2_588_);
lean_dec(v_h__2_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_instReprPower_repr_spec__0(lean_object* v_a_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = lean_nat_to_int(v_a_590_);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(5u);
v___x_606_ = lean_nat_to_int(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0));
v___x_615_ = lean_string_length(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13, &l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13_once, _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13);
v___x_617_ = lean_nat_to_int(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg(lean_object* v_x_622_){
_start:
{
lean_object* v_x_623_; lean_object* v_k_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_658_; 
v_x_623_ = lean_ctor_get(v_x_622_, 0);
v_k_624_ = lean_ctor_get(v_x_622_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_622_);
if (v_isSharedCheck_658_ == 0)
{
v___x_626_ = v_x_622_;
v_isShared_627_ = v_isSharedCheck_658_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_k_624_);
lean_inc(v_x_623_);
lean_dec(v_x_622_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_658_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_628_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5));
v___x_629_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6));
v___x_630_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7, &l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7_once, _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7);
v___x_631_ = l_Nat_reprFast(v_x_623_);
v___x_632_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 4);
lean_ctor_set(v___x_626_, 1, v___x_632_);
lean_ctor_set(v___x_626_, 0, v___x_630_);
v___x_634_ = v___x_626_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_632_);
v___x_634_ = v_reuseFailAlloc_657_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
uint8_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_635_ = 0;
v___x_636_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set_uint8(v___x_636_, sizeof(void*)*1, v___x_635_);
v___x_637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_629_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9));
v___x_639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = lean_box(1);
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11));
v___x_643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_628_);
v___x_645_ = l_Nat_reprFast(v_k_624_);
v___x_646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
v___x_647_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_630_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*1, v___x_635_);
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_644_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14, &l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14_once, _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14);
v___x_651_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15));
v___x_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_649_);
v___x_653_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16));
v___x_654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_650_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*1, v___x_635_);
return v___x_656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr(lean_object* v_x_659_, lean_object* v_prec_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg(v_x_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___boxed(lean_object* v_x_662_, lean_object* v_prec_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Grind_CommRing_instReprPower_repr(v_x_662_, v_prec_663_);
lean_dec(v_prec_663_);
return v_res_664_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePower_hash(lean_object* v_x_671_){
_start:
{
lean_object* v_x_672_; lean_object* v_k_673_; uint64_t v___x_674_; uint64_t v___x_675_; uint64_t v___x_676_; uint64_t v___x_677_; uint64_t v___x_678_; 
v_x_672_ = lean_ctor_get(v_x_671_, 0);
v_k_673_ = lean_ctor_get(v_x_671_, 1);
v___x_674_ = 0ULL;
v___x_675_ = lean_uint64_of_nat(v_x_672_);
v___x_676_ = lean_uint64_mix_hash(v___x_674_, v___x_675_);
v___x_677_ = lean_uint64_of_nat(v_k_673_);
v___x_678_ = lean_uint64_mix_hash(v___x_676_, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePower_hash___boxed(lean_object* v_x_679_){
_start:
{
uint64_t v_res_680_; lean_object* v_r_681_; 
v_res_680_ = l_Lean_Grind_CommRing_instHashablePower_hash(v_x_679_);
lean_dec_ref(v_x_679_);
v_r_681_ = lean_box_uint64(v_res_680_);
return v_r_681_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_varLt(lean_object* v_p_u2081_684_, lean_object* v_p_u2082_685_){
_start:
{
lean_object* v_x_686_; lean_object* v_x_687_; uint8_t v___x_688_; 
v_x_686_ = lean_ctor_get(v_p_u2081_684_, 0);
v_x_687_ = lean_ctor_get(v_p_u2082_685_, 0);
v___x_688_ = l_Nat_blt(v_x_686_, v_x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_varLt___boxed(lean_object* v_p_u2081_689_, lean_object* v_p_u2082_690_){
_start:
{
uint8_t v_res_691_; lean_object* v_r_692_; 
v_res_691_ = l_Lean_Grind_CommRing_Power_varLt(v_p_u2081_689_, v_p_u2082_690_);
lean_dec_ref(v_p_u2082_690_);
lean_dec_ref(v_p_u2081_689_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg(lean_object* v_inst_693_, lean_object* v_ctx_694_, lean_object* v_x_695_){
_start:
{
lean_object* v_ofNat_696_; lean_object* v_npow_697_; lean_object* v_x_698_; lean_object* v_k_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v_ofNat_696_ = lean_ctor_get(v_inst_693_, 3);
lean_inc(v_ofNat_696_);
v_npow_697_ = lean_ctor_get(v_inst_693_, 5);
lean_inc(v_npow_697_);
lean_dec_ref(v_inst_693_);
v_x_698_ = lean_ctor_get(v_x_695_, 0);
lean_inc(v_x_698_);
v_k_699_ = lean_ctor_get(v_x_695_, 1);
lean_inc(v_k_699_);
lean_dec_ref(v_x_695_);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_nat_dec_eq(v_k_699_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; uint8_t v___x_703_; 
lean_dec(v_ofNat_696_);
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = lean_nat_dec_eq(v_k_699_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = l_Lean_RArray_getImpl___redArg(v_ctx_694_, v_x_698_);
lean_dec(v_x_698_);
v___x_705_ = lean_apply_2(v_npow_697_, v___x_704_, v_k_699_);
return v___x_705_;
}
else
{
lean_object* v___x_706_; 
lean_dec(v_k_699_);
lean_dec(v_npow_697_);
v___x_706_ = l_Lean_RArray_getImpl___redArg(v_ctx_694_, v_x_698_);
lean_dec(v_x_698_);
return v___x_706_;
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec(v_k_699_);
lean_dec(v_x_698_);
lean_dec(v_npow_697_);
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_apply_1(v_ofNat_696_, v___x_707_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg___boxed(lean_object* v_inst_709_, lean_object* v_ctx_710_, lean_object* v_x_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Grind_CommRing_Power_denote___redArg(v_inst_709_, v_ctx_710_, v_x_711_);
lean_dec_ref(v_ctx_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote(lean_object* v_00_u03b1_713_, lean_object* v_inst_714_, lean_object* v_ctx_715_, lean_object* v_x_716_){
_start:
{
lean_object* v_ofNat_717_; lean_object* v_npow_718_; lean_object* v_x_719_; lean_object* v_k_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_ofNat_717_ = lean_ctor_get(v_inst_714_, 3);
lean_inc(v_ofNat_717_);
v_npow_718_ = lean_ctor_get(v_inst_714_, 5);
lean_inc(v_npow_718_);
lean_dec_ref(v_inst_714_);
v_x_719_ = lean_ctor_get(v_x_716_, 0);
lean_inc(v_x_719_);
v_k_720_ = lean_ctor_get(v_x_716_, 1);
lean_inc(v_k_720_);
lean_dec_ref(v_x_716_);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = lean_nat_dec_eq(v_k_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; uint8_t v___x_724_; 
lean_dec(v_ofNat_717_);
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = lean_nat_dec_eq(v_k_720_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = l_Lean_RArray_getImpl___redArg(v_ctx_715_, v_x_719_);
lean_dec(v_x_719_);
v___x_726_ = lean_apply_2(v_npow_718_, v___x_725_, v_k_720_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; 
lean_dec(v_k_720_);
lean_dec(v_npow_718_);
v___x_727_ = l_Lean_RArray_getImpl___redArg(v_ctx_715_, v_x_719_);
lean_dec(v_x_719_);
return v___x_727_;
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec(v_k_720_);
lean_dec(v_x_719_);
lean_dec(v_npow_718_);
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_apply_1(v_ofNat_717_, v___x_728_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___boxed(lean_object* v_00_u03b1_730_, lean_object* v_inst_731_, lean_object* v_ctx_732_, lean_object* v_x_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Grind_CommRing_Power_denote(v_00_u03b1_730_, v_inst_731_, v_ctx_732_, v_x_733_);
lean_dec_ref(v_ctx_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx___impl(lean_object* v_x_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = lean_obj_tag_nat(v_x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx___impl___boxed(lean_object* v_x_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Grind_CommRing_Mon_ctorIdx___impl(v_x_737_);
lean_dec(v_x_737_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___redArg(lean_object* v_t_739_, lean_object* v_k_740_){
_start:
{
if (lean_obj_tag(v_t_739_) == 0)
{
return v_k_740_;
}
else
{
lean_object* v_p_741_; lean_object* v_m_742_; lean_object* v___x_743_; 
v_p_741_ = lean_ctor_get(v_t_739_, 0);
lean_inc_ref(v_p_741_);
v_m_742_ = lean_ctor_get(v_t_739_, 1);
lean_inc(v_m_742_);
lean_dec_ref_known(v_t_739_, 2);
v___x_743_ = lean_apply_2(v_k_740_, v_p_741_, v_m_742_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim(lean_object* v_motive_744_, lean_object* v_ctorIdx_745_, lean_object* v_t_746_, lean_object* v_h_747_, lean_object* v_k_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_746_, v_k_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___boxed(lean_object* v_motive_750_, lean_object* v_ctorIdx_751_, lean_object* v_t_752_, lean_object* v_h_753_, lean_object* v_k_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Grind_CommRing_Mon_ctorElim(v_motive_750_, v_ctorIdx_751_, v_t_752_, v_h_753_, v_k_754_);
lean_dec(v_ctorIdx_751_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim___redArg(lean_object* v_t_756_, lean_object* v_unit_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_756_, v_unit_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim(lean_object* v_motive_759_, lean_object* v_t_760_, lean_object* v_h_761_, lean_object* v_unit_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_760_, v_unit_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim___redArg(lean_object* v_t_764_, lean_object* v_mult_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_764_, v_mult_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim(lean_object* v_motive_767_, lean_object* v_t_768_, lean_object* v_h_769_, lean_object* v_mult_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_768_, v_mult_770_);
return v___x_771_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqMon_beq(lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
if (lean_obj_tag(v_x_772_) == 0)
{
if (lean_obj_tag(v_x_773_) == 0)
{
uint8_t v___x_774_; 
v___x_774_ = 1;
return v___x_774_;
}
else
{
uint8_t v___x_775_; 
v___x_775_ = 0;
return v___x_775_;
}
}
else
{
if (lean_obj_tag(v_x_773_) == 1)
{
lean_object* v_p_776_; lean_object* v_m_777_; lean_object* v_p_778_; lean_object* v_m_779_; uint8_t v___x_780_; 
v_p_776_ = lean_ctor_get(v_x_772_, 0);
v_m_777_ = lean_ctor_get(v_x_772_, 1);
v_p_778_ = lean_ctor_get(v_x_773_, 0);
v_m_779_ = lean_ctor_get(v_x_773_, 1);
v___x_780_ = l_Lean_Grind_CommRing_instBEqPower_beq(v_p_776_, v_p_778_);
if (v___x_780_ == 0)
{
return v___x_780_;
}
else
{
v_x_772_ = v_m_777_;
v_x_773_ = v_m_779_;
goto _start;
}
}
else
{
uint8_t v___x_782_; 
v___x_782_ = 0;
return v___x_782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqMon_beq___boxed(lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_x_783_, v_x_784_);
lean_dec(v_x_784_);
lean_dec(v_x_783_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter___redArg(lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_h__1_791_, lean_object* v_h__2_792_, lean_object* v_h__3_793_){
_start:
{
if (lean_obj_tag(v_x_789_) == 0)
{
lean_dec(v_h__2_792_);
if (lean_obj_tag(v_x_790_) == 0)
{
lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec(v_h__3_793_);
v___x_794_ = lean_box(0);
v___x_795_ = lean_apply_1(v_h__1_791_, v___x_794_);
return v___x_795_;
}
else
{
lean_object* v___x_796_; 
lean_dec(v_h__1_791_);
v___x_796_ = lean_apply_4(v_h__3_793_, v_x_789_, v_x_790_, lean_box(0), lean_box(0));
return v___x_796_;
}
}
else
{
lean_dec(v_h__1_791_);
if (lean_obj_tag(v_x_790_) == 1)
{
lean_object* v_p_797_; lean_object* v_m_798_; lean_object* v_p_799_; lean_object* v_m_800_; lean_object* v___x_801_; 
lean_dec(v_h__3_793_);
v_p_797_ = lean_ctor_get(v_x_789_, 0);
lean_inc_ref(v_p_797_);
v_m_798_ = lean_ctor_get(v_x_789_, 1);
lean_inc(v_m_798_);
lean_dec_ref_known(v_x_789_, 2);
v_p_799_ = lean_ctor_get(v_x_790_, 0);
lean_inc_ref(v_p_799_);
v_m_800_ = lean_ctor_get(v_x_790_, 1);
lean_inc(v_m_800_);
lean_dec_ref_known(v_x_790_, 2);
v___x_801_ = lean_apply_4(v_h__2_792_, v_p_797_, v_m_798_, v_p_799_, v_m_800_);
return v___x_801_;
}
else
{
lean_object* v___x_802_; 
lean_dec(v_h__2_792_);
v___x_802_ = lean_apply_4(v_h__3_793_, v_x_789_, v_x_790_, lean_box(0), lean_box(0));
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter(lean_object* v_motive_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_h__1_806_, lean_object* v_h__2_807_, lean_object* v_h__3_808_){
_start:
{
if (lean_obj_tag(v_x_804_) == 0)
{
lean_dec(v_h__2_807_);
if (lean_obj_tag(v_x_805_) == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec(v_h__3_808_);
v___x_809_ = lean_box(0);
v___x_810_ = lean_apply_1(v_h__1_806_, v___x_809_);
return v___x_810_;
}
else
{
lean_object* v___x_811_; 
lean_dec(v_h__1_806_);
v___x_811_ = lean_apply_4(v_h__3_808_, v_x_804_, v_x_805_, lean_box(0), lean_box(0));
return v___x_811_;
}
}
else
{
lean_dec(v_h__1_806_);
if (lean_obj_tag(v_x_805_) == 1)
{
lean_object* v_p_812_; lean_object* v_m_813_; lean_object* v_p_814_; lean_object* v_m_815_; lean_object* v___x_816_; 
lean_dec(v_h__3_808_);
v_p_812_ = lean_ctor_get(v_x_804_, 0);
lean_inc_ref(v_p_812_);
v_m_813_ = lean_ctor_get(v_x_804_, 1);
lean_inc(v_m_813_);
lean_dec_ref_known(v_x_804_, 2);
v_p_814_ = lean_ctor_get(v_x_805_, 0);
lean_inc_ref(v_p_814_);
v_m_815_ = lean_ctor_get(v_x_805_, 1);
lean_inc(v_m_815_);
lean_dec_ref_known(v_x_805_, 2);
v___x_816_ = lean_apply_4(v_h__2_807_, v_p_812_, v_m_813_, v_p_814_, v_m_815_);
return v___x_816_;
}
else
{
lean_object* v___x_817_; 
lean_dec(v_h__2_807_);
v___x_817_ = lean_apply_4(v_h__3_808_, v_x_804_, v_x_805_, lean_box(0), lean_box(0));
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr(lean_object* v_x_827_, lean_object* v_prec_828_){
_start:
{
lean_object* v___y_830_; 
if (lean_obj_tag(v_x_827_) == 0)
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = lean_unsigned_to_nat(1024u);
v___x_837_ = lean_nat_dec_le(v___x_836_, v_prec_828_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
v___x_838_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_830_ = v___x_838_;
goto v___jp_829_;
}
else
{
lean_object* v___x_839_; 
v___x_839_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_830_ = v___x_839_;
goto v___jp_829_;
}
}
else
{
lean_object* v_p_840_; lean_object* v_m_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_864_; 
v_p_840_ = lean_ctor_get(v_x_827_, 0);
v_m_841_ = lean_ctor_get(v_x_827_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_x_827_);
if (v_isSharedCheck_864_ == 0)
{
v___x_843_ = v_x_827_;
v_isShared_844_ = v_isSharedCheck_864_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_m_841_);
lean_inc(v_p_840_);
lean_dec(v_x_827_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_864_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___y_847_; uint8_t v___x_861_; 
v___x_845_ = lean_unsigned_to_nat(1024u);
v___x_861_ = lean_nat_dec_le(v___x_845_, v_prec_828_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
v___x_862_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_847_ = v___x_862_;
goto v___jp_846_;
}
else
{
lean_object* v___x_863_; 
v___x_863_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_847_ = v___x_863_;
goto v___jp_846_;
}
v___jp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_848_ = lean_box(1);
v___x_849_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprMon_repr___closed__4));
v___x_850_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg(v_p_840_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 5);
lean_ctor_set(v___x_843_, 1, v___x_850_);
lean_ctor_set(v___x_843_, 0, v___x_849_);
v___x_852_ = v___x_843_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_850_);
v___x_852_ = v_reuseFailAlloc_860_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v___x_848_);
v___x_854_ = l_Lean_Grind_CommRing_instReprMon_repr(v_m_841_, v___x_845_);
v___x_855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
lean_inc(v___y_847_);
v___x_856_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_856_, 0, v___y_847_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = 0;
v___x_858_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*1, v___x_857_);
v___x_859_ = l_Repr_addAppParen(v___x_858_, v_prec_828_);
return v___x_859_;
}
}
}
}
v___jp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_831_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprMon_repr___closed__1));
lean_inc(v___y_830_);
v___x_832_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_832_, 0, v___y_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = 0;
v___x_834_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*1, v___x_833_);
v___x_835_ = l_Repr_addAppParen(v___x_834_, v_prec_828_);
return v___x_835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr___boxed(lean_object* v_x_865_, lean_object* v_prec_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Grind_CommRing_instReprMon_repr(v_x_865_, v_prec_866_);
lean_dec(v_prec_866_);
return v_res_867_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedMon_default(void){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = lean_box(0);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedMon(void){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = lean_box(0);
return v___x_871_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashableMon_hash(lean_object* v_x_872_){
_start:
{
if (lean_obj_tag(v_x_872_) == 0)
{
uint64_t v___x_873_; 
v___x_873_ = 0ULL;
return v___x_873_;
}
else
{
lean_object* v_p_874_; lean_object* v_m_875_; uint64_t v___x_876_; uint64_t v___x_877_; uint64_t v___x_878_; uint64_t v___x_879_; uint64_t v___x_880_; 
v_p_874_ = lean_ctor_get(v_x_872_, 0);
v_m_875_ = lean_ctor_get(v_x_872_, 1);
v___x_876_ = 1ULL;
v___x_877_ = l_Lean_Grind_CommRing_instHashablePower_hash(v_p_874_);
v___x_878_ = lean_uint64_mix_hash(v___x_876_, v___x_877_);
v___x_879_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_m_875_);
v___x_880_ = lean_uint64_mix_hash(v___x_878_, v___x_879_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableMon_hash___boxed(lean_object* v_x_881_){
_start:
{
uint64_t v_res_882_; lean_object* v_r_883_; 
v_res_882_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_x_881_);
lean_dec(v_x_881_);
v_r_883_ = lean_box_uint64(v_res_882_);
return v_r_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg(lean_object* v_inst_886_, lean_object* v_ctx_887_, lean_object* v_x_888_){
_start:
{
if (lean_obj_tag(v_x_888_) == 0)
{
lean_object* v_ofNat_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_ofNat_889_ = lean_ctor_get(v_inst_886_, 3);
lean_inc(v_ofNat_889_);
lean_dec_ref(v_inst_886_);
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = lean_apply_1(v_ofNat_889_, v___x_890_);
return v___x_891_;
}
else
{
lean_object* v_toMul_892_; lean_object* v_ofNat_893_; lean_object* v_npow_894_; lean_object* v_p_895_; lean_object* v_m_896_; lean_object* v___y_898_; lean_object* v_x_901_; lean_object* v_k_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v_toMul_892_ = lean_ctor_get(v_inst_886_, 1);
lean_inc(v_toMul_892_);
v_ofNat_893_ = lean_ctor_get(v_inst_886_, 3);
v_npow_894_ = lean_ctor_get(v_inst_886_, 5);
v_p_895_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_p_895_);
v_m_896_ = lean_ctor_get(v_x_888_, 1);
lean_inc(v_m_896_);
lean_dec_ref_known(v_x_888_, 2);
v_x_901_ = lean_ctor_get(v_p_895_, 0);
lean_inc(v_x_901_);
v_k_902_ = lean_ctor_get(v_p_895_, 1);
lean_inc(v_k_902_);
lean_dec_ref(v_p_895_);
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = lean_nat_dec_eq(v_k_902_, v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_dec_eq(v_k_902_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = l_Lean_RArray_getImpl___redArg(v_ctx_887_, v_x_901_);
lean_dec(v_x_901_);
lean_inc(v_npow_894_);
v___x_908_ = lean_apply_2(v_npow_894_, v___x_907_, v_k_902_);
v___y_898_ = v___x_908_;
goto v___jp_897_;
}
else
{
lean_object* v___x_909_; 
lean_dec(v_k_902_);
v___x_909_ = l_Lean_RArray_getImpl___redArg(v_ctx_887_, v_x_901_);
lean_dec(v_x_901_);
v___y_898_ = v___x_909_;
goto v___jp_897_;
}
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec(v_k_902_);
lean_dec(v_x_901_);
v___x_910_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_893_);
v___x_911_ = lean_apply_1(v_ofNat_893_, v___x_910_);
v___y_898_ = v___x_911_;
goto v___jp_897_;
}
v___jp_897_:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_886_, v_ctx_887_, v_m_896_);
v___x_900_ = lean_apply_2(v_toMul_892_, v___y_898_, v___x_899_);
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg___boxed(lean_object* v_inst_912_, lean_object* v_ctx_913_, lean_object* v_x_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_912_, v_ctx_913_, v_x_914_);
lean_dec_ref(v_ctx_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote(lean_object* v_00_u03b1_916_, lean_object* v_inst_917_, lean_object* v_ctx_918_, lean_object* v_x_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_917_, v_ctx_918_, v_x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___boxed(lean_object* v_00_u03b1_921_, lean_object* v_inst_922_, lean_object* v_ctx_923_, lean_object* v_x_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_Grind_CommRing_Mon_denote(v_00_u03b1_921_, v_inst_922_, v_ctx_923_, v_x_924_);
lean_dec_ref(v_ctx_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(lean_object* v_inst_926_, lean_object* v_ctx_927_, lean_object* v_m_928_, lean_object* v_acc_929_){
_start:
{
if (lean_obj_tag(v_m_928_) == 0)
{
lean_dec_ref(v_inst_926_);
return v_acc_929_;
}
else
{
lean_object* v_toMul_930_; lean_object* v_ofNat_931_; lean_object* v_npow_932_; lean_object* v_p_933_; lean_object* v_m_934_; lean_object* v___y_936_; lean_object* v_x_939_; lean_object* v_k_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v_toMul_930_ = lean_ctor_get(v_inst_926_, 1);
v_ofNat_931_ = lean_ctor_get(v_inst_926_, 3);
v_npow_932_ = lean_ctor_get(v_inst_926_, 5);
v_p_933_ = lean_ctor_get(v_m_928_, 0);
lean_inc_ref(v_p_933_);
v_m_934_ = lean_ctor_get(v_m_928_, 1);
lean_inc(v_m_934_);
lean_dec_ref_known(v_m_928_, 2);
v_x_939_ = lean_ctor_get(v_p_933_, 0);
lean_inc(v_x_939_);
v_k_940_ = lean_ctor_get(v_p_933_, 1);
lean_inc(v_k_940_);
lean_dec_ref(v_p_933_);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_nat_dec_eq(v_k_940_, v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_dec_eq(v_k_940_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = l_Lean_RArray_getImpl___redArg(v_ctx_927_, v_x_939_);
lean_dec(v_x_939_);
lean_inc(v_npow_932_);
v___x_946_ = lean_apply_2(v_npow_932_, v___x_945_, v_k_940_);
v___y_936_ = v___x_946_;
goto v___jp_935_;
}
else
{
lean_object* v___x_947_; 
lean_dec(v_k_940_);
v___x_947_ = l_Lean_RArray_getImpl___redArg(v_ctx_927_, v_x_939_);
lean_dec(v_x_939_);
v___y_936_ = v___x_947_;
goto v___jp_935_;
}
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v_k_940_);
lean_dec(v_x_939_);
v___x_948_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_931_);
v___x_949_ = lean_apply_1(v_ofNat_931_, v___x_948_);
v___y_936_ = v___x_949_;
goto v___jp_935_;
}
v___jp_935_:
{
lean_object* v___x_937_; 
lean_inc(v_toMul_930_);
v___x_937_ = lean_apply_2(v_toMul_930_, v_acc_929_, v___y_936_);
v_m_928_ = v_m_934_;
v_acc_929_ = v___x_937_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg___boxed(lean_object* v_inst_950_, lean_object* v_ctx_951_, lean_object* v_m_952_, lean_object* v_acc_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_950_, v_ctx_951_, v_m_952_, v_acc_953_);
lean_dec_ref(v_ctx_951_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go(lean_object* v_00_u03b1_955_, lean_object* v_inst_956_, lean_object* v_ctx_957_, lean_object* v_m_958_, lean_object* v_acc_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_956_, v_ctx_957_, v_m_958_, v_acc_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___boxed(lean_object* v_00_u03b1_961_, lean_object* v_inst_962_, lean_object* v_ctx_963_, lean_object* v_m_964_, lean_object* v_acc_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_Grind_CommRing_Mon_denote_x27_go(v_00_u03b1_961_, v_inst_962_, v_ctx_963_, v_m_964_, v_acc_965_);
lean_dec_ref(v_ctx_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg(lean_object* v_inst_967_, lean_object* v_ctx_968_, lean_object* v_m_969_){
_start:
{
if (lean_obj_tag(v_m_969_) == 0)
{
lean_object* v_ofNat_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_ofNat_970_ = lean_ctor_get(v_inst_967_, 3);
lean_inc(v_ofNat_970_);
lean_dec_ref(v_inst_967_);
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_apply_1(v_ofNat_970_, v___x_971_);
return v___x_972_;
}
else
{
lean_object* v_p_973_; lean_object* v_m_974_; lean_object* v_ofNat_975_; lean_object* v_npow_976_; lean_object* v_x_977_; lean_object* v_k_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v_p_973_ = lean_ctor_get(v_m_969_, 0);
lean_inc_ref(v_p_973_);
v_m_974_ = lean_ctor_get(v_m_969_, 1);
lean_inc(v_m_974_);
lean_dec_ref_known(v_m_969_, 2);
v_ofNat_975_ = lean_ctor_get(v_inst_967_, 3);
v_npow_976_ = lean_ctor_get(v_inst_967_, 5);
v_x_977_ = lean_ctor_get(v_p_973_, 0);
lean_inc(v_x_977_);
v_k_978_ = lean_ctor_get(v_p_973_, 1);
lean_inc(v_k_978_);
lean_dec_ref(v_p_973_);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_nat_dec_eq(v_k_978_, v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = lean_unsigned_to_nat(1u);
v___x_982_ = lean_nat_dec_eq(v_k_978_, v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = l_Lean_RArray_getImpl___redArg(v_ctx_968_, v_x_977_);
lean_dec(v_x_977_);
lean_inc(v_npow_976_);
v___x_984_ = lean_apply_2(v_npow_976_, v___x_983_, v_k_978_);
v___x_985_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_967_, v_ctx_968_, v_m_974_, v___x_984_);
return v___x_985_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec(v_k_978_);
v___x_986_ = l_Lean_RArray_getImpl___redArg(v_ctx_968_, v_x_977_);
lean_dec(v_x_977_);
v___x_987_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_967_, v_ctx_968_, v_m_974_, v___x_986_);
return v___x_987_;
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec(v_k_978_);
lean_dec(v_x_977_);
v___x_988_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_975_);
v___x_989_ = lean_apply_1(v_ofNat_975_, v___x_988_);
v___x_990_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_967_, v_ctx_968_, v_m_974_, v___x_989_);
return v___x_990_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg___boxed(lean_object* v_inst_991_, lean_object* v_ctx_992_, lean_object* v_m_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_Grind_CommRing_Mon_denote_x27___redArg(v_inst_991_, v_ctx_992_, v_m_993_);
lean_dec_ref(v_ctx_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27(lean_object* v_00_u03b1_995_, lean_object* v_inst_996_, lean_object* v_ctx_997_, lean_object* v_m_998_){
_start:
{
if (lean_obj_tag(v_m_998_) == 0)
{
lean_object* v_ofNat_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_ofNat_999_ = lean_ctor_get(v_inst_996_, 3);
lean_inc(v_ofNat_999_);
lean_dec_ref(v_inst_996_);
v___x_1000_ = lean_unsigned_to_nat(1u);
v___x_1001_ = lean_apply_1(v_ofNat_999_, v___x_1000_);
return v___x_1001_;
}
else
{
lean_object* v_p_1002_; lean_object* v_m_1003_; lean_object* v_ofNat_1004_; lean_object* v_npow_1005_; lean_object* v_x_1006_; lean_object* v_k_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v_p_1002_ = lean_ctor_get(v_m_998_, 0);
lean_inc_ref(v_p_1002_);
v_m_1003_ = lean_ctor_get(v_m_998_, 1);
lean_inc(v_m_1003_);
lean_dec_ref_known(v_m_998_, 2);
v_ofNat_1004_ = lean_ctor_get(v_inst_996_, 3);
v_npow_1005_ = lean_ctor_get(v_inst_996_, 5);
v_x_1006_ = lean_ctor_get(v_p_1002_, 0);
lean_inc(v_x_1006_);
v_k_1007_ = lean_ctor_get(v_p_1002_, 1);
lean_inc(v_k_1007_);
lean_dec_ref(v_p_1002_);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_nat_dec_eq(v_k_1007_, v___x_1008_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = lean_unsigned_to_nat(1u);
v___x_1011_ = lean_nat_dec_eq(v_k_1007_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = l_Lean_RArray_getImpl___redArg(v_ctx_997_, v_x_1006_);
lean_dec(v_x_1006_);
lean_inc(v_npow_1005_);
v___x_1013_ = lean_apply_2(v_npow_1005_, v___x_1012_, v_k_1007_);
v___x_1014_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_996_, v_ctx_997_, v_m_1003_, v___x_1013_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec(v_k_1007_);
v___x_1015_ = l_Lean_RArray_getImpl___redArg(v_ctx_997_, v_x_1006_);
lean_dec(v_x_1006_);
v___x_1016_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_996_, v_ctx_997_, v_m_1003_, v___x_1015_);
return v___x_1016_;
}
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_dec(v_k_1007_);
lean_dec(v_x_1006_);
v___x_1017_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_1004_);
v___x_1018_ = lean_apply_1(v_ofNat_1004_, v___x_1017_);
v___x_1019_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_996_, v_ctx_997_, v_m_1003_, v___x_1018_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___boxed(lean_object* v_00_u03b1_1020_, lean_object* v_inst_1021_, lean_object* v_ctx_1022_, lean_object* v_m_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Grind_CommRing_Mon_denote_x27(v_00_u03b1_1020_, v_inst_1021_, v_ctx_1022_, v_m_1023_);
lean_dec_ref(v_ctx_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ofVar(lean_object* v_x_1025_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_box(0);
v___x_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat(lean_object* v_m_u2081_1030_, lean_object* v_m_u2082_1031_){
_start:
{
if (lean_obj_tag(v_m_u2081_1030_) == 0)
{
lean_inc(v_m_u2082_1031_);
return v_m_u2082_1031_;
}
else
{
lean_object* v_p_1032_; lean_object* v_m_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1041_; 
v_p_1032_ = lean_ctor_get(v_m_u2081_1030_, 0);
v_m_1033_ = lean_ctor_get(v_m_u2081_1030_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_m_u2081_1030_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1035_ = v_m_u2081_1030_;
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_m_1033_);
lean_inc(v_p_1032_);
lean_dec(v_m_u2081_1030_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = l_Lean_Grind_CommRing_Mon_concat(v_m_1033_, v_m_u2082_1031_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v___x_1037_);
v___x_1039_ = v___x_1035_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_p_1032_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat___boxed(lean_object* v_m_u2081_1042_, lean_object* v_m_u2082_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_1042_, v_m_u2082_1043_);
lean_dec(v_m_u2082_1043_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow(lean_object* v_pw_1045_, lean_object* v_m_1046_){
_start:
{
if (lean_obj_tag(v_m_1046_) == 0)
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1047_, 0, v_pw_1045_);
lean_ctor_set(v___x_1047_, 1, v_m_1046_);
return v___x_1047_;
}
else
{
lean_object* v_p_1048_; lean_object* v_m_1049_; uint8_t v___x_1050_; 
v_p_1048_ = lean_ctor_get(v_m_1046_, 0);
lean_inc_ref(v_p_1048_);
v_m_1049_ = lean_ctor_get(v_m_1046_, 1);
v___x_1050_ = l_Lean_Grind_CommRing_Power_varLt(v_pw_1045_, v_p_1048_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1074_; 
lean_inc(v_m_1049_);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_m_1046_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; lean_object* v_unused_1076_; 
v_unused_1075_ = lean_ctor_get(v_m_1046_, 1);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_m_1046_, 0);
lean_dec(v_unused_1076_);
v___x_1052_ = v_m_1046_;
v_isShared_1053_ = v_isSharedCheck_1074_;
goto v_resetjp_1051_;
}
else
{
lean_dec(v_m_1046_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1074_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
uint8_t v___x_1054_; 
v___x_1054_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1048_, v_pw_1045_);
if (v___x_1054_ == 0)
{
lean_object* v_x_1055_; lean_object* v_k_1056_; lean_object* v_k_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1068_; 
v_x_1055_ = lean_ctor_get(v_pw_1045_, 0);
lean_inc(v_x_1055_);
v_k_1056_ = lean_ctor_get(v_pw_1045_, 1);
lean_inc(v_k_1056_);
lean_dec_ref(v_pw_1045_);
v_k_1057_ = lean_ctor_get(v_p_1048_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_p_1048_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v_p_1048_, 0);
lean_dec(v_unused_1069_);
v___x_1059_ = v_p_1048_;
v_isShared_1060_ = v_isSharedCheck_1068_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_k_1057_);
lean_dec(v_p_1048_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1068_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = lean_nat_add(v_k_1056_, v_k_1057_);
lean_dec(v_k_1057_);
lean_dec(v_k_1056_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 1, v___x_1061_);
lean_ctor_set(v___x_1059_, 0, v_x_1055_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_x_1055_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1065_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1063_);
v___x_1065_ = v___x_1052_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_m_1049_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1070_ = l_Lean_Grind_CommRing_Mon_mulPow(v_pw_1045_, v_m_1049_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 1, v___x_1070_);
v___x_1072_ = v___x_1052_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_p_1048_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
lean_object* v___x_1077_; 
lean_dec_ref(v_p_1048_);
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_pw_1045_);
lean_ctor_set(v___x_1077_, 1, v_m_1046_);
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow__nc(lean_object* v_pw_1078_, lean_object* v_m_1079_){
_start:
{
if (lean_obj_tag(v_m_1079_) == 0)
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_pw_1078_);
lean_ctor_set(v___x_1080_, 1, v_m_1079_);
return v___x_1080_;
}
else
{
lean_object* v_p_1081_; lean_object* v_m_1082_; lean_object* v_x_1083_; lean_object* v_k_1084_; lean_object* v_x_1085_; lean_object* v_k_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1105_; 
v_p_1081_ = lean_ctor_get(v_m_1079_, 0);
lean_inc_ref(v_p_1081_);
v_m_1082_ = lean_ctor_get(v_m_1079_, 1);
v_x_1083_ = lean_ctor_get(v_pw_1078_, 0);
v_k_1084_ = lean_ctor_get(v_pw_1078_, 1);
v_x_1085_ = lean_ctor_get(v_p_1081_, 0);
v_k_1086_ = lean_ctor_get(v_p_1081_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_p_1081_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1088_ = v_p_1081_;
v_isShared_1089_ = v_isSharedCheck_1105_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_k_1086_);
lean_inc(v_x_1085_);
lean_dec(v_p_1081_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1105_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
uint8_t v___x_1090_; 
v___x_1090_ = lean_nat_dec_eq(v_x_1083_, v_x_1085_);
lean_dec(v_x_1085_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; 
lean_del_object(v___x_1088_);
lean_dec(v_k_1086_);
v___x_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_pw_1078_);
lean_ctor_set(v___x_1091_, 1, v_m_1079_);
return v___x_1091_;
}
else
{
lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1102_; 
lean_inc(v_k_1084_);
lean_inc(v_x_1083_);
lean_inc(v_m_1082_);
lean_dec_ref(v_pw_1078_);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_m_1079_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; lean_object* v_unused_1104_; 
v_unused_1103_ = lean_ctor_get(v_m_1079_, 1);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_m_1079_, 0);
lean_dec(v_unused_1104_);
v___x_1093_ = v_m_1079_;
v_isShared_1094_ = v_isSharedCheck_1102_;
goto v_resetjp_1092_;
}
else
{
lean_dec(v_m_1079_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1102_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = lean_nat_add(v_k_1084_, v_k_1086_);
lean_dec(v_k_1086_);
lean_dec(v_k_1084_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___x_1095_);
lean_ctor_set(v___x_1088_, 0, v_x_1083_);
v___x_1097_ = v___x_1088_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_x_1083_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1099_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1097_);
v___x_1099_ = v___x_1093_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_m_1082_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length(lean_object* v_x_1106_){
_start:
{
if (lean_obj_tag(v_x_1106_) == 0)
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_unsigned_to_nat(0u);
return v___x_1107_;
}
else
{
lean_object* v_m_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v_m_1108_ = lean_ctor_get(v_x_1106_, 1);
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = l_Lean_Grind_CommRing_Mon_length(v_m_1108_);
v___x_1111_ = lean_nat_add(v___x_1109_, v___x_1110_);
lean_dec(v___x_1110_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length___boxed(lean_object* v_x_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_Grind_CommRing_Mon_length(v_x_1112_);
lean_dec(v_x_1112_);
return v_res_1113_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_hugeFuel(void){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_unsigned_to_nat(1000000u);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go(lean_object* v_fuel_1115_, lean_object* v_m_u2081_1116_, lean_object* v_m_u2082_1117_){
_start:
{
lean_object* v_zero_1118_; uint8_t v_isZero_1119_; 
v_zero_1118_ = lean_unsigned_to_nat(0u);
v_isZero_1119_ = lean_nat_dec_eq(v_fuel_1115_, v_zero_1118_);
if (v_isZero_1119_ == 1)
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_1116_, v_m_u2082_1117_);
lean_dec(v_m_u2082_1117_);
return v___x_1120_;
}
else
{
if (lean_obj_tag(v_m_u2082_1117_) == 0)
{
return v_m_u2081_1116_;
}
else
{
if (lean_obj_tag(v_m_u2081_1116_) == 0)
{
return v_m_u2082_1117_;
}
else
{
lean_object* v_p_1121_; lean_object* v_m_1122_; lean_object* v_p_1123_; lean_object* v_m_1124_; lean_object* v_one_1125_; lean_object* v_n_1126_; uint8_t v___x_1127_; 
v_p_1121_ = lean_ctor_get(v_m_u2082_1117_, 0);
lean_inc_ref(v_p_1121_);
v_m_1122_ = lean_ctor_get(v_m_u2082_1117_, 1);
v_p_1123_ = lean_ctor_get(v_m_u2081_1116_, 0);
v_m_1124_ = lean_ctor_get(v_m_u2081_1116_, 1);
v_one_1125_ = lean_unsigned_to_nat(1u);
v_n_1126_ = lean_nat_sub(v_fuel_1115_, v_one_1125_);
v___x_1127_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1123_, v_p_1121_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1158_; 
lean_inc(v_m_1122_);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_m_u2082_1117_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; lean_object* v_unused_1160_; 
v_unused_1159_ = lean_ctor_get(v_m_u2082_1117_, 1);
lean_dec(v_unused_1159_);
v_unused_1160_ = lean_ctor_get(v_m_u2082_1117_, 0);
lean_dec(v_unused_1160_);
v___x_1129_ = v_m_u2082_1117_;
v_isShared_1130_ = v_isSharedCheck_1158_;
goto v_resetjp_1128_;
}
else
{
lean_dec(v_m_u2082_1117_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1158_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1121_, v_p_1123_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1151_; 
lean_inc(v_m_1124_);
lean_inc_ref(v_p_1123_);
lean_del_object(v___x_1129_);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_m_u2081_1116_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; lean_object* v_unused_1153_; 
v_unused_1152_ = lean_ctor_get(v_m_u2081_1116_, 1);
lean_dec(v_unused_1152_);
v_unused_1153_ = lean_ctor_get(v_m_u2081_1116_, 0);
lean_dec(v_unused_1153_);
v___x_1133_ = v_m_u2081_1116_;
v_isShared_1134_ = v_isSharedCheck_1151_;
goto v_resetjp_1132_;
}
else
{
lean_dec(v_m_u2081_1116_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1151_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v_x_1135_; lean_object* v_k_1136_; lean_object* v_k_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1149_; 
v_x_1135_ = lean_ctor_get(v_p_1123_, 0);
lean_inc(v_x_1135_);
v_k_1136_ = lean_ctor_get(v_p_1123_, 1);
lean_inc(v_k_1136_);
lean_dec_ref(v_p_1123_);
v_k_1137_ = lean_ctor_get(v_p_1121_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_p_1121_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; 
v_unused_1150_ = lean_ctor_get(v_p_1121_, 0);
lean_dec(v_unused_1150_);
v___x_1139_ = v_p_1121_;
v_isShared_1140_ = v_isSharedCheck_1149_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_k_1137_);
lean_dec(v_p_1121_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1149_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1141_ = lean_nat_add(v_k_1136_, v_k_1137_);
lean_dec(v_k_1137_);
lean_dec(v_k_1136_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v___x_1141_);
lean_ctor_set(v___x_1139_, 0, v_x_1135_);
v___x_1143_ = v___x_1139_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_x_1135_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1144_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1126_, v_m_1124_, v_m_1122_);
lean_dec(v_n_1126_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 1, v___x_1144_);
lean_ctor_set(v___x_1133_, 0, v___x_1143_);
v___x_1146_ = v___x_1133_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1126_, v_m_u2081_1116_, v_m_1122_);
lean_dec(v_n_1126_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 1, v___x_1154_);
v___x_1156_ = v___x_1129_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_p_1121_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
else
{
lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1168_; 
lean_inc(v_m_1124_);
lean_inc_ref(v_p_1123_);
lean_dec_ref(v_p_1121_);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_m_u2081_1116_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; lean_object* v_unused_1170_; 
v_unused_1169_ = lean_ctor_get(v_m_u2081_1116_, 1);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_m_u2081_1116_, 0);
lean_dec(v_unused_1170_);
v___x_1162_ = v_m_u2081_1116_;
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
else
{
lean_dec(v_m_u2081_1116_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1126_, v_m_1124_, v_m_u2082_1117_);
lean_dec(v_n_1126_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_p_1123_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go___boxed(lean_object* v_fuel_1171_, lean_object* v_m_u2081_1172_, lean_object* v_m_u2082_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Grind_CommRing_Mon_mul_go(v_fuel_1171_, v_m_u2081_1172_, v_m_u2082_1173_);
lean_dec(v_fuel_1171_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul(lean_object* v_m_u2081_1175_, lean_object* v_m_u2082_1176_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_unsigned_to_nat(1000000u);
v___x_1178_ = l_Lean_Grind_CommRing_Mon_mul_go(v___x_1177_, v_m_u2081_1175_, v_m_u2082_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object* v_fuel_1179_, lean_object* v_h__1_1180_, lean_object* v_h__2_1181_){
_start:
{
lean_object* v_zero_1182_; uint8_t v_isZero_1183_; 
v_zero_1182_ = lean_unsigned_to_nat(0u);
v_isZero_1183_ = lean_nat_dec_eq(v_fuel_1179_, v_zero_1182_);
if (v_isZero_1183_ == 1)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec(v_h__2_1181_);
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_apply_1(v_h__1_1180_, v___x_1184_);
return v___x_1185_;
}
else
{
lean_object* v_one_1186_; lean_object* v_n_1187_; lean_object* v___x_1188_; 
lean_dec(v_h__1_1180_);
v_one_1186_ = lean_unsigned_to_nat(1u);
v_n_1187_ = lean_nat_sub(v_fuel_1179_, v_one_1186_);
v___x_1188_ = lean_apply_1(v_h__2_1181_, v_n_1187_);
return v___x_1188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object* v_fuel_1189_, lean_object* v_h__1_1190_, lean_object* v_h__2_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(v_fuel_1189_, v_h__1_1190_, v_h__2_1191_);
lean_dec(v_fuel_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object* v_motive_1193_, lean_object* v_fuel_1194_, lean_object* v_h__1_1195_, lean_object* v_h__2_1196_){
_start:
{
lean_object* v_zero_1197_; uint8_t v_isZero_1198_; 
v_zero_1197_ = lean_unsigned_to_nat(0u);
v_isZero_1198_ = lean_nat_dec_eq(v_fuel_1194_, v_zero_1197_);
if (v_isZero_1198_ == 1)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec(v_h__2_1196_);
v___x_1199_ = lean_box(0);
v___x_1200_ = lean_apply_1(v_h__1_1195_, v___x_1199_);
return v___x_1200_;
}
else
{
lean_object* v_one_1201_; lean_object* v_n_1202_; lean_object* v___x_1203_; 
lean_dec(v_h__1_1195_);
v_one_1201_ = lean_unsigned_to_nat(1u);
v_n_1202_ = lean_nat_sub(v_fuel_1194_, v_one_1201_);
v___x_1203_ = lean_apply_1(v_h__2_1196_, v_n_1202_);
return v___x_1203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object* v_motive_1204_, lean_object* v_fuel_1205_, lean_object* v_h__1_1206_, lean_object* v_h__2_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(v_motive_1204_, v_fuel_1205_, v_h__1_1206_, v_h__2_1207_);
lean_dec(v_fuel_1205_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter___redArg(lean_object* v_m_u2081_1209_, lean_object* v_m_u2082_1210_, lean_object* v_h__1_1211_, lean_object* v_h__2_1212_, lean_object* v_h__3_1213_){
_start:
{
if (lean_obj_tag(v_m_u2082_1210_) == 0)
{
lean_object* v___x_1214_; 
lean_dec(v_h__3_1213_);
lean_dec(v_h__2_1212_);
v___x_1214_ = lean_apply_1(v_h__1_1211_, v_m_u2081_1209_);
return v___x_1214_;
}
else
{
lean_dec(v_h__1_1211_);
if (lean_obj_tag(v_m_u2081_1209_) == 0)
{
lean_object* v___x_1215_; 
lean_dec(v_h__3_1213_);
v___x_1215_ = lean_apply_2(v_h__2_1212_, v_m_u2082_1210_, lean_box(0));
return v___x_1215_;
}
else
{
lean_object* v_p_1216_; lean_object* v_m_1217_; lean_object* v_p_1218_; lean_object* v_m_1219_; lean_object* v___x_1220_; 
lean_dec(v_h__2_1212_);
v_p_1216_ = lean_ctor_get(v_m_u2082_1210_, 0);
lean_inc_ref(v_p_1216_);
v_m_1217_ = lean_ctor_get(v_m_u2082_1210_, 1);
lean_inc(v_m_1217_);
lean_dec_ref_known(v_m_u2082_1210_, 2);
v_p_1218_ = lean_ctor_get(v_m_u2081_1209_, 0);
lean_inc_ref(v_p_1218_);
v_m_1219_ = lean_ctor_get(v_m_u2081_1209_, 1);
lean_inc(v_m_1219_);
lean_dec_ref_known(v_m_u2081_1209_, 2);
v___x_1220_ = lean_apply_4(v_h__3_1213_, v_p_1218_, v_m_1219_, v_p_1216_, v_m_1217_);
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter(lean_object* v_motive_1221_, lean_object* v_m_u2081_1222_, lean_object* v_m_u2082_1223_, lean_object* v_h__1_1224_, lean_object* v_h__2_1225_, lean_object* v_h__3_1226_){
_start:
{
if (lean_obj_tag(v_m_u2082_1223_) == 0)
{
lean_object* v___x_1227_; 
lean_dec(v_h__3_1226_);
lean_dec(v_h__2_1225_);
v___x_1227_ = lean_apply_1(v_h__1_1224_, v_m_u2081_1222_);
return v___x_1227_;
}
else
{
lean_dec(v_h__1_1224_);
if (lean_obj_tag(v_m_u2081_1222_) == 0)
{
lean_object* v___x_1228_; 
lean_dec(v_h__3_1226_);
v___x_1228_ = lean_apply_2(v_h__2_1225_, v_m_u2082_1223_, lean_box(0));
return v___x_1228_;
}
else
{
lean_object* v_p_1229_; lean_object* v_m_1230_; lean_object* v_p_1231_; lean_object* v_m_1232_; lean_object* v___x_1233_; 
lean_dec(v_h__2_1225_);
v_p_1229_ = lean_ctor_get(v_m_u2082_1223_, 0);
lean_inc_ref(v_p_1229_);
v_m_1230_ = lean_ctor_get(v_m_u2082_1223_, 1);
lean_inc(v_m_1230_);
lean_dec_ref_known(v_m_u2082_1223_, 2);
v_p_1231_ = lean_ctor_get(v_m_u2081_1222_, 0);
lean_inc_ref(v_p_1231_);
v_m_1232_ = lean_ctor_get(v_m_u2081_1222_, 1);
lean_inc(v_m_1232_);
lean_dec_ref_known(v_m_u2081_1222_, 2);
v___x_1233_ = lean_apply_4(v_h__3_1226_, v_p_1231_, v_m_1232_, v_p_1229_, v_m_1230_);
return v___x_1233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul__nc(lean_object* v_m_u2081_1234_, lean_object* v_m_u2082_1235_){
_start:
{
if (lean_obj_tag(v_m_u2081_1234_) == 0)
{
return v_m_u2082_1235_;
}
else
{
lean_object* v_m_1236_; 
v_m_1236_ = lean_ctor_get(v_m_u2081_1234_, 1);
if (lean_obj_tag(v_m_1236_) == 0)
{
lean_object* v_p_1237_; lean_object* v___x_1238_; 
v_p_1237_ = lean_ctor_get(v_m_u2081_1234_, 0);
lean_inc_ref(v_p_1237_);
lean_dec_ref_known(v_m_u2081_1234_, 2);
v___x_1238_ = l_Lean_Grind_CommRing_Mon_mulPow__nc(v_p_1237_, v_m_u2082_1235_);
return v___x_1238_;
}
else
{
lean_object* v_p_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1247_; 
lean_inc(v_m_1236_);
v_p_1239_ = lean_ctor_get(v_m_u2081_1234_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_m_u2081_1234_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v_m_u2081_1234_, 1);
lean_dec(v_unused_1248_);
v___x_1241_ = v_m_u2081_1234_;
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_p_1239_);
lean_dec(v_m_u2081_1234_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1247_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1243_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_1236_, v_m_u2082_1235_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v___x_1243_);
v___x_1245_ = v___x_1241_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_p_1239_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object* v_x_1249_){
_start:
{
if (lean_obj_tag(v_x_1249_) == 0)
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_unsigned_to_nat(0u);
return v___x_1250_;
}
else
{
lean_object* v_p_1251_; lean_object* v_m_1252_; lean_object* v_k_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_p_1251_ = lean_ctor_get(v_x_1249_, 0);
v_m_1252_ = lean_ctor_get(v_x_1249_, 1);
v_k_1253_ = lean_ctor_get(v_p_1251_, 1);
v___x_1254_ = l_Lean_Grind_CommRing_Mon_degree(v_m_1252_);
v___x_1255_ = lean_nat_add(v_k_1253_, v___x_1254_);
lean_dec(v___x_1254_);
return v___x_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree___boxed(lean_object* v_x_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Grind_CommRing_Mon_degree(v_x_1256_);
lean_dec(v_x_1256_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object* v_x_1258_, lean_object* v_h__1_1259_, lean_object* v_h__2_1260_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec(v_h__2_1260_);
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_apply_1(v_h__1_1259_, v___x_1261_);
return v___x_1262_;
}
else
{
lean_object* v_p_1263_; lean_object* v_m_1264_; lean_object* v___x_1265_; 
lean_dec(v_h__1_1259_);
v_p_1263_ = lean_ctor_get(v_x_1258_, 0);
lean_inc_ref(v_p_1263_);
v_m_1264_ = lean_ctor_get(v_x_1258_, 1);
lean_inc(v_m_1264_);
lean_dec_ref_known(v_x_1258_, 2);
v___x_1265_ = lean_apply_2(v_h__2_1260_, v_p_1263_, v_m_1264_);
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object* v_motive_1266_, lean_object* v_x_1267_, lean_object* v_h__1_1268_, lean_object* v_h__2_1269_){
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
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Var_revlex(lean_object* v_x_1275_, lean_object* v_y_1276_){
_start:
{
uint8_t v___x_1277_; 
v___x_1277_ = l_Nat_blt(v_x_1275_, v_y_1276_);
if (v___x_1277_ == 0)
{
uint8_t v___x_1278_; 
v___x_1278_ = l_Nat_blt(v_y_1276_, v_x_1275_);
if (v___x_1278_ == 0)
{
uint8_t v___x_1279_; 
v___x_1279_ = 1;
return v___x_1279_;
}
else
{
uint8_t v___x_1280_; 
v___x_1280_ = 0;
return v___x_1280_;
}
}
else
{
uint8_t v___x_1281_; 
v___x_1281_ = 2;
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_revlex___boxed(lean_object* v_x_1282_, lean_object* v_y_1283_){
_start:
{
uint8_t v_res_1284_; lean_object* v_r_1285_; 
v_res_1284_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1282_, v_y_1283_);
lean_dec(v_y_1283_);
lean_dec(v_x_1282_);
v_r_1285_ = lean_box(v_res_1284_);
return v_r_1285_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_powerRevlex(lean_object* v_k_u2081_1286_, lean_object* v_k_u2082_1287_){
_start:
{
uint8_t v___x_1288_; 
v___x_1288_ = l_Nat_blt(v_k_u2081_1286_, v_k_u2082_1287_);
if (v___x_1288_ == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = l_Nat_blt(v_k_u2082_1287_, v_k_u2081_1286_);
if (v___x_1289_ == 0)
{
uint8_t v___x_1290_; 
v___x_1290_ = 1;
return v___x_1290_;
}
else
{
uint8_t v___x_1291_; 
v___x_1291_ = 0;
return v___x_1291_;
}
}
else
{
uint8_t v___x_1292_; 
v___x_1292_ = 2;
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_powerRevlex___boxed(lean_object* v_k_u2081_1293_, lean_object* v_k_u2082_1294_){
_start:
{
uint8_t v_res_1295_; lean_object* v_r_1296_; 
v_res_1295_ = l_Lean_Grind_CommRing_powerRevlex(v_k_u2081_1293_, v_k_u2082_1294_);
lean_dec(v_k_u2082_1294_);
lean_dec(v_k_u2081_1293_);
v_r_1296_ = lean_box(v_res_1295_);
return v_r_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(uint8_t v_c_1297_, lean_object* v_h__1_1298_, lean_object* v_h__2_1299_){
_start:
{
if (v_c_1297_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec(v_h__1_1298_);
v___x_1300_ = lean_box(0);
v___x_1301_ = lean_apply_1(v_h__2_1299_, v___x_1300_);
return v___x_1301_;
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_dec(v_h__2_1299_);
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_apply_1(v_h__1_1298_, v___x_1302_);
return v___x_1303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg___boxed(lean_object* v_c_1304_, lean_object* v_h__1_1305_, lean_object* v_h__2_1306_){
_start:
{
uint8_t v_c_24__boxed_1307_; lean_object* v_res_1308_; 
v_c_24__boxed_1307_ = lean_unbox(v_c_1304_);
v_res_1308_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(v_c_24__boxed_1307_, v_h__1_1305_, v_h__2_1306_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(lean_object* v_motive_1309_, uint8_t v_c_1310_, lean_object* v_h__1_1311_, lean_object* v_h__2_1312_){
_start:
{
if (v_c_1310_ == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_dec(v_h__1_1311_);
v___x_1313_ = lean_box(0);
v___x_1314_ = lean_apply_1(v_h__2_1312_, v___x_1313_);
return v___x_1314_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec(v_h__2_1312_);
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_apply_1(v_h__1_1311_, v___x_1315_);
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___boxed(lean_object* v_motive_1317_, lean_object* v_c_1318_, lean_object* v_h__1_1319_, lean_object* v_h__2_1320_){
_start:
{
uint8_t v_c_35__boxed_1321_; lean_object* v_res_1322_; 
v_c_35__boxed_1321_ = lean_unbox(v_c_1318_);
v_res_1322_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(v_motive_1317_, v_c_35__boxed_1321_, v_h__1_1319_, v_h__2_1320_);
return v_res_1322_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_revlex(lean_object* v_p_u2081_1323_, lean_object* v_p_u2082_1324_){
_start:
{
lean_object* v_x_1325_; lean_object* v_k_1326_; lean_object* v_x_1327_; lean_object* v_k_1328_; uint8_t v___x_1329_; 
v_x_1325_ = lean_ctor_get(v_p_u2081_1323_, 0);
v_k_1326_ = lean_ctor_get(v_p_u2081_1323_, 1);
v_x_1327_ = lean_ctor_get(v_p_u2082_1324_, 0);
v_k_1328_ = lean_ctor_get(v_p_u2082_1324_, 1);
v___x_1329_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1325_, v_x_1327_);
if (v___x_1329_ == 1)
{
uint8_t v___x_1330_; 
v___x_1330_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1326_, v_k_1328_);
return v___x_1330_;
}
else
{
return v___x_1329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_revlex___boxed(lean_object* v_p_u2081_1331_, lean_object* v_p_u2082_1332_){
_start:
{
uint8_t v_res_1333_; lean_object* v_r_1334_; 
v_res_1333_ = l_Lean_Grind_CommRing_Power_revlex(v_p_u2081_1331_, v_p_u2082_1332_);
lean_dec_ref(v_p_u2082_1332_);
lean_dec_ref(v_p_u2081_1331_);
v_r_1334_ = lean_box(v_res_1333_);
return v_r_1334_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexWF(lean_object* v_m_u2081_1335_, lean_object* v_m_u2082_1336_){
_start:
{
if (lean_obj_tag(v_m_u2081_1335_) == 0)
{
if (lean_obj_tag(v_m_u2082_1336_) == 0)
{
uint8_t v___x_1337_; 
v___x_1337_ = 1;
return v___x_1337_;
}
else
{
uint8_t v___x_1338_; 
v___x_1338_ = 2;
return v___x_1338_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1336_) == 0)
{
uint8_t v___x_1339_; 
v___x_1339_ = 0;
return v___x_1339_;
}
else
{
lean_object* v_p_1340_; lean_object* v_p_1341_; lean_object* v_m_1342_; lean_object* v_m_1343_; lean_object* v_x_1344_; lean_object* v_k_1345_; lean_object* v_x_1346_; lean_object* v_k_1347_; uint8_t v___x_1348_; 
v_p_1340_ = lean_ctor_get(v_m_u2081_1335_, 0);
v_p_1341_ = lean_ctor_get(v_m_u2082_1336_, 0);
v_m_1342_ = lean_ctor_get(v_m_u2081_1335_, 1);
v_m_1343_ = lean_ctor_get(v_m_u2082_1336_, 1);
v_x_1344_ = lean_ctor_get(v_p_1340_, 0);
v_k_1345_ = lean_ctor_get(v_p_1340_, 1);
v_x_1346_ = lean_ctor_get(v_p_1341_, 0);
v_k_1347_ = lean_ctor_get(v_p_1341_, 1);
v___x_1348_ = lean_nat_dec_eq(v_x_1344_, v_x_1346_);
if (v___x_1348_ == 0)
{
uint8_t v___x_1349_; 
v___x_1349_ = l_Nat_blt(v_x_1344_, v_x_1346_);
if (v___x_1349_ == 0)
{
uint8_t v___x_1350_; 
v___x_1350_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1335_, v_m_1343_);
if (v___x_1350_ == 1)
{
uint8_t v___x_1351_; 
v___x_1351_ = 2;
return v___x_1351_;
}
else
{
return v___x_1350_;
}
}
else
{
uint8_t v___x_1352_; 
v___x_1352_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1342_, v_m_u2082_1336_);
if (v___x_1352_ == 1)
{
uint8_t v___x_1353_; 
v___x_1353_ = 0;
return v___x_1353_;
}
else
{
return v___x_1352_;
}
}
}
else
{
uint8_t v___x_1354_; 
v___x_1354_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1342_, v_m_1343_);
if (v___x_1354_ == 1)
{
uint8_t v___x_1355_; 
v___x_1355_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1345_, v_k_1347_);
return v___x_1355_;
}
else
{
return v___x_1354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexWF___boxed(lean_object* v_m_u2081_1356_, lean_object* v_m_u2082_1357_){
_start:
{
uint8_t v_res_1358_; lean_object* v_r_1359_; 
v_res_1358_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1356_, v_m_u2082_1357_);
lean_dec(v_m_u2082_1357_);
lean_dec(v_m_u2081_1356_);
v_r_1359_ = lean_box(v_res_1358_);
return v_r_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(lean_object* v_m_u2081_1360_, lean_object* v_m_u2082_1361_, lean_object* v_h__1_1362_, lean_object* v_h__2_1363_, lean_object* v_h__3_1364_, lean_object* v_h__4_1365_){
_start:
{
if (lean_obj_tag(v_m_u2081_1360_) == 0)
{
lean_dec(v_h__4_1365_);
lean_dec(v_h__3_1364_);
if (lean_obj_tag(v_m_u2082_1361_) == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec(v_h__2_1363_);
v___x_1366_ = lean_box(0);
v___x_1367_ = lean_apply_1(v_h__1_1362_, v___x_1366_);
return v___x_1367_;
}
else
{
lean_object* v_p_1368_; lean_object* v_m_1369_; lean_object* v___x_1370_; 
lean_dec(v_h__1_1362_);
v_p_1368_ = lean_ctor_get(v_m_u2082_1361_, 0);
lean_inc_ref(v_p_1368_);
v_m_1369_ = lean_ctor_get(v_m_u2082_1361_, 1);
lean_inc(v_m_1369_);
lean_dec_ref_known(v_m_u2082_1361_, 2);
v___x_1370_ = lean_apply_2(v_h__2_1363_, v_p_1368_, v_m_1369_);
return v___x_1370_;
}
}
else
{
lean_dec(v_h__2_1363_);
lean_dec(v_h__1_1362_);
if (lean_obj_tag(v_m_u2082_1361_) == 0)
{
lean_object* v_p_1371_; lean_object* v_m_1372_; lean_object* v___x_1373_; 
lean_dec(v_h__4_1365_);
v_p_1371_ = lean_ctor_get(v_m_u2081_1360_, 0);
lean_inc_ref(v_p_1371_);
v_m_1372_ = lean_ctor_get(v_m_u2081_1360_, 1);
lean_inc(v_m_1372_);
lean_dec_ref_known(v_m_u2081_1360_, 2);
v___x_1373_ = lean_apply_2(v_h__3_1364_, v_p_1371_, v_m_1372_);
return v___x_1373_;
}
else
{
lean_object* v_p_1374_; lean_object* v_m_1375_; lean_object* v_p_1376_; lean_object* v_m_1377_; lean_object* v___x_1378_; 
lean_dec(v_h__3_1364_);
v_p_1374_ = lean_ctor_get(v_m_u2081_1360_, 0);
lean_inc_ref(v_p_1374_);
v_m_1375_ = lean_ctor_get(v_m_u2081_1360_, 1);
lean_inc(v_m_1375_);
lean_dec_ref_known(v_m_u2081_1360_, 2);
v_p_1376_ = lean_ctor_get(v_m_u2082_1361_, 0);
lean_inc_ref(v_p_1376_);
v_m_1377_ = lean_ctor_get(v_m_u2082_1361_, 1);
lean_inc(v_m_1377_);
lean_dec_ref_known(v_m_u2082_1361_, 2);
v___x_1378_ = lean_apply_4(v_h__4_1365_, v_p_1374_, v_m_1375_, v_p_1376_, v_m_1377_);
return v___x_1378_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter(lean_object* v_motive_1379_, lean_object* v_m_u2081_1380_, lean_object* v_m_u2082_1381_, lean_object* v_h__1_1382_, lean_object* v_h__2_1383_, lean_object* v_h__3_1384_, lean_object* v_h__4_1385_){
_start:
{
if (lean_obj_tag(v_m_u2081_1380_) == 0)
{
lean_dec(v_h__4_1385_);
lean_dec(v_h__3_1384_);
if (lean_obj_tag(v_m_u2082_1381_) == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec(v_h__2_1383_);
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_apply_1(v_h__1_1382_, v___x_1386_);
return v___x_1387_;
}
else
{
lean_object* v_p_1388_; lean_object* v_m_1389_; lean_object* v___x_1390_; 
lean_dec(v_h__1_1382_);
v_p_1388_ = lean_ctor_get(v_m_u2082_1381_, 0);
lean_inc_ref(v_p_1388_);
v_m_1389_ = lean_ctor_get(v_m_u2082_1381_, 1);
lean_inc(v_m_1389_);
lean_dec_ref_known(v_m_u2082_1381_, 2);
v___x_1390_ = lean_apply_2(v_h__2_1383_, v_p_1388_, v_m_1389_);
return v___x_1390_;
}
}
else
{
lean_dec(v_h__2_1383_);
lean_dec(v_h__1_1382_);
if (lean_obj_tag(v_m_u2082_1381_) == 0)
{
lean_object* v_p_1391_; lean_object* v_m_1392_; lean_object* v___x_1393_; 
lean_dec(v_h__4_1385_);
v_p_1391_ = lean_ctor_get(v_m_u2081_1380_, 0);
lean_inc_ref(v_p_1391_);
v_m_1392_ = lean_ctor_get(v_m_u2081_1380_, 1);
lean_inc(v_m_1392_);
lean_dec_ref_known(v_m_u2081_1380_, 2);
v___x_1393_ = lean_apply_2(v_h__3_1384_, v_p_1391_, v_m_1392_);
return v___x_1393_;
}
else
{
lean_object* v_p_1394_; lean_object* v_m_1395_; lean_object* v_p_1396_; lean_object* v_m_1397_; lean_object* v___x_1398_; 
lean_dec(v_h__3_1384_);
v_p_1394_ = lean_ctor_get(v_m_u2081_1380_, 0);
lean_inc_ref(v_p_1394_);
v_m_1395_ = lean_ctor_get(v_m_u2081_1380_, 1);
lean_inc(v_m_1395_);
lean_dec_ref_known(v_m_u2081_1380_, 2);
v_p_1396_ = lean_ctor_get(v_m_u2082_1381_, 0);
lean_inc_ref(v_p_1396_);
v_m_1397_ = lean_ctor_get(v_m_u2082_1381_, 1);
lean_inc(v_m_1397_);
lean_dec_ref_known(v_m_u2082_1381_, 2);
v___x_1398_ = lean_apply_4(v_h__4_1385_, v_p_1394_, v_m_1395_, v_p_1396_, v_m_1397_);
return v___x_1398_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexFuel(lean_object* v_fuel_1399_, lean_object* v_m_u2081_1400_, lean_object* v_m_u2082_1401_){
_start:
{
lean_object* v_zero_1402_; uint8_t v_isZero_1403_; 
v_zero_1402_ = lean_unsigned_to_nat(0u);
v_isZero_1403_ = lean_nat_dec_eq(v_fuel_1399_, v_zero_1402_);
if (v_isZero_1403_ == 1)
{
uint8_t v___x_1404_; 
v___x_1404_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1400_, v_m_u2082_1401_);
return v___x_1404_;
}
else
{
if (lean_obj_tag(v_m_u2081_1400_) == 0)
{
if (lean_obj_tag(v_m_u2082_1401_) == 0)
{
uint8_t v___x_1405_; 
v___x_1405_ = 1;
return v___x_1405_;
}
else
{
uint8_t v___x_1406_; 
v___x_1406_ = 2;
return v___x_1406_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1401_) == 0)
{
uint8_t v___x_1407_; 
v___x_1407_ = 0;
return v___x_1407_;
}
else
{
lean_object* v_p_1408_; lean_object* v_p_1409_; lean_object* v_m_1410_; lean_object* v_m_1411_; lean_object* v_x_1412_; lean_object* v_k_1413_; lean_object* v_x_1414_; lean_object* v_k_1415_; lean_object* v_one_1416_; lean_object* v_n_1417_; uint8_t v___x_1418_; 
v_p_1408_ = lean_ctor_get(v_m_u2081_1400_, 0);
v_p_1409_ = lean_ctor_get(v_m_u2082_1401_, 0);
v_m_1410_ = lean_ctor_get(v_m_u2081_1400_, 1);
v_m_1411_ = lean_ctor_get(v_m_u2082_1401_, 1);
v_x_1412_ = lean_ctor_get(v_p_1408_, 0);
v_k_1413_ = lean_ctor_get(v_p_1408_, 1);
v_x_1414_ = lean_ctor_get(v_p_1409_, 0);
v_k_1415_ = lean_ctor_get(v_p_1409_, 1);
v_one_1416_ = lean_unsigned_to_nat(1u);
v_n_1417_ = lean_nat_sub(v_fuel_1399_, v_one_1416_);
v___x_1418_ = lean_nat_dec_eq(v_x_1412_, v_x_1414_);
if (v___x_1418_ == 0)
{
uint8_t v___x_1419_; 
v___x_1419_ = l_Nat_blt(v_x_1412_, v_x_1414_);
if (v___x_1419_ == 0)
{
uint8_t v___x_1420_; 
v___x_1420_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1417_, v_m_u2081_1400_, v_m_1411_);
lean_dec(v_n_1417_);
if (v___x_1420_ == 1)
{
uint8_t v___x_1421_; 
v___x_1421_ = 2;
return v___x_1421_;
}
else
{
return v___x_1420_;
}
}
else
{
uint8_t v___x_1422_; 
v___x_1422_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1417_, v_m_1410_, v_m_u2082_1401_);
lean_dec(v_n_1417_);
if (v___x_1422_ == 1)
{
uint8_t v___x_1423_; 
v___x_1423_ = 0;
return v___x_1423_;
}
else
{
return v___x_1422_;
}
}
}
else
{
uint8_t v___x_1424_; 
v___x_1424_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1417_, v_m_1410_, v_m_1411_);
lean_dec(v_n_1417_);
if (v___x_1424_ == 1)
{
uint8_t v___x_1425_; 
v___x_1425_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1413_, v_k_1415_);
return v___x_1425_;
}
else
{
return v___x_1424_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexFuel___boxed(lean_object* v_fuel_1426_, lean_object* v_m_u2081_1427_, lean_object* v_m_u2082_1428_){
_start:
{
uint8_t v_res_1429_; lean_object* v_r_1430_; 
v_res_1429_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_fuel_1426_, v_m_u2081_1427_, v_m_u2082_1428_);
lean_dec(v_m_u2082_1428_);
lean_dec(v_m_u2081_1427_);
lean_dec(v_fuel_1426_);
v_r_1430_ = lean_box(v_res_1429_);
return v_r_1430_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlex(lean_object* v_m_u2081_1431_, lean_object* v_m_u2082_1432_){
_start:
{
lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1433_ = lean_unsigned_to_nat(1000000u);
v___x_1434_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v___x_1433_, v_m_u2081_1431_, v_m_u2082_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlex___boxed(lean_object* v_m_u2081_1435_, lean_object* v_m_u2082_1436_){
_start:
{
uint8_t v_res_1437_; lean_object* v_r_1438_; 
v_res_1437_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1435_, v_m_u2082_1436_);
lean_dec(v_m_u2082_1436_);
lean_dec(v_m_u2081_1435_);
v_r_1438_ = lean_box(v_res_1437_);
return v_r_1438_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object* v_m_u2081_1439_, lean_object* v_m_u2082_1440_){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1441_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2081_1439_);
v___x_1442_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2082_1440_);
v___x_1443_ = lean_nat_dec_lt(v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_nat_dec_eq(v___x_1441_, v___x_1442_);
lean_dec(v___x_1442_);
lean_dec(v___x_1441_);
if (v___x_1444_ == 0)
{
uint8_t v___x_1445_; 
v___x_1445_ = 2;
return v___x_1445_;
}
else
{
uint8_t v___x_1446_; 
v___x_1446_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1439_, v_m_u2082_1440_);
return v___x_1446_;
}
}
else
{
uint8_t v___x_1447_; 
lean_dec(v___x_1442_);
lean_dec(v___x_1441_);
v___x_1447_ = 0;
return v___x_1447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_grevlex___boxed(lean_object* v_m_u2081_1448_, lean_object* v_m_u2082_1449_){
_start:
{
uint8_t v_res_1450_; lean_object* v_r_1451_; 
v_res_1450_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_u2081_1448_, v_m_u2082_1449_);
lean_dec(v_m_u2082_1449_);
lean_dec(v_m_u2081_1448_);
v_r_1451_ = lean_box(v_res_1450_);
return v_r_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___impl(lean_object* v_x_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_obj_tag_nat(v_x_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___impl___boxed(lean_object* v_x_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_Grind_CommRing_Poly_ctorIdx___impl(v_x_1454_);
lean_dec_ref(v_x_1454_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___redArg(lean_object* v_t_1456_, lean_object* v_k_1457_){
_start:
{
if (lean_obj_tag(v_t_1456_) == 0)
{
lean_object* v_k_1458_; lean_object* v___x_1459_; 
v_k_1458_ = lean_ctor_get(v_t_1456_, 0);
lean_inc(v_k_1458_);
lean_dec_ref_known(v_t_1456_, 1);
v___x_1459_ = lean_apply_1(v_k_1457_, v_k_1458_);
return v___x_1459_;
}
else
{
lean_object* v_k_1460_; lean_object* v_v_1461_; lean_object* v_p_1462_; lean_object* v___x_1463_; 
v_k_1460_ = lean_ctor_get(v_t_1456_, 0);
lean_inc(v_k_1460_);
v_v_1461_ = lean_ctor_get(v_t_1456_, 1);
lean_inc(v_v_1461_);
v_p_1462_ = lean_ctor_get(v_t_1456_, 2);
lean_inc_ref(v_p_1462_);
lean_dec_ref_known(v_t_1456_, 3);
v___x_1463_ = lean_apply_3(v_k_1457_, v_k_1460_, v_v_1461_, v_p_1462_);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim(lean_object* v_motive_1464_, lean_object* v_ctorIdx_1465_, lean_object* v_t_1466_, lean_object* v_h_1467_, lean_object* v_k_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1466_, v_k_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___boxed(lean_object* v_motive_1470_, lean_object* v_ctorIdx_1471_, lean_object* v_t_1472_, lean_object* v_h_1473_, lean_object* v_k_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Grind_CommRing_Poly_ctorElim(v_motive_1470_, v_ctorIdx_1471_, v_t_1472_, v_h_1473_, v_k_1474_);
lean_dec(v_ctorIdx_1471_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim___redArg(lean_object* v_t_1476_, lean_object* v_num_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1476_, v_num_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim(lean_object* v_motive_1479_, lean_object* v_t_1480_, lean_object* v_h_1481_, lean_object* v_num_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1480_, v_num_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim___redArg(lean_object* v_t_1484_, lean_object* v_add_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1484_, v_add_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim(lean_object* v_motive_1487_, lean_object* v_t_1488_, lean_object* v_h_1489_, lean_object* v_add_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1488_, v_add_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPoly_beq(lean_object* v_x_1492_, lean_object* v_x_1493_){
_start:
{
if (lean_obj_tag(v_x_1492_) == 0)
{
if (lean_obj_tag(v_x_1493_) == 0)
{
lean_object* v_k_1494_; lean_object* v_k_1495_; uint8_t v___x_1496_; 
v_k_1494_ = lean_ctor_get(v_x_1492_, 0);
v_k_1495_ = lean_ctor_get(v_x_1493_, 0);
v___x_1496_ = lean_int_dec_eq(v_k_1494_, v_k_1495_);
return v___x_1496_;
}
else
{
uint8_t v___x_1497_; 
v___x_1497_ = 0;
return v___x_1497_;
}
}
else
{
if (lean_obj_tag(v_x_1493_) == 1)
{
lean_object* v_k_1498_; lean_object* v_v_1499_; lean_object* v_p_1500_; lean_object* v_k_1501_; lean_object* v_v_1502_; lean_object* v_p_1503_; uint8_t v___x_1504_; 
v_k_1498_ = lean_ctor_get(v_x_1492_, 0);
v_v_1499_ = lean_ctor_get(v_x_1492_, 1);
v_p_1500_ = lean_ctor_get(v_x_1492_, 2);
v_k_1501_ = lean_ctor_get(v_x_1493_, 0);
v_v_1502_ = lean_ctor_get(v_x_1493_, 1);
v_p_1503_ = lean_ctor_get(v_x_1493_, 2);
v___x_1504_ = lean_int_dec_eq(v_k_1498_, v_k_1501_);
if (v___x_1504_ == 0)
{
return v___x_1504_;
}
else
{
uint8_t v___x_1505_; 
v___x_1505_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_v_1499_, v_v_1502_);
if (v___x_1505_ == 0)
{
return v___x_1505_;
}
else
{
v_x_1492_ = v_p_1500_;
v_x_1493_ = v_p_1503_;
goto _start;
}
}
}
else
{
uint8_t v___x_1507_; 
v___x_1507_ = 0;
return v___x_1507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPoly_beq___boxed(lean_object* v_x_1508_, lean_object* v_x_1509_){
_start:
{
uint8_t v_res_1510_; lean_object* v_r_1511_; 
v_res_1510_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_x_1508_, v_x_1509_);
lean_dec_ref(v_x_1509_);
lean_dec_ref(v_x_1508_);
v_r_1511_ = lean_box(v_res_1510_);
return v_r_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_1514_, lean_object* v_x_1515_, lean_object* v_h__1_1516_, lean_object* v_h__2_1517_, lean_object* v_h__3_1518_){
_start:
{
if (lean_obj_tag(v_x_1514_) == 0)
{
lean_dec(v_h__2_1517_);
if (lean_obj_tag(v_x_1515_) == 0)
{
lean_object* v_k_1519_; lean_object* v_k_1520_; lean_object* v___x_1521_; 
lean_dec(v_h__3_1518_);
v_k_1519_ = lean_ctor_get(v_x_1514_, 0);
lean_inc(v_k_1519_);
lean_dec_ref_known(v_x_1514_, 1);
v_k_1520_ = lean_ctor_get(v_x_1515_, 0);
lean_inc(v_k_1520_);
lean_dec_ref_known(v_x_1515_, 1);
v___x_1521_ = lean_apply_2(v_h__1_1516_, v_k_1519_, v_k_1520_);
return v___x_1521_;
}
else
{
lean_object* v___x_1522_; 
lean_dec(v_h__1_1516_);
v___x_1522_ = lean_apply_4(v_h__3_1518_, v_x_1514_, v_x_1515_, lean_box(0), lean_box(0));
return v___x_1522_;
}
}
else
{
lean_dec(v_h__1_1516_);
if (lean_obj_tag(v_x_1515_) == 1)
{
lean_object* v_k_1523_; lean_object* v_v_1524_; lean_object* v_p_1525_; lean_object* v_k_1526_; lean_object* v_v_1527_; lean_object* v_p_1528_; lean_object* v___x_1529_; 
lean_dec(v_h__3_1518_);
v_k_1523_ = lean_ctor_get(v_x_1514_, 0);
lean_inc(v_k_1523_);
v_v_1524_ = lean_ctor_get(v_x_1514_, 1);
lean_inc(v_v_1524_);
v_p_1525_ = lean_ctor_get(v_x_1514_, 2);
lean_inc_ref(v_p_1525_);
lean_dec_ref_known(v_x_1514_, 3);
v_k_1526_ = lean_ctor_get(v_x_1515_, 0);
lean_inc(v_k_1526_);
v_v_1527_ = lean_ctor_get(v_x_1515_, 1);
lean_inc(v_v_1527_);
v_p_1528_ = lean_ctor_get(v_x_1515_, 2);
lean_inc_ref(v_p_1528_);
lean_dec_ref_known(v_x_1515_, 3);
v___x_1529_ = lean_apply_6(v_h__2_1517_, v_k_1523_, v_v_1524_, v_p_1525_, v_k_1526_, v_v_1527_, v_p_1528_);
return v___x_1529_;
}
else
{
lean_object* v___x_1530_; 
lean_dec(v_h__2_1517_);
v___x_1530_ = lean_apply_4(v_h__3_1518_, v_x_1514_, v_x_1515_, lean_box(0), lean_box(0));
return v___x_1530_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_, lean_object* v_h__1_1534_, lean_object* v_h__2_1535_, lean_object* v_h__3_1536_){
_start:
{
if (lean_obj_tag(v_x_1532_) == 0)
{
lean_dec(v_h__2_1535_);
if (lean_obj_tag(v_x_1533_) == 0)
{
lean_object* v_k_1537_; lean_object* v_k_1538_; lean_object* v___x_1539_; 
lean_dec(v_h__3_1536_);
v_k_1537_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_k_1537_);
lean_dec_ref_known(v_x_1532_, 1);
v_k_1538_ = lean_ctor_get(v_x_1533_, 0);
lean_inc(v_k_1538_);
lean_dec_ref_known(v_x_1533_, 1);
v___x_1539_ = lean_apply_2(v_h__1_1534_, v_k_1537_, v_k_1538_);
return v___x_1539_;
}
else
{
lean_object* v___x_1540_; 
lean_dec(v_h__1_1534_);
v___x_1540_ = lean_apply_4(v_h__3_1536_, v_x_1532_, v_x_1533_, lean_box(0), lean_box(0));
return v___x_1540_;
}
}
else
{
lean_dec(v_h__1_1534_);
if (lean_obj_tag(v_x_1533_) == 1)
{
lean_object* v_k_1541_; lean_object* v_v_1542_; lean_object* v_p_1543_; lean_object* v_k_1544_; lean_object* v_v_1545_; lean_object* v_p_1546_; lean_object* v___x_1547_; 
lean_dec(v_h__3_1536_);
v_k_1541_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_k_1541_);
v_v_1542_ = lean_ctor_get(v_x_1532_, 1);
lean_inc(v_v_1542_);
v_p_1543_ = lean_ctor_get(v_x_1532_, 2);
lean_inc_ref(v_p_1543_);
lean_dec_ref_known(v_x_1532_, 3);
v_k_1544_ = lean_ctor_get(v_x_1533_, 0);
lean_inc(v_k_1544_);
v_v_1545_ = lean_ctor_get(v_x_1533_, 1);
lean_inc(v_v_1545_);
v_p_1546_ = lean_ctor_get(v_x_1533_, 2);
lean_inc_ref(v_p_1546_);
lean_dec_ref_known(v_x_1533_, 3);
v___x_1547_ = lean_apply_6(v_h__2_1535_, v_k_1541_, v_v_1542_, v_p_1543_, v_k_1544_, v_v_1545_, v_p_1546_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; 
lean_dec(v_h__2_1535_);
v___x_1548_ = lean_apply_4(v_h__3_1536_, v_x_1532_, v_x_1533_, lean_box(0), lean_box(0));
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr(lean_object* v_x_1561_, lean_object* v_prec_1562_){
_start:
{
lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; 
if (lean_obj_tag(v_x_1561_) == 0)
{
lean_object* v_k_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1595_; 
v_k_1572_ = lean_ctor_get(v_x_1561_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_x_1561_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1574_ = v_x_1561_;
v_isShared_1575_ = v_isSharedCheck_1595_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_k_1572_);
lean_dec(v_x_1561_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1595_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___y_1577_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = lean_unsigned_to_nat(1024u);
v___x_1592_ = lean_nat_dec_le(v___x_1591_, v_prec_1562_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1577_ = v___x_1593_;
goto v___jp_1576_;
}
else
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1577_ = v___x_1594_;
goto v___jp_1576_;
}
v___jp_1576_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1578_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__2));
v___x_1579_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1580_ = lean_int_dec_lt(v_k_1572_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1581_ = l_Int_repr(v_k_1572_);
lean_dec(v_k_1572_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 3);
lean_ctor_set(v___x_1574_, 0, v___x_1581_);
v___x_1583_ = v___x_1574_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
v___y_1564_ = v___y_1577_;
v___y_1565_ = v___x_1578_;
v___y_1566_ = v___x_1583_;
goto v___jp_1563_;
}
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1585_ = lean_unsigned_to_nat(1024u);
v___x_1586_ = l_Int_repr(v_k_1572_);
lean_dec(v_k_1572_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 3);
lean_ctor_set(v___x_1574_, 0, v___x_1586_);
v___x_1588_ = v___x_1574_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Repr_addAppParen(v___x_1588_, v___x_1585_);
v___y_1564_ = v___y_1577_;
v___y_1565_ = v___x_1578_;
v___y_1566_ = v___x_1589_;
goto v___jp_1563_;
}
}
}
}
}
else
{
lean_object* v_k_1596_; lean_object* v_v_1597_; lean_object* v_p_1598_; lean_object* v___x_1599_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1617_; uint8_t v___x_1627_; 
v_k_1596_ = lean_ctor_get(v_x_1561_, 0);
lean_inc(v_k_1596_);
v_v_1597_ = lean_ctor_get(v_x_1561_, 1);
lean_inc(v_v_1597_);
v_p_1598_ = lean_ctor_get(v_x_1561_, 2);
lean_inc_ref(v_p_1598_);
lean_dec_ref_known(v_x_1561_, 3);
v___x_1599_ = lean_unsigned_to_nat(1024u);
v___x_1627_ = lean_nat_dec_le(v___x_1599_, v_prec_1562_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1617_ = v___x_1628_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1617_ = v___x_1629_;
goto v___jp_1616_;
}
v___jp_1600_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_inc(v___y_1601_);
v___x_1605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___y_1601_);
lean_ctor_set(v___x_1605_, 1, v___y_1604_);
lean_inc_n(v___y_1602_, 2);
v___x_1606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v___y_1602_);
v___x_1607_ = l_Lean_Grind_CommRing_instReprMon_repr(v_v_1597_, v___x_1599_);
v___x_1608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
lean_ctor_set(v___x_1609_, 1, v___y_1602_);
v___x_1610_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_p_1598_, v___x_1599_);
v___x_1611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
lean_inc(v___y_1603_);
v___x_1612_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___y_1603_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = 0;
v___x_1614_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set_uint8(v___x_1614_, sizeof(void*)*1, v___x_1613_);
v___x_1615_ = l_Repr_addAppParen(v___x_1614_, v_prec_1562_);
return v___x_1615_;
}
v___jp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1618_ = lean_box(1);
v___x_1619_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__5));
v___x_1620_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1621_ = lean_int_dec_lt(v_k_1596_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = l_Int_repr(v_k_1596_);
lean_dec(v_k_1596_);
v___x_1623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
v___y_1601_ = v___x_1619_;
v___y_1602_ = v___x_1618_;
v___y_1603_ = v___y_1617_;
v___y_1604_ = v___x_1623_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = l_Int_repr(v_k_1596_);
lean_dec(v_k_1596_);
v___x_1625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
v___x_1626_ = l_Repr_addAppParen(v___x_1625_, v___x_1599_);
v___y_1601_ = v___x_1619_;
v___y_1602_ = v___x_1618_;
v___y_1603_ = v___y_1617_;
v___y_1604_ = v___x_1626_;
goto v___jp_1600_;
}
}
}
v___jp_1563_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_inc(v___y_1565_);
v___x_1567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___y_1565_);
lean_ctor_set(v___x_1567_, 1, v___y_1566_);
lean_inc(v___y_1564_);
v___x_1568_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___y_1564_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = 0;
v___x_1570_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*1, v___x_1569_);
v___x_1571_ = l_Repr_addAppParen(v___x_1570_, v_prec_1562_);
return v___x_1571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___boxed(lean_object* v_x_1630_, lean_object* v_prec_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_x_1630_, v_prec_1631_);
lean_dec(v_prec_1631_);
return v_res_1632_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
return v___x_1636_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default(void){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_1637_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly(void){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
return v___x_1638_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePoly_hash(lean_object* v_x_1639_){
_start:
{
if (lean_obj_tag(v_x_1639_) == 0)
{
lean_object* v_k_1640_; uint64_t v___x_1641_; lean_object* v_intZero_1642_; uint8_t v_isNeg_1643_; 
v_k_1640_ = lean_ctor_get(v_x_1639_, 0);
v___x_1641_ = 0ULL;
v_intZero_1642_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1643_ = lean_int_dec_lt(v_k_1640_, v_intZero_1642_);
if (v_isNeg_1643_ == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint64_t v___x_1647_; uint64_t v___x_1648_; 
v_a_1644_ = lean_nat_abs(v_k_1640_);
v___x_1645_ = lean_unsigned_to_nat(2u);
v___x_1646_ = lean_nat_mul(v___x_1645_, v_a_1644_);
lean_dec(v_a_1644_);
v___x_1647_ = lean_uint64_of_nat(v___x_1646_);
lean_dec(v___x_1646_);
v___x_1648_ = lean_uint64_mix_hash(v___x_1641_, v___x_1647_);
return v___x_1648_;
}
else
{
lean_object* v_abs_1649_; lean_object* v_one_1650_; lean_object* v_a_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint64_t v___x_1655_; uint64_t v___x_1656_; 
v_abs_1649_ = lean_nat_abs(v_k_1640_);
v_one_1650_ = lean_unsigned_to_nat(1u);
v_a_1651_ = lean_nat_sub(v_abs_1649_, v_one_1650_);
lean_dec(v_abs_1649_);
v___x_1652_ = lean_unsigned_to_nat(2u);
v___x_1653_ = lean_nat_mul(v___x_1652_, v_a_1651_);
lean_dec(v_a_1651_);
v___x_1654_ = lean_nat_add(v___x_1653_, v_one_1650_);
lean_dec(v___x_1653_);
v___x_1655_ = lean_uint64_of_nat(v___x_1654_);
lean_dec(v___x_1654_);
v___x_1656_ = lean_uint64_mix_hash(v___x_1641_, v___x_1655_);
return v___x_1656_;
}
}
else
{
lean_object* v_k_1657_; lean_object* v_v_1658_; lean_object* v_p_1659_; uint64_t v___x_1660_; uint64_t v___y_1662_; lean_object* v_intZero_1668_; uint8_t v_isNeg_1669_; 
v_k_1657_ = lean_ctor_get(v_x_1639_, 0);
v_v_1658_ = lean_ctor_get(v_x_1639_, 1);
v_p_1659_ = lean_ctor_get(v_x_1639_, 2);
v___x_1660_ = 1ULL;
v_intZero_1668_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1669_ = lean_int_dec_lt(v_k_1657_, v_intZero_1668_);
if (v_isNeg_1669_ == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint64_t v___x_1673_; 
v_a_1670_ = lean_nat_abs(v_k_1657_);
v___x_1671_ = lean_unsigned_to_nat(2u);
v___x_1672_ = lean_nat_mul(v___x_1671_, v_a_1670_);
lean_dec(v_a_1670_);
v___x_1673_ = lean_uint64_of_nat(v___x_1672_);
lean_dec(v___x_1672_);
v___y_1662_ = v___x_1673_;
goto v___jp_1661_;
}
else
{
lean_object* v_abs_1674_; lean_object* v_one_1675_; lean_object* v_a_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; uint64_t v___x_1680_; 
v_abs_1674_ = lean_nat_abs(v_k_1657_);
v_one_1675_ = lean_unsigned_to_nat(1u);
v_a_1676_ = lean_nat_sub(v_abs_1674_, v_one_1675_);
lean_dec(v_abs_1674_);
v___x_1677_ = lean_unsigned_to_nat(2u);
v___x_1678_ = lean_nat_mul(v___x_1677_, v_a_1676_);
lean_dec(v_a_1676_);
v___x_1679_ = lean_nat_add(v___x_1678_, v_one_1675_);
lean_dec(v___x_1678_);
v___x_1680_ = lean_uint64_of_nat(v___x_1679_);
lean_dec(v___x_1679_);
v___y_1662_ = v___x_1680_;
goto v___jp_1661_;
}
v___jp_1661_:
{
uint64_t v___x_1663_; uint64_t v___x_1664_; uint64_t v___x_1665_; uint64_t v___x_1666_; uint64_t v___x_1667_; 
v___x_1663_ = lean_uint64_mix_hash(v___x_1660_, v___y_1662_);
v___x_1664_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_v_1658_);
v___x_1665_ = lean_uint64_mix_hash(v___x_1663_, v___x_1664_);
v___x_1666_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_p_1659_);
v___x_1667_ = lean_uint64_mix_hash(v___x_1665_, v___x_1666_);
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePoly_hash___boxed(lean_object* v_x_1681_){
_start:
{
uint64_t v_res_1682_; lean_object* v_r_1683_; 
v_res_1682_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_x_1681_);
lean_dec_ref(v_x_1681_);
v_r_1683_ = lean_box_uint64(v_res_1682_);
return v_r_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg(lean_object* v_inst_1686_, lean_object* v_ctx_1687_, lean_object* v_p_1688_){
_start:
{
lean_object* v_toSemiring_1689_; lean_object* v_intCast_1690_; lean_object* v_toAdd_1691_; lean_object* v___x_1692_; 
v_toSemiring_1689_ = lean_ctor_get(v_inst_1686_, 0);
v_intCast_1690_ = lean_ctor_get(v_inst_1686_, 3);
v_toAdd_1691_ = lean_ctor_get(v_toSemiring_1689_, 0);
lean_inc(v_toAdd_1691_);
lean_inc_ref(v_inst_1686_);
v___x_1692_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1686_);
if (lean_obj_tag(v_p_1688_) == 0)
{
lean_object* v_k_1693_; lean_object* v___x_1694_; 
lean_inc(v_intCast_1690_);
lean_dec_ref(v___x_1692_);
lean_dec(v_toAdd_1691_);
lean_dec_ref(v_inst_1686_);
v_k_1693_ = lean_ctor_get(v_p_1688_, 0);
lean_inc(v_k_1693_);
lean_dec_ref_known(v_p_1688_, 1);
v___x_1694_ = lean_apply_1(v_intCast_1690_, v_k_1693_);
return v___x_1694_;
}
else
{
lean_object* v_zsmul_1695_; lean_object* v_k_1696_; lean_object* v_v_1697_; lean_object* v_p_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_zsmul_1695_ = lean_ctor_get(v___x_1692_, 2);
lean_inc(v_zsmul_1695_);
lean_dec_ref(v___x_1692_);
v_k_1696_ = lean_ctor_get(v_p_1688_, 0);
lean_inc(v_k_1696_);
v_v_1697_ = lean_ctor_get(v_p_1688_, 1);
lean_inc(v_v_1697_);
v_p_1698_ = lean_ctor_get(v_p_1688_, 2);
lean_inc_ref(v_p_1698_);
lean_dec_ref_known(v_p_1688_, 3);
lean_inc_ref(v_toSemiring_1689_);
v___x_1699_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_toSemiring_1689_, v_ctx_1687_, v_v_1697_);
v___x_1700_ = lean_apply_2(v_zsmul_1695_, v_k_1696_, v___x_1699_);
v___x_1701_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1686_, v_ctx_1687_, v_p_1698_);
v___x_1702_ = lean_apply_2(v_toAdd_1691_, v___x_1700_, v___x_1701_);
return v___x_1702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg___boxed(lean_object* v_inst_1703_, lean_object* v_ctx_1704_, lean_object* v_p_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1703_, v_ctx_1704_, v_p_1705_);
lean_dec_ref(v_ctx_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote(lean_object* v_00_u03b1_1707_, lean_object* v_inst_1708_, lean_object* v_ctx_1709_, lean_object* v_p_1710_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1708_, v_ctx_1709_, v_p_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___boxed(lean_object* v_00_u03b1_1712_, lean_object* v_inst_1713_, lean_object* v_ctx_1714_, lean_object* v_p_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Grind_CommRing_Poly_denote(v_00_u03b1_1712_, v_inst_1713_, v_ctx_1714_, v_p_1715_);
lean_dec_ref(v_ctx_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg(lean_object* v_inst_1717_, lean_object* v_ctx_1718_, lean_object* v_k_1719_, lean_object* v_m_1720_){
_start:
{
lean_object* v_toSemiring_1721_; lean_object* v___x_1722_; lean_object* v_zsmul_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v_toSemiring_1721_ = lean_ctor_get(v_inst_1717_, 0);
lean_inc_ref(v_toSemiring_1721_);
v___x_1722_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1717_);
v_zsmul_1723_ = lean_ctor_get(v___x_1722_, 2);
lean_inc(v_zsmul_1723_);
lean_dec_ref(v___x_1722_);
v___x_1724_ = lean_unsigned_to_nat(1u);
v___x_1725_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1726_ = lean_int_dec_eq(v_k_1719_, v___x_1725_);
if (v___x_1726_ == 0)
{
if (lean_obj_tag(v_m_1720_) == 0)
{
lean_object* v_ofNat_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_ofNat_1727_ = lean_ctor_get(v_toSemiring_1721_, 3);
lean_inc(v_ofNat_1727_);
lean_dec_ref(v_toSemiring_1721_);
v___x_1728_ = lean_apply_1(v_ofNat_1727_, v___x_1724_);
v___x_1729_ = lean_apply_2(v_zsmul_1723_, v_k_1719_, v___x_1728_);
return v___x_1729_;
}
else
{
lean_object* v_p_1730_; lean_object* v_m_1731_; lean_object* v_ofNat_1732_; lean_object* v_npow_1733_; lean_object* v_x_1734_; lean_object* v_k_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v_p_1730_ = lean_ctor_get(v_m_1720_, 0);
lean_inc_ref(v_p_1730_);
v_m_1731_ = lean_ctor_get(v_m_1720_, 1);
lean_inc(v_m_1731_);
lean_dec_ref_known(v_m_1720_, 2);
v_ofNat_1732_ = lean_ctor_get(v_toSemiring_1721_, 3);
v_npow_1733_ = lean_ctor_get(v_toSemiring_1721_, 5);
v_x_1734_ = lean_ctor_get(v_p_1730_, 0);
lean_inc(v_x_1734_);
v_k_1735_ = lean_ctor_get(v_p_1730_, 1);
lean_inc(v_k_1735_);
lean_dec_ref(v_p_1730_);
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = lean_nat_dec_eq(v_k_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_nat_dec_eq(v_k_1735_, v___x_1724_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1739_ = l_Lean_RArray_getImpl___redArg(v_ctx_1718_, v_x_1734_);
lean_dec(v_x_1734_);
lean_inc(v_npow_1733_);
v___x_1740_ = lean_apply_2(v_npow_1733_, v___x_1739_, v_k_1735_);
v___x_1741_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1721_, v_ctx_1718_, v_m_1731_, v___x_1740_);
v___x_1742_ = lean_apply_2(v_zsmul_1723_, v_k_1719_, v___x_1741_);
return v___x_1742_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec(v_k_1735_);
v___x_1743_ = l_Lean_RArray_getImpl___redArg(v_ctx_1718_, v_x_1734_);
lean_dec(v_x_1734_);
v___x_1744_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1721_, v_ctx_1718_, v_m_1731_, v___x_1743_);
v___x_1745_ = lean_apply_2(v_zsmul_1723_, v_k_1719_, v___x_1744_);
return v___x_1745_;
}
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec(v_k_1735_);
lean_dec(v_x_1734_);
lean_inc(v_ofNat_1732_);
v___x_1746_ = lean_apply_1(v_ofNat_1732_, v___x_1724_);
v___x_1747_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1721_, v_ctx_1718_, v_m_1731_, v___x_1746_);
v___x_1748_ = lean_apply_2(v_zsmul_1723_, v_k_1719_, v___x_1747_);
return v___x_1748_;
}
}
}
else
{
lean_dec(v_zsmul_1723_);
lean_dec(v_k_1719_);
if (lean_obj_tag(v_m_1720_) == 0)
{
lean_object* v_ofNat_1749_; lean_object* v___x_1750_; 
v_ofNat_1749_ = lean_ctor_get(v_toSemiring_1721_, 3);
lean_inc(v_ofNat_1749_);
lean_dec_ref(v_toSemiring_1721_);
v___x_1750_ = lean_apply_1(v_ofNat_1749_, v___x_1724_);
return v___x_1750_;
}
else
{
lean_object* v_p_1751_; lean_object* v_m_1752_; lean_object* v_ofNat_1753_; lean_object* v_npow_1754_; lean_object* v_x_1755_; lean_object* v_k_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v_p_1751_ = lean_ctor_get(v_m_1720_, 0);
lean_inc_ref(v_p_1751_);
v_m_1752_ = lean_ctor_get(v_m_1720_, 1);
lean_inc(v_m_1752_);
lean_dec_ref_known(v_m_1720_, 2);
v_ofNat_1753_ = lean_ctor_get(v_toSemiring_1721_, 3);
v_npow_1754_ = lean_ctor_get(v_toSemiring_1721_, 5);
v_x_1755_ = lean_ctor_get(v_p_1751_, 0);
lean_inc(v_x_1755_);
v_k_1756_ = lean_ctor_get(v_p_1751_, 1);
lean_inc(v_k_1756_);
lean_dec_ref(v_p_1751_);
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = lean_nat_dec_eq(v_k_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
uint8_t v___x_1759_; 
v___x_1759_ = lean_nat_dec_eq(v_k_1756_, v___x_1724_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = l_Lean_RArray_getImpl___redArg(v_ctx_1718_, v_x_1755_);
lean_dec(v_x_1755_);
lean_inc(v_npow_1754_);
v___x_1761_ = lean_apply_2(v_npow_1754_, v___x_1760_, v_k_1756_);
v___x_1762_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1721_, v_ctx_1718_, v_m_1752_, v___x_1761_);
return v___x_1762_;
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_dec(v_k_1756_);
v___x_1763_ = l_Lean_RArray_getImpl___redArg(v_ctx_1718_, v_x_1755_);
lean_dec(v_x_1755_);
v___x_1764_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1721_, v_ctx_1718_, v_m_1752_, v___x_1763_);
return v___x_1764_;
}
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_dec(v_k_1756_);
lean_dec(v_x_1755_);
lean_inc(v_ofNat_1753_);
v___x_1765_ = lean_apply_1(v_ofNat_1753_, v___x_1724_);
v___x_1766_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1721_, v_ctx_1718_, v_m_1752_, v___x_1765_);
return v___x_1766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg___boxed(lean_object* v_inst_1767_, lean_object* v_ctx_1768_, lean_object* v_k_1769_, lean_object* v_m_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_Grind_CommRing_denoteTerm___redArg(v_inst_1767_, v_ctx_1768_, v_k_1769_, v_m_1770_);
lean_dec_ref(v_ctx_1768_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm(lean_object* v_00_u03b1_1772_, lean_object* v_inst_1773_, lean_object* v_ctx_1774_, lean_object* v_k_1775_, lean_object* v_m_1776_){
_start:
{
lean_object* v_toSemiring_1777_; lean_object* v___x_1778_; lean_object* v_zsmul_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v_toSemiring_1777_ = lean_ctor_get(v_inst_1773_, 0);
lean_inc_ref(v_toSemiring_1777_);
v___x_1778_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1773_);
v_zsmul_1779_ = lean_ctor_get(v___x_1778_, 2);
lean_inc(v_zsmul_1779_);
lean_dec_ref(v___x_1778_);
v___x_1780_ = lean_unsigned_to_nat(1u);
v___x_1781_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1782_ = lean_int_dec_eq(v_k_1775_, v___x_1781_);
if (v___x_1782_ == 0)
{
if (lean_obj_tag(v_m_1776_) == 0)
{
lean_object* v_ofNat_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v_ofNat_1783_ = lean_ctor_get(v_toSemiring_1777_, 3);
lean_inc(v_ofNat_1783_);
lean_dec_ref(v_toSemiring_1777_);
v___x_1784_ = lean_apply_1(v_ofNat_1783_, v___x_1780_);
v___x_1785_ = lean_apply_2(v_zsmul_1779_, v_k_1775_, v___x_1784_);
return v___x_1785_;
}
else
{
lean_object* v_p_1786_; lean_object* v_m_1787_; lean_object* v_ofNat_1788_; lean_object* v_npow_1789_; lean_object* v_x_1790_; lean_object* v_k_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_p_1786_ = lean_ctor_get(v_m_1776_, 0);
lean_inc_ref(v_p_1786_);
v_m_1787_ = lean_ctor_get(v_m_1776_, 1);
lean_inc(v_m_1787_);
lean_dec_ref_known(v_m_1776_, 2);
v_ofNat_1788_ = lean_ctor_get(v_toSemiring_1777_, 3);
v_npow_1789_ = lean_ctor_get(v_toSemiring_1777_, 5);
v_x_1790_ = lean_ctor_get(v_p_1786_, 0);
lean_inc(v_x_1790_);
v_k_1791_ = lean_ctor_get(v_p_1786_, 1);
lean_inc(v_k_1791_);
lean_dec_ref(v_p_1786_);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = lean_nat_dec_eq(v_k_1791_, v___x_1792_);
if (v___x_1793_ == 0)
{
uint8_t v___x_1794_; 
v___x_1794_ = lean_nat_dec_eq(v_k_1791_, v___x_1780_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1795_ = l_Lean_RArray_getImpl___redArg(v_ctx_1774_, v_x_1790_);
lean_dec(v_x_1790_);
lean_inc(v_npow_1789_);
v___x_1796_ = lean_apply_2(v_npow_1789_, v___x_1795_, v_k_1791_);
v___x_1797_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1777_, v_ctx_1774_, v_m_1787_, v___x_1796_);
v___x_1798_ = lean_apply_2(v_zsmul_1779_, v_k_1775_, v___x_1797_);
return v___x_1798_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec(v_k_1791_);
v___x_1799_ = l_Lean_RArray_getImpl___redArg(v_ctx_1774_, v_x_1790_);
lean_dec(v_x_1790_);
v___x_1800_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1777_, v_ctx_1774_, v_m_1787_, v___x_1799_);
v___x_1801_ = lean_apply_2(v_zsmul_1779_, v_k_1775_, v___x_1800_);
return v___x_1801_;
}
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_dec(v_k_1791_);
lean_dec(v_x_1790_);
lean_inc(v_ofNat_1788_);
v___x_1802_ = lean_apply_1(v_ofNat_1788_, v___x_1780_);
v___x_1803_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1777_, v_ctx_1774_, v_m_1787_, v___x_1802_);
v___x_1804_ = lean_apply_2(v_zsmul_1779_, v_k_1775_, v___x_1803_);
return v___x_1804_;
}
}
}
else
{
lean_dec(v_zsmul_1779_);
lean_dec(v_k_1775_);
if (lean_obj_tag(v_m_1776_) == 0)
{
lean_object* v_ofNat_1805_; lean_object* v___x_1806_; 
v_ofNat_1805_ = lean_ctor_get(v_toSemiring_1777_, 3);
lean_inc(v_ofNat_1805_);
lean_dec_ref(v_toSemiring_1777_);
v___x_1806_ = lean_apply_1(v_ofNat_1805_, v___x_1780_);
return v___x_1806_;
}
else
{
lean_object* v_p_1807_; lean_object* v_m_1808_; lean_object* v_ofNat_1809_; lean_object* v_npow_1810_; lean_object* v_x_1811_; lean_object* v_k_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v_p_1807_ = lean_ctor_get(v_m_1776_, 0);
lean_inc_ref(v_p_1807_);
v_m_1808_ = lean_ctor_get(v_m_1776_, 1);
lean_inc(v_m_1808_);
lean_dec_ref_known(v_m_1776_, 2);
v_ofNat_1809_ = lean_ctor_get(v_toSemiring_1777_, 3);
v_npow_1810_ = lean_ctor_get(v_toSemiring_1777_, 5);
v_x_1811_ = lean_ctor_get(v_p_1807_, 0);
lean_inc(v_x_1811_);
v_k_1812_ = lean_ctor_get(v_p_1807_, 1);
lean_inc(v_k_1812_);
lean_dec_ref(v_p_1807_);
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_nat_dec_eq(v_k_1812_, v___x_1813_);
if (v___x_1814_ == 0)
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_nat_dec_eq(v_k_1812_, v___x_1780_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = l_Lean_RArray_getImpl___redArg(v_ctx_1774_, v_x_1811_);
lean_dec(v_x_1811_);
lean_inc(v_npow_1810_);
v___x_1817_ = lean_apply_2(v_npow_1810_, v___x_1816_, v_k_1812_);
v___x_1818_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1777_, v_ctx_1774_, v_m_1808_, v___x_1817_);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec(v_k_1812_);
v___x_1819_ = l_Lean_RArray_getImpl___redArg(v_ctx_1774_, v_x_1811_);
lean_dec(v_x_1811_);
v___x_1820_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1777_, v_ctx_1774_, v_m_1808_, v___x_1819_);
return v___x_1820_;
}
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec(v_k_1812_);
lean_dec(v_x_1811_);
lean_inc(v_ofNat_1809_);
v___x_1821_ = lean_apply_1(v_ofNat_1809_, v___x_1780_);
v___x_1822_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1777_, v_ctx_1774_, v_m_1808_, v___x_1821_);
return v___x_1822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___boxed(lean_object* v_00_u03b1_1823_, lean_object* v_inst_1824_, lean_object* v_ctx_1825_, lean_object* v_k_1826_, lean_object* v_m_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Grind_CommRing_denoteTerm(v_00_u03b1_1823_, v_inst_1824_, v_ctx_1825_, v_k_1826_, v_m_1827_);
lean_dec_ref(v_ctx_1825_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(lean_object* v_inst_1829_, lean_object* v_ctx_1830_, lean_object* v_p_1831_, lean_object* v_acc_1832_){
_start:
{
if (lean_obj_tag(v_p_1831_) == 0)
{
lean_object* v_toSemiring_1833_; lean_object* v_intCast_1834_; lean_object* v_toAdd_1835_; lean_object* v_k_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v_toSemiring_1833_ = lean_ctor_get(v_inst_1829_, 0);
lean_inc_ref(v_toSemiring_1833_);
v_intCast_1834_ = lean_ctor_get(v_inst_1829_, 3);
lean_inc(v_intCast_1834_);
lean_dec_ref(v_inst_1829_);
v_toAdd_1835_ = lean_ctor_get(v_toSemiring_1833_, 0);
lean_inc(v_toAdd_1835_);
lean_dec_ref(v_toSemiring_1833_);
v_k_1836_ = lean_ctor_get(v_p_1831_, 0);
lean_inc(v_k_1836_);
lean_dec_ref_known(v_p_1831_, 1);
v___x_1837_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1838_ = lean_int_dec_eq(v_k_1836_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_apply_1(v_intCast_1834_, v_k_1836_);
v___x_1840_ = lean_apply_2(v_toAdd_1835_, v_acc_1832_, v___x_1839_);
return v___x_1840_;
}
else
{
lean_dec(v_k_1836_);
lean_dec(v_toAdd_1835_);
lean_dec(v_intCast_1834_);
return v_acc_1832_;
}
}
else
{
lean_object* v_toSemiring_1841_; lean_object* v_toAdd_1842_; lean_object* v_ofNat_1843_; lean_object* v_npow_1844_; lean_object* v_k_1845_; lean_object* v_v_1846_; lean_object* v_p_1847_; lean_object* v___y_1849_; lean_object* v___x_1852_; lean_object* v_zsmul_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v_toSemiring_1841_ = lean_ctor_get(v_inst_1829_, 0);
v_toAdd_1842_ = lean_ctor_get(v_toSemiring_1841_, 0);
v_ofNat_1843_ = lean_ctor_get(v_toSemiring_1841_, 3);
v_npow_1844_ = lean_ctor_get(v_toSemiring_1841_, 5);
v_k_1845_ = lean_ctor_get(v_p_1831_, 0);
lean_inc(v_k_1845_);
v_v_1846_ = lean_ctor_get(v_p_1831_, 1);
lean_inc(v_v_1846_);
v_p_1847_ = lean_ctor_get(v_p_1831_, 2);
lean_inc_ref(v_p_1847_);
lean_dec_ref_known(v_p_1831_, 3);
lean_inc_ref(v_inst_1829_);
v___x_1852_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1829_);
v_zsmul_1853_ = lean_ctor_get(v___x_1852_, 2);
lean_inc(v_zsmul_1853_);
lean_dec_ref(v___x_1852_);
v___x_1854_ = lean_unsigned_to_nat(1u);
v___x_1855_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1856_ = lean_int_dec_eq(v_k_1845_, v___x_1855_);
if (v___x_1856_ == 0)
{
if (lean_obj_tag(v_v_1846_) == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
lean_inc(v_ofNat_1843_);
v___x_1857_ = lean_apply_1(v_ofNat_1843_, v___x_1854_);
v___x_1858_ = lean_apply_2(v_zsmul_1853_, v_k_1845_, v___x_1857_);
v___y_1849_ = v___x_1858_;
goto v___jp_1848_;
}
else
{
lean_object* v_p_1859_; lean_object* v_m_1860_; lean_object* v_x_1861_; lean_object* v_k_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v_p_1859_ = lean_ctor_get(v_v_1846_, 0);
lean_inc_ref(v_p_1859_);
v_m_1860_ = lean_ctor_get(v_v_1846_, 1);
lean_inc(v_m_1860_);
lean_dec_ref_known(v_v_1846_, 2);
v_x_1861_ = lean_ctor_get(v_p_1859_, 0);
lean_inc(v_x_1861_);
v_k_1862_ = lean_ctor_get(v_p_1859_, 1);
lean_inc(v_k_1862_);
lean_dec_ref(v_p_1859_);
v___x_1863_ = lean_unsigned_to_nat(0u);
v___x_1864_ = lean_nat_dec_eq(v_k_1862_, v___x_1863_);
if (v___x_1864_ == 0)
{
uint8_t v___x_1865_; 
v___x_1865_ = lean_nat_dec_eq(v_k_1862_, v___x_1854_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1866_ = l_Lean_RArray_getImpl___redArg(v_ctx_1830_, v_x_1861_);
lean_dec(v_x_1861_);
lean_inc(v_npow_1844_);
v___x_1867_ = lean_apply_2(v_npow_1844_, v___x_1866_, v_k_1862_);
lean_inc_ref(v_toSemiring_1841_);
v___x_1868_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1841_, v_ctx_1830_, v_m_1860_, v___x_1867_);
v___x_1869_ = lean_apply_2(v_zsmul_1853_, v_k_1845_, v___x_1868_);
v___y_1849_ = v___x_1869_;
goto v___jp_1848_;
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_dec(v_k_1862_);
v___x_1870_ = l_Lean_RArray_getImpl___redArg(v_ctx_1830_, v_x_1861_);
lean_dec(v_x_1861_);
lean_inc_ref(v_toSemiring_1841_);
v___x_1871_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1841_, v_ctx_1830_, v_m_1860_, v___x_1870_);
v___x_1872_ = lean_apply_2(v_zsmul_1853_, v_k_1845_, v___x_1871_);
v___y_1849_ = v___x_1872_;
goto v___jp_1848_;
}
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec(v_k_1862_);
lean_dec(v_x_1861_);
lean_inc(v_ofNat_1843_);
v___x_1873_ = lean_apply_1(v_ofNat_1843_, v___x_1854_);
lean_inc_ref(v_toSemiring_1841_);
v___x_1874_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1841_, v_ctx_1830_, v_m_1860_, v___x_1873_);
v___x_1875_ = lean_apply_2(v_zsmul_1853_, v_k_1845_, v___x_1874_);
v___y_1849_ = v___x_1875_;
goto v___jp_1848_;
}
}
}
else
{
lean_dec(v_zsmul_1853_);
lean_dec(v_k_1845_);
if (lean_obj_tag(v_v_1846_) == 0)
{
lean_object* v___x_1876_; 
lean_inc(v_ofNat_1843_);
v___x_1876_ = lean_apply_1(v_ofNat_1843_, v___x_1854_);
v___y_1849_ = v___x_1876_;
goto v___jp_1848_;
}
else
{
lean_object* v_p_1877_; lean_object* v_m_1878_; lean_object* v_x_1879_; lean_object* v_k_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; 
v_p_1877_ = lean_ctor_get(v_v_1846_, 0);
lean_inc_ref(v_p_1877_);
v_m_1878_ = lean_ctor_get(v_v_1846_, 1);
lean_inc(v_m_1878_);
lean_dec_ref_known(v_v_1846_, 2);
v_x_1879_ = lean_ctor_get(v_p_1877_, 0);
lean_inc(v_x_1879_);
v_k_1880_ = lean_ctor_get(v_p_1877_, 1);
lean_inc(v_k_1880_);
lean_dec_ref(v_p_1877_);
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = lean_nat_dec_eq(v_k_1880_, v___x_1881_);
if (v___x_1882_ == 0)
{
uint8_t v___x_1883_; 
v___x_1883_ = lean_nat_dec_eq(v_k_1880_, v___x_1854_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = l_Lean_RArray_getImpl___redArg(v_ctx_1830_, v_x_1879_);
lean_dec(v_x_1879_);
lean_inc(v_npow_1844_);
v___x_1885_ = lean_apply_2(v_npow_1844_, v___x_1884_, v_k_1880_);
lean_inc_ref(v_toSemiring_1841_);
v___x_1886_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1841_, v_ctx_1830_, v_m_1878_, v___x_1885_);
v___y_1849_ = v___x_1886_;
goto v___jp_1848_;
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec(v_k_1880_);
v___x_1887_ = l_Lean_RArray_getImpl___redArg(v_ctx_1830_, v_x_1879_);
lean_dec(v_x_1879_);
lean_inc_ref(v_toSemiring_1841_);
v___x_1888_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1841_, v_ctx_1830_, v_m_1878_, v___x_1887_);
v___y_1849_ = v___x_1888_;
goto v___jp_1848_;
}
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec(v_k_1880_);
lean_dec(v_x_1879_);
lean_inc(v_ofNat_1843_);
v___x_1889_ = lean_apply_1(v_ofNat_1843_, v___x_1854_);
lean_inc_ref(v_toSemiring_1841_);
v___x_1890_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1841_, v_ctx_1830_, v_m_1878_, v___x_1889_);
v___y_1849_ = v___x_1890_;
goto v___jp_1848_;
}
}
}
v___jp_1848_:
{
lean_object* v___x_1850_; 
lean_inc(v_toAdd_1842_);
v___x_1850_ = lean_apply_2(v_toAdd_1842_, v_acc_1832_, v___y_1849_);
v_p_1831_ = v_p_1847_;
v_acc_1832_ = v___x_1850_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg___boxed(lean_object* v_inst_1891_, lean_object* v_ctx_1892_, lean_object* v_p_1893_, lean_object* v_acc_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1891_, v_ctx_1892_, v_p_1893_, v_acc_1894_);
lean_dec_ref(v_ctx_1892_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go(lean_object* v_00_u03b1_1896_, lean_object* v_inst_1897_, lean_object* v_ctx_1898_, lean_object* v_p_1899_, lean_object* v_acc_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1897_, v_ctx_1898_, v_p_1899_, v_acc_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___boxed(lean_object* v_00_u03b1_1902_, lean_object* v_inst_1903_, lean_object* v_ctx_1904_, lean_object* v_p_1905_, lean_object* v_acc_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_Grind_CommRing_Poly_denote_x27_go(v_00_u03b1_1902_, v_inst_1903_, v_ctx_1904_, v_p_1905_, v_acc_1906_);
lean_dec_ref(v_ctx_1904_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg(lean_object* v_inst_1908_, lean_object* v_ctx_1909_, lean_object* v_p_1910_){
_start:
{
if (lean_obj_tag(v_p_1910_) == 0)
{
lean_object* v_intCast_1911_; lean_object* v_k_1912_; lean_object* v___x_1913_; 
v_intCast_1911_ = lean_ctor_get(v_inst_1908_, 3);
lean_inc(v_intCast_1911_);
lean_dec_ref(v_inst_1908_);
v_k_1912_ = lean_ctor_get(v_p_1910_, 0);
lean_inc(v_k_1912_);
lean_dec_ref_known(v_p_1910_, 1);
v___x_1913_ = lean_apply_1(v_intCast_1911_, v_k_1912_);
return v___x_1913_;
}
else
{
lean_object* v_toSemiring_1914_; lean_object* v_k_1915_; lean_object* v_v_1916_; lean_object* v_p_1917_; lean_object* v___x_1918_; lean_object* v_zsmul_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v_toSemiring_1914_ = lean_ctor_get(v_inst_1908_, 0);
v_k_1915_ = lean_ctor_get(v_p_1910_, 0);
lean_inc(v_k_1915_);
v_v_1916_ = lean_ctor_get(v_p_1910_, 1);
lean_inc(v_v_1916_);
v_p_1917_ = lean_ctor_get(v_p_1910_, 2);
lean_inc_ref(v_p_1917_);
lean_dec_ref_known(v_p_1910_, 3);
lean_inc_ref(v_inst_1908_);
v___x_1918_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1908_);
v_zsmul_1919_ = lean_ctor_get(v___x_1918_, 2);
lean_inc(v_zsmul_1919_);
lean_dec_ref(v___x_1918_);
v___x_1920_ = lean_unsigned_to_nat(1u);
v___x_1921_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1922_ = lean_int_dec_eq(v_k_1915_, v___x_1921_);
if (v___x_1922_ == 0)
{
if (lean_obj_tag(v_v_1916_) == 0)
{
lean_object* v_ofNat_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_ofNat_1923_ = lean_ctor_get(v_toSemiring_1914_, 3);
lean_inc(v_ofNat_1923_);
v___x_1924_ = lean_apply_1(v_ofNat_1923_, v___x_1920_);
v___x_1925_ = lean_apply_2(v_zsmul_1919_, v_k_1915_, v___x_1924_);
v___x_1926_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1908_, v_ctx_1909_, v_p_1917_, v___x_1925_);
return v___x_1926_;
}
else
{
lean_object* v_p_1927_; lean_object* v_m_1928_; lean_object* v_ofNat_1929_; lean_object* v_npow_1930_; lean_object* v_x_1931_; lean_object* v_k_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v_p_1927_ = lean_ctor_get(v_v_1916_, 0);
lean_inc_ref(v_p_1927_);
v_m_1928_ = lean_ctor_get(v_v_1916_, 1);
lean_inc(v_m_1928_);
lean_dec_ref_known(v_v_1916_, 2);
v_ofNat_1929_ = lean_ctor_get(v_toSemiring_1914_, 3);
v_npow_1930_ = lean_ctor_get(v_toSemiring_1914_, 5);
v_x_1931_ = lean_ctor_get(v_p_1927_, 0);
lean_inc(v_x_1931_);
v_k_1932_ = lean_ctor_get(v_p_1927_, 1);
lean_inc(v_k_1932_);
lean_dec_ref(v_p_1927_);
v___x_1933_ = lean_unsigned_to_nat(0u);
v___x_1934_ = lean_nat_dec_eq(v_k_1932_, v___x_1933_);
if (v___x_1934_ == 0)
{
uint8_t v___x_1935_; 
v___x_1935_ = lean_nat_dec_eq(v_k_1932_, v___x_1920_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1936_ = l_Lean_RArray_getImpl___redArg(v_ctx_1909_, v_x_1931_);
lean_dec(v_x_1931_);
lean_inc(v_npow_1930_);
v___x_1937_ = lean_apply_2(v_npow_1930_, v___x_1936_, v_k_1932_);
lean_inc_ref(v_toSemiring_1914_);
v___x_1938_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1914_, v_ctx_1909_, v_m_1928_, v___x_1937_);
v___x_1939_ = lean_apply_2(v_zsmul_1919_, v_k_1915_, v___x_1938_);
v___x_1940_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1908_, v_ctx_1909_, v_p_1917_, v___x_1939_);
return v___x_1940_;
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec(v_k_1932_);
v___x_1941_ = l_Lean_RArray_getImpl___redArg(v_ctx_1909_, v_x_1931_);
lean_dec(v_x_1931_);
lean_inc_ref(v_toSemiring_1914_);
v___x_1942_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1914_, v_ctx_1909_, v_m_1928_, v___x_1941_);
v___x_1943_ = lean_apply_2(v_zsmul_1919_, v_k_1915_, v___x_1942_);
v___x_1944_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1908_, v_ctx_1909_, v_p_1917_, v___x_1943_);
return v___x_1944_;
}
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
lean_dec(v_k_1932_);
lean_dec(v_x_1931_);
lean_inc(v_ofNat_1929_);
v___x_1945_ = lean_apply_1(v_ofNat_1929_, v___x_1920_);
lean_inc_ref(v_toSemiring_1914_);
v___x_1946_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1914_, v_ctx_1909_, v_m_1928_, v___x_1945_);
v___x_1947_ = lean_apply_2(v_zsmul_1919_, v_k_1915_, v___x_1946_);
v___x_1948_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1908_, v_ctx_1909_, v_p_1917_, v___x_1947_);
return v___x_1948_;
}
}
}
else
{
lean_dec(v_zsmul_1919_);
lean_dec(v_k_1915_);
if (lean_obj_tag(v_v_1916_) == 0)
{
lean_object* v_ofNat_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v_ofNat_1949_ = lean_ctor_get(v_toSemiring_1914_, 3);
lean_inc(v_ofNat_1949_);
v___x_1950_ = lean_apply_1(v_ofNat_1949_, v___x_1920_);
v___x_1951_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1908_, v_ctx_1909_, v_p_1917_, v___x_1950_);
return v___x_1951_;
}
else
{
lean_object* v_p_1952_; lean_object* v_m_1953_; lean_object* v_ofNat_1954_; lean_object* v_npow_1955_; lean_object* v_x_1956_; lean_object* v_k_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v_p_1952_ = lean_ctor_get(v_v_1916_, 0);
lean_inc_ref(v_p_1952_);
v_m_1953_ = lean_ctor_get(v_v_1916_, 1);
lean_inc(v_m_1953_);
lean_dec_ref_known(v_v_1916_, 2);
v_ofNat_1954_ = lean_ctor_get(v_toSemiring_1914_, 3);
v_npow_1955_ = lean_ctor_get(v_toSemiring_1914_, 5);
v_x_1956_ = lean_ctor_get(v_p_1952_, 0);
lean_inc(v_x_1956_);
v_k_1957_ = lean_ctor_get(v_p_1952_, 1);
lean_inc(v_k_1957_);
lean_dec_ref(v_p_1952_);
v___x_1958_ = lean_unsigned_to_nat(0u);
v___x_1959_ = lean_nat_dec_eq(v_k_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
uint8_t v___x_1960_; 
v___x_1960_ = lean_nat_dec_eq(v_k_1957_, v___x_1920_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1961_ = l_Lean_RArray_getImpl___redArg(v_ctx_1909_, v_x_1956_);
lean_dec(v_x_1956_);
lean_inc(v_npow_1955_);
v___x_1962_ = lean_apply_2(v_npow_1955_, v___x_1961_, v_k_1957_);
lean_inc_ref(v_toSemiring_1914_);
v___x_1963_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1914_, v_ctx_1909_, v_m_1953_, v___x_1962_);
v___x_1964_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1908_, v_ctx_1909_, v_p_1917_, v___x_1963_);
return v___x_1964_;
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_dec(v_k_1957_);
v___x_1965_ = l_Lean_RArray_getImpl___redArg(v_ctx_1909_, v_x_1956_);
lean_dec(v_x_1956_);
lean_inc_ref(v_toSemiring_1914_);
v___x_1966_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1914_, v_ctx_1909_, v_m_1953_, v___x_1965_);
v___x_1967_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1908_, v_ctx_1909_, v_p_1917_, v___x_1966_);
return v___x_1967_;
}
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_dec(v_k_1957_);
lean_dec(v_x_1956_);
lean_inc(v_ofNat_1954_);
v___x_1968_ = lean_apply_1(v_ofNat_1954_, v___x_1920_);
lean_inc_ref(v_toSemiring_1914_);
v___x_1969_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1914_, v_ctx_1909_, v_m_1953_, v___x_1968_);
v___x_1970_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1908_, v_ctx_1909_, v_p_1917_, v___x_1969_);
return v___x_1970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg___boxed(lean_object* v_inst_1971_, lean_object* v_ctx_1972_, lean_object* v_p_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_Grind_CommRing_Poly_denote_x27___redArg(v_inst_1971_, v_ctx_1972_, v_p_1973_);
lean_dec_ref(v_ctx_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27(lean_object* v_00_u03b1_1975_, lean_object* v_inst_1976_, lean_object* v_ctx_1977_, lean_object* v_p_1978_){
_start:
{
if (lean_obj_tag(v_p_1978_) == 0)
{
lean_object* v_intCast_1979_; lean_object* v_k_1980_; lean_object* v___x_1981_; 
v_intCast_1979_ = lean_ctor_get(v_inst_1976_, 3);
lean_inc(v_intCast_1979_);
lean_dec_ref(v_inst_1976_);
v_k_1980_ = lean_ctor_get(v_p_1978_, 0);
lean_inc(v_k_1980_);
lean_dec_ref_known(v_p_1978_, 1);
v___x_1981_ = lean_apply_1(v_intCast_1979_, v_k_1980_);
return v___x_1981_;
}
else
{
lean_object* v_toSemiring_1982_; lean_object* v_k_1983_; lean_object* v_v_1984_; lean_object* v_p_1985_; lean_object* v___x_1986_; lean_object* v_zsmul_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v_toSemiring_1982_ = lean_ctor_get(v_inst_1976_, 0);
v_k_1983_ = lean_ctor_get(v_p_1978_, 0);
lean_inc(v_k_1983_);
v_v_1984_ = lean_ctor_get(v_p_1978_, 1);
lean_inc(v_v_1984_);
v_p_1985_ = lean_ctor_get(v_p_1978_, 2);
lean_inc_ref(v_p_1985_);
lean_dec_ref_known(v_p_1978_, 3);
lean_inc_ref(v_inst_1976_);
v___x_1986_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1976_);
v_zsmul_1987_ = lean_ctor_get(v___x_1986_, 2);
lean_inc(v_zsmul_1987_);
lean_dec_ref(v___x_1986_);
v___x_1988_ = lean_unsigned_to_nat(1u);
v___x_1989_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1990_ = lean_int_dec_eq(v_k_1983_, v___x_1989_);
if (v___x_1990_ == 0)
{
if (lean_obj_tag(v_v_1984_) == 0)
{
lean_object* v_ofNat_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_ofNat_1991_ = lean_ctor_get(v_toSemiring_1982_, 3);
lean_inc(v_ofNat_1991_);
v___x_1992_ = lean_apply_1(v_ofNat_1991_, v___x_1988_);
v___x_1993_ = lean_apply_2(v_zsmul_1987_, v_k_1983_, v___x_1992_);
v___x_1994_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1976_, v_ctx_1977_, v_p_1985_, v___x_1993_);
return v___x_1994_;
}
else
{
lean_object* v_p_1995_; lean_object* v_m_1996_; lean_object* v_ofNat_1997_; lean_object* v_npow_1998_; lean_object* v_x_1999_; lean_object* v_k_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v_p_1995_ = lean_ctor_get(v_v_1984_, 0);
lean_inc_ref(v_p_1995_);
v_m_1996_ = lean_ctor_get(v_v_1984_, 1);
lean_inc(v_m_1996_);
lean_dec_ref_known(v_v_1984_, 2);
v_ofNat_1997_ = lean_ctor_get(v_toSemiring_1982_, 3);
v_npow_1998_ = lean_ctor_get(v_toSemiring_1982_, 5);
v_x_1999_ = lean_ctor_get(v_p_1995_, 0);
lean_inc(v_x_1999_);
v_k_2000_ = lean_ctor_get(v_p_1995_, 1);
lean_inc(v_k_2000_);
lean_dec_ref(v_p_1995_);
v___x_2001_ = lean_unsigned_to_nat(0u);
v___x_2002_ = lean_nat_dec_eq(v_k_2000_, v___x_2001_);
if (v___x_2002_ == 0)
{
uint8_t v___x_2003_; 
v___x_2003_ = lean_nat_dec_eq(v_k_2000_, v___x_1988_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2004_ = l_Lean_RArray_getImpl___redArg(v_ctx_1977_, v_x_1999_);
lean_dec(v_x_1999_);
lean_inc(v_npow_1998_);
v___x_2005_ = lean_apply_2(v_npow_1998_, v___x_2004_, v_k_2000_);
lean_inc_ref(v_toSemiring_1982_);
v___x_2006_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1982_, v_ctx_1977_, v_m_1996_, v___x_2005_);
v___x_2007_ = lean_apply_2(v_zsmul_1987_, v_k_1983_, v___x_2006_);
v___x_2008_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1976_, v_ctx_1977_, v_p_1985_, v___x_2007_);
return v___x_2008_;
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
lean_dec(v_k_2000_);
v___x_2009_ = l_Lean_RArray_getImpl___redArg(v_ctx_1977_, v_x_1999_);
lean_dec(v_x_1999_);
lean_inc_ref(v_toSemiring_1982_);
v___x_2010_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1982_, v_ctx_1977_, v_m_1996_, v___x_2009_);
v___x_2011_ = lean_apply_2(v_zsmul_1987_, v_k_1983_, v___x_2010_);
v___x_2012_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1976_, v_ctx_1977_, v_p_1985_, v___x_2011_);
return v___x_2012_;
}
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_dec(v_k_2000_);
lean_dec(v_x_1999_);
lean_inc(v_ofNat_1997_);
v___x_2013_ = lean_apply_1(v_ofNat_1997_, v___x_1988_);
lean_inc_ref(v_toSemiring_1982_);
v___x_2014_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1982_, v_ctx_1977_, v_m_1996_, v___x_2013_);
v___x_2015_ = lean_apply_2(v_zsmul_1987_, v_k_1983_, v___x_2014_);
v___x_2016_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1976_, v_ctx_1977_, v_p_1985_, v___x_2015_);
return v___x_2016_;
}
}
}
else
{
lean_dec(v_zsmul_1987_);
lean_dec(v_k_1983_);
if (lean_obj_tag(v_v_1984_) == 0)
{
lean_object* v_ofNat_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_ofNat_2017_ = lean_ctor_get(v_toSemiring_1982_, 3);
lean_inc(v_ofNat_2017_);
v___x_2018_ = lean_apply_1(v_ofNat_2017_, v___x_1988_);
v___x_2019_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1976_, v_ctx_1977_, v_p_1985_, v___x_2018_);
return v___x_2019_;
}
else
{
lean_object* v_p_2020_; lean_object* v_m_2021_; lean_object* v_ofNat_2022_; lean_object* v_npow_2023_; lean_object* v_x_2024_; lean_object* v_k_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_p_2020_ = lean_ctor_get(v_v_1984_, 0);
lean_inc_ref(v_p_2020_);
v_m_2021_ = lean_ctor_get(v_v_1984_, 1);
lean_inc(v_m_2021_);
lean_dec_ref_known(v_v_1984_, 2);
v_ofNat_2022_ = lean_ctor_get(v_toSemiring_1982_, 3);
v_npow_2023_ = lean_ctor_get(v_toSemiring_1982_, 5);
v_x_2024_ = lean_ctor_get(v_p_2020_, 0);
lean_inc(v_x_2024_);
v_k_2025_ = lean_ctor_get(v_p_2020_, 1);
lean_inc(v_k_2025_);
lean_dec_ref(v_p_2020_);
v___x_2026_ = lean_unsigned_to_nat(0u);
v___x_2027_ = lean_nat_dec_eq(v_k_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_nat_dec_eq(v_k_2025_, v___x_1988_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2029_ = l_Lean_RArray_getImpl___redArg(v_ctx_1977_, v_x_2024_);
lean_dec(v_x_2024_);
lean_inc(v_npow_2023_);
v___x_2030_ = lean_apply_2(v_npow_2023_, v___x_2029_, v_k_2025_);
lean_inc_ref(v_toSemiring_1982_);
v___x_2031_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1982_, v_ctx_1977_, v_m_2021_, v___x_2030_);
v___x_2032_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1976_, v_ctx_1977_, v_p_1985_, v___x_2031_);
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec(v_k_2025_);
v___x_2033_ = l_Lean_RArray_getImpl___redArg(v_ctx_1977_, v_x_2024_);
lean_dec(v_x_2024_);
lean_inc_ref(v_toSemiring_1982_);
v___x_2034_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1982_, v_ctx_1977_, v_m_2021_, v___x_2033_);
v___x_2035_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1976_, v_ctx_1977_, v_p_1985_, v___x_2034_);
return v___x_2035_;
}
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_dec(v_k_2025_);
lean_dec(v_x_2024_);
lean_inc(v_ofNat_2022_);
v___x_2036_ = lean_apply_1(v_ofNat_2022_, v___x_1988_);
lean_inc_ref(v_toSemiring_1982_);
v___x_2037_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1982_, v_ctx_1977_, v_m_2021_, v___x_2036_);
v___x_2038_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1976_, v_ctx_1977_, v_p_1985_, v___x_2037_);
return v___x_2038_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___boxed(lean_object* v_00_u03b1_2039_, lean_object* v_inst_2040_, lean_object* v_ctx_2041_, lean_object* v_p_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_Grind_CommRing_Poly_denote_x27(v_00_u03b1_2039_, v_inst_2040_, v_ctx_2041_, v_p_2042_);
lean_dec_ref(v_ctx_2041_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object* v_m_2044_){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2046_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2047_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2045_);
lean_ctor_set(v___x_2047_, 1, v_m_2044_);
lean_ctor_set(v___x_2047_, 2, v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object* v_x_2048_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = l_Lean_Grind_CommRing_Mon_ofVar(v_x_2048_);
v___x_2050_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_isSorted(lean_object* v_x_2051_){
_start:
{
if (lean_obj_tag(v_x_2051_) == 0)
{
uint8_t v___x_2052_; 
v___x_2052_ = 1;
return v___x_2052_;
}
else
{
lean_object* v_p_2053_; 
v_p_2053_ = lean_ctor_get(v_x_2051_, 2);
if (lean_obj_tag(v_p_2053_) == 0)
{
uint8_t v___x_2054_; 
v___x_2054_ = 1;
return v___x_2054_;
}
else
{
lean_object* v_v_2055_; lean_object* v_v_2056_; uint8_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v_v_2055_ = lean_ctor_get(v_x_2051_, 1);
v_v_2056_ = lean_ctor_get(v_p_2053_, 1);
v___x_2057_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2055_, v_v_2056_);
v___x_2058_ = lean_box(v___x_2057_);
v___x_2059_ = lean_obj_tag_nat(v___x_2058_);
lean_dec(v___x_2058_);
v___x_2060_ = lean_unsigned_to_nat(2u);
v___x_2061_ = lean_nat_dec_eq(v___x_2059_, v___x_2060_);
if (v___x_2061_ == 0)
{
return v___x_2061_;
}
else
{
v_x_2051_ = v_p_2053_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isSorted___boxed(lean_object* v_x_2063_){
_start:
{
uint8_t v_res_2064_; lean_object* v_r_2065_; 
v_res_2064_ = l_Lean_Grind_CommRing_Poly_isSorted(v_x_2063_);
lean_dec_ref(v_x_2063_);
v_r_2065_ = lean_box(v_res_2064_);
return v_r_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go(lean_object* v_k_2066_, lean_object* v_a_2067_){
_start:
{
if (lean_obj_tag(v_a_2067_) == 0)
{
lean_object* v_k_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2076_; 
v_k_2068_ = lean_ctor_get(v_a_2067_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_a_2067_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2070_ = v_a_2067_;
v_isShared_2071_ = v_isSharedCheck_2076_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_k_2068_);
lean_dec(v_a_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2076_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2072_ = lean_int_add(v_k_2068_, v_k_2066_);
lean_dec(v_k_2068_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2072_);
v___x_2074_ = v___x_2070_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
else
{
lean_object* v_k_2077_; lean_object* v_v_2078_; lean_object* v_p_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2087_; 
v_k_2077_ = lean_ctor_get(v_a_2067_, 0);
v_v_2078_ = lean_ctor_get(v_a_2067_, 1);
v_p_2079_ = lean_ctor_get(v_a_2067_, 2);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_a_2067_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2081_ = v_a_2067_;
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_p_2079_);
lean_inc(v_v_2078_);
lean_inc(v_k_2077_);
lean_dec(v_a_2067_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2066_, v_p_2079_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 2, v___x_2083_);
v___x_2085_ = v___x_2081_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_k_2077_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_v_2078_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go___boxed(lean_object* v_k_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2088_, v_a_2089_);
lean_dec(v_k_2088_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object* v_p_2091_, lean_object* v_k_2092_){
_start:
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2094_ = lean_int_dec_eq(v_k_2092_, v___x_2093_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2092_, v_p_2091_);
return v___x_2095_;
}
else
{
return v_p_2091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst___boxed(lean_object* v_p_2096_, lean_object* v_k_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2096_, v_k_2097_);
lean_dec(v_k_2097_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object* v_p_2099_, lean_object* v_h__1_2100_, lean_object* v_h__2_2101_){
_start:
{
if (lean_obj_tag(v_p_2099_) == 0)
{
lean_object* v_k_2102_; lean_object* v___x_2103_; 
lean_dec(v_h__2_2101_);
v_k_2102_ = lean_ctor_get(v_p_2099_, 0);
lean_inc(v_k_2102_);
lean_dec_ref_known(v_p_2099_, 1);
v___x_2103_ = lean_apply_1(v_h__1_2100_, v_k_2102_);
return v___x_2103_;
}
else
{
lean_object* v_k_2104_; lean_object* v_v_2105_; lean_object* v_p_2106_; lean_object* v___x_2107_; 
lean_dec(v_h__1_2100_);
v_k_2104_ = lean_ctor_get(v_p_2099_, 0);
lean_inc(v_k_2104_);
v_v_2105_ = lean_ctor_get(v_p_2099_, 1);
lean_inc(v_v_2105_);
v_p_2106_ = lean_ctor_get(v_p_2099_, 2);
lean_inc_ref(v_p_2106_);
lean_dec_ref_known(v_p_2099_, 3);
v___x_2107_ = lean_apply_3(v_h__2_2101_, v_k_2104_, v_v_2105_, v_p_2106_);
return v___x_2107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object* v_motive_2108_, lean_object* v_p_2109_, lean_object* v_h__1_2110_, lean_object* v_h__2_2111_){
_start:
{
if (lean_obj_tag(v_p_2109_) == 0)
{
lean_object* v_k_2112_; lean_object* v___x_2113_; 
lean_dec(v_h__2_2111_);
v_k_2112_ = lean_ctor_get(v_p_2109_, 0);
lean_inc(v_k_2112_);
lean_dec_ref_known(v_p_2109_, 1);
v___x_2113_ = lean_apply_1(v_h__1_2110_, v_k_2112_);
return v___x_2113_;
}
else
{
lean_object* v_k_2114_; lean_object* v_v_2115_; lean_object* v_p_2116_; lean_object* v___x_2117_; 
lean_dec(v_h__1_2110_);
v_k_2114_ = lean_ctor_get(v_p_2109_, 0);
lean_inc(v_k_2114_);
v_v_2115_ = lean_ctor_get(v_p_2109_, 1);
lean_inc(v_v_2115_);
v_p_2116_ = lean_ctor_get(v_p_2109_, 2);
lean_inc_ref(v_p_2116_);
lean_dec_ref_known(v_p_2109_, 3);
v___x_2117_ = lean_apply_3(v_h__2_2111_, v_k_2114_, v_v_2115_, v_p_2116_);
return v___x_2117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert_go(lean_object* v_k_2118_, lean_object* v_m_2119_, lean_object* v_a_2120_){
_start:
{
if (lean_obj_tag(v_a_2120_) == 0)
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2121_, 0, v_k_2118_);
lean_ctor_set(v___x_2121_, 1, v_m_2119_);
lean_ctor_set(v___x_2121_, 2, v_a_2120_);
return v___x_2121_;
}
else
{
lean_object* v_k_2122_; lean_object* v_v_2123_; lean_object* v_p_2124_; uint8_t v___x_2125_; 
v_k_2122_ = lean_ctor_get(v_a_2120_, 0);
v_v_2123_ = lean_ctor_get(v_a_2120_, 1);
v_p_2124_ = lean_ctor_get(v_a_2120_, 2);
v___x_2125_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2119_, v_v_2123_);
switch(v___x_2125_)
{
case 0:
{
lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2133_; 
lean_inc_ref(v_p_2124_);
lean_inc(v_v_2123_);
lean_inc(v_k_2122_);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_a_2120_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; lean_object* v_unused_2135_; lean_object* v_unused_2136_; 
v_unused_2134_ = lean_ctor_get(v_a_2120_, 2);
lean_dec(v_unused_2134_);
v_unused_2135_ = lean_ctor_get(v_a_2120_, 1);
lean_dec(v_unused_2135_);
v_unused_2136_ = lean_ctor_get(v_a_2120_, 0);
lean_dec(v_unused_2136_);
v___x_2127_ = v_a_2120_;
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
else
{
lean_dec(v_a_2120_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2118_, v_m_2119_, v_p_2124_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 2, v___x_2129_);
v___x_2131_ = v___x_2127_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_k_2122_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_v_2123_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
case 1:
{
lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2146_; 
lean_inc_ref(v_p_2124_);
lean_inc(v_k_2122_);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_a_2120_);
if (v_isSharedCheck_2146_ == 0)
{
lean_object* v_unused_2147_; lean_object* v_unused_2148_; lean_object* v_unused_2149_; 
v_unused_2147_ = lean_ctor_get(v_a_2120_, 2);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v_a_2120_, 1);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_a_2120_, 0);
lean_dec(v_unused_2149_);
v___x_2138_ = v_a_2120_;
v_isShared_2139_ = v_isSharedCheck_2146_;
goto v_resetjp_2137_;
}
else
{
lean_dec(v_a_2120_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2146_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_k_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_k_2140_ = lean_int_add(v_k_2118_, v_k_2122_);
lean_dec(v_k_2122_);
lean_dec(v_k_2118_);
v___x_2141_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2142_ = lean_int_dec_eq(v_k_2140_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2144_; 
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 1, v_m_2119_);
lean_ctor_set(v___x_2138_, 0, v_k_2140_);
v___x_2144_ = v___x_2138_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_k_2140_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_m_2119_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_p_2124_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
else
{
lean_dec(v_k_2140_);
lean_del_object(v___x_2138_);
lean_dec(v_m_2119_);
return v_p_2124_;
}
}
}
default: 
{
lean_object* v___x_2150_; 
v___x_2150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2150_, 0, v_k_2118_);
lean_ctor_set(v___x_2150_, 1, v_m_2119_);
lean_ctor_set(v___x_2150_, 2, v_a_2120_);
return v___x_2150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert(lean_object* v_k_2151_, lean_object* v_m_2152_, lean_object* v_p_2153_){
_start:
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2155_ = lean_int_dec_eq(v_k_2151_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2156_ = lean_box(0);
v___x_2157_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2152_, v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2151_, v_m_2152_, v_p_2153_);
return v___x_2158_;
}
else
{
lean_object* v___x_2159_; 
lean_dec(v_m_2152_);
v___x_2159_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2153_, v_k_2151_);
lean_dec(v_k_2151_);
return v___x_2159_;
}
}
else
{
lean_dec(v_m_2152_);
lean_dec(v_k_2151_);
return v_p_2153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_concat(lean_object* v_p_u2081_2160_, lean_object* v_p_u2082_2161_){
_start:
{
if (lean_obj_tag(v_p_u2081_2160_) == 0)
{
lean_object* v_k_2162_; lean_object* v___x_2163_; 
v_k_2162_ = lean_ctor_get(v_p_u2081_2160_, 0);
lean_inc(v_k_2162_);
lean_dec_ref_known(v_p_u2081_2160_, 1);
v___x_2163_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2161_, v_k_2162_);
lean_dec(v_k_2162_);
return v___x_2163_;
}
else
{
lean_object* v_k_2164_; lean_object* v_v_2165_; lean_object* v_p_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2174_; 
v_k_2164_ = lean_ctor_get(v_p_u2081_2160_, 0);
v_v_2165_ = lean_ctor_get(v_p_u2081_2160_, 1);
v_p_2166_ = lean_ctor_get(v_p_u2081_2160_, 2);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_p_u2081_2160_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2168_ = v_p_u2081_2160_;
v_isShared_2169_ = v_isSharedCheck_2174_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_p_2166_);
lean_inc(v_v_2165_);
lean_inc(v_k_2164_);
lean_dec(v_p_u2081_2160_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2174_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2170_ = l_Lean_Grind_CommRing_Poly_concat(v_p_2166_, v_p_u2082_2161_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 2, v___x_2170_);
v___x_2172_ = v___x_2168_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_k_2164_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_v_2165_);
lean_ctor_set(v_reuseFailAlloc_2173_, 2, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go(lean_object* v_k_2175_, lean_object* v_a_2176_){
_start:
{
if (lean_obj_tag(v_a_2176_) == 0)
{
lean_object* v_k_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2185_; 
v_k_2177_ = lean_ctor_get(v_a_2176_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_a_2176_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2179_ = v_a_2176_;
v_isShared_2180_ = v_isSharedCheck_2185_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_k_2177_);
lean_dec(v_a_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2185_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2181_ = lean_int_mul(v_k_2175_, v_k_2177_);
lean_dec(v_k_2177_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2181_);
v___x_2183_ = v___x_2179_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
else
{
lean_object* v_k_2186_; lean_object* v_v_2187_; lean_object* v_p_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2197_; 
v_k_2186_ = lean_ctor_get(v_a_2176_, 0);
v_v_2187_ = lean_ctor_get(v_a_2176_, 1);
v_p_2188_ = lean_ctor_get(v_a_2176_, 2);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_a_2176_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2190_ = v_a_2176_;
v_isShared_2191_ = v_isSharedCheck_2197_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_p_2188_);
lean_inc(v_v_2187_);
lean_inc(v_k_2186_);
lean_dec(v_a_2176_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2197_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2192_ = lean_int_mul(v_k_2175_, v_k_2186_);
lean_dec(v_k_2186_);
v___x_2193_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2175_, v_p_2188_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 2, v___x_2193_);
lean_ctor_set(v___x_2190_, 0, v___x_2192_);
v___x_2195_ = v___x_2190_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_v_2187_);
lean_ctor_set(v_reuseFailAlloc_2196_, 2, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go___boxed(lean_object* v_k_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2198_, v_a_2199_);
lean_dec(v_k_2198_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object* v_k_2201_, lean_object* v_p_2202_){
_start:
{
lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2204_ = lean_int_dec_eq(v_k_2201_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2205_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2206_ = lean_int_dec_eq(v_k_2201_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2201_, v_p_2202_);
return v___x_2207_;
}
else
{
return v_p_2202_;
}
}
else
{
lean_object* v___x_2208_; 
lean_dec_ref(v_p_2202_);
v___x_2208_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst___boxed(lean_object* v_k_2209_, lean_object* v_p_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2209_, v_p_2210_);
lean_dec(v_k_2209_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go(lean_object* v_k_2212_, lean_object* v_m_2213_, lean_object* v_a_2214_){
_start:
{
if (lean_obj_tag(v_a_2214_) == 0)
{
lean_object* v_k_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; 
v_k_2215_ = lean_ctor_get(v_a_2214_, 0);
lean_inc(v_k_2215_);
lean_dec_ref_known(v_a_2214_, 1);
v___x_2216_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2217_ = lean_int_dec_eq(v_k_2215_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = lean_int_mul(v_k_2212_, v_k_2215_);
lean_dec(v_k_2215_);
v___x_2219_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v_m_2213_);
lean_ctor_set(v___x_2220_, 2, v___x_2219_);
return v___x_2220_;
}
else
{
lean_object* v___x_2221_; 
lean_dec(v_k_2215_);
lean_dec(v_m_2213_);
v___x_2221_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2221_;
}
}
else
{
lean_object* v_k_2222_; lean_object* v_v_2223_; lean_object* v_p_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2234_; 
v_k_2222_ = lean_ctor_get(v_a_2214_, 0);
v_v_2223_ = lean_ctor_get(v_a_2214_, 1);
v_p_2224_ = lean_ctor_get(v_a_2214_, 2);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_a_2214_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2226_ = v_a_2214_;
v_isShared_2227_ = v_isSharedCheck_2234_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_p_2224_);
lean_inc(v_v_2223_);
lean_inc(v_k_2222_);
lean_dec(v_a_2214_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2234_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2228_ = lean_int_mul(v_k_2212_, v_k_2222_);
lean_dec(v_k_2222_);
lean_inc(v_m_2213_);
v___x_2229_ = l_Lean_Grind_CommRing_Mon_mul(v_m_2213_, v_v_2223_);
v___x_2230_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2212_, v_m_2213_, v_p_2224_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 2, v___x_2230_);
lean_ctor_set(v___x_2226_, 1, v___x_2229_);
lean_ctor_set(v___x_2226_, 0, v___x_2228_);
v___x_2232_ = v___x_2226_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2233_, 2, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go___boxed(lean_object* v_k_2235_, lean_object* v_m_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2235_, v_m_2236_, v_a_2237_);
lean_dec(v_k_2235_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object* v_k_2239_, lean_object* v_m_2240_, lean_object* v_p_2241_){
_start:
{
lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2242_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2243_ = lean_int_dec_eq(v_k_2239_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2244_ = lean_box(0);
v___x_2245_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2240_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2239_, v_m_2240_, v_p_2241_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; 
lean_dec(v_m_2240_);
v___x_2247_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2239_, v_p_2241_);
return v___x_2247_;
}
}
else
{
lean_object* v___x_2248_; 
lean_dec_ref(v_p_2241_);
lean_dec(v_m_2240_);
v___x_2248_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon___boxed(lean_object* v_k_2249_, lean_object* v_m_2250_, lean_object* v_p_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2249_, v_m_2250_, v_p_2251_);
lean_dec(v_k_2249_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go(lean_object* v_k_2253_, lean_object* v_m_2254_, lean_object* v_p_2255_, lean_object* v_acc_2256_){
_start:
{
if (lean_obj_tag(v_p_2255_) == 0)
{
lean_object* v_k_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v_k_2257_ = lean_ctor_get(v_p_2255_, 0);
lean_inc(v_k_2257_);
lean_dec_ref_known(v_p_2255_, 1);
v___x_2258_ = lean_int_mul(v_k_2253_, v_k_2257_);
lean_dec(v_k_2257_);
v___x_2259_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2258_, v_m_2254_, v_acc_2256_);
return v___x_2259_;
}
else
{
lean_object* v_k_2260_; lean_object* v_v_2261_; lean_object* v_p_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_k_2260_ = lean_ctor_get(v_p_2255_, 0);
lean_inc(v_k_2260_);
v_v_2261_ = lean_ctor_get(v_p_2255_, 1);
lean_inc(v_v_2261_);
v_p_2262_ = lean_ctor_get(v_p_2255_, 2);
lean_inc_ref(v_p_2262_);
lean_dec_ref_known(v_p_2255_, 3);
v___x_2263_ = lean_int_mul(v_k_2253_, v_k_2260_);
lean_dec(v_k_2260_);
lean_inc(v_m_2254_);
v___x_2264_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_2254_, v_v_2261_);
v___x_2265_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2263_, v___x_2264_, v_acc_2256_);
v_p_2255_ = v_p_2262_;
v_acc_2256_ = v___x_2265_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go___boxed(lean_object* v_k_2267_, lean_object* v_m_2268_, lean_object* v_p_2269_, lean_object* v_acc_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2267_, v_m_2268_, v_p_2269_, v_acc_2270_);
lean_dec(v_k_2267_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc(lean_object* v_k_2272_, lean_object* v_m_2273_, lean_object* v_p_2274_){
_start:
{
lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2276_ = lean_int_dec_eq(v_k_2272_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2277_ = lean_box(0);
v___x_2278_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2273_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2280_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2272_, v_m_2273_, v_p_2274_, v___x_2279_);
return v___x_2280_;
}
else
{
lean_object* v___x_2281_; 
lean_dec(v_m_2273_);
v___x_2281_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2272_, v_p_2274_);
return v___x_2281_;
}
}
else
{
lean_object* v___x_2282_; 
lean_dec_ref(v_p_2274_);
lean_dec(v_m_2273_);
v___x_2282_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc___boxed(lean_object* v_k_2283_, lean_object* v_m_2284_, lean_object* v_p_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2283_, v_m_2284_, v_p_2285_);
lean_dec(v_k_2283_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_go(lean_object* v_fuel_2287_, lean_object* v_p_u2081_2288_, lean_object* v_p_u2082_2289_){
_start:
{
lean_object* v_zero_2290_; uint8_t v_isZero_2291_; 
v_zero_2290_ = lean_unsigned_to_nat(0u);
v_isZero_2291_ = lean_nat_dec_eq(v_fuel_2287_, v_zero_2290_);
if (v_isZero_2291_ == 1)
{
lean_object* v___x_2292_; 
lean_dec(v_fuel_2287_);
v___x_2292_ = l_Lean_Grind_CommRing_Poly_concat(v_p_u2081_2288_, v_p_u2082_2289_);
return v___x_2292_;
}
else
{
if (lean_obj_tag(v_p_u2081_2288_) == 0)
{
lean_dec(v_fuel_2287_);
if (lean_obj_tag(v_p_u2082_2289_) == 0)
{
lean_object* v_k_2293_; lean_object* v_k_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2302_; 
v_k_2293_ = lean_ctor_get(v_p_u2081_2288_, 0);
lean_inc(v_k_2293_);
lean_dec_ref_known(v_p_u2081_2288_, 1);
v_k_2294_ = lean_ctor_get(v_p_u2082_2289_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_p_u2082_2289_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2296_ = v_p_u2082_2289_;
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_k_2294_);
lean_dec(v_p_u2082_2289_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = lean_int_add(v_k_2293_, v_k_2294_);
lean_dec(v_k_2294_);
lean_dec(v_k_2293_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2298_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
else
{
lean_object* v_k_2303_; lean_object* v___x_2304_; 
v_k_2303_ = lean_ctor_get(v_p_u2081_2288_, 0);
lean_inc(v_k_2303_);
lean_dec_ref_known(v_p_u2081_2288_, 1);
v___x_2304_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2289_, v_k_2303_);
lean_dec(v_k_2303_);
return v___x_2304_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_2289_) == 0)
{
lean_object* v_k_2305_; lean_object* v___x_2306_; 
lean_dec(v_fuel_2287_);
v_k_2305_ = lean_ctor_get(v_p_u2082_2289_, 0);
lean_inc(v_k_2305_);
lean_dec_ref_known(v_p_u2082_2289_, 1);
v___x_2306_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2081_2288_, v_k_2305_);
lean_dec(v_k_2305_);
return v___x_2306_;
}
else
{
lean_object* v_k_2307_; lean_object* v_v_2308_; lean_object* v_p_2309_; lean_object* v_k_2310_; lean_object* v_v_2311_; lean_object* v_p_2312_; lean_object* v_one_2313_; lean_object* v_n_2314_; uint8_t v___x_2315_; 
v_k_2307_ = lean_ctor_get(v_p_u2081_2288_, 0);
v_v_2308_ = lean_ctor_get(v_p_u2081_2288_, 1);
v_p_2309_ = lean_ctor_get(v_p_u2081_2288_, 2);
v_k_2310_ = lean_ctor_get(v_p_u2082_2289_, 0);
v_v_2311_ = lean_ctor_get(v_p_u2082_2289_, 1);
v_p_2312_ = lean_ctor_get(v_p_u2082_2289_, 2);
v_one_2313_ = lean_unsigned_to_nat(1u);
v_n_2314_ = lean_nat_sub(v_fuel_2287_, v_one_2313_);
lean_dec(v_fuel_2287_);
v___x_2315_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2308_, v_v_2311_);
switch(v___x_2315_)
{
case 0:
{
lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2323_; 
lean_inc_ref(v_p_2312_);
lean_inc(v_v_2311_);
lean_inc(v_k_2310_);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_p_u2082_2289_);
if (v_isSharedCheck_2323_ == 0)
{
lean_object* v_unused_2324_; lean_object* v_unused_2325_; lean_object* v_unused_2326_; 
v_unused_2324_ = lean_ctor_get(v_p_u2082_2289_, 2);
lean_dec(v_unused_2324_);
v_unused_2325_ = lean_ctor_get(v_p_u2082_2289_, 1);
lean_dec(v_unused_2325_);
v_unused_2326_ = lean_ctor_get(v_p_u2082_2289_, 0);
lean_dec(v_unused_2326_);
v___x_2317_ = v_p_u2082_2289_;
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
else
{
lean_dec(v_p_u2082_2289_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2319_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2314_, v_p_u2081_2288_, v_p_2312_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 2, v___x_2319_);
v___x_2321_ = v___x_2317_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_k_2310_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_v_2311_);
lean_ctor_set(v_reuseFailAlloc_2322_, 2, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
case 1:
{
lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2338_; 
lean_inc_ref(v_p_2312_);
lean_inc(v_k_2310_);
lean_inc_ref(v_p_2309_);
lean_inc(v_v_2308_);
lean_inc(v_k_2307_);
lean_dec_ref_known(v_p_u2081_2288_, 3);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_p_u2082_2289_);
if (v_isSharedCheck_2338_ == 0)
{
lean_object* v_unused_2339_; lean_object* v_unused_2340_; lean_object* v_unused_2341_; 
v_unused_2339_ = lean_ctor_get(v_p_u2082_2289_, 2);
lean_dec(v_unused_2339_);
v_unused_2340_ = lean_ctor_get(v_p_u2082_2289_, 1);
lean_dec(v_unused_2340_);
v_unused_2341_ = lean_ctor_get(v_p_u2082_2289_, 0);
lean_dec(v_unused_2341_);
v___x_2328_ = v_p_u2082_2289_;
v_isShared_2329_ = v_isSharedCheck_2338_;
goto v_resetjp_2327_;
}
else
{
lean_dec(v_p_u2082_2289_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2338_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_k_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v_k_2330_ = lean_int_add(v_k_2307_, v_k_2310_);
lean_dec(v_k_2310_);
lean_dec(v_k_2307_);
v___x_2331_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2332_ = lean_int_dec_eq(v_k_2330_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2314_, v_p_2309_, v_p_2312_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 2, v___x_2333_);
lean_ctor_set(v___x_2328_, 1, v_v_2308_);
lean_ctor_set(v___x_2328_, 0, v_k_2330_);
v___x_2335_ = v___x_2328_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_k_2330_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
else
{
lean_dec(v_k_2330_);
lean_del_object(v___x_2328_);
lean_dec(v_v_2308_);
v_fuel_2287_ = v_n_2314_;
v_p_u2081_2288_ = v_p_2309_;
v_p_u2082_2289_ = v_p_2312_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2349_; 
lean_inc_ref(v_p_2309_);
lean_inc(v_v_2308_);
lean_inc(v_k_2307_);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_p_u2081_2288_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; lean_object* v_unused_2351_; lean_object* v_unused_2352_; 
v_unused_2350_ = lean_ctor_get(v_p_u2081_2288_, 2);
lean_dec(v_unused_2350_);
v_unused_2351_ = lean_ctor_get(v_p_u2081_2288_, 1);
lean_dec(v_unused_2351_);
v_unused_2352_ = lean_ctor_get(v_p_u2081_2288_, 0);
lean_dec(v_unused_2352_);
v___x_2343_ = v_p_u2081_2288_;
v_isShared_2344_ = v_isSharedCheck_2349_;
goto v_resetjp_2342_;
}
else
{
lean_dec(v_p_u2081_2288_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2349_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2345_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2314_, v_p_2309_, v_p_u2082_2289_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 2, v___x_2345_);
v___x_2347_ = v___x_2343_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2348_, 2, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object* v_p_u2081_2353_, lean_object* v_p_u2082_2354_){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_unsigned_to_nat(1000000u);
v___x_2356_ = l_Lean_Grind_CommRing_Poly_combine_go(v___x_2355_, v_p_u2081_2353_, v_p_u2082_2354_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object* v_p_u2081_2357_, lean_object* v_p_u2082_2358_, lean_object* v_h__1_2359_, lean_object* v_h__2_2360_, lean_object* v_h__3_2361_, lean_object* v_h__4_2362_){
_start:
{
if (lean_obj_tag(v_p_u2081_2357_) == 0)
{
lean_dec(v_h__4_2362_);
lean_dec(v_h__3_2361_);
if (lean_obj_tag(v_p_u2082_2358_) == 0)
{
lean_object* v_k_2363_; lean_object* v_k_2364_; lean_object* v___x_2365_; 
lean_dec(v_h__2_2360_);
v_k_2363_ = lean_ctor_get(v_p_u2081_2357_, 0);
lean_inc(v_k_2363_);
lean_dec_ref_known(v_p_u2081_2357_, 1);
v_k_2364_ = lean_ctor_get(v_p_u2082_2358_, 0);
lean_inc(v_k_2364_);
lean_dec_ref_known(v_p_u2082_2358_, 1);
v___x_2365_ = lean_apply_2(v_h__1_2359_, v_k_2363_, v_k_2364_);
return v___x_2365_;
}
else
{
lean_object* v_k_2366_; lean_object* v_k_2367_; lean_object* v_v_2368_; lean_object* v_p_2369_; lean_object* v___x_2370_; 
lean_dec(v_h__1_2359_);
v_k_2366_ = lean_ctor_get(v_p_u2081_2357_, 0);
lean_inc(v_k_2366_);
lean_dec_ref_known(v_p_u2081_2357_, 1);
v_k_2367_ = lean_ctor_get(v_p_u2082_2358_, 0);
lean_inc(v_k_2367_);
v_v_2368_ = lean_ctor_get(v_p_u2082_2358_, 1);
lean_inc(v_v_2368_);
v_p_2369_ = lean_ctor_get(v_p_u2082_2358_, 2);
lean_inc_ref(v_p_2369_);
lean_dec_ref_known(v_p_u2082_2358_, 3);
v___x_2370_ = lean_apply_4(v_h__2_2360_, v_k_2366_, v_k_2367_, v_v_2368_, v_p_2369_);
return v___x_2370_;
}
}
else
{
lean_dec(v_h__2_2360_);
lean_dec(v_h__1_2359_);
if (lean_obj_tag(v_p_u2082_2358_) == 0)
{
lean_object* v_k_2371_; lean_object* v_v_2372_; lean_object* v_p_2373_; lean_object* v_k_2374_; lean_object* v___x_2375_; 
lean_dec(v_h__4_2362_);
v_k_2371_ = lean_ctor_get(v_p_u2081_2357_, 0);
lean_inc(v_k_2371_);
v_v_2372_ = lean_ctor_get(v_p_u2081_2357_, 1);
lean_inc(v_v_2372_);
v_p_2373_ = lean_ctor_get(v_p_u2081_2357_, 2);
lean_inc_ref(v_p_2373_);
lean_dec_ref_known(v_p_u2081_2357_, 3);
v_k_2374_ = lean_ctor_get(v_p_u2082_2358_, 0);
lean_inc(v_k_2374_);
lean_dec_ref_known(v_p_u2082_2358_, 1);
v___x_2375_ = lean_apply_4(v_h__3_2361_, v_k_2371_, v_v_2372_, v_p_2373_, v_k_2374_);
return v___x_2375_;
}
else
{
lean_object* v_k_2376_; lean_object* v_v_2377_; lean_object* v_p_2378_; lean_object* v_k_2379_; lean_object* v_v_2380_; lean_object* v_p_2381_; lean_object* v___x_2382_; 
lean_dec(v_h__3_2361_);
v_k_2376_ = lean_ctor_get(v_p_u2081_2357_, 0);
lean_inc(v_k_2376_);
v_v_2377_ = lean_ctor_get(v_p_u2081_2357_, 1);
lean_inc(v_v_2377_);
v_p_2378_ = lean_ctor_get(v_p_u2081_2357_, 2);
lean_inc_ref(v_p_2378_);
lean_dec_ref_known(v_p_u2081_2357_, 3);
v_k_2379_ = lean_ctor_get(v_p_u2082_2358_, 0);
lean_inc(v_k_2379_);
v_v_2380_ = lean_ctor_get(v_p_u2082_2358_, 1);
lean_inc(v_v_2380_);
v_p_2381_ = lean_ctor_get(v_p_u2082_2358_, 2);
lean_inc_ref(v_p_2381_);
lean_dec_ref_known(v_p_u2082_2358_, 3);
v___x_2382_ = lean_apply_6(v_h__4_2362_, v_k_2376_, v_v_2377_, v_p_2378_, v_k_2379_, v_v_2380_, v_p_2381_);
return v___x_2382_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object* v_motive_2383_, lean_object* v_p_u2081_2384_, lean_object* v_p_u2082_2385_, lean_object* v_h__1_2386_, lean_object* v_h__2_2387_, lean_object* v_h__3_2388_, lean_object* v_h__4_2389_){
_start:
{
if (lean_obj_tag(v_p_u2081_2384_) == 0)
{
lean_dec(v_h__4_2389_);
lean_dec(v_h__3_2388_);
if (lean_obj_tag(v_p_u2082_2385_) == 0)
{
lean_object* v_k_2390_; lean_object* v_k_2391_; lean_object* v___x_2392_; 
lean_dec(v_h__2_2387_);
v_k_2390_ = lean_ctor_get(v_p_u2081_2384_, 0);
lean_inc(v_k_2390_);
lean_dec_ref_known(v_p_u2081_2384_, 1);
v_k_2391_ = lean_ctor_get(v_p_u2082_2385_, 0);
lean_inc(v_k_2391_);
lean_dec_ref_known(v_p_u2082_2385_, 1);
v___x_2392_ = lean_apply_2(v_h__1_2386_, v_k_2390_, v_k_2391_);
return v___x_2392_;
}
else
{
lean_object* v_k_2393_; lean_object* v_k_2394_; lean_object* v_v_2395_; lean_object* v_p_2396_; lean_object* v___x_2397_; 
lean_dec(v_h__1_2386_);
v_k_2393_ = lean_ctor_get(v_p_u2081_2384_, 0);
lean_inc(v_k_2393_);
lean_dec_ref_known(v_p_u2081_2384_, 1);
v_k_2394_ = lean_ctor_get(v_p_u2082_2385_, 0);
lean_inc(v_k_2394_);
v_v_2395_ = lean_ctor_get(v_p_u2082_2385_, 1);
lean_inc(v_v_2395_);
v_p_2396_ = lean_ctor_get(v_p_u2082_2385_, 2);
lean_inc_ref(v_p_2396_);
lean_dec_ref_known(v_p_u2082_2385_, 3);
v___x_2397_ = lean_apply_4(v_h__2_2387_, v_k_2393_, v_k_2394_, v_v_2395_, v_p_2396_);
return v___x_2397_;
}
}
else
{
lean_dec(v_h__2_2387_);
lean_dec(v_h__1_2386_);
if (lean_obj_tag(v_p_u2082_2385_) == 0)
{
lean_object* v_k_2398_; lean_object* v_v_2399_; lean_object* v_p_2400_; lean_object* v_k_2401_; lean_object* v___x_2402_; 
lean_dec(v_h__4_2389_);
v_k_2398_ = lean_ctor_get(v_p_u2081_2384_, 0);
lean_inc(v_k_2398_);
v_v_2399_ = lean_ctor_get(v_p_u2081_2384_, 1);
lean_inc(v_v_2399_);
v_p_2400_ = lean_ctor_get(v_p_u2081_2384_, 2);
lean_inc_ref(v_p_2400_);
lean_dec_ref_known(v_p_u2081_2384_, 3);
v_k_2401_ = lean_ctor_get(v_p_u2082_2385_, 0);
lean_inc(v_k_2401_);
lean_dec_ref_known(v_p_u2082_2385_, 1);
v___x_2402_ = lean_apply_4(v_h__3_2388_, v_k_2398_, v_v_2399_, v_p_2400_, v_k_2401_);
return v___x_2402_;
}
else
{
lean_object* v_k_2403_; lean_object* v_v_2404_; lean_object* v_p_2405_; lean_object* v_k_2406_; lean_object* v_v_2407_; lean_object* v_p_2408_; lean_object* v___x_2409_; 
lean_dec(v_h__3_2388_);
v_k_2403_ = lean_ctor_get(v_p_u2081_2384_, 0);
lean_inc(v_k_2403_);
v_v_2404_ = lean_ctor_get(v_p_u2081_2384_, 1);
lean_inc(v_v_2404_);
v_p_2405_ = lean_ctor_get(v_p_u2081_2384_, 2);
lean_inc_ref(v_p_2405_);
lean_dec_ref_known(v_p_u2081_2384_, 3);
v_k_2406_ = lean_ctor_get(v_p_u2082_2385_, 0);
lean_inc(v_k_2406_);
v_v_2407_ = lean_ctor_get(v_p_u2082_2385_, 1);
lean_inc(v_v_2407_);
v_p_2408_ = lean_ctor_get(v_p_u2082_2385_, 2);
lean_inc_ref(v_p_2408_);
lean_dec_ref_known(v_p_u2082_2385_, 3);
v___x_2409_ = lean_apply_6(v_h__4_2389_, v_k_2403_, v_v_2404_, v_p_2405_, v_k_2406_, v_v_2407_, v_p_2408_);
return v___x_2409_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t v_x_2410_, lean_object* v_h__1_2411_, lean_object* v_h__2_2412_, lean_object* v_h__3_2413_){
_start:
{
switch(v_x_2410_)
{
case 0:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
lean_dec(v_h__2_2412_);
lean_dec(v_h__1_2411_);
v___x_2414_ = lean_box(0);
v___x_2415_ = lean_apply_1(v_h__3_2413_, v___x_2414_);
return v___x_2415_;
}
case 1:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
lean_dec(v_h__3_2413_);
lean_dec(v_h__2_2412_);
v___x_2416_ = lean_box(0);
v___x_2417_ = lean_apply_1(v_h__1_2411_, v___x_2416_);
return v___x_2417_;
}
default: 
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_dec(v_h__3_2413_);
lean_dec(v_h__1_2411_);
v___x_2418_ = lean_box(0);
v___x_2419_ = lean_apply_1(v_h__2_2412_, v___x_2418_);
return v___x_2419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object* v_x_2420_, lean_object* v_h__1_2421_, lean_object* v_h__2_2422_, lean_object* v_h__3_2423_){
_start:
{
uint8_t v_x_33__boxed_2424_; lean_object* v_res_2425_; 
v_x_33__boxed_2424_ = lean_unbox(v_x_2420_);
v_res_2425_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(v_x_33__boxed_2424_, v_h__1_2421_, v_h__2_2422_, v_h__3_2423_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object* v_motive_2426_, uint8_t v_x_2427_, lean_object* v_h__1_2428_, lean_object* v_h__2_2429_, lean_object* v_h__3_2430_){
_start:
{
switch(v_x_2427_)
{
case 0:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
lean_dec(v_h__2_2429_);
lean_dec(v_h__1_2428_);
v___x_2431_ = lean_box(0);
v___x_2432_ = lean_apply_1(v_h__3_2430_, v___x_2431_);
return v___x_2432_;
}
case 1:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_dec(v_h__3_2430_);
lean_dec(v_h__2_2429_);
v___x_2433_ = lean_box(0);
v___x_2434_ = lean_apply_1(v_h__1_2428_, v___x_2433_);
return v___x_2434_;
}
default: 
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec(v_h__3_2430_);
lean_dec(v_h__1_2428_);
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_apply_1(v_h__2_2429_, v___x_2435_);
return v___x_2436_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object* v_motive_2437_, lean_object* v_x_2438_, lean_object* v_h__1_2439_, lean_object* v_h__2_2440_, lean_object* v_h__3_2441_){
_start:
{
uint8_t v_x_48__boxed_2442_; lean_object* v_res_2443_; 
v_x_48__boxed_2442_ = lean_unbox(v_x_2438_);
v_res_2443_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(v_motive_2437_, v_x_48__boxed_2442_, v_h__1_2439_, v_h__2_2440_, v_h__3_2441_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul_go(lean_object* v_p_u2082_2444_, lean_object* v_p_u2081_2445_, lean_object* v_acc_2446_){
_start:
{
if (lean_obj_tag(v_p_u2081_2445_) == 0)
{
lean_object* v_k_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v_k_2447_ = lean_ctor_get(v_p_u2081_2445_, 0);
lean_inc(v_k_2447_);
lean_dec_ref_known(v_p_u2081_2445_, 1);
v___x_2448_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2447_, v_p_u2082_2444_);
lean_dec(v_k_2447_);
v___x_2449_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2446_, v___x_2448_);
return v___x_2449_;
}
else
{
lean_object* v_k_2450_; lean_object* v_v_2451_; lean_object* v_p_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_k_2450_ = lean_ctor_get(v_p_u2081_2445_, 0);
lean_inc(v_k_2450_);
v_v_2451_ = lean_ctor_get(v_p_u2081_2445_, 1);
lean_inc(v_v_2451_);
v_p_2452_ = lean_ctor_get(v_p_u2081_2445_, 2);
lean_inc_ref(v_p_2452_);
lean_dec_ref_known(v_p_u2081_2445_, 3);
lean_inc_ref(v_p_u2082_2444_);
v___x_2453_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2450_, v_v_2451_, v_p_u2082_2444_);
lean_dec(v_k_2450_);
v___x_2454_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2446_, v___x_2453_);
v_p_u2081_2445_ = v_p_2452_;
v_acc_2446_ = v___x_2454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul(lean_object* v_p_u2081_2456_, lean_object* v_p_u2082_2457_){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2459_ = l_Lean_Grind_CommRing_Poly_mul_go(v_p_u2082_2457_, v_p_u2081_2456_, v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc_go(lean_object* v_p_u2082_2460_, lean_object* v_p_u2081_2461_, lean_object* v_acc_2462_){
_start:
{
if (lean_obj_tag(v_p_u2081_2461_) == 0)
{
lean_object* v_k_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_k_2463_ = lean_ctor_get(v_p_u2081_2461_, 0);
lean_inc(v_k_2463_);
lean_dec_ref_known(v_p_u2081_2461_, 1);
v___x_2464_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2463_, v_p_u2082_2460_);
lean_dec(v_k_2463_);
v___x_2465_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2462_, v___x_2464_);
return v___x_2465_;
}
else
{
lean_object* v_k_2466_; lean_object* v_v_2467_; lean_object* v_p_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_k_2466_ = lean_ctor_get(v_p_u2081_2461_, 0);
lean_inc(v_k_2466_);
v_v_2467_ = lean_ctor_get(v_p_u2081_2461_, 1);
lean_inc(v_v_2467_);
v_p_2468_ = lean_ctor_get(v_p_u2081_2461_, 2);
lean_inc_ref(v_p_2468_);
lean_dec_ref_known(v_p_u2081_2461_, 3);
lean_inc_ref(v_p_u2082_2460_);
v___x_2469_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2466_, v_v_2467_, v_p_u2082_2460_);
lean_dec(v_k_2466_);
v___x_2470_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2462_, v___x_2469_);
v_p_u2081_2461_ = v_p_2468_;
v_acc_2462_ = v___x_2470_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object* v_p_u2081_2472_, lean_object* v_p_u2082_2473_){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2475_ = l_Lean_Grind_CommRing_Poly_mul__nc_go(v_p_u2082_2473_, v_p_u2081_2472_, v___x_2474_);
return v___x_2475_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_pow___closed__0(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow(lean_object* v_p_2478_, lean_object* v_k_2479_){
_start:
{
lean_object* v_zero_2480_; uint8_t v_isZero_2481_; 
v_zero_2480_ = lean_unsigned_to_nat(0u);
v_isZero_2481_ = lean_nat_dec_eq(v_k_2479_, v_zero_2480_);
if (v_isZero_2481_ == 1)
{
lean_object* v___x_2482_; 
lean_dec_ref(v_p_2478_);
v___x_2482_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2482_;
}
else
{
lean_object* v_one_2483_; lean_object* v_n_2484_; uint8_t v___x_2485_; 
v_one_2483_ = lean_unsigned_to_nat(1u);
v_n_2484_ = lean_nat_sub(v_k_2479_, v_one_2483_);
v___x_2485_ = lean_nat_dec_eq(v_n_2484_, v_zero_2480_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_inc_ref(v_p_2478_);
v___x_2486_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2478_, v_n_2484_);
lean_dec(v_n_2484_);
v___x_2487_ = l_Lean_Grind_CommRing_Poly_mul(v_p_2478_, v___x_2486_);
return v___x_2487_;
}
else
{
lean_dec(v_n_2484_);
return v_p_2478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow___boxed(lean_object* v_p_2488_, lean_object* v_k_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2488_, v_k_2489_);
lean_dec(v_k_2489_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc(lean_object* v_p_2491_, lean_object* v_k_2492_){
_start:
{
lean_object* v_zero_2493_; uint8_t v_isZero_2494_; 
v_zero_2493_ = lean_unsigned_to_nat(0u);
v_isZero_2494_ = lean_nat_dec_eq(v_k_2492_, v_zero_2493_);
if (v_isZero_2494_ == 1)
{
lean_object* v___x_2495_; 
lean_dec_ref(v_p_2491_);
v___x_2495_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2495_;
}
else
{
lean_object* v_one_2496_; lean_object* v_n_2497_; uint8_t v___x_2498_; 
v_one_2496_ = lean_unsigned_to_nat(1u);
v_n_2497_ = lean_nat_sub(v_k_2492_, v_one_2496_);
v___x_2498_ = lean_nat_dec_eq(v_n_2497_, v_zero_2493_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_inc_ref(v_p_2491_);
v___x_2499_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2491_, v_n_2497_);
lean_dec(v_n_2497_);
v___x_2500_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2499_, v_p_2491_);
return v___x_2500_;
}
else
{
lean_dec(v_n_2497_);
return v_p_2491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc___boxed(lean_object* v_p_2501_, lean_object* v_k_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2501_, v_k_2502_);
lean_dec(v_k_2502_);
return v_res_2503_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2505_ = lean_int_neg(v___x_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object* v_x_2506_){
_start:
{
switch(lean_obj_tag(v_x_2506_))
{
case 0:
{
lean_object* v_k_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
v_k_2507_ = lean_ctor_get(v_x_2506_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_x_2506_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v_x_2506_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_k_2507_);
lean_dec(v_x_2506_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_k_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
case 1:
{
lean_object* v_k_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2523_; 
v_k_2515_ = lean_ctor_get(v_x_2506_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_x_2506_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2517_ = v_x_2506_;
v_isShared_2518_ = v_isSharedCheck_2523_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_k_2515_);
lean_dec(v_x_2506_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2523_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; lean_object* v___x_2521_; 
v___x_2519_ = lean_nat_to_int(v_k_2515_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set_tag(v___x_2517_, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2519_);
v___x_2521_ = v___x_2517_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
case 2:
{
lean_object* v_k_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
v_k_2524_ = lean_ctor_get(v_x_2506_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_x_2506_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v_x_2506_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_k_2524_);
lean_dec(v_x_2506_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set_tag(v___x_2526_, 0);
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_k_2524_);
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
lean_object* v_i_2532_; lean_object* v___x_2533_; 
v_i_2532_ = lean_ctor_get(v_x_2506_, 0);
lean_inc(v_i_2532_);
lean_dec_ref_known(v_x_2506_, 1);
v___x_2533_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2532_);
return v___x_2533_;
}
case 4:
{
lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v_a_2534_ = lean_ctor_get(v_x_2506_, 0);
lean_inc_ref(v_a_2534_);
lean_dec_ref_known(v_x_2506_, 1);
v___x_2535_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2536_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2534_);
v___x_2537_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2535_, v___x_2536_);
return v___x_2537_;
}
case 5:
{
lean_object* v_a_2538_; lean_object* v_b_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v_a_2538_ = lean_ctor_get(v_x_2506_, 0);
lean_inc_ref(v_a_2538_);
v_b_2539_ = lean_ctor_get(v_x_2506_, 1);
lean_inc_ref(v_b_2539_);
lean_dec_ref_known(v_x_2506_, 2);
v___x_2540_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2538_);
v___x_2541_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2539_);
v___x_2542_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2540_, v___x_2541_);
return v___x_2542_;
}
case 6:
{
lean_object* v_a_2543_; lean_object* v_b_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v_a_2543_ = lean_ctor_get(v_x_2506_, 0);
lean_inc_ref(v_a_2543_);
v_b_2544_ = lean_ctor_get(v_x_2506_, 1);
lean_inc_ref(v_b_2544_);
lean_dec_ref_known(v_x_2506_, 2);
v___x_2545_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2543_);
v___x_2546_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2547_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2544_);
v___x_2548_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2546_, v___x_2547_);
v___x_2549_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2545_, v___x_2548_);
return v___x_2549_;
}
case 7:
{
lean_object* v_a_2550_; lean_object* v_b_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_a_2550_ = lean_ctor_get(v_x_2506_, 0);
lean_inc_ref(v_a_2550_);
v_b_2551_ = lean_ctor_get(v_x_2506_, 1);
lean_inc_ref(v_b_2551_);
lean_dec_ref_known(v_x_2506_, 2);
v___x_2552_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2550_);
v___x_2553_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2551_);
v___x_2554_ = l_Lean_Grind_CommRing_Poly_mul(v___x_2552_, v___x_2553_);
return v___x_2554_;
}
default: 
{
lean_object* v_a_2555_; lean_object* v_k_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2588_; 
v_a_2555_ = lean_ctor_get(v_x_2506_, 0);
v_k_2556_ = lean_ctor_get(v_x_2506_, 1);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_x_2506_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2558_ = v_x_2506_;
v_isShared_2559_ = v_isSharedCheck_2588_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_k_2556_);
lean_inc(v_a_2555_);
lean_dec(v_x_2506_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2588_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v_n_2561_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2564_ = lean_unsigned_to_nat(0u);
v___x_2565_ = lean_nat_dec_eq(v_k_2556_, v___x_2564_);
if (v___x_2565_ == 0)
{
switch(lean_obj_tag(v_a_2555_))
{
case 0:
{
lean_object* v_k_2566_; 
lean_del_object(v___x_2558_);
v_k_2566_ = lean_ctor_get(v_a_2555_, 0);
lean_inc(v_k_2566_);
lean_dec_ref_known(v_a_2555_, 1);
v_n_2561_ = v_k_2566_;
goto v___jp_2560_;
}
case 2:
{
lean_object* v_k_2567_; 
lean_del_object(v___x_2558_);
v_k_2567_ = lean_ctor_get(v_a_2555_, 0);
lean_inc(v_k_2567_);
lean_dec_ref_known(v_a_2555_, 1);
v_n_2561_ = v_k_2567_;
goto v___jp_2560_;
}
case 1:
{
lean_object* v_k_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2577_; 
lean_del_object(v___x_2558_);
v_k_2568_ = lean_ctor_get(v_a_2555_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v_a_2555_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2570_ = v_a_2555_;
v_isShared_2571_ = v_isSharedCheck_2577_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_k_2568_);
lean_dec(v_a_2555_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2577_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2572_ = lean_nat_to_int(v_k_2568_);
v___x_2573_ = l_Int_pow(v___x_2572_, v_k_2556_);
lean_dec(v_k_2556_);
lean_dec(v___x_2572_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2573_);
v___x_2575_ = v___x_2570_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
case 3:
{
lean_object* v_i_2578_; lean_object* v___x_2580_; 
v_i_2578_ = lean_ctor_get(v_a_2555_, 0);
lean_inc(v_i_2578_);
lean_dec_ref_known(v_a_2555_, 1);
if (v_isShared_2559_ == 0)
{
lean_ctor_set_tag(v___x_2558_, 0);
lean_ctor_set(v___x_2558_, 0, v_i_2578_);
v___x_2580_ = v___x_2558_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_i_2578_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_k_2556_);
v___x_2580_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = lean_box(0);
v___x_2582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2582_);
return v___x_2583_;
}
}
default: 
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_del_object(v___x_2558_);
v___x_2585_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2555_);
v___x_2586_ = l_Lean_Grind_CommRing_Poly_pow(v___x_2585_, v_k_2556_);
lean_dec(v_k_2556_);
return v___x_2586_;
}
}
}
else
{
lean_object* v___x_2587_; 
lean_del_object(v___x_2558_);
lean_dec(v_k_2556_);
lean_dec_ref(v_a_2555_);
v___x_2587_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2587_;
}
v___jp_2560_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = l_Int_pow(v_n_2561_, v_k_2556_);
lean_dec(v_k_2556_);
lean_dec(v_n_2561_);
v___x_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
return v___x_2563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf(lean_object* v_m_2589_, lean_object* v_x_2590_){
_start:
{
if (lean_obj_tag(v_m_2589_) == 0)
{
lean_object* v___x_2591_; 
v___x_2591_ = lean_unsigned_to_nat(0u);
return v___x_2591_;
}
else
{
lean_object* v_p_2592_; lean_object* v_m_2593_; lean_object* v_x_2594_; lean_object* v_k_2595_; uint8_t v___x_2596_; 
v_p_2592_ = lean_ctor_get(v_m_2589_, 0);
v_m_2593_ = lean_ctor_get(v_m_2589_, 1);
v_x_2594_ = lean_ctor_get(v_p_2592_, 0);
v_k_2595_ = lean_ctor_get(v_p_2592_, 1);
v___x_2596_ = lean_nat_dec_eq(v_x_2594_, v_x_2590_);
if (v___x_2596_ == 0)
{
v_m_2589_ = v_m_2593_;
goto _start;
}
else
{
lean_inc(v_k_2595_);
return v_k_2595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf___boxed(lean_object* v_m_2598_, lean_object* v_x_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_2598_, v_x_2599_);
lean_dec(v_x_2599_);
lean_dec(v_m_2598_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar(lean_object* v_m_2601_, lean_object* v_x_2602_){
_start:
{
if (lean_obj_tag(v_m_2601_) == 0)
{
return v_m_2601_;
}
else
{
lean_object* v_p_2603_; lean_object* v_m_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2614_; 
v_p_2603_ = lean_ctor_get(v_m_2601_, 0);
v_m_2604_ = lean_ctor_get(v_m_2601_, 1);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_m_2601_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2606_ = v_m_2601_;
v_isShared_2607_ = v_isSharedCheck_2614_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_m_2604_);
lean_inc(v_p_2603_);
lean_dec(v_m_2601_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2614_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v_x_2608_; uint8_t v___x_2609_; 
v_x_2608_ = lean_ctor_get(v_p_2603_, 0);
v___x_2609_ = lean_nat_dec_eq(v_x_2608_, v_x_2602_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2610_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2604_, v_x_2602_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 1, v___x_2610_);
v___x_2612_ = v___x_2606_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_p_2603_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
else
{
lean_del_object(v___x_2606_);
lean_dec_ref(v_p_2603_);
return v_m_2604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar___boxed(lean_object* v_m_2615_, lean_object* v_x_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2615_, v_x_2616_);
lean_dec(v_x_2616_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27(lean_object* v_c_2618_, lean_object* v_x_2619_, lean_object* v_p_2620_, lean_object* v_acc_2621_){
_start:
{
if (lean_obj_tag(v_p_2620_) == 0)
{
lean_object* v_k_2622_; lean_object* v___x_2623_; 
v_k_2622_ = lean_ctor_get(v_p_2620_, 0);
lean_inc(v_k_2622_);
lean_dec_ref_known(v_p_2620_, 1);
v___x_2623_ = l_Lean_Grind_CommRing_Poly_addConst(v_acc_2621_, v_k_2622_);
lean_dec(v_k_2622_);
return v___x_2623_;
}
else
{
lean_object* v_k_2624_; lean_object* v_v_2625_; lean_object* v_p_2626_; lean_object* v_n_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v_k_2624_ = lean_ctor_get(v_p_2620_, 0);
lean_inc(v_k_2624_);
v_v_2625_ = lean_ctor_get(v_p_2620_, 1);
lean_inc(v_v_2625_);
v_p_2626_ = lean_ctor_get(v_p_2620_, 2);
lean_inc_ref(v_p_2626_);
lean_dec_ref_known(v_p_2620_, 3);
v_n_2630_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_2625_, v_x_2619_);
v___x_2631_ = lean_unsigned_to_nat(0u);
v___x_2632_ = lean_nat_dec_lt(v___x_2631_, v_n_2630_);
if (v___x_2632_ == 0)
{
lean_dec(v_n_2630_);
goto v___jp_2627_;
}
else
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2633_ = l_Int_pow(v_c_2618_, v_n_2630_);
lean_dec(v_n_2630_);
v___x_2634_ = lean_int_emod(v_k_2624_, v___x_2633_);
v___x_2635_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2636_ = lean_int_dec_eq(v___x_2634_, v___x_2635_);
lean_dec(v___x_2634_);
if (v___x_2636_ == 0)
{
lean_dec(v___x_2633_);
goto v___jp_2627_;
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = lean_int_ediv(v_k_2624_, v___x_2633_);
lean_dec(v___x_2633_);
lean_dec(v_k_2624_);
v___x_2638_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_v_2625_, v_x_2619_);
v___x_2639_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2637_, v___x_2638_, v_acc_2621_);
v_p_2620_ = v_p_2626_;
v_acc_2621_ = v___x_2639_;
goto _start;
}
}
v___jp_2627_:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lean_Grind_CommRing_Poly_insert(v_k_2624_, v_v_2625_, v_acc_2621_);
v_p_2620_ = v_p_2626_;
v_acc_2621_ = v___x_2628_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27___boxed(lean_object* v_c_2641_, lean_object* v_x_2642_, lean_object* v_p_2643_, lean_object* v_acc_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2641_, v_x_2642_, v_p_2643_, v_acc_2644_);
lean_dec(v_x_2642_);
lean_dec(v_c_2641_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar(lean_object* v_c_2646_, lean_object* v_x_2647_, lean_object* v_p_2648_){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2650_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2646_, v_x_2647_, v_p_2648_, v___x_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar___boxed(lean_object* v_c_2651_, lean_object* v_x_2652_, lean_object* v_p_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Lean_Grind_CommRing_Poly_cancelVar(v_c_2651_, v_x_2652_, v_p_2653_);
lean_dec(v_x_2652_);
lean_dec(v_c_2651_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(lean_object* v_p_2655_, lean_object* v_acc_2656_){
_start:
{
lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2657_ = lean_unsigned_to_nat(1u);
v___x_2658_ = lean_nat_dec_eq(v_acc_2656_, v___x_2657_);
if (v___x_2658_ == 0)
{
if (lean_obj_tag(v_p_2655_) == 0)
{
lean_object* v_k_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v_k_2659_ = lean_ctor_get(v_p_2655_, 0);
v___x_2660_ = lean_nat_abs(v_k_2659_);
v___x_2661_ = lean_nat_gcd(v_acc_2656_, v___x_2660_);
lean_dec(v___x_2660_);
lean_dec(v_acc_2656_);
return v___x_2661_;
}
else
{
lean_object* v_k_2662_; lean_object* v_p_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v_k_2662_ = lean_ctor_get(v_p_2655_, 0);
v_p_2663_ = lean_ctor_get(v_p_2655_, 2);
v___x_2664_ = lean_nat_abs(v_k_2662_);
v___x_2665_ = lean_nat_gcd(v_acc_2656_, v___x_2664_);
lean_dec(v___x_2664_);
lean_dec(v_acc_2656_);
v_p_2655_ = v_p_2663_;
v_acc_2656_ = v___x_2665_;
goto _start;
}
}
else
{
return v_acc_2656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs_go___boxed(lean_object* v_p_2667_, lean_object* v_acc_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_2667_, v_acc_2668_);
lean_dec_ref(v_p_2667_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs(lean_object* v_x_2670_){
_start:
{
if (lean_obj_tag(v_x_2670_) == 0)
{
lean_object* v_k_2671_; lean_object* v___x_2672_; 
v_k_2671_ = lean_ctor_get(v_x_2670_, 0);
v___x_2672_ = lean_nat_abs(v_k_2671_);
return v___x_2672_;
}
else
{
lean_object* v_k_2673_; lean_object* v_p_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_k_2673_ = lean_ctor_get(v_x_2670_, 0);
v_p_2674_ = lean_ctor_get(v_x_2670_, 2);
v___x_2675_ = lean_nat_abs(v_k_2673_);
v___x_2676_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_2674_, v___x_2675_);
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs___boxed(lean_object* v_x_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs(v_x_2677_);
lean_dec_ref(v_x_2677_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst(lean_object* v_p_2679_, lean_object* v_a_2680_){
_start:
{
if (lean_obj_tag(v_p_2679_) == 0)
{
lean_object* v_k_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2689_; 
v_k_2681_ = lean_ctor_get(v_p_2679_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_p_2679_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2683_ = v_p_2679_;
v_isShared_2684_ = v_isSharedCheck_2689_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_k_2681_);
lean_dec(v_p_2679_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2689_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2685_ = lean_int_ediv(v_k_2681_, v_a_2680_);
lean_dec(v_k_2681_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2685_);
v___x_2687_ = v___x_2683_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
else
{
lean_object* v_k_2690_; lean_object* v_v_2691_; lean_object* v_p_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2701_; 
v_k_2690_ = lean_ctor_get(v_p_2679_, 0);
v_v_2691_ = lean_ctor_get(v_p_2679_, 1);
v_p_2692_ = lean_ctor_get(v_p_2679_, 2);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_p_2679_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2694_ = v_p_2679_;
v_isShared_2695_ = v_isSharedCheck_2701_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_p_2692_);
lean_inc(v_v_2691_);
lean_inc(v_k_2690_);
lean_dec(v_p_2679_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2701_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2696_ = lean_int_ediv(v_k_2690_, v_a_2680_);
lean_dec(v_k_2690_);
v___x_2697_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_2692_, v_a_2680_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 2, v___x_2697_);
lean_ctor_set(v___x_2694_, 0, v___x_2696_);
v___x_2699_ = v___x_2694_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_v_2691_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst___boxed(lean_object* v_p_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_2702_, v_a_2703_);
lean_dec(v_a_2703_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(lean_object* v_x_2705_, lean_object* v_p_2706_, lean_object* v_max_2707_){
_start:
{
if (lean_obj_tag(v_p_2706_) == 0)
{
return v_max_2707_;
}
else
{
lean_object* v_v_2708_; lean_object* v_p_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; 
v_v_2708_ = lean_ctor_get(v_p_2706_, 1);
v_p_2709_ = lean_ctor_get(v_p_2706_, 2);
v___x_2710_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_2708_, v_x_2705_);
v___x_2711_ = lean_nat_dec_le(v_max_2707_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_dec(v___x_2710_);
v_p_2706_ = v_p_2709_;
goto _start;
}
else
{
lean_dec(v_max_2707_);
v_p_2706_ = v_p_2709_;
v_max_2707_ = v___x_2710_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf_go___boxed(lean_object* v_x_2714_, lean_object* v_p_2715_, lean_object* v_max_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_2714_, v_p_2715_, v_max_2716_);
lean_dec_ref(v_p_2715_);
lean_dec(v_x_2714_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf(lean_object* v_p_2718_, lean_object* v_x_2719_){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = lean_unsigned_to_nat(0u);
v___x_2721_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_2719_, v_p_2718_, v___x_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf___boxed(lean_object* v_p_2722_, lean_object* v_x_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_2722_, v_x_2723_);
lean_dec(v_x_2723_);
lean_dec_ref(v_p_2722_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(lean_object* v_x_2725_, lean_object* v_h__1_2726_, lean_object* v_h__2_2727_, lean_object* v_h__3_2728_, lean_object* v_h__4_2729_, lean_object* v_h__5_2730_, lean_object* v_h__6_2731_, lean_object* v_h__7_2732_, lean_object* v_h__8_2733_, lean_object* v_h__9_2734_){
_start:
{
switch(lean_obj_tag(v_x_2725_))
{
case 0:
{
lean_object* v_k_2735_; lean_object* v___x_2736_; 
lean_dec(v_h__9_2734_);
lean_dec(v_h__8_2733_);
lean_dec(v_h__7_2732_);
lean_dec(v_h__6_2731_);
lean_dec(v_h__5_2730_);
lean_dec(v_h__4_2729_);
lean_dec(v_h__3_2728_);
lean_dec(v_h__2_2727_);
v_k_2735_ = lean_ctor_get(v_x_2725_, 0);
lean_inc(v_k_2735_);
lean_dec_ref_known(v_x_2725_, 1);
v___x_2736_ = lean_apply_1(v_h__1_2726_, v_k_2735_);
return v___x_2736_;
}
case 1:
{
lean_object* v_k_2737_; lean_object* v___x_2738_; 
lean_dec(v_h__9_2734_);
lean_dec(v_h__8_2733_);
lean_dec(v_h__7_2732_);
lean_dec(v_h__6_2731_);
lean_dec(v_h__5_2730_);
lean_dec(v_h__4_2729_);
lean_dec(v_h__2_2727_);
lean_dec(v_h__1_2726_);
v_k_2737_ = lean_ctor_get(v_x_2725_, 0);
lean_inc(v_k_2737_);
lean_dec_ref_known(v_x_2725_, 1);
v___x_2738_ = lean_apply_1(v_h__3_2728_, v_k_2737_);
return v___x_2738_;
}
case 2:
{
lean_object* v_k_2739_; lean_object* v___x_2740_; 
lean_dec(v_h__9_2734_);
lean_dec(v_h__8_2733_);
lean_dec(v_h__7_2732_);
lean_dec(v_h__6_2731_);
lean_dec(v_h__5_2730_);
lean_dec(v_h__4_2729_);
lean_dec(v_h__3_2728_);
lean_dec(v_h__1_2726_);
v_k_2739_ = lean_ctor_get(v_x_2725_, 0);
lean_inc(v_k_2739_);
lean_dec_ref_known(v_x_2725_, 1);
v___x_2740_ = lean_apply_1(v_h__2_2727_, v_k_2739_);
return v___x_2740_;
}
case 3:
{
lean_object* v_i_2741_; lean_object* v___x_2742_; 
lean_dec(v_h__9_2734_);
lean_dec(v_h__8_2733_);
lean_dec(v_h__7_2732_);
lean_dec(v_h__6_2731_);
lean_dec(v_h__5_2730_);
lean_dec(v_h__3_2728_);
lean_dec(v_h__2_2727_);
lean_dec(v_h__1_2726_);
v_i_2741_ = lean_ctor_get(v_x_2725_, 0);
lean_inc(v_i_2741_);
lean_dec_ref_known(v_x_2725_, 1);
v___x_2742_ = lean_apply_1(v_h__4_2729_, v_i_2741_);
return v___x_2742_;
}
case 4:
{
lean_object* v_a_2743_; lean_object* v___x_2744_; 
lean_dec(v_h__9_2734_);
lean_dec(v_h__8_2733_);
lean_dec(v_h__6_2731_);
lean_dec(v_h__5_2730_);
lean_dec(v_h__4_2729_);
lean_dec(v_h__3_2728_);
lean_dec(v_h__2_2727_);
lean_dec(v_h__1_2726_);
v_a_2743_ = lean_ctor_get(v_x_2725_, 0);
lean_inc_ref(v_a_2743_);
lean_dec_ref_known(v_x_2725_, 1);
v___x_2744_ = lean_apply_1(v_h__7_2732_, v_a_2743_);
return v___x_2744_;
}
case 5:
{
lean_object* v_a_2745_; lean_object* v_b_2746_; lean_object* v___x_2747_; 
lean_dec(v_h__9_2734_);
lean_dec(v_h__8_2733_);
lean_dec(v_h__7_2732_);
lean_dec(v_h__6_2731_);
lean_dec(v_h__4_2729_);
lean_dec(v_h__3_2728_);
lean_dec(v_h__2_2727_);
lean_dec(v_h__1_2726_);
v_a_2745_ = lean_ctor_get(v_x_2725_, 0);
lean_inc_ref(v_a_2745_);
v_b_2746_ = lean_ctor_get(v_x_2725_, 1);
lean_inc_ref(v_b_2746_);
lean_dec_ref_known(v_x_2725_, 2);
v___x_2747_ = lean_apply_2(v_h__5_2730_, v_a_2745_, v_b_2746_);
return v___x_2747_;
}
case 6:
{
lean_object* v_a_2748_; lean_object* v_b_2749_; lean_object* v___x_2750_; 
lean_dec(v_h__9_2734_);
lean_dec(v_h__7_2732_);
lean_dec(v_h__6_2731_);
lean_dec(v_h__5_2730_);
lean_dec(v_h__4_2729_);
lean_dec(v_h__3_2728_);
lean_dec(v_h__2_2727_);
lean_dec(v_h__1_2726_);
v_a_2748_ = lean_ctor_get(v_x_2725_, 0);
lean_inc_ref(v_a_2748_);
v_b_2749_ = lean_ctor_get(v_x_2725_, 1);
lean_inc_ref(v_b_2749_);
lean_dec_ref_known(v_x_2725_, 2);
v___x_2750_ = lean_apply_2(v_h__8_2733_, v_a_2748_, v_b_2749_);
return v___x_2750_;
}
case 7:
{
lean_object* v_a_2751_; lean_object* v_b_2752_; lean_object* v___x_2753_; 
lean_dec(v_h__9_2734_);
lean_dec(v_h__8_2733_);
lean_dec(v_h__7_2732_);
lean_dec(v_h__5_2730_);
lean_dec(v_h__4_2729_);
lean_dec(v_h__3_2728_);
lean_dec(v_h__2_2727_);
lean_dec(v_h__1_2726_);
v_a_2751_ = lean_ctor_get(v_x_2725_, 0);
lean_inc_ref(v_a_2751_);
v_b_2752_ = lean_ctor_get(v_x_2725_, 1);
lean_inc_ref(v_b_2752_);
lean_dec_ref_known(v_x_2725_, 2);
v___x_2753_ = lean_apply_2(v_h__6_2731_, v_a_2751_, v_b_2752_);
return v___x_2753_;
}
default: 
{
lean_object* v_a_2754_; lean_object* v_k_2755_; lean_object* v___x_2756_; 
lean_dec(v_h__8_2733_);
lean_dec(v_h__7_2732_);
lean_dec(v_h__6_2731_);
lean_dec(v_h__5_2730_);
lean_dec(v_h__4_2729_);
lean_dec(v_h__3_2728_);
lean_dec(v_h__2_2727_);
lean_dec(v_h__1_2726_);
v_a_2754_ = lean_ctor_get(v_x_2725_, 0);
lean_inc_ref(v_a_2754_);
v_k_2755_ = lean_ctor_get(v_x_2725_, 1);
lean_inc(v_k_2755_);
lean_dec_ref_known(v_x_2725_, 2);
v___x_2756_ = lean_apply_2(v_h__9_2734_, v_a_2754_, v_k_2755_);
return v___x_2756_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter(lean_object* v_motive_2757_, lean_object* v_x_2758_, lean_object* v_h__1_2759_, lean_object* v_h__2_2760_, lean_object* v_h__3_2761_, lean_object* v_h__4_2762_, lean_object* v_h__5_2763_, lean_object* v_h__6_2764_, lean_object* v_h__7_2765_, lean_object* v_h__8_2766_, lean_object* v_h__9_2767_){
_start:
{
switch(lean_obj_tag(v_x_2758_))
{
case 0:
{
lean_object* v_k_2768_; lean_object* v___x_2769_; 
lean_dec(v_h__9_2767_);
lean_dec(v_h__8_2766_);
lean_dec(v_h__7_2765_);
lean_dec(v_h__6_2764_);
lean_dec(v_h__5_2763_);
lean_dec(v_h__4_2762_);
lean_dec(v_h__3_2761_);
lean_dec(v_h__2_2760_);
v_k_2768_ = lean_ctor_get(v_x_2758_, 0);
lean_inc(v_k_2768_);
lean_dec_ref_known(v_x_2758_, 1);
v___x_2769_ = lean_apply_1(v_h__1_2759_, v_k_2768_);
return v___x_2769_;
}
case 1:
{
lean_object* v_k_2770_; lean_object* v___x_2771_; 
lean_dec(v_h__9_2767_);
lean_dec(v_h__8_2766_);
lean_dec(v_h__7_2765_);
lean_dec(v_h__6_2764_);
lean_dec(v_h__5_2763_);
lean_dec(v_h__4_2762_);
lean_dec(v_h__2_2760_);
lean_dec(v_h__1_2759_);
v_k_2770_ = lean_ctor_get(v_x_2758_, 0);
lean_inc(v_k_2770_);
lean_dec_ref_known(v_x_2758_, 1);
v___x_2771_ = lean_apply_1(v_h__3_2761_, v_k_2770_);
return v___x_2771_;
}
case 2:
{
lean_object* v_k_2772_; lean_object* v___x_2773_; 
lean_dec(v_h__9_2767_);
lean_dec(v_h__8_2766_);
lean_dec(v_h__7_2765_);
lean_dec(v_h__6_2764_);
lean_dec(v_h__5_2763_);
lean_dec(v_h__4_2762_);
lean_dec(v_h__3_2761_);
lean_dec(v_h__1_2759_);
v_k_2772_ = lean_ctor_get(v_x_2758_, 0);
lean_inc(v_k_2772_);
lean_dec_ref_known(v_x_2758_, 1);
v___x_2773_ = lean_apply_1(v_h__2_2760_, v_k_2772_);
return v___x_2773_;
}
case 3:
{
lean_object* v_i_2774_; lean_object* v___x_2775_; 
lean_dec(v_h__9_2767_);
lean_dec(v_h__8_2766_);
lean_dec(v_h__7_2765_);
lean_dec(v_h__6_2764_);
lean_dec(v_h__5_2763_);
lean_dec(v_h__3_2761_);
lean_dec(v_h__2_2760_);
lean_dec(v_h__1_2759_);
v_i_2774_ = lean_ctor_get(v_x_2758_, 0);
lean_inc(v_i_2774_);
lean_dec_ref_known(v_x_2758_, 1);
v___x_2775_ = lean_apply_1(v_h__4_2762_, v_i_2774_);
return v___x_2775_;
}
case 4:
{
lean_object* v_a_2776_; lean_object* v___x_2777_; 
lean_dec(v_h__9_2767_);
lean_dec(v_h__8_2766_);
lean_dec(v_h__6_2764_);
lean_dec(v_h__5_2763_);
lean_dec(v_h__4_2762_);
lean_dec(v_h__3_2761_);
lean_dec(v_h__2_2760_);
lean_dec(v_h__1_2759_);
v_a_2776_ = lean_ctor_get(v_x_2758_, 0);
lean_inc_ref(v_a_2776_);
lean_dec_ref_known(v_x_2758_, 1);
v___x_2777_ = lean_apply_1(v_h__7_2765_, v_a_2776_);
return v___x_2777_;
}
case 5:
{
lean_object* v_a_2778_; lean_object* v_b_2779_; lean_object* v___x_2780_; 
lean_dec(v_h__9_2767_);
lean_dec(v_h__8_2766_);
lean_dec(v_h__7_2765_);
lean_dec(v_h__6_2764_);
lean_dec(v_h__4_2762_);
lean_dec(v_h__3_2761_);
lean_dec(v_h__2_2760_);
lean_dec(v_h__1_2759_);
v_a_2778_ = lean_ctor_get(v_x_2758_, 0);
lean_inc_ref(v_a_2778_);
v_b_2779_ = lean_ctor_get(v_x_2758_, 1);
lean_inc_ref(v_b_2779_);
lean_dec_ref_known(v_x_2758_, 2);
v___x_2780_ = lean_apply_2(v_h__5_2763_, v_a_2778_, v_b_2779_);
return v___x_2780_;
}
case 6:
{
lean_object* v_a_2781_; lean_object* v_b_2782_; lean_object* v___x_2783_; 
lean_dec(v_h__9_2767_);
lean_dec(v_h__7_2765_);
lean_dec(v_h__6_2764_);
lean_dec(v_h__5_2763_);
lean_dec(v_h__4_2762_);
lean_dec(v_h__3_2761_);
lean_dec(v_h__2_2760_);
lean_dec(v_h__1_2759_);
v_a_2781_ = lean_ctor_get(v_x_2758_, 0);
lean_inc_ref(v_a_2781_);
v_b_2782_ = lean_ctor_get(v_x_2758_, 1);
lean_inc_ref(v_b_2782_);
lean_dec_ref_known(v_x_2758_, 2);
v___x_2783_ = lean_apply_2(v_h__8_2766_, v_a_2781_, v_b_2782_);
return v___x_2783_;
}
case 7:
{
lean_object* v_a_2784_; lean_object* v_b_2785_; lean_object* v___x_2786_; 
lean_dec(v_h__9_2767_);
lean_dec(v_h__8_2766_);
lean_dec(v_h__7_2765_);
lean_dec(v_h__5_2763_);
lean_dec(v_h__4_2762_);
lean_dec(v_h__3_2761_);
lean_dec(v_h__2_2760_);
lean_dec(v_h__1_2759_);
v_a_2784_ = lean_ctor_get(v_x_2758_, 0);
lean_inc_ref(v_a_2784_);
v_b_2785_ = lean_ctor_get(v_x_2758_, 1);
lean_inc_ref(v_b_2785_);
lean_dec_ref_known(v_x_2758_, 2);
v___x_2786_ = lean_apply_2(v_h__6_2764_, v_a_2784_, v_b_2785_);
return v___x_2786_;
}
default: 
{
lean_object* v_a_2787_; lean_object* v_k_2788_; lean_object* v___x_2789_; 
lean_dec(v_h__8_2766_);
lean_dec(v_h__7_2765_);
lean_dec(v_h__6_2764_);
lean_dec(v_h__5_2763_);
lean_dec(v_h__4_2762_);
lean_dec(v_h__3_2761_);
lean_dec(v_h__2_2760_);
lean_dec(v_h__1_2759_);
v_a_2787_ = lean_ctor_get(v_x_2758_, 0);
lean_inc_ref(v_a_2787_);
v_k_2788_ = lean_ctor_get(v_x_2758_, 1);
lean_inc(v_k_2788_);
lean_dec_ref_known(v_x_2758_, 2);
v___x_2789_ = lean_apply_2(v_h__9_2767_, v_a_2787_, v_k_2788_);
return v___x_2789_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter___redArg(lean_object* v_a_2790_, lean_object* v_h__1_2791_, lean_object* v_h__2_2792_, lean_object* v_h__3_2793_, lean_object* v_h__4_2794_, lean_object* v_h__5_2795_){
_start:
{
switch(lean_obj_tag(v_a_2790_))
{
case 0:
{
lean_object* v_k_2796_; lean_object* v___x_2797_; 
lean_dec(v_h__5_2795_);
lean_dec(v_h__4_2794_);
lean_dec(v_h__3_2793_);
lean_dec(v_h__2_2792_);
v_k_2796_ = lean_ctor_get(v_a_2790_, 0);
lean_inc(v_k_2796_);
lean_dec_ref_known(v_a_2790_, 1);
v___x_2797_ = lean_apply_1(v_h__1_2791_, v_k_2796_);
return v___x_2797_;
}
case 2:
{
lean_object* v_k_2798_; lean_object* v___x_2799_; 
lean_dec(v_h__5_2795_);
lean_dec(v_h__4_2794_);
lean_dec(v_h__3_2793_);
lean_dec(v_h__1_2791_);
v_k_2798_ = lean_ctor_get(v_a_2790_, 0);
lean_inc(v_k_2798_);
lean_dec_ref_known(v_a_2790_, 1);
v___x_2799_ = lean_apply_1(v_h__2_2792_, v_k_2798_);
return v___x_2799_;
}
case 1:
{
lean_object* v_k_2800_; lean_object* v___x_2801_; 
lean_dec(v_h__5_2795_);
lean_dec(v_h__4_2794_);
lean_dec(v_h__2_2792_);
lean_dec(v_h__1_2791_);
v_k_2800_ = lean_ctor_get(v_a_2790_, 0);
lean_inc(v_k_2800_);
lean_dec_ref_known(v_a_2790_, 1);
v___x_2801_ = lean_apply_1(v_h__3_2793_, v_k_2800_);
return v___x_2801_;
}
case 3:
{
lean_object* v_i_2802_; lean_object* v___x_2803_; 
lean_dec(v_h__5_2795_);
lean_dec(v_h__3_2793_);
lean_dec(v_h__2_2792_);
lean_dec(v_h__1_2791_);
v_i_2802_ = lean_ctor_get(v_a_2790_, 0);
lean_inc(v_i_2802_);
lean_dec_ref_known(v_a_2790_, 1);
v___x_2803_ = lean_apply_1(v_h__4_2794_, v_i_2802_);
return v___x_2803_;
}
default: 
{
lean_object* v___x_2804_; 
lean_dec(v_h__4_2794_);
lean_dec(v_h__3_2793_);
lean_dec(v_h__2_2792_);
lean_dec(v_h__1_2791_);
v___x_2804_ = lean_apply_5(v_h__5_2795_, v_a_2790_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2804_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter(lean_object* v_motive_2805_, lean_object* v_a_2806_, lean_object* v_h__1_2807_, lean_object* v_h__2_2808_, lean_object* v_h__3_2809_, lean_object* v_h__4_2810_, lean_object* v_h__5_2811_){
_start:
{
switch(lean_obj_tag(v_a_2806_))
{
case 0:
{
lean_object* v_k_2812_; lean_object* v___x_2813_; 
lean_dec(v_h__5_2811_);
lean_dec(v_h__4_2810_);
lean_dec(v_h__3_2809_);
lean_dec(v_h__2_2808_);
v_k_2812_ = lean_ctor_get(v_a_2806_, 0);
lean_inc(v_k_2812_);
lean_dec_ref_known(v_a_2806_, 1);
v___x_2813_ = lean_apply_1(v_h__1_2807_, v_k_2812_);
return v___x_2813_;
}
case 2:
{
lean_object* v_k_2814_; lean_object* v___x_2815_; 
lean_dec(v_h__5_2811_);
lean_dec(v_h__4_2810_);
lean_dec(v_h__3_2809_);
lean_dec(v_h__1_2807_);
v_k_2814_ = lean_ctor_get(v_a_2806_, 0);
lean_inc(v_k_2814_);
lean_dec_ref_known(v_a_2806_, 1);
v___x_2815_ = lean_apply_1(v_h__2_2808_, v_k_2814_);
return v___x_2815_;
}
case 1:
{
lean_object* v_k_2816_; lean_object* v___x_2817_; 
lean_dec(v_h__5_2811_);
lean_dec(v_h__4_2810_);
lean_dec(v_h__2_2808_);
lean_dec(v_h__1_2807_);
v_k_2816_ = lean_ctor_get(v_a_2806_, 0);
lean_inc(v_k_2816_);
lean_dec_ref_known(v_a_2806_, 1);
v___x_2817_ = lean_apply_1(v_h__3_2809_, v_k_2816_);
return v___x_2817_;
}
case 3:
{
lean_object* v_i_2818_; lean_object* v___x_2819_; 
lean_dec(v_h__5_2811_);
lean_dec(v_h__3_2809_);
lean_dec(v_h__2_2808_);
lean_dec(v_h__1_2807_);
v_i_2818_ = lean_ctor_get(v_a_2806_, 0);
lean_inc(v_i_2818_);
lean_dec_ref_known(v_a_2806_, 1);
v___x_2819_ = lean_apply_1(v_h__4_2810_, v_i_2818_);
return v___x_2819_;
}
default: 
{
lean_object* v___x_2820_; 
lean_dec(v_h__4_2810_);
lean_dec(v_h__3_2809_);
lean_dec(v_h__2_2808_);
lean_dec(v_h__1_2807_);
v___x_2820_ = lean_apply_5(v_h__5_2811_, v_a_2806_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly__nc(lean_object* v_x_2821_){
_start:
{
switch(lean_obj_tag(v_x_2821_))
{
case 0:
{
lean_object* v_k_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
v_k_2822_ = lean_ctor_get(v_x_2821_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_x_2821_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v_x_2821_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_k_2822_);
lean_dec(v_x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_k_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
case 1:
{
lean_object* v_k_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2838_; 
v_k_2830_ = lean_ctor_get(v_x_2821_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_x_2821_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2832_ = v_x_2821_;
v_isShared_2833_ = v_isSharedCheck_2838_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_k_2830_);
lean_dec(v_x_2821_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2838_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2834_; lean_object* v___x_2836_; 
v___x_2834_ = lean_nat_to_int(v_k_2830_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set_tag(v___x_2832_, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2834_);
v___x_2836_ = v___x_2832_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
case 2:
{
lean_object* v_k_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
v_k_2839_ = lean_ctor_get(v_x_2821_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_x_2821_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v_x_2821_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_k_2839_);
lean_dec(v_x_2821_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set_tag(v___x_2841_, 0);
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_k_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
case 3:
{
lean_object* v_i_2847_; lean_object* v___x_2848_; 
v_i_2847_ = lean_ctor_get(v_x_2821_, 0);
lean_inc(v_i_2847_);
lean_dec_ref_known(v_x_2821_, 1);
v___x_2848_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2847_);
return v___x_2848_;
}
case 4:
{
lean_object* v_a_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_a_2849_ = lean_ctor_get(v_x_2821_, 0);
lean_inc_ref(v_a_2849_);
lean_dec_ref_known(v_x_2821_, 1);
v___x_2850_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2851_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2849_);
v___x_2852_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2850_, v___x_2851_);
return v___x_2852_;
}
case 5:
{
lean_object* v_a_2853_; lean_object* v_b_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_a_2853_ = lean_ctor_get(v_x_2821_, 0);
lean_inc_ref(v_a_2853_);
v_b_2854_ = lean_ctor_get(v_x_2821_, 1);
lean_inc_ref(v_b_2854_);
lean_dec_ref_known(v_x_2821_, 2);
v___x_2855_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2853_);
v___x_2856_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2854_);
v___x_2857_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2855_, v___x_2856_);
return v___x_2857_;
}
case 6:
{
lean_object* v_a_2858_; lean_object* v_b_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_a_2858_ = lean_ctor_get(v_x_2821_, 0);
lean_inc_ref(v_a_2858_);
v_b_2859_ = lean_ctor_get(v_x_2821_, 1);
lean_inc_ref(v_b_2859_);
lean_dec_ref_known(v_x_2821_, 2);
v___x_2860_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2858_);
v___x_2861_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2862_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2859_);
v___x_2863_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2861_, v___x_2862_);
v___x_2864_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2860_, v___x_2863_);
return v___x_2864_;
}
case 7:
{
lean_object* v_a_2865_; lean_object* v_b_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_a_2865_ = lean_ctor_get(v_x_2821_, 0);
lean_inc_ref(v_a_2865_);
v_b_2866_ = lean_ctor_get(v_x_2821_, 1);
lean_inc_ref(v_b_2866_);
lean_dec_ref_known(v_x_2821_, 2);
v___x_2867_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2865_);
v___x_2868_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2866_);
v___x_2869_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2867_, v___x_2868_);
return v___x_2869_;
}
default: 
{
lean_object* v_a_2870_; lean_object* v_k_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2903_; 
v_a_2870_ = lean_ctor_get(v_x_2821_, 0);
v_k_2871_ = lean_ctor_get(v_x_2821_, 1);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_x_2821_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2873_ = v_x_2821_;
v_isShared_2874_ = v_isSharedCheck_2903_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_k_2871_);
lean_inc(v_a_2870_);
lean_dec(v_x_2821_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2903_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v_n_2876_; lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = lean_unsigned_to_nat(0u);
v___x_2880_ = lean_nat_dec_eq(v_k_2871_, v___x_2879_);
if (v___x_2880_ == 0)
{
switch(lean_obj_tag(v_a_2870_))
{
case 0:
{
lean_object* v_k_2881_; 
lean_del_object(v___x_2873_);
v_k_2881_ = lean_ctor_get(v_a_2870_, 0);
lean_inc(v_k_2881_);
lean_dec_ref_known(v_a_2870_, 1);
v_n_2876_ = v_k_2881_;
goto v___jp_2875_;
}
case 2:
{
lean_object* v_k_2882_; 
lean_del_object(v___x_2873_);
v_k_2882_ = lean_ctor_get(v_a_2870_, 0);
lean_inc(v_k_2882_);
lean_dec_ref_known(v_a_2870_, 1);
v_n_2876_ = v_k_2882_;
goto v___jp_2875_;
}
case 1:
{
lean_object* v_k_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2892_; 
lean_del_object(v___x_2873_);
v_k_2883_ = lean_ctor_get(v_a_2870_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v_a_2870_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2885_ = v_a_2870_;
v_isShared_2886_ = v_isSharedCheck_2892_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_k_2883_);
lean_dec(v_a_2870_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2892_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2887_ = lean_nat_to_int(v_k_2883_);
v___x_2888_ = l_Int_pow(v___x_2887_, v_k_2871_);
lean_dec(v_k_2871_);
lean_dec(v___x_2887_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set_tag(v___x_2885_, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2888_);
v___x_2890_ = v___x_2885_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2888_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
case 3:
{
lean_object* v_i_2893_; lean_object* v___x_2895_; 
v_i_2893_ = lean_ctor_get(v_a_2870_, 0);
lean_inc(v_i_2893_);
lean_dec_ref_known(v_a_2870_, 1);
if (v_isShared_2874_ == 0)
{
lean_ctor_set_tag(v___x_2873_, 0);
lean_ctor_set(v___x_2873_, 0, v_i_2893_);
v___x_2895_ = v___x_2873_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_i_2893_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_k_2871_);
v___x_2895_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2896_ = lean_box(0);
v___x_2897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2895_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
v___x_2898_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2897_);
return v___x_2898_;
}
}
default: 
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
lean_del_object(v___x_2873_);
v___x_2900_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2870_);
v___x_2901_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_2900_, v_k_2871_);
lean_dec(v_k_2871_);
return v___x_2901_;
}
}
}
else
{
lean_object* v___x_2902_; 
lean_del_object(v___x_2873_);
lean_dec(v_k_2871_);
lean_dec_ref(v_a_2870_);
v___x_2902_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2902_;
}
v___jp_2875_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = l_Int_pow(v_n_2876_, v_k_2871_);
lean_dec(v_k_2871_);
lean_dec(v_n_2876_);
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
return v___x_2878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_normEq0(lean_object* v_p_2904_, lean_object* v_c_2905_){
_start:
{
if (lean_obj_tag(v_p_2904_) == 0)
{
lean_object* v_k_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v_k_2906_ = lean_ctor_get(v_p_2904_, 0);
v___x_2907_ = lean_nat_to_int(v_c_2905_);
v___x_2908_ = lean_int_emod(v_k_2906_, v___x_2907_);
lean_dec(v___x_2907_);
v___x_2909_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2910_ = lean_int_dec_eq(v___x_2908_, v___x_2909_);
lean_dec(v___x_2908_);
if (v___x_2910_ == 0)
{
return v_p_2904_;
}
else
{
lean_object* v___x_2911_; 
lean_dec_ref_known(v_p_2904_, 1);
v___x_2911_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2911_;
}
}
else
{
lean_object* v_k_2912_; lean_object* v_v_2913_; lean_object* v_p_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2927_; 
v_k_2912_ = lean_ctor_get(v_p_2904_, 0);
v_v_2913_ = lean_ctor_get(v_p_2904_, 1);
v_p_2914_ = lean_ctor_get(v_p_2904_, 2);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_p_2904_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2916_ = v_p_2904_;
v_isShared_2917_ = v_isSharedCheck_2927_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_p_2914_);
lean_inc(v_v_2913_);
lean_inc(v_k_2912_);
lean_dec(v_p_2904_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2927_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; uint8_t v___x_2921_; 
lean_inc(v_c_2905_);
v___x_2918_ = lean_nat_to_int(v_c_2905_);
v___x_2919_ = lean_int_emod(v_k_2912_, v___x_2918_);
lean_dec(v___x_2918_);
v___x_2920_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2921_ = lean_int_dec_eq(v___x_2919_, v___x_2920_);
lean_dec(v___x_2919_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2922_; lean_object* v___x_2924_; 
v___x_2922_ = l_Lean_Grind_CommRing_Poly_normEq0(v_p_2914_, v_c_2905_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 2, v___x_2922_);
v___x_2924_ = v___x_2916_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_k_2912_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_v_2913_);
lean_ctor_set(v_reuseFailAlloc_2925_, 2, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
else
{
lean_del_object(v___x_2916_);
lean_dec(v_v_2913_);
lean_dec(v_k_2912_);
v_p_2904_ = v_p_2914_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object* v_p_2928_, lean_object* v_k_2929_, lean_object* v_c_2930_){
_start:
{
if (lean_obj_tag(v_p_2928_) == 0)
{
lean_object* v_k_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2941_; 
v_k_2931_ = lean_ctor_get(v_p_2928_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_p_2928_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2933_ = v_p_2928_;
v_isShared_2934_ = v_isSharedCheck_2941_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_k_2931_);
lean_dec(v_p_2928_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2941_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2935_ = lean_int_add(v_k_2931_, v_k_2929_);
lean_dec(v_k_2931_);
v___x_2936_ = lean_nat_to_int(v_c_2930_);
v___x_2937_ = lean_int_emod(v___x_2935_, v___x_2936_);
lean_dec(v___x_2936_);
lean_dec(v___x_2935_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2937_);
v___x_2939_ = v___x_2933_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
else
{
lean_object* v_k_2942_; lean_object* v_v_2943_; lean_object* v_p_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2952_; 
v_k_2942_ = lean_ctor_get(v_p_2928_, 0);
v_v_2943_ = lean_ctor_get(v_p_2928_, 1);
v_p_2944_ = lean_ctor_get(v_p_2928_, 2);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_p_2928_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2946_ = v_p_2928_;
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_p_2944_);
lean_inc(v_v_2943_);
lean_inc(v_k_2942_);
lean_dec(v_p_2928_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2948_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2944_, v_k_2929_, v_c_2930_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 2, v___x_2948_);
v___x_2950_ = v___x_2946_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_k_2942_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_v_2943_);
lean_ctor_set(v_reuseFailAlloc_2951_, 2, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC___boxed(lean_object* v_p_2953_, lean_object* v_k_2954_, lean_object* v_c_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2953_, v_k_2954_, v_c_2955_);
lean_dec(v_k_2954_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC_go(lean_object* v_m_2957_, lean_object* v_c_2958_, lean_object* v_k_2959_, lean_object* v_a_2960_){
_start:
{
if (lean_obj_tag(v_a_2960_) == 0)
{
lean_object* v___x_2961_; 
lean_dec(v_c_2958_);
v___x_2961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2961_, 0, v_k_2959_);
lean_ctor_set(v___x_2961_, 1, v_m_2957_);
lean_ctor_set(v___x_2961_, 2, v_a_2960_);
return v___x_2961_;
}
else
{
lean_object* v_k_2962_; lean_object* v_v_2963_; lean_object* v_p_2964_; uint8_t v___x_2965_; 
v_k_2962_ = lean_ctor_get(v_a_2960_, 0);
v_v_2963_ = lean_ctor_get(v_a_2960_, 1);
v_p_2964_ = lean_ctor_get(v_a_2960_, 2);
v___x_2965_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2957_, v_v_2963_);
switch(v___x_2965_)
{
case 0:
{
lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2973_; 
lean_inc_ref(v_p_2964_);
lean_inc(v_v_2963_);
lean_inc(v_k_2962_);
v_isSharedCheck_2973_ = !lean_is_exclusive(v_a_2960_);
if (v_isSharedCheck_2973_ == 0)
{
lean_object* v_unused_2974_; lean_object* v_unused_2975_; lean_object* v_unused_2976_; 
v_unused_2974_ = lean_ctor_get(v_a_2960_, 2);
lean_dec(v_unused_2974_);
v_unused_2975_ = lean_ctor_get(v_a_2960_, 1);
lean_dec(v_unused_2975_);
v_unused_2976_ = lean_ctor_get(v_a_2960_, 0);
lean_dec(v_unused_2976_);
v___x_2967_ = v_a_2960_;
v_isShared_2968_ = v_isSharedCheck_2973_;
goto v_resetjp_2966_;
}
else
{
lean_dec(v_a_2960_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2973_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2971_; 
v___x_2969_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_2957_, v_c_2958_, v_k_2959_, v_p_2964_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 2, v___x_2969_);
v___x_2971_ = v___x_2967_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_k_2962_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v_v_2963_);
lean_ctor_set(v_reuseFailAlloc_2972_, 2, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
case 1:
{
lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2988_; 
lean_inc_ref(v_p_2964_);
lean_inc(v_k_2962_);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_a_2960_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; lean_object* v_unused_2990_; lean_object* v_unused_2991_; 
v_unused_2989_ = lean_ctor_get(v_a_2960_, 2);
lean_dec(v_unused_2989_);
v_unused_2990_ = lean_ctor_get(v_a_2960_, 1);
lean_dec(v_unused_2990_);
v_unused_2991_ = lean_ctor_get(v_a_2960_, 0);
lean_dec(v_unused_2991_);
v___x_2978_ = v_a_2960_;
v_isShared_2979_ = v_isSharedCheck_2988_;
goto v_resetjp_2977_;
}
else
{
lean_dec(v_a_2960_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2988_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v_k_x27_x27_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2980_ = lean_int_add(v_k_2959_, v_k_2962_);
lean_dec(v_k_2962_);
lean_dec(v_k_2959_);
v___x_2981_ = lean_nat_to_int(v_c_2958_);
v_k_x27_x27_2982_ = lean_int_emod(v___x_2980_, v___x_2981_);
lean_dec(v___x_2981_);
lean_dec(v___x_2980_);
v___x_2983_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2984_ = lean_int_dec_eq(v_k_x27_x27_2982_, v___x_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2986_; 
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 1, v_m_2957_);
lean_ctor_set(v___x_2978_, 0, v_k_x27_x27_2982_);
v___x_2986_ = v___x_2978_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_k_x27_x27_2982_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_m_2957_);
lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_p_2964_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
else
{
lean_dec(v_k_x27_x27_2982_);
lean_del_object(v___x_2978_);
lean_dec(v_m_2957_);
return v_p_2964_;
}
}
}
default: 
{
lean_object* v___x_2992_; 
lean_dec(v_c_2958_);
v___x_2992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2992_, 0, v_k_2959_);
lean_ctor_set(v___x_2992_, 1, v_m_2957_);
lean_ctor_set(v___x_2992_, 2, v_a_2960_);
return v___x_2992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC(lean_object* v_k_2993_, lean_object* v_m_2994_, lean_object* v_p_2995_, lean_object* v_c_2996_){
_start:
{
lean_object* v___x_2997_; lean_object* v_k_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
lean_inc(v_c_2996_);
v___x_2997_ = lean_nat_to_int(v_c_2996_);
v_k_2998_ = lean_int_emod(v_k_2993_, v___x_2997_);
lean_dec(v___x_2997_);
v___x_2999_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3000_ = lean_int_dec_eq(v_k_2998_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_2994_, v_c_2996_, v_k_2998_, v_p_2995_);
return v___x_3001_;
}
else
{
lean_dec(v_k_2998_);
lean_dec(v_c_2996_);
lean_dec(v_m_2994_);
return v_p_2995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC___boxed(lean_object* v_k_3002_, lean_object* v_m_3003_, lean_object* v_p_3004_, lean_object* v_c_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_Grind_CommRing_Poly_insertC(v_k_3002_, v_m_3003_, v_p_3004_, v_c_3005_);
lean_dec(v_k_3002_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go(lean_object* v_k_3007_, lean_object* v_c_3008_, lean_object* v_a_3009_){
_start:
{
if (lean_obj_tag(v_a_3009_) == 0)
{
lean_object* v_k_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3020_; 
v_k_3010_ = lean_ctor_get(v_a_3009_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_a_3009_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3012_ = v_a_3009_;
v_isShared_3013_ = v_isSharedCheck_3020_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_k_3010_);
lean_dec(v_a_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3020_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3014_ = lean_int_mul(v_k_3007_, v_k_3010_);
lean_dec(v_k_3010_);
v___x_3015_ = lean_nat_to_int(v_c_3008_);
v___x_3016_ = lean_int_emod(v___x_3014_, v___x_3015_);
lean_dec(v___x_3015_);
lean_dec(v___x_3014_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v___x_3016_);
v___x_3018_ = v___x_3012_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
else
{
lean_object* v_k_3021_; lean_object* v_v_3022_; lean_object* v_p_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3037_; 
v_k_3021_ = lean_ctor_get(v_a_3009_, 0);
v_v_3022_ = lean_ctor_get(v_a_3009_, 1);
v_p_3023_ = lean_ctor_get(v_a_3009_, 2);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_a_3009_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3025_ = v_a_3009_;
v_isShared_3026_ = v_isSharedCheck_3037_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_p_3023_);
lean_inc(v_v_3022_);
lean_inc(v_k_3021_);
lean_dec(v_a_3009_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3037_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v_k_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3027_ = lean_int_mul(v_k_3007_, v_k_3021_);
lean_dec(v_k_3021_);
lean_inc(v_c_3008_);
v___x_3028_ = lean_nat_to_int(v_c_3008_);
v_k_3029_ = lean_int_emod(v___x_3027_, v___x_3028_);
lean_dec(v___x_3028_);
lean_dec(v___x_3027_);
v___x_3030_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3031_ = lean_int_dec_eq(v_k_3029_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3032_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_3007_, v_c_3008_, v_p_3023_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 2, v___x_3032_);
lean_ctor_set(v___x_3025_, 0, v_k_3029_);
v___x_3034_ = v___x_3025_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_k_3029_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_v_3022_);
lean_ctor_set(v_reuseFailAlloc_3035_, 2, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
else
{
lean_dec(v_k_3029_);
lean_del_object(v___x_3025_);
lean_dec(v_v_3022_);
v_a_3009_ = v_p_3023_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go___boxed(lean_object* v_k_3038_, lean_object* v_c_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_3038_, v_c_3039_, v_a_3040_);
lean_dec(v_k_3038_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object* v_k_3042_, lean_object* v_p_3043_, lean_object* v_c_3044_){
_start:
{
lean_object* v___x_3045_; lean_object* v_k_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
lean_inc(v_c_3044_);
v___x_3045_ = lean_nat_to_int(v_c_3044_);
v_k_3046_ = lean_int_emod(v_k_3042_, v___x_3045_);
lean_dec(v___x_3045_);
v___x_3047_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3048_ = lean_int_dec_eq(v_k_3046_, v___x_3047_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3049_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_3050_ = lean_int_dec_eq(v_k_3046_, v___x_3049_);
lean_dec(v_k_3046_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; 
v___x_3051_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_3042_, v_c_3044_, v_p_3043_);
return v___x_3051_;
}
else
{
lean_dec(v_c_3044_);
return v_p_3043_;
}
}
else
{
lean_object* v___x_3052_; 
lean_dec(v_k_3046_);
lean_dec(v_c_3044_);
lean_dec_ref(v_p_3043_);
v___x_3052_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC___boxed(lean_object* v_k_3053_, lean_object* v_p_3054_, lean_object* v_c_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3053_, v_p_3054_, v_c_3055_);
lean_dec(v_k_3053_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go(lean_object* v_k_3057_, lean_object* v_m_3058_, lean_object* v_c_3059_, lean_object* v_a_3060_){
_start:
{
if (lean_obj_tag(v_a_3060_) == 0)
{
lean_object* v_k_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v_k_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v_k_3061_ = lean_ctor_get(v_a_3060_, 0);
lean_inc(v_k_3061_);
lean_dec_ref_known(v_a_3060_, 1);
v___x_3062_ = lean_int_mul(v_k_3057_, v_k_3061_);
lean_dec(v_k_3061_);
v___x_3063_ = lean_nat_to_int(v_c_3059_);
v_k_3064_ = lean_int_emod(v___x_3062_, v___x_3063_);
lean_dec(v___x_3063_);
lean_dec(v___x_3062_);
v___x_3065_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3066_ = lean_int_dec_eq(v_k_3064_, v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3068_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3068_, 0, v_k_3064_);
lean_ctor_set(v___x_3068_, 1, v_m_3058_);
lean_ctor_set(v___x_3068_, 2, v___x_3067_);
return v___x_3068_;
}
else
{
lean_object* v___x_3069_; 
lean_dec(v_k_3064_);
lean_dec(v_m_3058_);
v___x_3069_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3069_;
}
}
else
{
lean_object* v_k_3070_; lean_object* v_v_3071_; lean_object* v_p_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3087_; 
v_k_3070_ = lean_ctor_get(v_a_3060_, 0);
v_v_3071_ = lean_ctor_get(v_a_3060_, 1);
v_p_3072_ = lean_ctor_get(v_a_3060_, 2);
v_isSharedCheck_3087_ = !lean_is_exclusive(v_a_3060_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3074_ = v_a_3060_;
v_isShared_3075_ = v_isSharedCheck_3087_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_p_3072_);
lean_inc(v_v_3071_);
lean_inc(v_k_3070_);
lean_dec(v_a_3060_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3087_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v_k_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3076_ = lean_int_mul(v_k_3057_, v_k_3070_);
lean_dec(v_k_3070_);
lean_inc(v_c_3059_);
v___x_3077_ = lean_nat_to_int(v_c_3059_);
v_k_3078_ = lean_int_emod(v___x_3076_, v___x_3077_);
lean_dec(v___x_3077_);
lean_dec(v___x_3076_);
v___x_3079_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3080_ = lean_int_dec_eq(v_k_3078_, v___x_3079_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3084_; 
lean_inc(v_m_3058_);
v___x_3081_ = l_Lean_Grind_CommRing_Mon_mul(v_m_3058_, v_v_3071_);
v___x_3082_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3057_, v_m_3058_, v_c_3059_, v_p_3072_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 2, v___x_3082_);
lean_ctor_set(v___x_3074_, 1, v___x_3081_);
lean_ctor_set(v___x_3074_, 0, v_k_3078_);
v___x_3084_ = v___x_3074_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_k_3078_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v___x_3081_);
lean_ctor_set(v_reuseFailAlloc_3085_, 2, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
else
{
lean_dec(v_k_3078_);
lean_del_object(v___x_3074_);
lean_dec(v_v_3071_);
v_a_3060_ = v_p_3072_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go___boxed(lean_object* v_k_3088_, lean_object* v_m_3089_, lean_object* v_c_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3088_, v_m_3089_, v_c_3090_, v_a_3091_);
lean_dec(v_k_3088_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object* v_k_3093_, lean_object* v_m_3094_, lean_object* v_p_3095_, lean_object* v_c_3096_){
_start:
{
lean_object* v___x_3097_; lean_object* v_k_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
lean_inc(v_c_3096_);
v___x_3097_ = lean_nat_to_int(v_c_3096_);
v_k_3098_ = lean_int_emod(v_k_3093_, v___x_3097_);
lean_dec(v___x_3097_);
v___x_3099_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3100_ = lean_int_dec_eq(v_k_3098_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3101_ = lean_box(0);
v___x_3102_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_3094_, v___x_3101_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3103_; 
lean_dec(v_k_3098_);
v___x_3103_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3093_, v_m_3094_, v_c_3096_, v_p_3095_);
return v___x_3103_;
}
else
{
lean_object* v___x_3104_; 
lean_dec(v_m_3094_);
v___x_3104_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3098_, v_p_3095_, v_c_3096_);
lean_dec(v_k_3098_);
return v___x_3104_;
}
}
else
{
lean_object* v___x_3105_; 
lean_dec(v_k_3098_);
lean_dec(v_c_3096_);
lean_dec_ref(v_p_3095_);
lean_dec(v_m_3094_);
v___x_3105_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC___boxed(lean_object* v_k_3106_, lean_object* v_m_3107_, lean_object* v_p_3108_, lean_object* v_c_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_3106_, v_m_3107_, v_p_3108_, v_c_3109_);
lean_dec(v_k_3106_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(lean_object* v_k_3111_, lean_object* v_m_3112_, lean_object* v_c_3113_, lean_object* v_p_3114_, lean_object* v_acc_3115_){
_start:
{
if (lean_obj_tag(v_p_3114_) == 0)
{
lean_object* v_k_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v_k_3116_ = lean_ctor_get(v_p_3114_, 0);
lean_inc(v_k_3116_);
lean_dec_ref_known(v_p_3114_, 1);
v___x_3117_ = lean_int_mul(v_k_3111_, v_k_3116_);
lean_dec(v_k_3116_);
v___x_3118_ = lean_nat_to_int(v_c_3113_);
v___x_3119_ = lean_int_emod(v___x_3117_, v___x_3118_);
lean_dec(v___x_3118_);
lean_dec(v___x_3117_);
v___x_3120_ = l_Lean_Grind_CommRing_Poly_insert(v___x_3119_, v_m_3112_, v_acc_3115_);
return v___x_3120_;
}
else
{
lean_object* v_k_3121_; lean_object* v_v_3122_; lean_object* v_p_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v_k_3121_ = lean_ctor_get(v_p_3114_, 0);
lean_inc(v_k_3121_);
v_v_3122_ = lean_ctor_get(v_p_3114_, 1);
lean_inc(v_v_3122_);
v_p_3123_ = lean_ctor_get(v_p_3114_, 2);
lean_inc_ref(v_p_3123_);
lean_dec_ref_known(v_p_3114_, 3);
v___x_3124_ = lean_int_mul(v_k_3111_, v_k_3121_);
lean_dec(v_k_3121_);
lean_inc(v_c_3113_);
v___x_3125_ = lean_nat_to_int(v_c_3113_);
v___x_3126_ = lean_int_emod(v___x_3124_, v___x_3125_);
lean_dec(v___x_3125_);
lean_dec(v___x_3124_);
lean_inc(v_m_3112_);
v___x_3127_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_3112_, v_v_3122_);
v___x_3128_ = l_Lean_Grind_CommRing_Poly_insert(v___x_3126_, v___x_3127_, v_acc_3115_);
v_p_3114_ = v_p_3123_;
v_acc_3115_ = v___x_3128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go___boxed(lean_object* v_k_3130_, lean_object* v_m_3131_, lean_object* v_c_3132_, lean_object* v_p_3133_, lean_object* v_acc_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_3130_, v_m_3131_, v_c_3132_, v_p_3133_, v_acc_3134_);
lean_dec(v_k_3130_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc(lean_object* v_k_3136_, lean_object* v_m_3137_, lean_object* v_p_3138_, lean_object* v_c_3139_){
_start:
{
lean_object* v___x_3140_; lean_object* v_k_3141_; lean_object* v___x_3142_; uint8_t v___x_3143_; 
lean_inc(v_c_3139_);
v___x_3140_ = lean_nat_to_int(v_c_3139_);
v_k_3141_ = lean_int_emod(v_k_3136_, v___x_3140_);
lean_dec(v___x_3140_);
v___x_3142_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3143_ = lean_int_dec_eq(v_k_3141_, v___x_3142_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3144_; uint8_t v___x_3145_; 
v___x_3144_ = lean_box(0);
v___x_3145_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_3137_, v___x_3144_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_dec(v_k_3141_);
v___x_3146_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3147_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_3136_, v_m_3137_, v_c_3139_, v_p_3138_, v___x_3146_);
return v___x_3147_;
}
else
{
lean_object* v___x_3148_; 
lean_dec(v_m_3137_);
v___x_3148_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3141_, v_p_3138_, v_c_3139_);
lean_dec(v_k_3141_);
return v___x_3148_;
}
}
else
{
lean_object* v___x_3149_; 
lean_dec(v_k_3141_);
lean_dec(v_c_3139_);
lean_dec_ref(v_p_3138_);
lean_dec(v_m_3137_);
v___x_3149_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc___boxed(lean_object* v_k_3150_, lean_object* v_m_3151_, lean_object* v_p_3152_, lean_object* v_c_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3150_, v_m_3151_, v_p_3152_, v_c_3153_);
lean_dec(v_k_3150_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineC(lean_object* v_p_u2081_3155_, lean_object* v_p_u2082_3156_, lean_object* v_c_3157_){
_start:
{
if (lean_obj_tag(v_p_u2081_3155_) == 0)
{
if (lean_obj_tag(v_p_u2082_3156_) == 0)
{
lean_object* v_k_3158_; lean_object* v_k_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3169_; 
v_k_3158_ = lean_ctor_get(v_p_u2081_3155_, 0);
lean_inc(v_k_3158_);
lean_dec_ref_known(v_p_u2081_3155_, 1);
v_k_3159_ = lean_ctor_get(v_p_u2082_3156_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v_p_u2082_3156_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3161_ = v_p_u2082_3156_;
v_isShared_3162_ = v_isSharedCheck_3169_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_k_3159_);
lean_dec(v_p_u2082_3156_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3169_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3163_ = lean_int_add(v_k_3158_, v_k_3159_);
lean_dec(v_k_3159_);
lean_dec(v_k_3158_);
v___x_3164_ = lean_nat_to_int(v_c_3157_);
v___x_3165_ = lean_int_emod(v___x_3163_, v___x_3164_);
lean_dec(v___x_3164_);
lean_dec(v___x_3163_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v___x_3165_);
v___x_3167_ = v___x_3161_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
else
{
lean_object* v_k_3170_; lean_object* v___x_3171_; 
v_k_3170_ = lean_ctor_get(v_p_u2081_3155_, 0);
lean_inc(v_k_3170_);
lean_dec_ref_known(v_p_u2081_3155_, 1);
v___x_3171_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2082_3156_, v_k_3170_, v_c_3157_);
lean_dec(v_k_3170_);
return v___x_3171_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_3156_) == 0)
{
lean_object* v_k_3172_; lean_object* v___x_3173_; 
v_k_3172_ = lean_ctor_get(v_p_u2082_3156_, 0);
lean_inc(v_k_3172_);
lean_dec_ref_known(v_p_u2082_3156_, 1);
v___x_3173_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2081_3155_, v_k_3172_, v_c_3157_);
lean_dec(v_k_3172_);
return v___x_3173_;
}
else
{
lean_object* v_k_3174_; lean_object* v_v_3175_; lean_object* v_p_3176_; lean_object* v_k_3177_; lean_object* v_v_3178_; lean_object* v_p_3179_; uint8_t v___x_3180_; 
v_k_3174_ = lean_ctor_get(v_p_u2081_3155_, 0);
v_v_3175_ = lean_ctor_get(v_p_u2081_3155_, 1);
v_p_3176_ = lean_ctor_get(v_p_u2081_3155_, 2);
v_k_3177_ = lean_ctor_get(v_p_u2082_3156_, 0);
v_v_3178_ = lean_ctor_get(v_p_u2082_3156_, 1);
v_p_3179_ = lean_ctor_get(v_p_u2082_3156_, 2);
v___x_3180_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_3175_, v_v_3178_);
switch(v___x_3180_)
{
case 0:
{
lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3188_; 
lean_inc_ref(v_p_3179_);
lean_inc(v_v_3178_);
lean_inc(v_k_3177_);
v_isSharedCheck_3188_ = !lean_is_exclusive(v_p_u2082_3156_);
if (v_isSharedCheck_3188_ == 0)
{
lean_object* v_unused_3189_; lean_object* v_unused_3190_; lean_object* v_unused_3191_; 
v_unused_3189_ = lean_ctor_get(v_p_u2082_3156_, 2);
lean_dec(v_unused_3189_);
v_unused_3190_ = lean_ctor_get(v_p_u2082_3156_, 1);
lean_dec(v_unused_3190_);
v_unused_3191_ = lean_ctor_get(v_p_u2082_3156_, 0);
lean_dec(v_unused_3191_);
v___x_3182_ = v_p_u2082_3156_;
v_isShared_3183_ = v_isSharedCheck_3188_;
goto v_resetjp_3181_;
}
else
{
lean_dec(v_p_u2082_3156_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3188_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; lean_object* v___x_3186_; 
v___x_3184_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_u2081_3155_, v_p_3179_, v_c_3157_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 2, v___x_3184_);
v___x_3186_ = v___x_3182_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_k_3177_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_v_3178_);
lean_ctor_set(v_reuseFailAlloc_3187_, 2, v___x_3184_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
case 1:
{
lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3205_; 
lean_inc_ref(v_p_3179_);
lean_inc(v_k_3177_);
lean_inc_ref(v_p_3176_);
lean_inc(v_v_3175_);
lean_inc(v_k_3174_);
lean_dec_ref_known(v_p_u2081_3155_, 3);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_p_u2082_3156_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; lean_object* v_unused_3207_; lean_object* v_unused_3208_; 
v_unused_3206_ = lean_ctor_get(v_p_u2082_3156_, 2);
lean_dec(v_unused_3206_);
v_unused_3207_ = lean_ctor_get(v_p_u2082_3156_, 1);
lean_dec(v_unused_3207_);
v_unused_3208_ = lean_ctor_get(v_p_u2082_3156_, 0);
lean_dec(v_unused_3208_);
v___x_3193_ = v_p_u2082_3156_;
v_isShared_3194_ = v_isSharedCheck_3205_;
goto v_resetjp_3192_;
}
else
{
lean_dec(v_p_u2082_3156_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3205_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v_k_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
v___x_3195_ = lean_int_add(v_k_3174_, v_k_3177_);
lean_dec(v_k_3177_);
lean_dec(v_k_3174_);
lean_inc(v_c_3157_);
v___x_3196_ = lean_nat_to_int(v_c_3157_);
v_k_3197_ = lean_int_emod(v___x_3195_, v___x_3196_);
lean_dec(v___x_3196_);
lean_dec(v___x_3195_);
v___x_3198_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3199_ = lean_int_dec_eq(v_k_3197_, v___x_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3200_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3176_, v_p_3179_, v_c_3157_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 2, v___x_3200_);
lean_ctor_set(v___x_3193_, 1, v_v_3175_);
lean_ctor_set(v___x_3193_, 0, v_k_3197_);
v___x_3202_ = v___x_3193_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_k_3197_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3203_, 2, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
else
{
lean_dec(v_k_3197_);
lean_del_object(v___x_3193_);
lean_dec(v_v_3175_);
v_p_u2081_3155_ = v_p_3176_;
v_p_u2082_3156_ = v_p_3179_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3216_; 
lean_inc_ref(v_p_3176_);
lean_inc(v_v_3175_);
lean_inc(v_k_3174_);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_p_u2081_3155_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; lean_object* v_unused_3218_; lean_object* v_unused_3219_; 
v_unused_3217_ = lean_ctor_get(v_p_u2081_3155_, 2);
lean_dec(v_unused_3217_);
v_unused_3218_ = lean_ctor_get(v_p_u2081_3155_, 1);
lean_dec(v_unused_3218_);
v_unused_3219_ = lean_ctor_get(v_p_u2081_3155_, 0);
lean_dec(v_unused_3219_);
v___x_3210_ = v_p_u2081_3155_;
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
else
{
lean_dec(v_p_u2081_3155_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3176_, v_p_u2082_3156_, v_c_3157_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 2, v___x_3212_);
v___x_3214_ = v___x_3210_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3215_, 2, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC_go(lean_object* v_p_u2082_3220_, lean_object* v_c_3221_, lean_object* v_p_u2081_3222_, lean_object* v_acc_3223_){
_start:
{
if (lean_obj_tag(v_p_u2081_3222_) == 0)
{
lean_object* v_k_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v_k_3224_ = lean_ctor_get(v_p_u2081_3222_, 0);
lean_inc(v_k_3224_);
lean_dec_ref_known(v_p_u2081_3222_, 1);
lean_inc(v_c_3221_);
v___x_3225_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3224_, v_p_u2082_3220_, v_c_3221_);
lean_dec(v_k_3224_);
v___x_3226_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3223_, v___x_3225_, v_c_3221_);
return v___x_3226_;
}
else
{
lean_object* v_k_3227_; lean_object* v_v_3228_; lean_object* v_p_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v_k_3227_ = lean_ctor_get(v_p_u2081_3222_, 0);
lean_inc(v_k_3227_);
v_v_3228_ = lean_ctor_get(v_p_u2081_3222_, 1);
lean_inc(v_v_3228_);
v_p_3229_ = lean_ctor_get(v_p_u2081_3222_, 2);
lean_inc_ref(v_p_3229_);
lean_dec_ref_known(v_p_u2081_3222_, 3);
lean_inc_n(v_c_3221_, 2);
lean_inc_ref(v_p_u2082_3220_);
v___x_3230_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_3227_, v_v_3228_, v_p_u2082_3220_, v_c_3221_);
lean_dec(v_k_3227_);
v___x_3231_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3223_, v___x_3230_, v_c_3221_);
v_p_u2081_3222_ = v_p_3229_;
v_acc_3223_ = v___x_3231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC(lean_object* v_p_u2081_3233_, lean_object* v_p_u2082_3234_, lean_object* v_c_3235_){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3237_ = l_Lean_Grind_CommRing_Poly_mulC_go(v_p_u2082_3234_, v_c_3235_, v_p_u2081_3233_, v___x_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc_go(lean_object* v_p_u2082_3238_, lean_object* v_c_3239_, lean_object* v_p_u2081_3240_, lean_object* v_acc_3241_){
_start:
{
if (lean_obj_tag(v_p_u2081_3240_) == 0)
{
lean_object* v_k_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v_k_3242_ = lean_ctor_get(v_p_u2081_3240_, 0);
lean_inc(v_k_3242_);
lean_dec_ref_known(v_p_u2081_3240_, 1);
lean_inc(v_c_3239_);
v___x_3243_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3242_, v_p_u2082_3238_, v_c_3239_);
lean_dec(v_k_3242_);
v___x_3244_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3241_, v___x_3243_, v_c_3239_);
return v___x_3244_;
}
else
{
lean_object* v_k_3245_; lean_object* v_v_3246_; lean_object* v_p_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v_k_3245_ = lean_ctor_get(v_p_u2081_3240_, 0);
lean_inc(v_k_3245_);
v_v_3246_ = lean_ctor_get(v_p_u2081_3240_, 1);
lean_inc(v_v_3246_);
v_p_3247_ = lean_ctor_get(v_p_u2081_3240_, 2);
lean_inc_ref(v_p_3247_);
lean_dec_ref_known(v_p_u2081_3240_, 3);
lean_inc_n(v_c_3239_, 2);
lean_inc_ref(v_p_u2082_3238_);
v___x_3248_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3245_, v_v_3246_, v_p_u2082_3238_, v_c_3239_);
lean_dec(v_k_3245_);
v___x_3249_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3241_, v___x_3248_, v_c_3239_);
v_p_u2081_3240_ = v_p_3247_;
v_acc_3241_ = v___x_3249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc(lean_object* v_p_u2081_3251_, lean_object* v_p_u2082_3252_, lean_object* v_c_3253_){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3255_ = l_Lean_Grind_CommRing_Poly_mulC__nc_go(v_p_u2082_3252_, v_c_3253_, v_p_u2081_3251_, v___x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC(lean_object* v_p_3256_, lean_object* v_k_3257_, lean_object* v_c_3258_){
_start:
{
lean_object* v_zero_3259_; uint8_t v_isZero_3260_; 
v_zero_3259_ = lean_unsigned_to_nat(0u);
v_isZero_3260_ = lean_nat_dec_eq(v_k_3257_, v_zero_3259_);
if (v_isZero_3260_ == 1)
{
lean_object* v___x_3261_; 
lean_dec(v_c_3258_);
lean_dec_ref(v_p_3256_);
v___x_3261_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3261_;
}
else
{
lean_object* v_one_3262_; lean_object* v_n_3263_; uint8_t v___x_3264_; 
v_one_3262_ = lean_unsigned_to_nat(1u);
v_n_3263_ = lean_nat_sub(v_k_3257_, v_one_3262_);
v___x_3264_ = lean_nat_dec_eq(v_n_3263_, v_zero_3259_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_inc(v_c_3258_);
lean_inc_ref(v_p_3256_);
v___x_3265_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3256_, v_n_3263_, v_c_3258_);
lean_dec(v_n_3263_);
v___x_3266_ = l_Lean_Grind_CommRing_Poly_mulC(v_p_3256_, v___x_3265_, v_c_3258_);
return v___x_3266_;
}
else
{
lean_dec(v_n_3263_);
lean_dec(v_c_3258_);
return v_p_3256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC___boxed(lean_object* v_p_3267_, lean_object* v_k_3268_, lean_object* v_c_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3267_, v_k_3268_, v_c_3269_);
lean_dec(v_k_3268_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc(lean_object* v_p_3271_, lean_object* v_k_3272_, lean_object* v_c_3273_){
_start:
{
lean_object* v_zero_3274_; uint8_t v_isZero_3275_; 
v_zero_3274_ = lean_unsigned_to_nat(0u);
v_isZero_3275_ = lean_nat_dec_eq(v_k_3272_, v_zero_3274_);
if (v_isZero_3275_ == 1)
{
lean_object* v___x_3276_; 
lean_dec(v_c_3273_);
lean_dec_ref(v_p_3271_);
v___x_3276_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3276_;
}
else
{
lean_object* v_one_3277_; lean_object* v_n_3278_; uint8_t v___x_3279_; 
v_one_3277_ = lean_unsigned_to_nat(1u);
v_n_3278_ = lean_nat_sub(v_k_3272_, v_one_3277_);
v___x_3279_ = lean_nat_dec_eq(v_n_3278_, v_zero_3274_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_inc(v_c_3273_);
lean_inc_ref(v_p_3271_);
v___x_3280_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3271_, v_n_3278_, v_c_3273_);
lean_dec(v_n_3278_);
v___x_3281_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3280_, v_p_3271_, v_c_3273_);
return v___x_3281_;
}
else
{
lean_dec(v_n_3278_);
lean_dec(v_c_3273_);
return v_p_3271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc___boxed(lean_object* v_p_3282_, lean_object* v_k_3283_, lean_object* v_c_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3282_, v_k_3283_, v_c_3284_);
lean_dec(v_k_3283_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC_go(lean_object* v_c_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v_k_3289_; 
switch(lean_obj_tag(v_a_3287_))
{
case 1:
{
lean_object* v_k_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3303_; 
v_k_3293_ = lean_ctor_get(v_a_3287_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v_a_3287_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3295_ = v_a_3287_;
v_isShared_3296_ = v_isSharedCheck_3303_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_k_3293_);
lean_dec(v_a_3287_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3303_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3301_; 
v___x_3297_ = lean_nat_to_int(v_k_3293_);
v___x_3298_ = lean_nat_to_int(v_c_3286_);
v___x_3299_ = lean_int_emod(v___x_3297_, v___x_3298_);
lean_dec(v___x_3298_);
lean_dec(v___x_3297_);
if (v_isShared_3296_ == 0)
{
lean_ctor_set_tag(v___x_3295_, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3299_);
v___x_3301_ = v___x_3295_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3299_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
case 3:
{
lean_object* v_i_3304_; lean_object* v___x_3305_; 
lean_dec(v_c_3286_);
v_i_3304_ = lean_ctor_get(v_a_3287_, 0);
lean_inc(v_i_3304_);
lean_dec_ref_known(v_a_3287_, 1);
v___x_3305_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3304_);
return v___x_3305_;
}
case 4:
{
lean_object* v_a_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v_a_3306_ = lean_ctor_get(v_a_3287_, 0);
lean_inc_ref(v_a_3306_);
lean_dec_ref_known(v_a_3287_, 1);
v___x_3307_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3286_);
v___x_3308_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3286_, v_a_3306_);
v___x_3309_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3307_, v___x_3308_, v_c_3286_);
return v___x_3309_;
}
case 5:
{
lean_object* v_a_3310_; lean_object* v_b_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v_a_3310_ = lean_ctor_get(v_a_3287_, 0);
lean_inc_ref(v_a_3310_);
v_b_3311_ = lean_ctor_get(v_a_3287_, 1);
lean_inc_ref(v_b_3311_);
lean_dec_ref_known(v_a_3287_, 2);
lean_inc_n(v_c_3286_, 2);
v___x_3312_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3286_, v_a_3310_);
v___x_3313_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3286_, v_b_3311_);
v___x_3314_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3312_, v___x_3313_, v_c_3286_);
return v___x_3314_;
}
case 6:
{
lean_object* v_a_3315_; lean_object* v_b_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v_a_3315_ = lean_ctor_get(v_a_3287_, 0);
lean_inc_ref(v_a_3315_);
v_b_3316_ = lean_ctor_get(v_a_3287_, 1);
lean_inc_ref(v_b_3316_);
lean_dec_ref_known(v_a_3287_, 2);
lean_inc_n(v_c_3286_, 3);
v___x_3317_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3286_, v_a_3315_);
v___x_3318_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_3319_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3286_, v_b_3316_);
v___x_3320_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3318_, v___x_3319_, v_c_3286_);
v___x_3321_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3317_, v___x_3320_, v_c_3286_);
return v___x_3321_;
}
case 7:
{
lean_object* v_a_3322_; lean_object* v_b_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v_a_3322_ = lean_ctor_get(v_a_3287_, 0);
lean_inc_ref(v_a_3322_);
v_b_3323_ = lean_ctor_get(v_a_3287_, 1);
lean_inc_ref(v_b_3323_);
lean_dec_ref_known(v_a_3287_, 2);
lean_inc_n(v_c_3286_, 2);
v___x_3324_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3286_, v_a_3322_);
v___x_3325_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3286_, v_b_3323_);
v___x_3326_ = l_Lean_Grind_CommRing_Poly_mulC(v___x_3324_, v___x_3325_, v_c_3286_);
return v___x_3326_;
}
case 8:
{
lean_object* v_a_3327_; lean_object* v_k_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3355_; 
v_a_3327_ = lean_ctor_get(v_a_3287_, 0);
v_k_3328_ = lean_ctor_get(v_a_3287_, 1);
v_isSharedCheck_3355_ = !lean_is_exclusive(v_a_3287_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3330_ = v_a_3287_;
v_isShared_3331_ = v_isSharedCheck_3355_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_k_3328_);
lean_inc(v_a_3327_);
lean_dec(v_a_3287_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3355_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; uint8_t v___x_3333_; 
v___x_3332_ = lean_unsigned_to_nat(0u);
v___x_3333_ = lean_nat_dec_eq(v_k_3328_, v___x_3332_);
if (v___x_3333_ == 0)
{
switch(lean_obj_tag(v_a_3327_))
{
case 0:
{
lean_object* v_k_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3344_; 
lean_del_object(v___x_3330_);
v_k_3334_ = lean_ctor_get(v_a_3327_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_a_3327_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3336_ = v_a_3327_;
v_isShared_3337_ = v_isSharedCheck_3344_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_k_3334_);
lean_dec(v_a_3327_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3344_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3338_ = l_Int_pow(v_k_3334_, v_k_3328_);
lean_dec(v_k_3328_);
lean_dec(v_k_3334_);
v___x_3339_ = lean_nat_to_int(v_c_3286_);
v___x_3340_ = lean_int_emod(v___x_3338_, v___x_3339_);
lean_dec(v___x_3339_);
lean_dec(v___x_3338_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3340_);
v___x_3342_ = v___x_3336_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
case 3:
{
lean_object* v_i_3345_; lean_object* v___x_3347_; 
lean_dec(v_c_3286_);
v_i_3345_ = lean_ctor_get(v_a_3327_, 0);
lean_inc(v_i_3345_);
lean_dec_ref_known(v_a_3327_, 1);
if (v_isShared_3331_ == 0)
{
lean_ctor_set_tag(v___x_3330_, 0);
lean_ctor_set(v___x_3330_, 0, v_i_3345_);
v___x_3347_ = v___x_3330_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_i_3345_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_k_3328_);
v___x_3347_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = lean_box(0);
v___x_3349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3347_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3350_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3349_);
return v___x_3350_;
}
}
default: 
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_del_object(v___x_3330_);
lean_inc(v_c_3286_);
v___x_3352_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3286_, v_a_3327_);
v___x_3353_ = l_Lean_Grind_CommRing_Poly_powC(v___x_3352_, v_k_3328_, v_c_3286_);
lean_dec(v_k_3328_);
return v___x_3353_;
}
}
}
else
{
lean_object* v___x_3354_; 
lean_del_object(v___x_3330_);
lean_dec(v_k_3328_);
lean_dec_ref(v_a_3327_);
lean_dec(v_c_3286_);
v___x_3354_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3354_;
}
}
}
default: 
{
lean_object* v_k_3356_; 
v_k_3356_ = lean_ctor_get(v_a_3287_, 0);
lean_inc(v_k_3356_);
lean_dec_ref(v_a_3287_);
v_k_3289_ = v_k_3356_;
goto v___jp_3288_;
}
}
v___jp_3288_:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3290_ = lean_nat_to_int(v_c_3286_);
v___x_3291_ = lean_int_emod(v_k_3289_, v___x_3290_);
lean_dec(v___x_3290_);
lean_dec(v_k_3289_);
v___x_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
return v___x_3292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC(lean_object* v_e_3357_, lean_object* v_c_3358_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3358_, v_e_3357_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(lean_object* v_c_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v_k_3363_; 
switch(lean_obj_tag(v_a_3361_))
{
case 1:
{
lean_object* v_k_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3377_; 
v_k_3367_ = lean_ctor_get(v_a_3361_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v_a_3361_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3369_ = v_a_3361_;
v_isShared_3370_ = v_isSharedCheck_3377_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_k_3367_);
lean_dec(v_a_3361_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3377_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3371_ = lean_nat_to_int(v_k_3367_);
v___x_3372_ = lean_nat_to_int(v_c_3360_);
v___x_3373_ = lean_int_emod(v___x_3371_, v___x_3372_);
lean_dec(v___x_3372_);
lean_dec(v___x_3371_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set_tag(v___x_3369_, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3373_);
v___x_3375_ = v___x_3369_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
case 3:
{
lean_object* v_i_3378_; lean_object* v___x_3379_; 
lean_dec(v_c_3360_);
v_i_3378_ = lean_ctor_get(v_a_3361_, 0);
lean_inc(v_i_3378_);
lean_dec_ref_known(v_a_3361_, 1);
v___x_3379_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3378_);
return v___x_3379_;
}
case 4:
{
lean_object* v_a_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v_a_3380_ = lean_ctor_get(v_a_3361_, 0);
lean_inc_ref(v_a_3380_);
lean_dec_ref_known(v_a_3361_, 1);
v___x_3381_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3360_);
v___x_3382_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3360_, v_a_3380_);
v___x_3383_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3381_, v___x_3382_, v_c_3360_);
return v___x_3383_;
}
case 5:
{
lean_object* v_a_3384_; lean_object* v_b_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_a_3384_ = lean_ctor_get(v_a_3361_, 0);
lean_inc_ref(v_a_3384_);
v_b_3385_ = lean_ctor_get(v_a_3361_, 1);
lean_inc_ref(v_b_3385_);
lean_dec_ref_known(v_a_3361_, 2);
lean_inc_n(v_c_3360_, 2);
v___x_3386_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3360_, v_a_3384_);
v___x_3387_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3360_, v_b_3385_);
v___x_3388_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3386_, v___x_3387_, v_c_3360_);
return v___x_3388_;
}
case 6:
{
lean_object* v_a_3389_; lean_object* v_b_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v_a_3389_ = lean_ctor_get(v_a_3361_, 0);
lean_inc_ref(v_a_3389_);
v_b_3390_ = lean_ctor_get(v_a_3361_, 1);
lean_inc_ref(v_b_3390_);
lean_dec_ref_known(v_a_3361_, 2);
lean_inc_n(v_c_3360_, 3);
v___x_3391_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3360_, v_a_3389_);
v___x_3392_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_3393_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3360_, v_b_3390_);
v___x_3394_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3392_, v___x_3393_, v_c_3360_);
v___x_3395_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3391_, v___x_3394_, v_c_3360_);
return v___x_3395_;
}
case 7:
{
lean_object* v_a_3396_; lean_object* v_b_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v_a_3396_ = lean_ctor_get(v_a_3361_, 0);
lean_inc_ref(v_a_3396_);
v_b_3397_ = lean_ctor_get(v_a_3361_, 1);
lean_inc_ref(v_b_3397_);
lean_dec_ref_known(v_a_3361_, 2);
lean_inc_n(v_c_3360_, 2);
v___x_3398_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3360_, v_a_3396_);
v___x_3399_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3360_, v_b_3397_);
v___x_3400_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3398_, v___x_3399_, v_c_3360_);
return v___x_3400_;
}
case 8:
{
lean_object* v_a_3401_; lean_object* v_k_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3429_; 
v_a_3401_ = lean_ctor_get(v_a_3361_, 0);
v_k_3402_ = lean_ctor_get(v_a_3361_, 1);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_a_3361_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3404_ = v_a_3361_;
v_isShared_3405_ = v_isSharedCheck_3429_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_k_3402_);
lean_inc(v_a_3401_);
lean_dec(v_a_3361_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3429_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3406_ = lean_unsigned_to_nat(0u);
v___x_3407_ = lean_nat_dec_eq(v_k_3402_, v___x_3406_);
if (v___x_3407_ == 0)
{
switch(lean_obj_tag(v_a_3401_))
{
case 0:
{
lean_object* v_k_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3418_; 
lean_del_object(v___x_3404_);
v_k_3408_ = lean_ctor_get(v_a_3401_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_a_3401_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3410_ = v_a_3401_;
v_isShared_3411_ = v_isSharedCheck_3418_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_k_3408_);
lean_dec(v_a_3401_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3418_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3416_; 
v___x_3412_ = l_Int_pow(v_k_3408_, v_k_3402_);
lean_dec(v_k_3402_);
lean_dec(v_k_3408_);
v___x_3413_ = lean_nat_to_int(v_c_3360_);
v___x_3414_ = lean_int_emod(v___x_3412_, v___x_3413_);
lean_dec(v___x_3413_);
lean_dec(v___x_3412_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v___x_3414_);
v___x_3416_ = v___x_3410_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
case 3:
{
lean_object* v_i_3419_; lean_object* v___x_3421_; 
lean_dec(v_c_3360_);
v_i_3419_ = lean_ctor_get(v_a_3401_, 0);
lean_inc(v_i_3419_);
lean_dec_ref_known(v_a_3401_, 1);
if (v_isShared_3405_ == 0)
{
lean_ctor_set_tag(v___x_3404_, 0);
lean_ctor_set(v___x_3404_, 0, v_i_3419_);
v___x_3421_ = v___x_3404_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_i_3419_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_k_3402_);
v___x_3421_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = lean_box(0);
v___x_3423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3423_);
return v___x_3424_;
}
}
default: 
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
lean_del_object(v___x_3404_);
lean_inc(v_c_3360_);
v___x_3426_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3360_, v_a_3401_);
v___x_3427_ = l_Lean_Grind_CommRing_Poly_powC__nc(v___x_3426_, v_k_3402_, v_c_3360_);
lean_dec(v_k_3402_);
return v___x_3427_;
}
}
}
else
{
lean_object* v___x_3428_; 
lean_del_object(v___x_3404_);
lean_dec(v_k_3402_);
lean_dec_ref(v_a_3401_);
lean_dec(v_c_3360_);
v___x_3428_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3428_;
}
}
}
default: 
{
lean_object* v_k_3430_; 
v_k_3430_ = lean_ctor_get(v_a_3361_, 0);
lean_inc(v_k_3430_);
lean_dec_ref(v_a_3361_);
v_k_3363_ = v_k_3430_;
goto v___jp_3362_;
}
}
v___jp_3362_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3364_ = lean_nat_to_int(v_c_3360_);
v___x_3365_ = lean_int_emod(v_k_3363_, v___x_3364_);
lean_dec(v___x_3364_);
lean_dec(v_k_3363_);
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
return v___x_3366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc(lean_object* v_e_3431_, lean_object* v_c_3432_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3432_, v_e_3431_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter___redArg(lean_object* v_x_3434_, lean_object* v_h__1_3435_){
_start:
{
lean_object* v_x_3436_; lean_object* v_k_3437_; lean_object* v___x_3438_; 
v_x_3436_ = lean_ctor_get(v_x_3434_, 0);
lean_inc(v_x_3436_);
v_k_3437_ = lean_ctor_get(v_x_3434_, 1);
lean_inc(v_k_3437_);
lean_dec_ref(v_x_3434_);
v___x_3438_ = lean_apply_2(v_h__1_3435_, v_x_3436_, v_k_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter(lean_object* v_motive_3439_, lean_object* v_x_3440_, lean_object* v_h__1_3441_){
_start:
{
lean_object* v_x_3442_; lean_object* v_k_3443_; lean_object* v___x_3444_; 
v_x_3442_ = lean_ctor_get(v_x_3440_, 0);
lean_inc(v_x_3442_);
v_k_3443_ = lean_ctor_get(v_x_3440_, 1);
lean_inc(v_k_3443_);
lean_dec_ref(v_x_3440_);
v___x_3444_ = lean_apply_2(v_h__1_3441_, v_x_3442_, v_k_3443_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(lean_object* v_k_3445_, lean_object* v_h__1_3446_, lean_object* v_h__2_3447_, lean_object* v_h__3_3448_){
_start:
{
lean_object* v___x_3449_; uint8_t v___x_3450_; 
v___x_3449_ = lean_unsigned_to_nat(0u);
v___x_3450_ = lean_nat_dec_eq(v_k_3445_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; uint8_t v___x_3452_; 
lean_dec(v_h__1_3446_);
v___x_3451_ = lean_unsigned_to_nat(1u);
v___x_3452_ = lean_nat_dec_eq(v_k_3445_, v___x_3451_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; 
lean_dec(v_h__2_3447_);
v___x_3453_ = lean_apply_3(v_h__3_3448_, v_k_3445_, lean_box(0), lean_box(0));
return v___x_3453_;
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
lean_dec(v_h__3_3448_);
lean_dec(v_k_3445_);
v___x_3454_ = lean_box(0);
v___x_3455_ = lean_apply_1(v_h__2_3447_, v___x_3454_);
return v___x_3455_;
}
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
lean_dec(v_h__3_3448_);
lean_dec(v_h__2_3447_);
lean_dec(v_k_3445_);
v___x_3456_ = lean_box(0);
v___x_3457_ = lean_apply_1(v_h__1_3446_, v___x_3456_);
return v___x_3457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(lean_object* v_motive_3458_, lean_object* v_k_3459_, lean_object* v_h__1_3460_, lean_object* v_h__2_3461_, lean_object* v_h__3_3462_){
_start:
{
lean_object* v___x_3463_; uint8_t v___x_3464_; 
v___x_3463_ = lean_unsigned_to_nat(0u);
v___x_3464_ = lean_nat_dec_eq(v_k_3459_, v___x_3463_);
if (v___x_3464_ == 0)
{
lean_object* v___x_3465_; uint8_t v___x_3466_; 
lean_dec(v_h__1_3460_);
v___x_3465_ = lean_unsigned_to_nat(1u);
v___x_3466_ = lean_nat_dec_eq(v_k_3459_, v___x_3465_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; 
lean_dec(v_h__2_3461_);
v___x_3467_ = lean_apply_3(v_h__3_3462_, v_k_3459_, lean_box(0), lean_box(0));
return v___x_3467_;
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
lean_dec(v_h__3_3462_);
lean_dec(v_k_3459_);
v___x_3468_ = lean_box(0);
v___x_3469_ = lean_apply_1(v_h__2_3461_, v___x_3468_);
return v___x_3469_;
}
}
else
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_dec(v_h__3_3462_);
lean_dec(v_h__2_3461_);
lean_dec(v_k_3459_);
v___x_3470_ = lean_box(0);
v___x_3471_ = lean_apply_1(v_h__1_3460_, v___x_3470_);
return v___x_3471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(lean_object* v_m_u2081_3472_, lean_object* v_h__1_3473_, lean_object* v_h__2_3474_, lean_object* v_h__3_3475_){
_start:
{
if (lean_obj_tag(v_m_u2081_3472_) == 0)
{
lean_object* v___x_3476_; lean_object* v___x_3477_; 
lean_dec(v_h__3_3475_);
lean_dec(v_h__2_3474_);
v___x_3476_ = lean_box(0);
v___x_3477_ = lean_apply_1(v_h__1_3473_, v___x_3476_);
return v___x_3477_;
}
else
{
lean_object* v_m_3478_; 
lean_dec(v_h__1_3473_);
v_m_3478_ = lean_ctor_get(v_m_u2081_3472_, 1);
if (lean_obj_tag(v_m_3478_) == 0)
{
lean_object* v_p_3479_; lean_object* v___x_3480_; 
lean_dec(v_h__3_3475_);
v_p_3479_ = lean_ctor_get(v_m_u2081_3472_, 0);
lean_inc_ref(v_p_3479_);
lean_dec_ref_known(v_m_u2081_3472_, 2);
v___x_3480_ = lean_apply_1(v_h__2_3474_, v_p_3479_);
return v___x_3480_;
}
else
{
lean_object* v_p_3481_; lean_object* v___x_3482_; 
lean_inc(v_m_3478_);
lean_dec(v_h__2_3474_);
v_p_3481_ = lean_ctor_get(v_m_u2081_3472_, 0);
lean_inc_ref(v_p_3481_);
lean_dec_ref_known(v_m_u2081_3472_, 2);
v___x_3482_ = lean_apply_3(v_h__3_3475_, v_p_3481_, v_m_3478_, lean_box(0));
return v___x_3482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(lean_object* v_motive_3483_, lean_object* v_m_u2081_3484_, lean_object* v_h__1_3485_, lean_object* v_h__2_3486_, lean_object* v_h__3_3487_){
_start:
{
if (lean_obj_tag(v_m_u2081_3484_) == 0)
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
lean_dec(v_h__3_3487_);
lean_dec(v_h__2_3486_);
v___x_3488_ = lean_box(0);
v___x_3489_ = lean_apply_1(v_h__1_3485_, v___x_3488_);
return v___x_3489_;
}
else
{
lean_object* v_m_3490_; 
lean_dec(v_h__1_3485_);
v_m_3490_ = lean_ctor_get(v_m_u2081_3484_, 1);
if (lean_obj_tag(v_m_3490_) == 0)
{
lean_object* v_p_3491_; lean_object* v___x_3492_; 
lean_dec(v_h__3_3487_);
v_p_3491_ = lean_ctor_get(v_m_u2081_3484_, 0);
lean_inc_ref(v_p_3491_);
lean_dec_ref_known(v_m_u2081_3484_, 2);
v___x_3492_ = lean_apply_1(v_h__2_3486_, v_p_3491_);
return v___x_3492_;
}
else
{
lean_object* v_p_3493_; lean_object* v___x_3494_; 
lean_inc(v_m_3490_);
lean_dec(v_h__2_3486_);
v_p_3493_ = lean_ctor_get(v_m_u2081_3484_, 0);
lean_inc_ref(v_p_3493_);
lean_dec_ref_known(v_m_u2081_3484_, 2);
v___x_3494_ = lean_apply_3(v_h__3_3487_, v_p_3493_, v_m_3490_, lean_box(0));
return v___x_3494_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(uint8_t v_a_3495_, lean_object* v_h__1_3496_, lean_object* v_h__2_3497_){
_start:
{
if (v_a_3495_ == 1)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
lean_dec(v_h__2_3497_);
v___x_3498_ = lean_box(0);
v___x_3499_ = lean_apply_1(v_h__1_3496_, v___x_3498_);
return v___x_3499_;
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
lean_dec(v_h__1_3496_);
v___x_3500_ = lean_box(v_a_3495_);
v___x_3501_ = lean_apply_2(v_h__2_3497_, v___x_3500_, lean_box(0));
return v___x_3501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object* v_a_3502_, lean_object* v_h__1_3503_, lean_object* v_h__2_3504_){
_start:
{
uint8_t v_a_13__boxed_3505_; lean_object* v_res_3506_; 
v_a_13__boxed_3505_ = lean_unbox(v_a_3502_);
v_res_3506_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(v_a_13__boxed_3505_, v_h__1_3503_, v_h__2_3504_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(lean_object* v_motive_3507_, uint8_t v_a_3508_, lean_object* v_h__1_3509_, lean_object* v_h__2_3510_){
_start:
{
if (v_a_3508_ == 1)
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_dec(v_h__2_3510_);
v___x_3511_ = lean_box(0);
v___x_3512_ = lean_apply_1(v_h__1_3509_, v___x_3511_);
return v___x_3512_;
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
lean_dec(v_h__1_3509_);
v___x_3513_ = lean_box(v_a_3508_);
v___x_3514_ = lean_apply_2(v_h__2_3510_, v___x_3513_, lean_box(0));
return v___x_3514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___boxed(lean_object* v_motive_3515_, lean_object* v_a_3516_, lean_object* v_h__1_3517_, lean_object* v_h__2_3518_){
_start:
{
uint8_t v_a_24__boxed_3519_; lean_object* v_res_3520_; 
v_a_24__boxed_3519_ = lean_unbox(v_a_3516_);
v_res_3520_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(v_motive_3515_, v_a_24__boxed_3519_, v_h__1_3517_, v_h__2_3518_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(lean_object* v_p_3521_, lean_object* v_h__1_3522_, lean_object* v_h__2_3523_, lean_object* v_h__3_3524_){
_start:
{
if (lean_obj_tag(v_p_3521_) == 0)
{
lean_object* v_k_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; 
lean_dec(v_h__3_3524_);
v_k_3525_ = lean_ctor_get(v_p_3521_, 0);
lean_inc(v_k_3525_);
lean_dec_ref_known(v_p_3521_, 1);
v___x_3526_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3527_ = lean_int_dec_eq(v_k_3525_, v___x_3526_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; 
lean_dec(v_h__1_3522_);
v___x_3528_ = lean_apply_2(v_h__2_3523_, v_k_3525_, lean_box(0));
return v___x_3528_;
}
else
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_dec(v_k_3525_);
lean_dec(v_h__2_3523_);
v___x_3529_ = lean_box(0);
v___x_3530_ = lean_apply_1(v_h__1_3522_, v___x_3529_);
return v___x_3530_;
}
}
else
{
lean_object* v_k_3531_; lean_object* v_v_3532_; lean_object* v_p_3533_; lean_object* v___x_3534_; 
lean_dec(v_h__2_3523_);
lean_dec(v_h__1_3522_);
v_k_3531_ = lean_ctor_get(v_p_3521_, 0);
lean_inc(v_k_3531_);
v_v_3532_ = lean_ctor_get(v_p_3521_, 1);
lean_inc(v_v_3532_);
v_p_3533_ = lean_ctor_get(v_p_3521_, 2);
lean_inc_ref(v_p_3533_);
lean_dec_ref_known(v_p_3521_, 3);
v___x_3534_ = lean_apply_3(v_h__3_3524_, v_k_3531_, v_v_3532_, v_p_3533_);
return v___x_3534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(lean_object* v_motive_3535_, lean_object* v_p_3536_, lean_object* v_h__1_3537_, lean_object* v_h__2_3538_, lean_object* v_h__3_3539_){
_start:
{
if (lean_obj_tag(v_p_3536_) == 0)
{
lean_object* v_k_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
lean_dec(v_h__3_3539_);
v_k_3540_ = lean_ctor_get(v_p_3536_, 0);
lean_inc(v_k_3540_);
lean_dec_ref_known(v_p_3536_, 1);
v___x_3541_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3542_ = lean_int_dec_eq(v_k_3540_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; 
lean_dec(v_h__1_3537_);
v___x_3543_ = lean_apply_2(v_h__2_3538_, v_k_3540_, lean_box(0));
return v___x_3543_;
}
else
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
lean_dec(v_k_3540_);
lean_dec(v_h__2_3538_);
v___x_3544_ = lean_box(0);
v___x_3545_ = lean_apply_1(v_h__1_3537_, v___x_3544_);
return v___x_3545_;
}
}
else
{
lean_object* v_k_3546_; lean_object* v_v_3547_; lean_object* v_p_3548_; lean_object* v___x_3549_; 
lean_dec(v_h__2_3538_);
lean_dec(v_h__1_3537_);
v_k_3546_ = lean_ctor_get(v_p_3536_, 0);
lean_inc(v_k_3546_);
v_v_3547_ = lean_ctor_get(v_p_3536_, 1);
lean_inc(v_v_3547_);
v_p_3548_ = lean_ctor_get(v_p_3536_, 2);
lean_inc_ref(v_p_3548_);
lean_dec_ref_known(v_p_3536_, 3);
v___x_3549_ = lean_apply_3(v_h__3_3539_, v_k_3546_, v_v_3547_, v_p_3548_);
return v___x_3549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object* v_k_3550_, lean_object* v_h__1_3551_, lean_object* v_h__2_3552_, lean_object* v_h__3_3553_){
_start:
{
lean_object* v_zero_3554_; uint8_t v_isZero_3555_; 
v_zero_3554_ = lean_unsigned_to_nat(0u);
v_isZero_3555_ = lean_nat_dec_eq(v_k_3550_, v_zero_3554_);
if (v_isZero_3555_ == 1)
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
lean_dec(v_h__3_3553_);
lean_dec(v_h__2_3552_);
v___x_3556_ = lean_box(0);
v___x_3557_ = lean_apply_1(v_h__1_3551_, v___x_3556_);
return v___x_3557_;
}
else
{
lean_object* v_one_3558_; lean_object* v_n_3559_; uint8_t v___x_3560_; 
lean_dec(v_h__1_3551_);
v_one_3558_ = lean_unsigned_to_nat(1u);
v_n_3559_ = lean_nat_sub(v_k_3550_, v_one_3558_);
v___x_3560_ = lean_nat_dec_eq(v_n_3559_, v_zero_3554_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; 
lean_dec(v_h__2_3552_);
v___x_3561_ = lean_apply_2(v_h__3_3553_, v_n_3559_, lean_box(0));
return v___x_3561_;
}
else
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
lean_dec(v_n_3559_);
lean_dec(v_h__3_3553_);
v___x_3562_ = lean_box(0);
v___x_3563_ = lean_apply_1(v_h__2_3552_, v___x_3562_);
return v___x_3563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object* v_k_3564_, lean_object* v_h__1_3565_, lean_object* v_h__2_3566_, lean_object* v_h__3_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(v_k_3564_, v_h__1_3565_, v_h__2_3566_, v_h__3_3567_);
lean_dec(v_k_3564_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object* v_motive_3569_, lean_object* v_k_3570_, lean_object* v_h__1_3571_, lean_object* v_h__2_3572_, lean_object* v_h__3_3573_){
_start:
{
lean_object* v_zero_3574_; uint8_t v_isZero_3575_; 
v_zero_3574_ = lean_unsigned_to_nat(0u);
v_isZero_3575_ = lean_nat_dec_eq(v_k_3570_, v_zero_3574_);
if (v_isZero_3575_ == 1)
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
lean_dec(v_h__3_3573_);
lean_dec(v_h__2_3572_);
v___x_3576_ = lean_box(0);
v___x_3577_ = lean_apply_1(v_h__1_3571_, v___x_3576_);
return v___x_3577_;
}
else
{
lean_object* v_one_3578_; lean_object* v_n_3579_; uint8_t v___x_3580_; 
lean_dec(v_h__1_3571_);
v_one_3578_ = lean_unsigned_to_nat(1u);
v_n_3579_ = lean_nat_sub(v_k_3570_, v_one_3578_);
v___x_3580_ = lean_nat_dec_eq(v_n_3579_, v_zero_3574_);
if (v___x_3580_ == 0)
{
lean_object* v___x_3581_; 
lean_dec(v_h__2_3572_);
v___x_3581_ = lean_apply_2(v_h__3_3573_, v_n_3579_, lean_box(0));
return v___x_3581_;
}
else
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
lean_dec(v_n_3579_);
lean_dec(v_h__3_3573_);
v___x_3582_ = lean_box(0);
v___x_3583_ = lean_apply_1(v_h__2_3572_, v___x_3582_);
return v___x_3583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object* v_motive_3584_, lean_object* v_k_3585_, lean_object* v_h__1_3586_, lean_object* v_h__2_3587_, lean_object* v_h__3_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(v_motive_3584_, v_k_3585_, v_h__1_3586_, v_h__2_3587_, v_h__3_3588_);
lean_dec(v_k_3585_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(lean_object* v_x_3590_, lean_object* v_h__1_3591_, lean_object* v_h__2_3592_, lean_object* v_h__3_3593_, lean_object* v_h__4_3594_, lean_object* v_h__5_3595_, lean_object* v_h__6_3596_, lean_object* v_h__7_3597_, lean_object* v_h__8_3598_, lean_object* v_h__9_3599_){
_start:
{
switch(lean_obj_tag(v_x_3590_))
{
case 0:
{
lean_object* v_k_3600_; lean_object* v___x_3601_; 
lean_dec(v_h__9_3599_);
lean_dec(v_h__8_3598_);
lean_dec(v_h__7_3597_);
lean_dec(v_h__6_3596_);
lean_dec(v_h__5_3595_);
lean_dec(v_h__4_3594_);
lean_dec(v_h__3_3593_);
lean_dec(v_h__2_3592_);
v_k_3600_ = lean_ctor_get(v_x_3590_, 0);
lean_inc(v_k_3600_);
lean_dec_ref_known(v_x_3590_, 1);
v___x_3601_ = lean_apply_1(v_h__1_3591_, v_k_3600_);
return v___x_3601_;
}
case 1:
{
lean_object* v_k_3602_; lean_object* v___x_3603_; 
lean_dec(v_h__9_3599_);
lean_dec(v_h__8_3598_);
lean_dec(v_h__7_3597_);
lean_dec(v_h__6_3596_);
lean_dec(v_h__5_3595_);
lean_dec(v_h__4_3594_);
lean_dec(v_h__3_3593_);
lean_dec(v_h__1_3591_);
v_k_3602_ = lean_ctor_get(v_x_3590_, 0);
lean_inc(v_k_3602_);
lean_dec_ref_known(v_x_3590_, 1);
v___x_3603_ = lean_apply_1(v_h__2_3592_, v_k_3602_);
return v___x_3603_;
}
case 2:
{
lean_object* v_k_3604_; lean_object* v___x_3605_; 
lean_dec(v_h__9_3599_);
lean_dec(v_h__8_3598_);
lean_dec(v_h__7_3597_);
lean_dec(v_h__6_3596_);
lean_dec(v_h__5_3595_);
lean_dec(v_h__4_3594_);
lean_dec(v_h__2_3592_);
lean_dec(v_h__1_3591_);
v_k_3604_ = lean_ctor_get(v_x_3590_, 0);
lean_inc(v_k_3604_);
lean_dec_ref_known(v_x_3590_, 1);
v___x_3605_ = lean_apply_1(v_h__3_3593_, v_k_3604_);
return v___x_3605_;
}
case 3:
{
lean_object* v_i_3606_; lean_object* v___x_3607_; 
lean_dec(v_h__9_3599_);
lean_dec(v_h__8_3598_);
lean_dec(v_h__7_3597_);
lean_dec(v_h__6_3596_);
lean_dec(v_h__5_3595_);
lean_dec(v_h__3_3593_);
lean_dec(v_h__2_3592_);
lean_dec(v_h__1_3591_);
v_i_3606_ = lean_ctor_get(v_x_3590_, 0);
lean_inc(v_i_3606_);
lean_dec_ref_known(v_x_3590_, 1);
v___x_3607_ = lean_apply_1(v_h__4_3594_, v_i_3606_);
return v___x_3607_;
}
case 4:
{
lean_object* v_a_3608_; lean_object* v___x_3609_; 
lean_dec(v_h__9_3599_);
lean_dec(v_h__8_3598_);
lean_dec(v_h__6_3596_);
lean_dec(v_h__5_3595_);
lean_dec(v_h__4_3594_);
lean_dec(v_h__3_3593_);
lean_dec(v_h__2_3592_);
lean_dec(v_h__1_3591_);
v_a_3608_ = lean_ctor_get(v_x_3590_, 0);
lean_inc_ref(v_a_3608_);
lean_dec_ref_known(v_x_3590_, 1);
v___x_3609_ = lean_apply_1(v_h__7_3597_, v_a_3608_);
return v___x_3609_;
}
case 5:
{
lean_object* v_a_3610_; lean_object* v_b_3611_; lean_object* v___x_3612_; 
lean_dec(v_h__9_3599_);
lean_dec(v_h__8_3598_);
lean_dec(v_h__7_3597_);
lean_dec(v_h__6_3596_);
lean_dec(v_h__4_3594_);
lean_dec(v_h__3_3593_);
lean_dec(v_h__2_3592_);
lean_dec(v_h__1_3591_);
v_a_3610_ = lean_ctor_get(v_x_3590_, 0);
lean_inc_ref(v_a_3610_);
v_b_3611_ = lean_ctor_get(v_x_3590_, 1);
lean_inc_ref(v_b_3611_);
lean_dec_ref_known(v_x_3590_, 2);
v___x_3612_ = lean_apply_2(v_h__5_3595_, v_a_3610_, v_b_3611_);
return v___x_3612_;
}
case 6:
{
lean_object* v_a_3613_; lean_object* v_b_3614_; lean_object* v___x_3615_; 
lean_dec(v_h__9_3599_);
lean_dec(v_h__7_3597_);
lean_dec(v_h__6_3596_);
lean_dec(v_h__5_3595_);
lean_dec(v_h__4_3594_);
lean_dec(v_h__3_3593_);
lean_dec(v_h__2_3592_);
lean_dec(v_h__1_3591_);
v_a_3613_ = lean_ctor_get(v_x_3590_, 0);
lean_inc_ref(v_a_3613_);
v_b_3614_ = lean_ctor_get(v_x_3590_, 1);
lean_inc_ref(v_b_3614_);
lean_dec_ref_known(v_x_3590_, 2);
v___x_3615_ = lean_apply_2(v_h__8_3598_, v_a_3613_, v_b_3614_);
return v___x_3615_;
}
case 7:
{
lean_object* v_a_3616_; lean_object* v_b_3617_; lean_object* v___x_3618_; 
lean_dec(v_h__9_3599_);
lean_dec(v_h__8_3598_);
lean_dec(v_h__7_3597_);
lean_dec(v_h__5_3595_);
lean_dec(v_h__4_3594_);
lean_dec(v_h__3_3593_);
lean_dec(v_h__2_3592_);
lean_dec(v_h__1_3591_);
v_a_3616_ = lean_ctor_get(v_x_3590_, 0);
lean_inc_ref(v_a_3616_);
v_b_3617_ = lean_ctor_get(v_x_3590_, 1);
lean_inc_ref(v_b_3617_);
lean_dec_ref_known(v_x_3590_, 2);
v___x_3618_ = lean_apply_2(v_h__6_3596_, v_a_3616_, v_b_3617_);
return v___x_3618_;
}
default: 
{
lean_object* v_a_3619_; lean_object* v_k_3620_; lean_object* v___x_3621_; 
lean_dec(v_h__8_3598_);
lean_dec(v_h__7_3597_);
lean_dec(v_h__6_3596_);
lean_dec(v_h__5_3595_);
lean_dec(v_h__4_3594_);
lean_dec(v_h__3_3593_);
lean_dec(v_h__2_3592_);
lean_dec(v_h__1_3591_);
v_a_3619_ = lean_ctor_get(v_x_3590_, 0);
lean_inc_ref(v_a_3619_);
v_k_3620_ = lean_ctor_get(v_x_3590_, 1);
lean_inc(v_k_3620_);
lean_dec_ref_known(v_x_3590_, 2);
v___x_3621_ = lean_apply_2(v_h__9_3599_, v_a_3619_, v_k_3620_);
return v___x_3621_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter(lean_object* v_motive_3622_, lean_object* v_x_3623_, lean_object* v_h__1_3624_, lean_object* v_h__2_3625_, lean_object* v_h__3_3626_, lean_object* v_h__4_3627_, lean_object* v_h__5_3628_, lean_object* v_h__6_3629_, lean_object* v_h__7_3630_, lean_object* v_h__8_3631_, lean_object* v_h__9_3632_){
_start:
{
switch(lean_obj_tag(v_x_3623_))
{
case 0:
{
lean_object* v_k_3633_; lean_object* v___x_3634_; 
lean_dec(v_h__9_3632_);
lean_dec(v_h__8_3631_);
lean_dec(v_h__7_3630_);
lean_dec(v_h__6_3629_);
lean_dec(v_h__5_3628_);
lean_dec(v_h__4_3627_);
lean_dec(v_h__3_3626_);
lean_dec(v_h__2_3625_);
v_k_3633_ = lean_ctor_get(v_x_3623_, 0);
lean_inc(v_k_3633_);
lean_dec_ref_known(v_x_3623_, 1);
v___x_3634_ = lean_apply_1(v_h__1_3624_, v_k_3633_);
return v___x_3634_;
}
case 1:
{
lean_object* v_k_3635_; lean_object* v___x_3636_; 
lean_dec(v_h__9_3632_);
lean_dec(v_h__8_3631_);
lean_dec(v_h__7_3630_);
lean_dec(v_h__6_3629_);
lean_dec(v_h__5_3628_);
lean_dec(v_h__4_3627_);
lean_dec(v_h__3_3626_);
lean_dec(v_h__1_3624_);
v_k_3635_ = lean_ctor_get(v_x_3623_, 0);
lean_inc(v_k_3635_);
lean_dec_ref_known(v_x_3623_, 1);
v___x_3636_ = lean_apply_1(v_h__2_3625_, v_k_3635_);
return v___x_3636_;
}
case 2:
{
lean_object* v_k_3637_; lean_object* v___x_3638_; 
lean_dec(v_h__9_3632_);
lean_dec(v_h__8_3631_);
lean_dec(v_h__7_3630_);
lean_dec(v_h__6_3629_);
lean_dec(v_h__5_3628_);
lean_dec(v_h__4_3627_);
lean_dec(v_h__2_3625_);
lean_dec(v_h__1_3624_);
v_k_3637_ = lean_ctor_get(v_x_3623_, 0);
lean_inc(v_k_3637_);
lean_dec_ref_known(v_x_3623_, 1);
v___x_3638_ = lean_apply_1(v_h__3_3626_, v_k_3637_);
return v___x_3638_;
}
case 3:
{
lean_object* v_i_3639_; lean_object* v___x_3640_; 
lean_dec(v_h__9_3632_);
lean_dec(v_h__8_3631_);
lean_dec(v_h__7_3630_);
lean_dec(v_h__6_3629_);
lean_dec(v_h__5_3628_);
lean_dec(v_h__3_3626_);
lean_dec(v_h__2_3625_);
lean_dec(v_h__1_3624_);
v_i_3639_ = lean_ctor_get(v_x_3623_, 0);
lean_inc(v_i_3639_);
lean_dec_ref_known(v_x_3623_, 1);
v___x_3640_ = lean_apply_1(v_h__4_3627_, v_i_3639_);
return v___x_3640_;
}
case 4:
{
lean_object* v_a_3641_; lean_object* v___x_3642_; 
lean_dec(v_h__9_3632_);
lean_dec(v_h__8_3631_);
lean_dec(v_h__6_3629_);
lean_dec(v_h__5_3628_);
lean_dec(v_h__4_3627_);
lean_dec(v_h__3_3626_);
lean_dec(v_h__2_3625_);
lean_dec(v_h__1_3624_);
v_a_3641_ = lean_ctor_get(v_x_3623_, 0);
lean_inc_ref(v_a_3641_);
lean_dec_ref_known(v_x_3623_, 1);
v___x_3642_ = lean_apply_1(v_h__7_3630_, v_a_3641_);
return v___x_3642_;
}
case 5:
{
lean_object* v_a_3643_; lean_object* v_b_3644_; lean_object* v___x_3645_; 
lean_dec(v_h__9_3632_);
lean_dec(v_h__8_3631_);
lean_dec(v_h__7_3630_);
lean_dec(v_h__6_3629_);
lean_dec(v_h__4_3627_);
lean_dec(v_h__3_3626_);
lean_dec(v_h__2_3625_);
lean_dec(v_h__1_3624_);
v_a_3643_ = lean_ctor_get(v_x_3623_, 0);
lean_inc_ref(v_a_3643_);
v_b_3644_ = lean_ctor_get(v_x_3623_, 1);
lean_inc_ref(v_b_3644_);
lean_dec_ref_known(v_x_3623_, 2);
v___x_3645_ = lean_apply_2(v_h__5_3628_, v_a_3643_, v_b_3644_);
return v___x_3645_;
}
case 6:
{
lean_object* v_a_3646_; lean_object* v_b_3647_; lean_object* v___x_3648_; 
lean_dec(v_h__9_3632_);
lean_dec(v_h__7_3630_);
lean_dec(v_h__6_3629_);
lean_dec(v_h__5_3628_);
lean_dec(v_h__4_3627_);
lean_dec(v_h__3_3626_);
lean_dec(v_h__2_3625_);
lean_dec(v_h__1_3624_);
v_a_3646_ = lean_ctor_get(v_x_3623_, 0);
lean_inc_ref(v_a_3646_);
v_b_3647_ = lean_ctor_get(v_x_3623_, 1);
lean_inc_ref(v_b_3647_);
lean_dec_ref_known(v_x_3623_, 2);
v___x_3648_ = lean_apply_2(v_h__8_3631_, v_a_3646_, v_b_3647_);
return v___x_3648_;
}
case 7:
{
lean_object* v_a_3649_; lean_object* v_b_3650_; lean_object* v___x_3651_; 
lean_dec(v_h__9_3632_);
lean_dec(v_h__8_3631_);
lean_dec(v_h__7_3630_);
lean_dec(v_h__5_3628_);
lean_dec(v_h__4_3627_);
lean_dec(v_h__3_3626_);
lean_dec(v_h__2_3625_);
lean_dec(v_h__1_3624_);
v_a_3649_ = lean_ctor_get(v_x_3623_, 0);
lean_inc_ref(v_a_3649_);
v_b_3650_ = lean_ctor_get(v_x_3623_, 1);
lean_inc_ref(v_b_3650_);
lean_dec_ref_known(v_x_3623_, 2);
v___x_3651_ = lean_apply_2(v_h__6_3629_, v_a_3649_, v_b_3650_);
return v___x_3651_;
}
default: 
{
lean_object* v_a_3652_; lean_object* v_k_3653_; lean_object* v___x_3654_; 
lean_dec(v_h__8_3631_);
lean_dec(v_h__7_3630_);
lean_dec(v_h__6_3629_);
lean_dec(v_h__5_3628_);
lean_dec(v_h__4_3627_);
lean_dec(v_h__3_3626_);
lean_dec(v_h__2_3625_);
lean_dec(v_h__1_3624_);
v_a_3652_ = lean_ctor_get(v_x_3623_, 0);
lean_inc_ref(v_a_3652_);
v_k_3653_ = lean_ctor_get(v_x_3623_, 1);
lean_inc(v_k_3653_);
lean_dec_ref_known(v_x_3623_, 2);
v___x_3654_ = lean_apply_2(v_h__9_3632_, v_a_3652_, v_k_3653_);
return v___x_3654_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter___redArg(lean_object* v_a_3655_, lean_object* v_h__1_3656_, lean_object* v_h__2_3657_, lean_object* v_h__3_3658_){
_start:
{
switch(lean_obj_tag(v_a_3655_))
{
case 0:
{
lean_object* v_k_3659_; lean_object* v___x_3660_; 
lean_dec(v_h__3_3658_);
lean_dec(v_h__2_3657_);
v_k_3659_ = lean_ctor_get(v_a_3655_, 0);
lean_inc(v_k_3659_);
lean_dec_ref_known(v_a_3655_, 1);
v___x_3660_ = lean_apply_1(v_h__1_3656_, v_k_3659_);
return v___x_3660_;
}
case 3:
{
lean_object* v_i_3661_; lean_object* v___x_3662_; 
lean_dec(v_h__3_3658_);
lean_dec(v_h__1_3656_);
v_i_3661_ = lean_ctor_get(v_a_3655_, 0);
lean_inc(v_i_3661_);
lean_dec_ref_known(v_a_3655_, 1);
v___x_3662_ = lean_apply_1(v_h__2_3657_, v_i_3661_);
return v___x_3662_;
}
default: 
{
lean_object* v___x_3663_; 
lean_dec(v_h__2_3657_);
lean_dec(v_h__1_3656_);
v___x_3663_ = lean_apply_3(v_h__3_3658_, v_a_3655_, lean_box(0), lean_box(0));
return v___x_3663_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter(lean_object* v_motive_3664_, lean_object* v_a_3665_, lean_object* v_h__1_3666_, lean_object* v_h__2_3667_, lean_object* v_h__3_3668_){
_start:
{
switch(lean_obj_tag(v_a_3665_))
{
case 0:
{
lean_object* v_k_3669_; lean_object* v___x_3670_; 
lean_dec(v_h__3_3668_);
lean_dec(v_h__2_3667_);
v_k_3669_ = lean_ctor_get(v_a_3665_, 0);
lean_inc(v_k_3669_);
lean_dec_ref_known(v_a_3665_, 1);
v___x_3670_ = lean_apply_1(v_h__1_3666_, v_k_3669_);
return v___x_3670_;
}
case 3:
{
lean_object* v_i_3671_; lean_object* v___x_3672_; 
lean_dec(v_h__3_3668_);
lean_dec(v_h__1_3666_);
v_i_3671_ = lean_ctor_get(v_a_3665_, 0);
lean_inc(v_i_3671_);
lean_dec_ref_known(v_a_3665_, 1);
v___x_3672_ = lean_apply_1(v_h__2_3667_, v_i_3671_);
return v___x_3672_;
}
default: 
{
lean_object* v___x_3673_; 
lean_dec(v_h__2_3667_);
lean_dec(v_h__1_3666_);
v___x_3673_ = lean_apply_3(v_h__3_3668_, v_a_3665_, lean_box(0), lean_box(0));
return v___x_3673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(lean_object* v_inst_3674_, lean_object* v_ctx_3675_, lean_object* v_m_3676_, lean_object* v_acc_3677_){
_start:
{
if (lean_obj_tag(v_m_3676_) == 0)
{
lean_dec_ref(v_inst_3674_);
return v_acc_3677_;
}
else
{
lean_object* v_toSemiring_3678_; lean_object* v_toMul_3679_; lean_object* v_ofNat_3680_; lean_object* v_npow_3681_; lean_object* v_p_3682_; lean_object* v_m_3683_; lean_object* v___y_3685_; lean_object* v_x_3688_; lean_object* v_k_3689_; lean_object* v___x_3690_; uint8_t v___x_3691_; 
v_toSemiring_3678_ = lean_ctor_get(v_inst_3674_, 0);
v_toMul_3679_ = lean_ctor_get(v_toSemiring_3678_, 1);
v_ofNat_3680_ = lean_ctor_get(v_toSemiring_3678_, 3);
v_npow_3681_ = lean_ctor_get(v_toSemiring_3678_, 5);
v_p_3682_ = lean_ctor_get(v_m_3676_, 0);
lean_inc_ref(v_p_3682_);
v_m_3683_ = lean_ctor_get(v_m_3676_, 1);
lean_inc(v_m_3683_);
lean_dec_ref_known(v_m_3676_, 2);
v_x_3688_ = lean_ctor_get(v_p_3682_, 0);
lean_inc(v_x_3688_);
v_k_3689_ = lean_ctor_get(v_p_3682_, 1);
lean_inc(v_k_3689_);
lean_dec_ref(v_p_3682_);
v___x_3690_ = lean_unsigned_to_nat(0u);
v___x_3691_ = lean_nat_dec_eq(v_k_3689_, v___x_3690_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; uint8_t v___x_3693_; 
v___x_3692_ = lean_unsigned_to_nat(1u);
v___x_3693_ = lean_nat_dec_eq(v_k_3689_, v___x_3692_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = l_Lean_RArray_getImpl___redArg(v_ctx_3675_, v_x_3688_);
lean_dec(v_x_3688_);
lean_inc(v_npow_3681_);
v___x_3695_ = lean_apply_2(v_npow_3681_, v___x_3694_, v_k_3689_);
v___y_3685_ = v___x_3695_;
goto v___jp_3684_;
}
else
{
lean_object* v___x_3696_; 
lean_dec(v_k_3689_);
v___x_3696_ = l_Lean_RArray_getImpl___redArg(v_ctx_3675_, v_x_3688_);
lean_dec(v_x_3688_);
v___y_3685_ = v___x_3696_;
goto v___jp_3684_;
}
}
else
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
lean_dec(v_k_3689_);
lean_dec(v_x_3688_);
v___x_3697_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3680_);
v___x_3698_ = lean_apply_1(v_ofNat_3680_, v___x_3697_);
v___y_3685_ = v___x_3698_;
goto v___jp_3684_;
}
v___jp_3684_:
{
lean_object* v___x_3686_; 
lean_inc(v_toMul_3679_);
v___x_3686_ = lean_apply_2(v_toMul_3679_, v_acc_3677_, v___y_3685_);
v_m_3676_ = v_m_3683_;
v_acc_3677_ = v___x_3686_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg___boxed(lean_object* v_inst_3699_, lean_object* v_ctx_3700_, lean_object* v_m_3701_, lean_object* v_acc_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3699_, v_ctx_3700_, v_m_3701_, v_acc_3702_);
lean_dec_ref(v_ctx_3700_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(lean_object* v_00_u03b1_3704_, lean_object* v_inst_3705_, lean_object* v_ctx_3706_, lean_object* v_m_3707_, lean_object* v_acc_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3705_, v_ctx_3706_, v_m_3707_, v_acc_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___boxed(lean_object* v_00_u03b1_3710_, lean_object* v_inst_3711_, lean_object* v_ctx_3712_, lean_object* v_m_3713_, lean_object* v_acc_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(v_00_u03b1_3710_, v_inst_3711_, v_ctx_3712_, v_m_3713_, v_acc_3714_);
lean_dec_ref(v_ctx_3712_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(lean_object* v_inst_3716_, lean_object* v_ctx_3717_, lean_object* v_m_3718_){
_start:
{
if (lean_obj_tag(v_m_3718_) == 0)
{
lean_object* v_toSemiring_3719_; lean_object* v_ofNat_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v_toSemiring_3719_ = lean_ctor_get(v_inst_3716_, 0);
lean_inc_ref(v_toSemiring_3719_);
lean_dec_ref(v_inst_3716_);
v_ofNat_3720_ = lean_ctor_get(v_toSemiring_3719_, 3);
lean_inc(v_ofNat_3720_);
lean_dec_ref(v_toSemiring_3719_);
v___x_3721_ = lean_unsigned_to_nat(1u);
v___x_3722_ = lean_apply_1(v_ofNat_3720_, v___x_3721_);
return v___x_3722_;
}
else
{
lean_object* v_toSemiring_3723_; lean_object* v_p_3724_; lean_object* v_m_3725_; lean_object* v_ofNat_3726_; lean_object* v_npow_3727_; lean_object* v_x_3728_; lean_object* v_k_3729_; lean_object* v___x_3730_; uint8_t v___x_3731_; 
v_toSemiring_3723_ = lean_ctor_get(v_inst_3716_, 0);
v_p_3724_ = lean_ctor_get(v_m_3718_, 0);
lean_inc_ref(v_p_3724_);
v_m_3725_ = lean_ctor_get(v_m_3718_, 1);
lean_inc(v_m_3725_);
lean_dec_ref_known(v_m_3718_, 2);
v_ofNat_3726_ = lean_ctor_get(v_toSemiring_3723_, 3);
v_npow_3727_ = lean_ctor_get(v_toSemiring_3723_, 5);
v_x_3728_ = lean_ctor_get(v_p_3724_, 0);
lean_inc(v_x_3728_);
v_k_3729_ = lean_ctor_get(v_p_3724_, 1);
lean_inc(v_k_3729_);
lean_dec_ref(v_p_3724_);
v___x_3730_ = lean_unsigned_to_nat(0u);
v___x_3731_ = lean_nat_dec_eq(v_k_3729_, v___x_3730_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3732_; uint8_t v___x_3733_; 
v___x_3732_ = lean_unsigned_to_nat(1u);
v___x_3733_ = lean_nat_dec_eq(v_k_3729_, v___x_3732_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3734_ = l_Lean_RArray_getImpl___redArg(v_ctx_3717_, v_x_3728_);
lean_dec(v_x_3728_);
lean_inc(v_npow_3727_);
v___x_3735_ = lean_apply_2(v_npow_3727_, v___x_3734_, v_k_3729_);
v___x_3736_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3716_, v_ctx_3717_, v_m_3725_, v___x_3735_);
return v___x_3736_;
}
else
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
lean_dec(v_k_3729_);
v___x_3737_ = l_Lean_RArray_getImpl___redArg(v_ctx_3717_, v_x_3728_);
lean_dec(v_x_3728_);
v___x_3738_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3716_, v_ctx_3717_, v_m_3725_, v___x_3737_);
return v___x_3738_;
}
}
else
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_dec(v_k_3729_);
lean_dec(v_x_3728_);
v___x_3739_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3726_);
v___x_3740_ = lean_apply_1(v_ofNat_3726_, v___x_3739_);
v___x_3741_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3716_, v_ctx_3717_, v_m_3725_, v___x_3740_);
return v___x_3741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3742_, lean_object* v_ctx_3743_, lean_object* v_m_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3742_, v_ctx_3743_, v_m_3744_);
lean_dec_ref(v_ctx_3743_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule(lean_object* v_00_u03b1_3746_, lean_object* v_inst_3747_, lean_object* v_ctx_3748_, lean_object* v_m_3749_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3747_, v_ctx_3748_, v_m_3749_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3751_, lean_object* v_inst_3752_, lean_object* v_ctx_3753_, lean_object* v_m_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule(v_00_u03b1_3751_, v_inst_3752_, v_ctx_3753_, v_m_3754_);
lean_dec_ref(v_ctx_3753_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(lean_object* v_inst_3756_, lean_object* v_ctx_3757_, lean_object* v_p_3758_){
_start:
{
lean_object* v___x_3759_; 
lean_inc_ref(v_inst_3756_);
v___x_3759_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_3756_);
if (lean_obj_tag(v_p_3758_) == 0)
{
lean_object* v_toSemiring_3760_; lean_object* v_zsmul_3761_; lean_object* v_ofNat_3762_; lean_object* v_k_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v_toSemiring_3760_ = lean_ctor_get(v_inst_3756_, 0);
lean_inc_ref(v_toSemiring_3760_);
lean_dec_ref(v_inst_3756_);
v_zsmul_3761_ = lean_ctor_get(v___x_3759_, 2);
lean_inc(v_zsmul_3761_);
lean_dec_ref(v___x_3759_);
v_ofNat_3762_ = lean_ctor_get(v_toSemiring_3760_, 3);
lean_inc(v_ofNat_3762_);
lean_dec_ref(v_toSemiring_3760_);
v_k_3763_ = lean_ctor_get(v_p_3758_, 0);
lean_inc(v_k_3763_);
lean_dec_ref_known(v_p_3758_, 1);
v___x_3764_ = lean_unsigned_to_nat(1u);
v___x_3765_ = lean_apply_1(v_ofNat_3762_, v___x_3764_);
v___x_3766_ = lean_apply_2(v_zsmul_3761_, v_k_3763_, v___x_3765_);
return v___x_3766_;
}
else
{
lean_object* v_toSemiring_3767_; lean_object* v_zsmul_3768_; lean_object* v_toAdd_3769_; lean_object* v_k_3770_; lean_object* v_v_3771_; lean_object* v_p_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v_toSemiring_3767_ = lean_ctor_get(v_inst_3756_, 0);
v_zsmul_3768_ = lean_ctor_get(v___x_3759_, 2);
lean_inc(v_zsmul_3768_);
lean_dec_ref(v___x_3759_);
v_toAdd_3769_ = lean_ctor_get(v_toSemiring_3767_, 0);
lean_inc(v_toAdd_3769_);
v_k_3770_ = lean_ctor_get(v_p_3758_, 0);
lean_inc(v_k_3770_);
v_v_3771_ = lean_ctor_get(v_p_3758_, 1);
lean_inc(v_v_3771_);
v_p_3772_ = lean_ctor_get(v_p_3758_, 2);
lean_inc_ref(v_p_3772_);
lean_dec_ref_known(v_p_3758_, 3);
lean_inc_ref(v_inst_3756_);
v___x_3773_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3756_, v_ctx_3757_, v_v_3771_);
v___x_3774_ = lean_apply_2(v_zsmul_3768_, v_k_3770_, v___x_3773_);
v___x_3775_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3756_, v_ctx_3757_, v_p_3772_);
v___x_3776_ = lean_apply_2(v_toAdd_3769_, v___x_3774_, v___x_3775_);
return v___x_3776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3777_, lean_object* v_ctx_3778_, lean_object* v_p_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3777_, v_ctx_3778_, v_p_3779_);
lean_dec_ref(v_ctx_3778_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule(lean_object* v_00_u03b1_3781_, lean_object* v_inst_3782_, lean_object* v_ctx_3783_, lean_object* v_p_3784_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3782_, v_ctx_3783_, v_p_3784_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3786_, lean_object* v_inst_3787_, lean_object* v_ctx_3788_, lean_object* v_p_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule(v_00_u03b1_3786_, v_inst_3787_, v_ctx_3788_, v_p_3789_);
lean_dec_ref(v_ctx_3788_);
return v_res_3790_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__gcd__cert(lean_object* v_a_3791_, lean_object* v_b_3792_, lean_object* v_p_u2081_3793_, lean_object* v_p_u2082_3794_, lean_object* v_p_3795_){
_start:
{
if (lean_obj_tag(v_p_u2081_3793_) == 0)
{
if (lean_obj_tag(v_p_u2082_3794_) == 0)
{
if (lean_obj_tag(v_p_3795_) == 0)
{
lean_object* v_k_3796_; lean_object* v_k_3797_; lean_object* v_k_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
v_k_3796_ = lean_ctor_get(v_p_u2081_3793_, 0);
v_k_3797_ = lean_ctor_get(v_p_u2082_3794_, 0);
v_k_3798_ = lean_ctor_get(v_p_3795_, 0);
v___x_3799_ = lean_int_mul(v_a_3791_, v_k_3796_);
v___x_3800_ = lean_int_mul(v_b_3792_, v_k_3797_);
v___x_3801_ = lean_int_add(v___x_3799_, v___x_3800_);
lean_dec(v___x_3800_);
lean_dec(v___x_3799_);
v___x_3802_ = lean_int_dec_eq(v_k_3798_, v___x_3801_);
lean_dec(v___x_3801_);
return v___x_3802_;
}
else
{
uint8_t v___x_3803_; 
v___x_3803_ = 0;
return v___x_3803_;
}
}
else
{
uint8_t v___x_3804_; 
v___x_3804_ = 0;
return v___x_3804_;
}
}
else
{
uint8_t v___x_3805_; 
v___x_3805_ = 0;
return v___x_3805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__gcd__cert___boxed(lean_object* v_a_3806_, lean_object* v_b_3807_, lean_object* v_p_u2081_3808_, lean_object* v_p_u2082_3809_, lean_object* v_p_3810_){
_start:
{
uint8_t v_res_3811_; lean_object* v_r_3812_; 
v_res_3811_ = l_Lean_Grind_CommRing_eq__gcd__cert(v_a_3806_, v_b_3807_, v_p_u2081_3808_, v_p_u2082_3809_, v_p_3810_);
lean_dec_ref(v_p_3810_);
lean_dec_ref(v_p_u2082_3809_);
lean_dec_ref(v_p_u2081_3808_);
lean_dec(v_b_3807_);
lean_dec(v_a_3806_);
v_r_3812_ = lean_box(v_res_3811_);
return v_r_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(lean_object* v_p_3813_, lean_object* v_h__1_3814_, lean_object* v_h__2_3815_){
_start:
{
if (lean_obj_tag(v_p_3813_) == 0)
{
lean_object* v_k_3816_; lean_object* v___x_3817_; 
lean_dec(v_h__1_3814_);
v_k_3816_ = lean_ctor_get(v_p_3813_, 0);
lean_inc(v_k_3816_);
lean_dec_ref_known(v_p_3813_, 1);
v___x_3817_ = lean_apply_1(v_h__2_3815_, v_k_3816_);
return v___x_3817_;
}
else
{
lean_object* v_k_3818_; lean_object* v_v_3819_; lean_object* v_p_3820_; lean_object* v___x_3821_; 
lean_dec(v_h__2_3815_);
v_k_3818_ = lean_ctor_get(v_p_3813_, 0);
lean_inc(v_k_3818_);
v_v_3819_ = lean_ctor_get(v_p_3813_, 1);
lean_inc(v_v_3819_);
v_p_3820_ = lean_ctor_get(v_p_3813_, 2);
lean_inc_ref(v_p_3820_);
lean_dec_ref_known(v_p_3813_, 3);
v___x_3821_ = lean_apply_3(v_h__1_3814_, v_k_3818_, v_v_3819_, v_p_3820_);
return v___x_3821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter(lean_object* v_motive_3822_, lean_object* v_p_3823_, lean_object* v_h__1_3824_, lean_object* v_h__2_3825_){
_start:
{
if (lean_obj_tag(v_p_3823_) == 0)
{
lean_object* v_k_3826_; lean_object* v___x_3827_; 
lean_dec(v_h__1_3824_);
v_k_3826_ = lean_ctor_get(v_p_3823_, 0);
lean_inc(v_k_3826_);
lean_dec_ref_known(v_p_3823_, 1);
v___x_3827_ = lean_apply_1(v_h__2_3825_, v_k_3826_);
return v___x_3827_;
}
else
{
lean_object* v_k_3828_; lean_object* v_v_3829_; lean_object* v_p_3830_; lean_object* v___x_3831_; 
lean_dec(v_h__2_3825_);
v_k_3828_ = lean_ctor_get(v_p_3823_, 0);
lean_inc(v_k_3828_);
v_v_3829_ = lean_ctor_get(v_p_3823_, 1);
lean_inc(v_v_3829_);
v_p_3830_ = lean_ctor_get(v_p_3823_, 2);
lean_inc_ref(v_p_3830_);
lean_dec_ref_known(v_p_3823_, 3);
v___x_3831_ = lean_apply_3(v_h__1_3824_, v_k_3828_, v_v_3829_, v_p_3830_);
return v___x_3831_;
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
lean_object* runtime_initialize_Init_Data_Nat_Gcd(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
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
lean_object* initialize_Init_Data_Nat_Gcd(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Gcd(builtin);
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
