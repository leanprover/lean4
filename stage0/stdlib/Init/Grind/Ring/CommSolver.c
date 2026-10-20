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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_instReprPower_repr_spec__0(lean_object* v_a_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_nat_to_int(v_a_566_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(5u);
v___x_582_ = lean_nat_to_int(v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0));
v___x_591_ = lean_string_length(v___x_590_);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13, &l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13_once, _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13);
v___x_593_ = lean_nat_to_int(v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg(lean_object* v_x_598_){
_start:
{
lean_object* v_x_599_; lean_object* v_k_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_634_; 
v_x_599_ = lean_ctor_get(v_x_598_, 0);
v_k_600_ = lean_ctor_get(v_x_598_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_634_ == 0)
{
v___x_602_ = v_x_598_;
v_isShared_603_ = v_isSharedCheck_634_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_k_600_);
lean_inc(v_x_599_);
lean_dec(v_x_598_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_634_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_604_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5));
v___x_605_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6));
v___x_606_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7, &l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7_once, _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7);
v___x_607_ = l_Nat_reprFast(v_x_599_);
v___x_608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
if (v_isShared_603_ == 0)
{
lean_ctor_set_tag(v___x_602_, 4);
lean_ctor_set(v___x_602_, 1, v___x_608_);
lean_ctor_set(v___x_602_, 0, v___x_606_);
v___x_610_ = v___x_602_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_608_);
v___x_610_ = v_reuseFailAlloc_633_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
uint8_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_611_ = 0;
v___x_612_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*1, v___x_611_);
v___x_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_605_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9));
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = lean_box(1);
v___x_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11));
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_604_);
v___x_621_ = l_Nat_reprFast(v_k_600_);
v___x_622_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
v___x_623_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_606_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*1, v___x_611_);
v___x_625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_620_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14, &l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14_once, _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14);
v___x_627_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15));
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_625_);
v___x_629_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16));
v___x_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_626_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*1, v___x_611_);
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr(lean_object* v_x_635_, lean_object* v_prec_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg(v_x_635_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___boxed(lean_object* v_x_638_, lean_object* v_prec_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Grind_CommRing_instReprPower_repr(v_x_638_, v_prec_639_);
lean_dec(v_prec_639_);
return v_res_640_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePower_hash(lean_object* v_x_647_){
_start:
{
lean_object* v_x_648_; lean_object* v_k_649_; uint64_t v___x_650_; uint64_t v___x_651_; uint64_t v___x_652_; uint64_t v___x_653_; uint64_t v___x_654_; 
v_x_648_ = lean_ctor_get(v_x_647_, 0);
v_k_649_ = lean_ctor_get(v_x_647_, 1);
v___x_650_ = 0ULL;
v___x_651_ = lean_uint64_of_nat(v_x_648_);
v___x_652_ = lean_uint64_mix_hash(v___x_650_, v___x_651_);
v___x_653_ = lean_uint64_of_nat(v_k_649_);
v___x_654_ = lean_uint64_mix_hash(v___x_652_, v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePower_hash___boxed(lean_object* v_x_655_){
_start:
{
uint64_t v_res_656_; lean_object* v_r_657_; 
v_res_656_ = l_Lean_Grind_CommRing_instHashablePower_hash(v_x_655_);
lean_dec_ref(v_x_655_);
v_r_657_ = lean_box_uint64(v_res_656_);
return v_r_657_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_varLt(lean_object* v_p_u2081_660_, lean_object* v_p_u2082_661_){
_start:
{
lean_object* v_x_662_; lean_object* v_x_663_; uint8_t v___x_664_; 
v_x_662_ = lean_ctor_get(v_p_u2081_660_, 0);
v_x_663_ = lean_ctor_get(v_p_u2082_661_, 0);
v___x_664_ = l_Nat_blt(v_x_662_, v_x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_varLt___boxed(lean_object* v_p_u2081_665_, lean_object* v_p_u2082_666_){
_start:
{
uint8_t v_res_667_; lean_object* v_r_668_; 
v_res_667_ = l_Lean_Grind_CommRing_Power_varLt(v_p_u2081_665_, v_p_u2082_666_);
lean_dec_ref(v_p_u2082_666_);
lean_dec_ref(v_p_u2081_665_);
v_r_668_ = lean_box(v_res_667_);
return v_r_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg(lean_object* v_inst_669_, lean_object* v_ctx_670_, lean_object* v_x_671_){
_start:
{
lean_object* v_ofNat_672_; lean_object* v_npow_673_; lean_object* v_x_674_; lean_object* v_k_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_ofNat_672_ = lean_ctor_get(v_inst_669_, 3);
lean_inc(v_ofNat_672_);
v_npow_673_ = lean_ctor_get(v_inst_669_, 5);
lean_inc(v_npow_673_);
lean_dec_ref(v_inst_669_);
v_x_674_ = lean_ctor_get(v_x_671_, 0);
lean_inc(v_x_674_);
v_k_675_ = lean_ctor_get(v_x_671_, 1);
lean_inc(v_k_675_);
lean_dec_ref(v_x_671_);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_nat_dec_eq(v_k_675_, v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; uint8_t v___x_679_; 
lean_dec(v_ofNat_672_);
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_nat_dec_eq(v_k_675_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = l_Lean_RArray_getImpl___redArg(v_ctx_670_, v_x_674_);
lean_dec(v_x_674_);
v___x_681_ = lean_apply_2(v_npow_673_, v___x_680_, v_k_675_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; 
lean_dec(v_k_675_);
lean_dec(v_npow_673_);
v___x_682_ = l_Lean_RArray_getImpl___redArg(v_ctx_670_, v_x_674_);
lean_dec(v_x_674_);
return v___x_682_;
}
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec(v_k_675_);
lean_dec(v_x_674_);
lean_dec(v_npow_673_);
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_apply_1(v_ofNat_672_, v___x_683_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg___boxed(lean_object* v_inst_685_, lean_object* v_ctx_686_, lean_object* v_x_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Grind_CommRing_Power_denote___redArg(v_inst_685_, v_ctx_686_, v_x_687_);
lean_dec_ref(v_ctx_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote(lean_object* v_00_u03b1_689_, lean_object* v_inst_690_, lean_object* v_ctx_691_, lean_object* v_x_692_){
_start:
{
lean_object* v_ofNat_693_; lean_object* v_npow_694_; lean_object* v_x_695_; lean_object* v_k_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_ofNat_693_ = lean_ctor_get(v_inst_690_, 3);
lean_inc(v_ofNat_693_);
v_npow_694_ = lean_ctor_get(v_inst_690_, 5);
lean_inc(v_npow_694_);
lean_dec_ref(v_inst_690_);
v_x_695_ = lean_ctor_get(v_x_692_, 0);
lean_inc(v_x_695_);
v_k_696_ = lean_ctor_get(v_x_692_, 1);
lean_inc(v_k_696_);
lean_dec_ref(v_x_692_);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_nat_dec_eq(v_k_696_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; uint8_t v___x_700_; 
lean_dec(v_ofNat_693_);
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_nat_dec_eq(v_k_696_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = l_Lean_RArray_getImpl___redArg(v_ctx_691_, v_x_695_);
lean_dec(v_x_695_);
v___x_702_ = lean_apply_2(v_npow_694_, v___x_701_, v_k_696_);
return v___x_702_;
}
else
{
lean_object* v___x_703_; 
lean_dec(v_k_696_);
lean_dec(v_npow_694_);
v___x_703_ = l_Lean_RArray_getImpl___redArg(v_ctx_691_, v_x_695_);
lean_dec(v_x_695_);
return v___x_703_;
}
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec(v_k_696_);
lean_dec(v_x_695_);
lean_dec(v_npow_694_);
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_apply_1(v_ofNat_693_, v___x_704_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___boxed(lean_object* v_00_u03b1_706_, lean_object* v_inst_707_, lean_object* v_ctx_708_, lean_object* v_x_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Grind_CommRing_Power_denote(v_00_u03b1_706_, v_inst_707_, v_ctx_708_, v_x_709_);
lean_dec_ref(v_ctx_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx___impl(lean_object* v_x_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = lean_obj_tag_nat(v_x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx___impl___boxed(lean_object* v_x_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Grind_CommRing_Mon_ctorIdx___impl(v_x_713_);
lean_dec(v_x_713_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___redArg(lean_object* v_t_715_, lean_object* v_k_716_){
_start:
{
if (lean_obj_tag(v_t_715_) == 0)
{
return v_k_716_;
}
else
{
lean_object* v_p_717_; lean_object* v_m_718_; lean_object* v___x_719_; 
v_p_717_ = lean_ctor_get(v_t_715_, 0);
lean_inc_ref(v_p_717_);
v_m_718_ = lean_ctor_get(v_t_715_, 1);
lean_inc(v_m_718_);
lean_dec_ref_known(v_t_715_, 2);
v___x_719_ = lean_apply_2(v_k_716_, v_p_717_, v_m_718_);
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim(lean_object* v_motive_720_, lean_object* v_ctorIdx_721_, lean_object* v_t_722_, lean_object* v_h_723_, lean_object* v_k_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_722_, v_k_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___boxed(lean_object* v_motive_726_, lean_object* v_ctorIdx_727_, lean_object* v_t_728_, lean_object* v_h_729_, lean_object* v_k_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Grind_CommRing_Mon_ctorElim(v_motive_726_, v_ctorIdx_727_, v_t_728_, v_h_729_, v_k_730_);
lean_dec(v_ctorIdx_727_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim___redArg(lean_object* v_t_732_, lean_object* v_unit_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_732_, v_unit_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim(lean_object* v_motive_735_, lean_object* v_t_736_, lean_object* v_h_737_, lean_object* v_unit_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_736_, v_unit_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim___redArg(lean_object* v_t_740_, lean_object* v_mult_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_740_, v_mult_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim(lean_object* v_motive_743_, lean_object* v_t_744_, lean_object* v_h_745_, lean_object* v_mult_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_744_, v_mult_746_);
return v___x_747_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqMon_beq(lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
if (lean_obj_tag(v_x_749_) == 0)
{
uint8_t v___x_750_; 
v___x_750_ = 1;
return v___x_750_;
}
else
{
uint8_t v___x_751_; 
v___x_751_ = 0;
return v___x_751_;
}
}
else
{
if (lean_obj_tag(v_x_749_) == 1)
{
lean_object* v_p_752_; lean_object* v_m_753_; lean_object* v_p_754_; lean_object* v_m_755_; uint8_t v___x_756_; 
v_p_752_ = lean_ctor_get(v_x_748_, 0);
v_m_753_ = lean_ctor_get(v_x_748_, 1);
v_p_754_ = lean_ctor_get(v_x_749_, 0);
v_m_755_ = lean_ctor_get(v_x_749_, 1);
v___x_756_ = l_Lean_Grind_CommRing_instBEqPower_beq(v_p_752_, v_p_754_);
if (v___x_756_ == 0)
{
return v___x_756_;
}
else
{
v_x_748_ = v_m_753_;
v_x_749_ = v_m_755_;
goto _start;
}
}
else
{
uint8_t v___x_758_; 
v___x_758_ = 0;
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqMon_beq___boxed(lean_object* v_x_759_, lean_object* v_x_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_x_759_, v_x_760_);
lean_dec(v_x_760_);
lean_dec(v_x_759_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter___redArg(lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_h__1_767_, lean_object* v_h__2_768_, lean_object* v_h__3_769_){
_start:
{
if (lean_obj_tag(v_x_765_) == 0)
{
lean_dec(v_h__2_768_);
if (lean_obj_tag(v_x_766_) == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec(v_h__3_769_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_apply_1(v_h__1_767_, v___x_770_);
return v___x_771_;
}
else
{
lean_object* v___x_772_; 
lean_dec(v_h__1_767_);
v___x_772_ = lean_apply_4(v_h__3_769_, v_x_765_, v_x_766_, lean_box(0), lean_box(0));
return v___x_772_;
}
}
else
{
lean_dec(v_h__1_767_);
if (lean_obj_tag(v_x_766_) == 1)
{
lean_object* v_p_773_; lean_object* v_m_774_; lean_object* v_p_775_; lean_object* v_m_776_; lean_object* v___x_777_; 
lean_dec(v_h__3_769_);
v_p_773_ = lean_ctor_get(v_x_765_, 0);
lean_inc_ref(v_p_773_);
v_m_774_ = lean_ctor_get(v_x_765_, 1);
lean_inc(v_m_774_);
lean_dec_ref_known(v_x_765_, 2);
v_p_775_ = lean_ctor_get(v_x_766_, 0);
lean_inc_ref(v_p_775_);
v_m_776_ = lean_ctor_get(v_x_766_, 1);
lean_inc(v_m_776_);
lean_dec_ref_known(v_x_766_, 2);
v___x_777_ = lean_apply_4(v_h__2_768_, v_p_773_, v_m_774_, v_p_775_, v_m_776_);
return v___x_777_;
}
else
{
lean_object* v___x_778_; 
lean_dec(v_h__2_768_);
v___x_778_ = lean_apply_4(v_h__3_769_, v_x_765_, v_x_766_, lean_box(0), lean_box(0));
return v___x_778_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter(lean_object* v_motive_779_, lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_h__1_782_, lean_object* v_h__2_783_, lean_object* v_h__3_784_){
_start:
{
if (lean_obj_tag(v_x_780_) == 0)
{
lean_dec(v_h__2_783_);
if (lean_obj_tag(v_x_781_) == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec(v_h__3_784_);
v___x_785_ = lean_box(0);
v___x_786_ = lean_apply_1(v_h__1_782_, v___x_785_);
return v___x_786_;
}
else
{
lean_object* v___x_787_; 
lean_dec(v_h__1_782_);
v___x_787_ = lean_apply_4(v_h__3_784_, v_x_780_, v_x_781_, lean_box(0), lean_box(0));
return v___x_787_;
}
}
else
{
lean_dec(v_h__1_782_);
if (lean_obj_tag(v_x_781_) == 1)
{
lean_object* v_p_788_; lean_object* v_m_789_; lean_object* v_p_790_; lean_object* v_m_791_; lean_object* v___x_792_; 
lean_dec(v_h__3_784_);
v_p_788_ = lean_ctor_get(v_x_780_, 0);
lean_inc_ref(v_p_788_);
v_m_789_ = lean_ctor_get(v_x_780_, 1);
lean_inc(v_m_789_);
lean_dec_ref_known(v_x_780_, 2);
v_p_790_ = lean_ctor_get(v_x_781_, 0);
lean_inc_ref(v_p_790_);
v_m_791_ = lean_ctor_get(v_x_781_, 1);
lean_inc(v_m_791_);
lean_dec_ref_known(v_x_781_, 2);
v___x_792_ = lean_apply_4(v_h__2_783_, v_p_788_, v_m_789_, v_p_790_, v_m_791_);
return v___x_792_;
}
else
{
lean_object* v___x_793_; 
lean_dec(v_h__2_783_);
v___x_793_ = lean_apply_4(v_h__3_784_, v_x_780_, v_x_781_, lean_box(0), lean_box(0));
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr(lean_object* v_x_803_, lean_object* v_prec_804_){
_start:
{
lean_object* v___y_806_; 
if (lean_obj_tag(v_x_803_) == 0)
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = lean_unsigned_to_nat(1024u);
v___x_813_ = lean_nat_dec_le(v___x_812_, v_prec_804_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; 
v___x_814_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_806_ = v___x_814_;
goto v___jp_805_;
}
else
{
lean_object* v___x_815_; 
v___x_815_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_806_ = v___x_815_;
goto v___jp_805_;
}
}
else
{
lean_object* v_p_816_; lean_object* v_m_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_840_; 
v_p_816_ = lean_ctor_get(v_x_803_, 0);
v_m_817_ = lean_ctor_get(v_x_803_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_x_803_);
if (v_isSharedCheck_840_ == 0)
{
v___x_819_ = v_x_803_;
v_isShared_820_ = v_isSharedCheck_840_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_m_817_);
lean_inc(v_p_816_);
lean_dec(v_x_803_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_840_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___y_823_; uint8_t v___x_837_; 
v___x_821_ = lean_unsigned_to_nat(1024u);
v___x_837_ = lean_nat_dec_le(v___x_821_, v_prec_804_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
v___x_838_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_823_ = v___x_838_;
goto v___jp_822_;
}
else
{
lean_object* v___x_839_; 
v___x_839_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_823_ = v___x_839_;
goto v___jp_822_;
}
v___jp_822_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_824_ = lean_box(1);
v___x_825_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprMon_repr___closed__4));
v___x_826_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg(v_p_816_);
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 5);
lean_ctor_set(v___x_819_, 1, v___x_826_);
lean_ctor_set(v___x_819_, 0, v___x_825_);
v___x_828_ = v___x_819_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v___x_826_);
v___x_828_ = v_reuseFailAlloc_836_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___x_824_);
v___x_830_ = l_Lean_Grind_CommRing_instReprMon_repr(v_m_817_, v___x_821_);
v___x_831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
lean_inc(v___y_823_);
v___x_832_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_832_, 0, v___y_823_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = 0;
v___x_834_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*1, v___x_833_);
v___x_835_ = l_Repr_addAppParen(v___x_834_, v_prec_804_);
return v___x_835_;
}
}
}
}
v___jp_805_:
{
lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_807_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprMon_repr___closed__1));
lean_inc(v___y_806_);
v___x_808_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_808_, 0, v___y_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = 0;
v___x_810_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*1, v___x_809_);
v___x_811_ = l_Repr_addAppParen(v___x_810_, v_prec_804_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr___boxed(lean_object* v_x_841_, lean_object* v_prec_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Grind_CommRing_instReprMon_repr(v_x_841_, v_prec_842_);
lean_dec(v_prec_842_);
return v_res_843_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedMon_default(void){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_box(0);
return v___x_846_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedMon(void){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = lean_box(0);
return v___x_847_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashableMon_hash(lean_object* v_x_848_){
_start:
{
if (lean_obj_tag(v_x_848_) == 0)
{
uint64_t v___x_849_; 
v___x_849_ = 0ULL;
return v___x_849_;
}
else
{
lean_object* v_p_850_; lean_object* v_m_851_; uint64_t v___x_852_; uint64_t v___x_853_; uint64_t v___x_854_; uint64_t v___x_855_; uint64_t v___x_856_; 
v_p_850_ = lean_ctor_get(v_x_848_, 0);
v_m_851_ = lean_ctor_get(v_x_848_, 1);
v___x_852_ = 1ULL;
v___x_853_ = l_Lean_Grind_CommRing_instHashablePower_hash(v_p_850_);
v___x_854_ = lean_uint64_mix_hash(v___x_852_, v___x_853_);
v___x_855_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_m_851_);
v___x_856_ = lean_uint64_mix_hash(v___x_854_, v___x_855_);
return v___x_856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableMon_hash___boxed(lean_object* v_x_857_){
_start:
{
uint64_t v_res_858_; lean_object* v_r_859_; 
v_res_858_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_x_857_);
lean_dec(v_x_857_);
v_r_859_ = lean_box_uint64(v_res_858_);
return v_r_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg(lean_object* v_inst_862_, lean_object* v_ctx_863_, lean_object* v_x_864_){
_start:
{
if (lean_obj_tag(v_x_864_) == 0)
{
lean_object* v_ofNat_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_ofNat_865_ = lean_ctor_get(v_inst_862_, 3);
lean_inc(v_ofNat_865_);
lean_dec_ref(v_inst_862_);
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lean_apply_1(v_ofNat_865_, v___x_866_);
return v___x_867_;
}
else
{
lean_object* v_toMul_868_; lean_object* v_ofNat_869_; lean_object* v_npow_870_; lean_object* v_p_871_; lean_object* v_m_872_; lean_object* v___y_874_; lean_object* v_x_877_; lean_object* v_k_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_toMul_868_ = lean_ctor_get(v_inst_862_, 1);
lean_inc(v_toMul_868_);
v_ofNat_869_ = lean_ctor_get(v_inst_862_, 3);
v_npow_870_ = lean_ctor_get(v_inst_862_, 5);
v_p_871_ = lean_ctor_get(v_x_864_, 0);
lean_inc_ref(v_p_871_);
v_m_872_ = lean_ctor_get(v_x_864_, 1);
lean_inc(v_m_872_);
lean_dec_ref_known(v_x_864_, 2);
v_x_877_ = lean_ctor_get(v_p_871_, 0);
lean_inc(v_x_877_);
v_k_878_ = lean_ctor_get(v_p_871_, 1);
lean_inc(v_k_878_);
lean_dec_ref(v_p_871_);
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = lean_nat_dec_eq(v_k_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_881_ = lean_unsigned_to_nat(1u);
v___x_882_ = lean_nat_dec_eq(v_k_878_, v___x_881_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = l_Lean_RArray_getImpl___redArg(v_ctx_863_, v_x_877_);
lean_dec(v_x_877_);
lean_inc(v_npow_870_);
v___x_884_ = lean_apply_2(v_npow_870_, v___x_883_, v_k_878_);
v___y_874_ = v___x_884_;
goto v___jp_873_;
}
else
{
lean_object* v___x_885_; 
lean_dec(v_k_878_);
v___x_885_ = l_Lean_RArray_getImpl___redArg(v_ctx_863_, v_x_877_);
lean_dec(v_x_877_);
v___y_874_ = v___x_885_;
goto v___jp_873_;
}
}
else
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec(v_k_878_);
lean_dec(v_x_877_);
v___x_886_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_869_);
v___x_887_ = lean_apply_1(v_ofNat_869_, v___x_886_);
v___y_874_ = v___x_887_;
goto v___jp_873_;
}
v___jp_873_:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_862_, v_ctx_863_, v_m_872_);
v___x_876_ = lean_apply_2(v_toMul_868_, v___y_874_, v___x_875_);
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg___boxed(lean_object* v_inst_888_, lean_object* v_ctx_889_, lean_object* v_x_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_888_, v_ctx_889_, v_x_890_);
lean_dec_ref(v_ctx_889_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote(lean_object* v_00_u03b1_892_, lean_object* v_inst_893_, lean_object* v_ctx_894_, lean_object* v_x_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_893_, v_ctx_894_, v_x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___boxed(lean_object* v_00_u03b1_897_, lean_object* v_inst_898_, lean_object* v_ctx_899_, lean_object* v_x_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Grind_CommRing_Mon_denote(v_00_u03b1_897_, v_inst_898_, v_ctx_899_, v_x_900_);
lean_dec_ref(v_ctx_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(lean_object* v_inst_902_, lean_object* v_ctx_903_, lean_object* v_m_904_, lean_object* v_acc_905_){
_start:
{
if (lean_obj_tag(v_m_904_) == 0)
{
lean_dec_ref(v_inst_902_);
return v_acc_905_;
}
else
{
lean_object* v_toMul_906_; lean_object* v_ofNat_907_; lean_object* v_npow_908_; lean_object* v_p_909_; lean_object* v_m_910_; lean_object* v___y_912_; lean_object* v_x_915_; lean_object* v_k_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_toMul_906_ = lean_ctor_get(v_inst_902_, 1);
v_ofNat_907_ = lean_ctor_get(v_inst_902_, 3);
v_npow_908_ = lean_ctor_get(v_inst_902_, 5);
v_p_909_ = lean_ctor_get(v_m_904_, 0);
lean_inc_ref(v_p_909_);
v_m_910_ = lean_ctor_get(v_m_904_, 1);
lean_inc(v_m_910_);
lean_dec_ref_known(v_m_904_, 2);
v_x_915_ = lean_ctor_get(v_p_909_, 0);
lean_inc(v_x_915_);
v_k_916_ = lean_ctor_get(v_p_909_, 1);
lean_inc(v_k_916_);
lean_dec_ref(v_p_909_);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = lean_nat_dec_eq(v_k_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_919_ = lean_unsigned_to_nat(1u);
v___x_920_ = lean_nat_dec_eq(v_k_916_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = l_Lean_RArray_getImpl___redArg(v_ctx_903_, v_x_915_);
lean_dec(v_x_915_);
lean_inc(v_npow_908_);
v___x_922_ = lean_apply_2(v_npow_908_, v___x_921_, v_k_916_);
v___y_912_ = v___x_922_;
goto v___jp_911_;
}
else
{
lean_object* v___x_923_; 
lean_dec(v_k_916_);
v___x_923_ = l_Lean_RArray_getImpl___redArg(v_ctx_903_, v_x_915_);
lean_dec(v_x_915_);
v___y_912_ = v___x_923_;
goto v___jp_911_;
}
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec(v_k_916_);
lean_dec(v_x_915_);
v___x_924_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_907_);
v___x_925_ = lean_apply_1(v_ofNat_907_, v___x_924_);
v___y_912_ = v___x_925_;
goto v___jp_911_;
}
v___jp_911_:
{
lean_object* v___x_913_; 
lean_inc(v_toMul_906_);
v___x_913_ = lean_apply_2(v_toMul_906_, v_acc_905_, v___y_912_);
v_m_904_ = v_m_910_;
v_acc_905_ = v___x_913_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg___boxed(lean_object* v_inst_926_, lean_object* v_ctx_927_, lean_object* v_m_928_, lean_object* v_acc_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_926_, v_ctx_927_, v_m_928_, v_acc_929_);
lean_dec_ref(v_ctx_927_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go(lean_object* v_00_u03b1_931_, lean_object* v_inst_932_, lean_object* v_ctx_933_, lean_object* v_m_934_, lean_object* v_acc_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_932_, v_ctx_933_, v_m_934_, v_acc_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___boxed(lean_object* v_00_u03b1_937_, lean_object* v_inst_938_, lean_object* v_ctx_939_, lean_object* v_m_940_, lean_object* v_acc_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Grind_CommRing_Mon_denote_x27_go(v_00_u03b1_937_, v_inst_938_, v_ctx_939_, v_m_940_, v_acc_941_);
lean_dec_ref(v_ctx_939_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg(lean_object* v_inst_943_, lean_object* v_ctx_944_, lean_object* v_m_945_){
_start:
{
if (lean_obj_tag(v_m_945_) == 0)
{
lean_object* v_ofNat_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_ofNat_946_ = lean_ctor_get(v_inst_943_, 3);
lean_inc(v_ofNat_946_);
lean_dec_ref(v_inst_943_);
v___x_947_ = lean_unsigned_to_nat(1u);
v___x_948_ = lean_apply_1(v_ofNat_946_, v___x_947_);
return v___x_948_;
}
else
{
lean_object* v_p_949_; lean_object* v_m_950_; lean_object* v_ofNat_951_; lean_object* v_npow_952_; lean_object* v_x_953_; lean_object* v_k_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v_p_949_ = lean_ctor_get(v_m_945_, 0);
lean_inc_ref(v_p_949_);
v_m_950_ = lean_ctor_get(v_m_945_, 1);
lean_inc(v_m_950_);
lean_dec_ref_known(v_m_945_, 2);
v_ofNat_951_ = lean_ctor_get(v_inst_943_, 3);
v_npow_952_ = lean_ctor_get(v_inst_943_, 5);
v_x_953_ = lean_ctor_get(v_p_949_, 0);
lean_inc(v_x_953_);
v_k_954_ = lean_ctor_get(v_p_949_, 1);
lean_inc(v_k_954_);
lean_dec_ref(v_p_949_);
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = lean_nat_dec_eq(v_k_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = lean_unsigned_to_nat(1u);
v___x_958_ = lean_nat_dec_eq(v_k_954_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = l_Lean_RArray_getImpl___redArg(v_ctx_944_, v_x_953_);
lean_dec(v_x_953_);
lean_inc(v_npow_952_);
v___x_960_ = lean_apply_2(v_npow_952_, v___x_959_, v_k_954_);
v___x_961_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_943_, v_ctx_944_, v_m_950_, v___x_960_);
return v___x_961_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec(v_k_954_);
v___x_962_ = l_Lean_RArray_getImpl___redArg(v_ctx_944_, v_x_953_);
lean_dec(v_x_953_);
v___x_963_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_943_, v_ctx_944_, v_m_950_, v___x_962_);
return v___x_963_;
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec(v_k_954_);
lean_dec(v_x_953_);
v___x_964_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_951_);
v___x_965_ = lean_apply_1(v_ofNat_951_, v___x_964_);
v___x_966_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_943_, v_ctx_944_, v_m_950_, v___x_965_);
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg___boxed(lean_object* v_inst_967_, lean_object* v_ctx_968_, lean_object* v_m_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Grind_CommRing_Mon_denote_x27___redArg(v_inst_967_, v_ctx_968_, v_m_969_);
lean_dec_ref(v_ctx_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27(lean_object* v_00_u03b1_971_, lean_object* v_inst_972_, lean_object* v_ctx_973_, lean_object* v_m_974_){
_start:
{
if (lean_obj_tag(v_m_974_) == 0)
{
lean_object* v_ofNat_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_ofNat_975_ = lean_ctor_get(v_inst_972_, 3);
lean_inc(v_ofNat_975_);
lean_dec_ref(v_inst_972_);
v___x_976_ = lean_unsigned_to_nat(1u);
v___x_977_ = lean_apply_1(v_ofNat_975_, v___x_976_);
return v___x_977_;
}
else
{
lean_object* v_p_978_; lean_object* v_m_979_; lean_object* v_ofNat_980_; lean_object* v_npow_981_; lean_object* v_x_982_; lean_object* v_k_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v_p_978_ = lean_ctor_get(v_m_974_, 0);
lean_inc_ref(v_p_978_);
v_m_979_ = lean_ctor_get(v_m_974_, 1);
lean_inc(v_m_979_);
lean_dec_ref_known(v_m_974_, 2);
v_ofNat_980_ = lean_ctor_get(v_inst_972_, 3);
v_npow_981_ = lean_ctor_get(v_inst_972_, 5);
v_x_982_ = lean_ctor_get(v_p_978_, 0);
lean_inc(v_x_982_);
v_k_983_ = lean_ctor_get(v_p_978_, 1);
lean_inc(v_k_983_);
lean_dec_ref(v_p_978_);
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = lean_nat_dec_eq(v_k_983_, v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = lean_unsigned_to_nat(1u);
v___x_987_ = lean_nat_dec_eq(v_k_983_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = l_Lean_RArray_getImpl___redArg(v_ctx_973_, v_x_982_);
lean_dec(v_x_982_);
lean_inc(v_npow_981_);
v___x_989_ = lean_apply_2(v_npow_981_, v___x_988_, v_k_983_);
v___x_990_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_972_, v_ctx_973_, v_m_979_, v___x_989_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; 
lean_dec(v_k_983_);
v___x_991_ = l_Lean_RArray_getImpl___redArg(v_ctx_973_, v_x_982_);
lean_dec(v_x_982_);
v___x_992_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_972_, v_ctx_973_, v_m_979_, v___x_991_);
return v___x_992_;
}
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec(v_k_983_);
lean_dec(v_x_982_);
v___x_993_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_980_);
v___x_994_ = lean_apply_1(v_ofNat_980_, v___x_993_);
v___x_995_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_972_, v_ctx_973_, v_m_979_, v___x_994_);
return v___x_995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___boxed(lean_object* v_00_u03b1_996_, lean_object* v_inst_997_, lean_object* v_ctx_998_, lean_object* v_m_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Grind_CommRing_Mon_denote_x27(v_00_u03b1_996_, v_inst_997_, v_ctx_998_, v_m_999_);
lean_dec_ref(v_ctx_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ofVar(lean_object* v_x_1001_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v_x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_box(0);
v___x_1005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat(lean_object* v_m_u2081_1006_, lean_object* v_m_u2082_1007_){
_start:
{
if (lean_obj_tag(v_m_u2081_1006_) == 0)
{
lean_inc(v_m_u2082_1007_);
return v_m_u2082_1007_;
}
else
{
lean_object* v_p_1008_; lean_object* v_m_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1017_; 
v_p_1008_ = lean_ctor_get(v_m_u2081_1006_, 0);
v_m_1009_ = lean_ctor_get(v_m_u2081_1006_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_m_u2081_1006_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1011_ = v_m_u2081_1006_;
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_m_1009_);
lean_inc(v_p_1008_);
lean_dec(v_m_u2081_1006_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = l_Lean_Grind_CommRing_Mon_concat(v_m_1009_, v_m_u2082_1007_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 1, v___x_1013_);
v___x_1015_ = v___x_1011_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_p_1008_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat___boxed(lean_object* v_m_u2081_1018_, lean_object* v_m_u2082_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_1018_, v_m_u2082_1019_);
lean_dec(v_m_u2082_1019_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow(lean_object* v_pw_1021_, lean_object* v_m_1022_){
_start:
{
if (lean_obj_tag(v_m_1022_) == 0)
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1023_, 0, v_pw_1021_);
lean_ctor_set(v___x_1023_, 1, v_m_1022_);
return v___x_1023_;
}
else
{
lean_object* v_p_1024_; lean_object* v_m_1025_; uint8_t v___x_1026_; 
v_p_1024_ = lean_ctor_get(v_m_1022_, 0);
lean_inc_ref(v_p_1024_);
v_m_1025_ = lean_ctor_get(v_m_1022_, 1);
v___x_1026_ = l_Lean_Grind_CommRing_Power_varLt(v_pw_1021_, v_p_1024_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1050_; 
lean_inc(v_m_1025_);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_m_1022_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; lean_object* v_unused_1052_; 
v_unused_1051_ = lean_ctor_get(v_m_1022_, 1);
lean_dec(v_unused_1051_);
v_unused_1052_ = lean_ctor_get(v_m_1022_, 0);
lean_dec(v_unused_1052_);
v___x_1028_ = v_m_1022_;
v_isShared_1029_ = v_isSharedCheck_1050_;
goto v_resetjp_1027_;
}
else
{
lean_dec(v_m_1022_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1050_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
uint8_t v___x_1030_; 
v___x_1030_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1024_, v_pw_1021_);
if (v___x_1030_ == 0)
{
lean_object* v_x_1031_; lean_object* v_k_1032_; lean_object* v_k_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1044_; 
v_x_1031_ = lean_ctor_get(v_pw_1021_, 0);
lean_inc(v_x_1031_);
v_k_1032_ = lean_ctor_get(v_pw_1021_, 1);
lean_inc(v_k_1032_);
lean_dec_ref(v_pw_1021_);
v_k_1033_ = lean_ctor_get(v_p_1024_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_p_1024_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v_p_1024_, 0);
lean_dec(v_unused_1045_);
v___x_1035_ = v_p_1024_;
v_isShared_1036_ = v_isSharedCheck_1044_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_k_1033_);
lean_dec(v_p_1024_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1044_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = lean_nat_add(v_k_1032_, v_k_1033_);
lean_dec(v_k_1033_);
lean_dec(v_k_1032_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v___x_1037_);
lean_ctor_set(v___x_1035_, 0, v_x_1031_);
v___x_1039_ = v___x_1035_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_x_1031_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1039_);
v___x_1041_ = v___x_1028_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_m_1025_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = l_Lean_Grind_CommRing_Mon_mulPow(v_pw_1021_, v_m_1025_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v___x_1046_);
v___x_1048_ = v___x_1028_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_p_1024_);
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
else
{
lean_object* v___x_1053_; 
lean_dec_ref(v_p_1024_);
v___x_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_pw_1021_);
lean_ctor_set(v___x_1053_, 1, v_m_1022_);
return v___x_1053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow__nc(lean_object* v_pw_1054_, lean_object* v_m_1055_){
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
lean_object* v_p_1057_; lean_object* v_m_1058_; lean_object* v_x_1059_; lean_object* v_k_1060_; lean_object* v_x_1061_; lean_object* v_k_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1081_; 
v_p_1057_ = lean_ctor_get(v_m_1055_, 0);
lean_inc_ref(v_p_1057_);
v_m_1058_ = lean_ctor_get(v_m_1055_, 1);
v_x_1059_ = lean_ctor_get(v_pw_1054_, 0);
v_k_1060_ = lean_ctor_get(v_pw_1054_, 1);
v_x_1061_ = lean_ctor_get(v_p_1057_, 0);
v_k_1062_ = lean_ctor_get(v_p_1057_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_p_1057_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1064_ = v_p_1057_;
v_isShared_1065_ = v_isSharedCheck_1081_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_k_1062_);
lean_inc(v_x_1061_);
lean_dec(v_p_1057_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1081_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
uint8_t v___x_1066_; 
v___x_1066_ = lean_nat_dec_eq(v_x_1059_, v_x_1061_);
lean_dec(v_x_1061_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
lean_del_object(v___x_1064_);
lean_dec(v_k_1062_);
v___x_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1067_, 0, v_pw_1054_);
lean_ctor_set(v___x_1067_, 1, v_m_1055_);
return v___x_1067_;
}
else
{
lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1078_; 
lean_inc(v_k_1060_);
lean_inc(v_x_1059_);
lean_inc(v_m_1058_);
lean_dec_ref(v_pw_1054_);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_m_1055_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; lean_object* v_unused_1080_; 
v_unused_1079_ = lean_ctor_get(v_m_1055_, 1);
lean_dec(v_unused_1079_);
v_unused_1080_ = lean_ctor_get(v_m_1055_, 0);
lean_dec(v_unused_1080_);
v___x_1069_ = v_m_1055_;
v_isShared_1070_ = v_isSharedCheck_1078_;
goto v_resetjp_1068_;
}
else
{
lean_dec(v_m_1055_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1078_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1071_ = lean_nat_add(v_k_1060_, v_k_1062_);
lean_dec(v_k_1062_);
lean_dec(v_k_1060_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 1, v___x_1071_);
lean_ctor_set(v___x_1064_, 0, v_x_1059_);
v___x_1073_ = v___x_1064_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_x_1059_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1075_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1073_);
v___x_1075_ = v___x_1069_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_m_1058_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length(lean_object* v_x_1082_){
_start:
{
if (lean_obj_tag(v_x_1082_) == 0)
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_unsigned_to_nat(0u);
return v___x_1083_;
}
else
{
lean_object* v_m_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_m_1084_ = lean_ctor_get(v_x_1082_, 1);
v___x_1085_ = lean_unsigned_to_nat(1u);
v___x_1086_ = l_Lean_Grind_CommRing_Mon_length(v_m_1084_);
v___x_1087_ = lean_nat_add(v___x_1085_, v___x_1086_);
lean_dec(v___x_1086_);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length___boxed(lean_object* v_x_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Grind_CommRing_Mon_length(v_x_1088_);
lean_dec(v_x_1088_);
return v_res_1089_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_hugeFuel(void){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_unsigned_to_nat(1000000u);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go(lean_object* v_fuel_1091_, lean_object* v_m_u2081_1092_, lean_object* v_m_u2082_1093_){
_start:
{
lean_object* v_zero_1094_; uint8_t v_isZero_1095_; 
v_zero_1094_ = lean_unsigned_to_nat(0u);
v_isZero_1095_ = lean_nat_dec_eq(v_fuel_1091_, v_zero_1094_);
if (v_isZero_1095_ == 1)
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_1092_, v_m_u2082_1093_);
lean_dec(v_m_u2082_1093_);
return v___x_1096_;
}
else
{
if (lean_obj_tag(v_m_u2082_1093_) == 0)
{
return v_m_u2081_1092_;
}
else
{
if (lean_obj_tag(v_m_u2081_1092_) == 0)
{
return v_m_u2082_1093_;
}
else
{
lean_object* v_p_1097_; lean_object* v_m_1098_; lean_object* v_p_1099_; lean_object* v_m_1100_; lean_object* v_one_1101_; lean_object* v_n_1102_; uint8_t v___x_1103_; 
v_p_1097_ = lean_ctor_get(v_m_u2082_1093_, 0);
lean_inc_ref(v_p_1097_);
v_m_1098_ = lean_ctor_get(v_m_u2082_1093_, 1);
v_p_1099_ = lean_ctor_get(v_m_u2081_1092_, 0);
v_m_1100_ = lean_ctor_get(v_m_u2081_1092_, 1);
v_one_1101_ = lean_unsigned_to_nat(1u);
v_n_1102_ = lean_nat_sub(v_fuel_1091_, v_one_1101_);
v___x_1103_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1099_, v_p_1097_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1134_; 
lean_inc(v_m_1098_);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_m_u2082_1093_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; lean_object* v_unused_1136_; 
v_unused_1135_ = lean_ctor_get(v_m_u2082_1093_, 1);
lean_dec(v_unused_1135_);
v_unused_1136_ = lean_ctor_get(v_m_u2082_1093_, 0);
lean_dec(v_unused_1136_);
v___x_1105_ = v_m_u2082_1093_;
v_isShared_1106_ = v_isSharedCheck_1134_;
goto v_resetjp_1104_;
}
else
{
lean_dec(v_m_u2082_1093_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1134_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
uint8_t v___x_1107_; 
v___x_1107_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1097_, v_p_1099_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1127_; 
lean_inc(v_m_1100_);
lean_inc_ref(v_p_1099_);
lean_del_object(v___x_1105_);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_m_u2081_1092_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; lean_object* v_unused_1129_; 
v_unused_1128_ = lean_ctor_get(v_m_u2081_1092_, 1);
lean_dec(v_unused_1128_);
v_unused_1129_ = lean_ctor_get(v_m_u2081_1092_, 0);
lean_dec(v_unused_1129_);
v___x_1109_ = v_m_u2081_1092_;
v_isShared_1110_ = v_isSharedCheck_1127_;
goto v_resetjp_1108_;
}
else
{
lean_dec(v_m_u2081_1092_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1127_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_x_1111_; lean_object* v_k_1112_; lean_object* v_k_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1125_; 
v_x_1111_ = lean_ctor_get(v_p_1099_, 0);
lean_inc(v_x_1111_);
v_k_1112_ = lean_ctor_get(v_p_1099_, 1);
lean_inc(v_k_1112_);
lean_dec_ref(v_p_1099_);
v_k_1113_ = lean_ctor_get(v_p_1097_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_p_1097_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v_p_1097_, 0);
lean_dec(v_unused_1126_);
v___x_1115_ = v_p_1097_;
v_isShared_1116_ = v_isSharedCheck_1125_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_k_1113_);
lean_dec(v_p_1097_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1125_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1117_ = lean_nat_add(v_k_1112_, v_k_1113_);
lean_dec(v_k_1113_);
lean_dec(v_k_1112_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 1, v___x_1117_);
lean_ctor_set(v___x_1115_, 0, v_x_1111_);
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_x_1111_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1120_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1102_, v_m_1100_, v_m_1098_);
lean_dec(v_n_1102_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v___x_1120_);
lean_ctor_set(v___x_1109_, 0, v___x_1119_);
v___x_1122_ = v___x_1109_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1102_, v_m_u2081_1092_, v_m_1098_);
lean_dec(v_n_1102_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 1, v___x_1130_);
v___x_1132_ = v___x_1105_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_p_1097_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1144_; 
lean_inc(v_m_1100_);
lean_inc_ref(v_p_1099_);
lean_dec_ref(v_p_1097_);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_m_u2081_1092_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; lean_object* v_unused_1146_; 
v_unused_1145_ = lean_ctor_get(v_m_u2081_1092_, 1);
lean_dec(v_unused_1145_);
v_unused_1146_ = lean_ctor_get(v_m_u2081_1092_, 0);
lean_dec(v_unused_1146_);
v___x_1138_ = v_m_u2081_1092_;
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
else
{
lean_dec(v_m_u2081_1092_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1102_, v_m_1100_, v_m_u2082_1093_);
lean_dec(v_n_1102_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_p_1099_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go___boxed(lean_object* v_fuel_1147_, lean_object* v_m_u2081_1148_, lean_object* v_m_u2082_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Grind_CommRing_Mon_mul_go(v_fuel_1147_, v_m_u2081_1148_, v_m_u2082_1149_);
lean_dec(v_fuel_1147_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul(lean_object* v_m_u2081_1151_, lean_object* v_m_u2082_1152_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_unsigned_to_nat(1000000u);
v___x_1154_ = l_Lean_Grind_CommRing_Mon_mul_go(v___x_1153_, v_m_u2081_1151_, v_m_u2082_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object* v_fuel_1155_, lean_object* v_h__1_1156_, lean_object* v_h__2_1157_){
_start:
{
lean_object* v_zero_1158_; uint8_t v_isZero_1159_; 
v_zero_1158_ = lean_unsigned_to_nat(0u);
v_isZero_1159_ = lean_nat_dec_eq(v_fuel_1155_, v_zero_1158_);
if (v_isZero_1159_ == 1)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v_h__2_1157_);
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_apply_1(v_h__1_1156_, v___x_1160_);
return v___x_1161_;
}
else
{
lean_object* v_one_1162_; lean_object* v_n_1163_; lean_object* v___x_1164_; 
lean_dec(v_h__1_1156_);
v_one_1162_ = lean_unsigned_to_nat(1u);
v_n_1163_ = lean_nat_sub(v_fuel_1155_, v_one_1162_);
v___x_1164_ = lean_apply_1(v_h__2_1157_, v_n_1163_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object* v_fuel_1165_, lean_object* v_h__1_1166_, lean_object* v_h__2_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(v_fuel_1165_, v_h__1_1166_, v_h__2_1167_);
lean_dec(v_fuel_1165_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object* v_motive_1169_, lean_object* v_fuel_1170_, lean_object* v_h__1_1171_, lean_object* v_h__2_1172_){
_start:
{
lean_object* v_zero_1173_; uint8_t v_isZero_1174_; 
v_zero_1173_ = lean_unsigned_to_nat(0u);
v_isZero_1174_ = lean_nat_dec_eq(v_fuel_1170_, v_zero_1173_);
if (v_isZero_1174_ == 1)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec(v_h__2_1172_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_apply_1(v_h__1_1171_, v___x_1175_);
return v___x_1176_;
}
else
{
lean_object* v_one_1177_; lean_object* v_n_1178_; lean_object* v___x_1179_; 
lean_dec(v_h__1_1171_);
v_one_1177_ = lean_unsigned_to_nat(1u);
v_n_1178_ = lean_nat_sub(v_fuel_1170_, v_one_1177_);
v___x_1179_ = lean_apply_1(v_h__2_1172_, v_n_1178_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object* v_motive_1180_, lean_object* v_fuel_1181_, lean_object* v_h__1_1182_, lean_object* v_h__2_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(v_motive_1180_, v_fuel_1181_, v_h__1_1182_, v_h__2_1183_);
lean_dec(v_fuel_1181_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter___redArg(lean_object* v_m_u2081_1185_, lean_object* v_m_u2082_1186_, lean_object* v_h__1_1187_, lean_object* v_h__2_1188_, lean_object* v_h__3_1189_){
_start:
{
if (lean_obj_tag(v_m_u2082_1186_) == 0)
{
lean_object* v___x_1190_; 
lean_dec(v_h__3_1189_);
lean_dec(v_h__2_1188_);
v___x_1190_ = lean_apply_1(v_h__1_1187_, v_m_u2081_1185_);
return v___x_1190_;
}
else
{
lean_dec(v_h__1_1187_);
if (lean_obj_tag(v_m_u2081_1185_) == 0)
{
lean_object* v___x_1191_; 
lean_dec(v_h__3_1189_);
v___x_1191_ = lean_apply_2(v_h__2_1188_, v_m_u2082_1186_, lean_box(0));
return v___x_1191_;
}
else
{
lean_object* v_p_1192_; lean_object* v_m_1193_; lean_object* v_p_1194_; lean_object* v_m_1195_; lean_object* v___x_1196_; 
lean_dec(v_h__2_1188_);
v_p_1192_ = lean_ctor_get(v_m_u2082_1186_, 0);
lean_inc_ref(v_p_1192_);
v_m_1193_ = lean_ctor_get(v_m_u2082_1186_, 1);
lean_inc(v_m_1193_);
lean_dec_ref_known(v_m_u2082_1186_, 2);
v_p_1194_ = lean_ctor_get(v_m_u2081_1185_, 0);
lean_inc_ref(v_p_1194_);
v_m_1195_ = lean_ctor_get(v_m_u2081_1185_, 1);
lean_inc(v_m_1195_);
lean_dec_ref_known(v_m_u2081_1185_, 2);
v___x_1196_ = lean_apply_4(v_h__3_1189_, v_p_1194_, v_m_1195_, v_p_1192_, v_m_1193_);
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter(lean_object* v_motive_1197_, lean_object* v_m_u2081_1198_, lean_object* v_m_u2082_1199_, lean_object* v_h__1_1200_, lean_object* v_h__2_1201_, lean_object* v_h__3_1202_){
_start:
{
if (lean_obj_tag(v_m_u2082_1199_) == 0)
{
lean_object* v___x_1203_; 
lean_dec(v_h__3_1202_);
lean_dec(v_h__2_1201_);
v___x_1203_ = lean_apply_1(v_h__1_1200_, v_m_u2081_1198_);
return v___x_1203_;
}
else
{
lean_dec(v_h__1_1200_);
if (lean_obj_tag(v_m_u2081_1198_) == 0)
{
lean_object* v___x_1204_; 
lean_dec(v_h__3_1202_);
v___x_1204_ = lean_apply_2(v_h__2_1201_, v_m_u2082_1199_, lean_box(0));
return v___x_1204_;
}
else
{
lean_object* v_p_1205_; lean_object* v_m_1206_; lean_object* v_p_1207_; lean_object* v_m_1208_; lean_object* v___x_1209_; 
lean_dec(v_h__2_1201_);
v_p_1205_ = lean_ctor_get(v_m_u2082_1199_, 0);
lean_inc_ref(v_p_1205_);
v_m_1206_ = lean_ctor_get(v_m_u2082_1199_, 1);
lean_inc(v_m_1206_);
lean_dec_ref_known(v_m_u2082_1199_, 2);
v_p_1207_ = lean_ctor_get(v_m_u2081_1198_, 0);
lean_inc_ref(v_p_1207_);
v_m_1208_ = lean_ctor_get(v_m_u2081_1198_, 1);
lean_inc(v_m_1208_);
lean_dec_ref_known(v_m_u2081_1198_, 2);
v___x_1209_ = lean_apply_4(v_h__3_1202_, v_p_1207_, v_m_1208_, v_p_1205_, v_m_1206_);
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul__nc(lean_object* v_m_u2081_1210_, lean_object* v_m_u2082_1211_){
_start:
{
if (lean_obj_tag(v_m_u2081_1210_) == 0)
{
return v_m_u2082_1211_;
}
else
{
lean_object* v_m_1212_; 
v_m_1212_ = lean_ctor_get(v_m_u2081_1210_, 1);
if (lean_obj_tag(v_m_1212_) == 0)
{
lean_object* v_p_1213_; lean_object* v___x_1214_; 
v_p_1213_ = lean_ctor_get(v_m_u2081_1210_, 0);
lean_inc_ref(v_p_1213_);
lean_dec_ref_known(v_m_u2081_1210_, 2);
v___x_1214_ = l_Lean_Grind_CommRing_Mon_mulPow__nc(v_p_1213_, v_m_u2082_1211_);
return v___x_1214_;
}
else
{
lean_object* v_p_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
lean_inc(v_m_1212_);
v_p_1215_ = lean_ctor_get(v_m_u2081_1210_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_m_u2081_1210_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v_m_u2081_1210_, 1);
lean_dec(v_unused_1224_);
v___x_1217_ = v_m_u2081_1210_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_p_1215_);
lean_dec(v_m_u2081_1210_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_1212_, v_m_u2082_1211_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v___x_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_p_1215_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object* v_x_1225_){
_start:
{
if (lean_obj_tag(v_x_1225_) == 0)
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_unsigned_to_nat(0u);
return v___x_1226_;
}
else
{
lean_object* v_p_1227_; lean_object* v_m_1228_; lean_object* v_k_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_p_1227_ = lean_ctor_get(v_x_1225_, 0);
v_m_1228_ = lean_ctor_get(v_x_1225_, 1);
v_k_1229_ = lean_ctor_get(v_p_1227_, 1);
v___x_1230_ = l_Lean_Grind_CommRing_Mon_degree(v_m_1228_);
v___x_1231_ = lean_nat_add(v_k_1229_, v___x_1230_);
lean_dec(v___x_1230_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree___boxed(lean_object* v_x_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_Grind_CommRing_Mon_degree(v_x_1232_);
lean_dec(v_x_1232_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object* v_x_1234_, lean_object* v_h__1_1235_, lean_object* v_h__2_1236_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v_h__2_1236_);
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_apply_1(v_h__1_1235_, v___x_1237_);
return v___x_1238_;
}
else
{
lean_object* v_p_1239_; lean_object* v_m_1240_; lean_object* v___x_1241_; 
lean_dec(v_h__1_1235_);
v_p_1239_ = lean_ctor_get(v_x_1234_, 0);
lean_inc_ref(v_p_1239_);
v_m_1240_ = lean_ctor_get(v_x_1234_, 1);
lean_inc(v_m_1240_);
lean_dec_ref_known(v_x_1234_, 2);
v___x_1241_ = lean_apply_2(v_h__2_1236_, v_p_1239_, v_m_1240_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object* v_motive_1242_, lean_object* v_x_1243_, lean_object* v_h__1_1244_, lean_object* v_h__2_1245_){
_start:
{
if (lean_obj_tag(v_x_1243_) == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec(v_h__2_1245_);
v___x_1246_ = lean_box(0);
v___x_1247_ = lean_apply_1(v_h__1_1244_, v___x_1246_);
return v___x_1247_;
}
else
{
lean_object* v_p_1248_; lean_object* v_m_1249_; lean_object* v___x_1250_; 
lean_dec(v_h__1_1244_);
v_p_1248_ = lean_ctor_get(v_x_1243_, 0);
lean_inc_ref(v_p_1248_);
v_m_1249_ = lean_ctor_get(v_x_1243_, 1);
lean_inc(v_m_1249_);
lean_dec_ref_known(v_x_1243_, 2);
v___x_1250_ = lean_apply_2(v_h__2_1245_, v_p_1248_, v_m_1249_);
return v___x_1250_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Var_revlex(lean_object* v_x_1251_, lean_object* v_y_1252_){
_start:
{
uint8_t v___x_1253_; 
v___x_1253_ = l_Nat_blt(v_x_1251_, v_y_1252_);
if (v___x_1253_ == 0)
{
uint8_t v___x_1254_; 
v___x_1254_ = l_Nat_blt(v_y_1252_, v_x_1251_);
if (v___x_1254_ == 0)
{
uint8_t v___x_1255_; 
v___x_1255_ = 1;
return v___x_1255_;
}
else
{
uint8_t v___x_1256_; 
v___x_1256_ = 0;
return v___x_1256_;
}
}
else
{
uint8_t v___x_1257_; 
v___x_1257_ = 2;
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_revlex___boxed(lean_object* v_x_1258_, lean_object* v_y_1259_){
_start:
{
uint8_t v_res_1260_; lean_object* v_r_1261_; 
v_res_1260_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1258_, v_y_1259_);
lean_dec(v_y_1259_);
lean_dec(v_x_1258_);
v_r_1261_ = lean_box(v_res_1260_);
return v_r_1261_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_powerRevlex(lean_object* v_k_u2081_1262_, lean_object* v_k_u2082_1263_){
_start:
{
uint8_t v___x_1264_; 
v___x_1264_ = l_Nat_blt(v_k_u2081_1262_, v_k_u2082_1263_);
if (v___x_1264_ == 0)
{
uint8_t v___x_1265_; 
v___x_1265_ = l_Nat_blt(v_k_u2082_1263_, v_k_u2081_1262_);
if (v___x_1265_ == 0)
{
uint8_t v___x_1266_; 
v___x_1266_ = 1;
return v___x_1266_;
}
else
{
uint8_t v___x_1267_; 
v___x_1267_ = 0;
return v___x_1267_;
}
}
else
{
uint8_t v___x_1268_; 
v___x_1268_ = 2;
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_powerRevlex___boxed(lean_object* v_k_u2081_1269_, lean_object* v_k_u2082_1270_){
_start:
{
uint8_t v_res_1271_; lean_object* v_r_1272_; 
v_res_1271_ = l_Lean_Grind_CommRing_powerRevlex(v_k_u2081_1269_, v_k_u2082_1270_);
lean_dec(v_k_u2082_1270_);
lean_dec(v_k_u2081_1269_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(uint8_t v_c_1273_, lean_object* v_h__1_1274_, lean_object* v_h__2_1275_){
_start:
{
if (v_c_1273_ == 0)
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_dec(v_h__1_1274_);
v___x_1276_ = lean_box(0);
v___x_1277_ = lean_apply_1(v_h__2_1275_, v___x_1276_);
return v___x_1277_;
}
else
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_dec(v_h__2_1275_);
v___x_1278_ = lean_box(0);
v___x_1279_ = lean_apply_1(v_h__1_1274_, v___x_1278_);
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg___boxed(lean_object* v_c_1280_, lean_object* v_h__1_1281_, lean_object* v_h__2_1282_){
_start:
{
uint8_t v_c_24__boxed_1283_; lean_object* v_res_1284_; 
v_c_24__boxed_1283_ = lean_unbox(v_c_1280_);
v_res_1284_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(v_c_24__boxed_1283_, v_h__1_1281_, v_h__2_1282_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(lean_object* v_motive_1285_, uint8_t v_c_1286_, lean_object* v_h__1_1287_, lean_object* v_h__2_1288_){
_start:
{
if (v_c_1286_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_dec(v_h__1_1287_);
v___x_1289_ = lean_box(0);
v___x_1290_ = lean_apply_1(v_h__2_1288_, v___x_1289_);
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec(v_h__2_1288_);
v___x_1291_ = lean_box(0);
v___x_1292_ = lean_apply_1(v_h__1_1287_, v___x_1291_);
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___boxed(lean_object* v_motive_1293_, lean_object* v_c_1294_, lean_object* v_h__1_1295_, lean_object* v_h__2_1296_){
_start:
{
uint8_t v_c_35__boxed_1297_; lean_object* v_res_1298_; 
v_c_35__boxed_1297_ = lean_unbox(v_c_1294_);
v_res_1298_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(v_motive_1293_, v_c_35__boxed_1297_, v_h__1_1295_, v_h__2_1296_);
return v_res_1298_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_revlex(lean_object* v_p_u2081_1299_, lean_object* v_p_u2082_1300_){
_start:
{
lean_object* v_x_1301_; lean_object* v_k_1302_; lean_object* v_x_1303_; lean_object* v_k_1304_; uint8_t v___x_1305_; 
v_x_1301_ = lean_ctor_get(v_p_u2081_1299_, 0);
v_k_1302_ = lean_ctor_get(v_p_u2081_1299_, 1);
v_x_1303_ = lean_ctor_get(v_p_u2082_1300_, 0);
v_k_1304_ = lean_ctor_get(v_p_u2082_1300_, 1);
v___x_1305_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1301_, v_x_1303_);
if (v___x_1305_ == 1)
{
uint8_t v___x_1306_; 
v___x_1306_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1302_, v_k_1304_);
return v___x_1306_;
}
else
{
return v___x_1305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_revlex___boxed(lean_object* v_p_u2081_1307_, lean_object* v_p_u2082_1308_){
_start:
{
uint8_t v_res_1309_; lean_object* v_r_1310_; 
v_res_1309_ = l_Lean_Grind_CommRing_Power_revlex(v_p_u2081_1307_, v_p_u2082_1308_);
lean_dec_ref(v_p_u2082_1308_);
lean_dec_ref(v_p_u2081_1307_);
v_r_1310_ = lean_box(v_res_1309_);
return v_r_1310_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexWF(lean_object* v_m_u2081_1311_, lean_object* v_m_u2082_1312_){
_start:
{
if (lean_obj_tag(v_m_u2081_1311_) == 0)
{
if (lean_obj_tag(v_m_u2082_1312_) == 0)
{
uint8_t v___x_1313_; 
v___x_1313_ = 1;
return v___x_1313_;
}
else
{
uint8_t v___x_1314_; 
v___x_1314_ = 2;
return v___x_1314_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1312_) == 0)
{
uint8_t v___x_1315_; 
v___x_1315_ = 0;
return v___x_1315_;
}
else
{
lean_object* v_p_1316_; lean_object* v_p_1317_; lean_object* v_m_1318_; lean_object* v_m_1319_; lean_object* v_x_1320_; lean_object* v_k_1321_; lean_object* v_x_1322_; lean_object* v_k_1323_; uint8_t v___x_1324_; 
v_p_1316_ = lean_ctor_get(v_m_u2081_1311_, 0);
v_p_1317_ = lean_ctor_get(v_m_u2082_1312_, 0);
v_m_1318_ = lean_ctor_get(v_m_u2081_1311_, 1);
v_m_1319_ = lean_ctor_get(v_m_u2082_1312_, 1);
v_x_1320_ = lean_ctor_get(v_p_1316_, 0);
v_k_1321_ = lean_ctor_get(v_p_1316_, 1);
v_x_1322_ = lean_ctor_get(v_p_1317_, 0);
v_k_1323_ = lean_ctor_get(v_p_1317_, 1);
v___x_1324_ = lean_nat_dec_eq(v_x_1320_, v_x_1322_);
if (v___x_1324_ == 0)
{
uint8_t v___x_1325_; 
v___x_1325_ = l_Nat_blt(v_x_1320_, v_x_1322_);
if (v___x_1325_ == 0)
{
uint8_t v___x_1326_; 
v___x_1326_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1311_, v_m_1319_);
if (v___x_1326_ == 1)
{
uint8_t v___x_1327_; 
v___x_1327_ = 2;
return v___x_1327_;
}
else
{
return v___x_1326_;
}
}
else
{
uint8_t v___x_1328_; 
v___x_1328_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1318_, v_m_u2082_1312_);
if (v___x_1328_ == 1)
{
uint8_t v___x_1329_; 
v___x_1329_ = 0;
return v___x_1329_;
}
else
{
return v___x_1328_;
}
}
}
else
{
uint8_t v___x_1330_; 
v___x_1330_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1318_, v_m_1319_);
if (v___x_1330_ == 1)
{
uint8_t v___x_1331_; 
v___x_1331_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1321_, v_k_1323_);
return v___x_1331_;
}
else
{
return v___x_1330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexWF___boxed(lean_object* v_m_u2081_1332_, lean_object* v_m_u2082_1333_){
_start:
{
uint8_t v_res_1334_; lean_object* v_r_1335_; 
v_res_1334_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1332_, v_m_u2082_1333_);
lean_dec(v_m_u2082_1333_);
lean_dec(v_m_u2081_1332_);
v_r_1335_ = lean_box(v_res_1334_);
return v_r_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(lean_object* v_m_u2081_1336_, lean_object* v_m_u2082_1337_, lean_object* v_h__1_1338_, lean_object* v_h__2_1339_, lean_object* v_h__3_1340_, lean_object* v_h__4_1341_){
_start:
{
if (lean_obj_tag(v_m_u2081_1336_) == 0)
{
lean_dec(v_h__4_1341_);
lean_dec(v_h__3_1340_);
if (lean_obj_tag(v_m_u2082_1337_) == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec(v_h__2_1339_);
v___x_1342_ = lean_box(0);
v___x_1343_ = lean_apply_1(v_h__1_1338_, v___x_1342_);
return v___x_1343_;
}
else
{
lean_object* v_p_1344_; lean_object* v_m_1345_; lean_object* v___x_1346_; 
lean_dec(v_h__1_1338_);
v_p_1344_ = lean_ctor_get(v_m_u2082_1337_, 0);
lean_inc_ref(v_p_1344_);
v_m_1345_ = lean_ctor_get(v_m_u2082_1337_, 1);
lean_inc(v_m_1345_);
lean_dec_ref_known(v_m_u2082_1337_, 2);
v___x_1346_ = lean_apply_2(v_h__2_1339_, v_p_1344_, v_m_1345_);
return v___x_1346_;
}
}
else
{
lean_dec(v_h__2_1339_);
lean_dec(v_h__1_1338_);
if (lean_obj_tag(v_m_u2082_1337_) == 0)
{
lean_object* v_p_1347_; lean_object* v_m_1348_; lean_object* v___x_1349_; 
lean_dec(v_h__4_1341_);
v_p_1347_ = lean_ctor_get(v_m_u2081_1336_, 0);
lean_inc_ref(v_p_1347_);
v_m_1348_ = lean_ctor_get(v_m_u2081_1336_, 1);
lean_inc(v_m_1348_);
lean_dec_ref_known(v_m_u2081_1336_, 2);
v___x_1349_ = lean_apply_2(v_h__3_1340_, v_p_1347_, v_m_1348_);
return v___x_1349_;
}
else
{
lean_object* v_p_1350_; lean_object* v_m_1351_; lean_object* v_p_1352_; lean_object* v_m_1353_; lean_object* v___x_1354_; 
lean_dec(v_h__3_1340_);
v_p_1350_ = lean_ctor_get(v_m_u2081_1336_, 0);
lean_inc_ref(v_p_1350_);
v_m_1351_ = lean_ctor_get(v_m_u2081_1336_, 1);
lean_inc(v_m_1351_);
lean_dec_ref_known(v_m_u2081_1336_, 2);
v_p_1352_ = lean_ctor_get(v_m_u2082_1337_, 0);
lean_inc_ref(v_p_1352_);
v_m_1353_ = lean_ctor_get(v_m_u2082_1337_, 1);
lean_inc(v_m_1353_);
lean_dec_ref_known(v_m_u2082_1337_, 2);
v___x_1354_ = lean_apply_4(v_h__4_1341_, v_p_1350_, v_m_1351_, v_p_1352_, v_m_1353_);
return v___x_1354_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter(lean_object* v_motive_1355_, lean_object* v_m_u2081_1356_, lean_object* v_m_u2082_1357_, lean_object* v_h__1_1358_, lean_object* v_h__2_1359_, lean_object* v_h__3_1360_, lean_object* v_h__4_1361_){
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
lean_dec_ref_known(v_m_u2082_1357_, 2);
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
lean_dec_ref_known(v_m_u2081_1356_, 2);
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
lean_dec_ref_known(v_m_u2081_1356_, 2);
v_p_1372_ = lean_ctor_get(v_m_u2082_1357_, 0);
lean_inc_ref(v_p_1372_);
v_m_1373_ = lean_ctor_get(v_m_u2082_1357_, 1);
lean_inc(v_m_1373_);
lean_dec_ref_known(v_m_u2082_1357_, 2);
v___x_1374_ = lean_apply_4(v_h__4_1361_, v_p_1370_, v_m_1371_, v_p_1372_, v_m_1373_);
return v___x_1374_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexFuel(lean_object* v_fuel_1375_, lean_object* v_m_u2081_1376_, lean_object* v_m_u2082_1377_){
_start:
{
lean_object* v_zero_1378_; uint8_t v_isZero_1379_; 
v_zero_1378_ = lean_unsigned_to_nat(0u);
v_isZero_1379_ = lean_nat_dec_eq(v_fuel_1375_, v_zero_1378_);
if (v_isZero_1379_ == 1)
{
uint8_t v___x_1380_; 
v___x_1380_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1376_, v_m_u2082_1377_);
return v___x_1380_;
}
else
{
if (lean_obj_tag(v_m_u2081_1376_) == 0)
{
if (lean_obj_tag(v_m_u2082_1377_) == 0)
{
uint8_t v___x_1381_; 
v___x_1381_ = 1;
return v___x_1381_;
}
else
{
uint8_t v___x_1382_; 
v___x_1382_ = 2;
return v___x_1382_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1377_) == 0)
{
uint8_t v___x_1383_; 
v___x_1383_ = 0;
return v___x_1383_;
}
else
{
lean_object* v_p_1384_; lean_object* v_p_1385_; lean_object* v_m_1386_; lean_object* v_m_1387_; lean_object* v_x_1388_; lean_object* v_k_1389_; lean_object* v_x_1390_; lean_object* v_k_1391_; lean_object* v_one_1392_; lean_object* v_n_1393_; uint8_t v___x_1394_; 
v_p_1384_ = lean_ctor_get(v_m_u2081_1376_, 0);
v_p_1385_ = lean_ctor_get(v_m_u2082_1377_, 0);
v_m_1386_ = lean_ctor_get(v_m_u2081_1376_, 1);
v_m_1387_ = lean_ctor_get(v_m_u2082_1377_, 1);
v_x_1388_ = lean_ctor_get(v_p_1384_, 0);
v_k_1389_ = lean_ctor_get(v_p_1384_, 1);
v_x_1390_ = lean_ctor_get(v_p_1385_, 0);
v_k_1391_ = lean_ctor_get(v_p_1385_, 1);
v_one_1392_ = lean_unsigned_to_nat(1u);
v_n_1393_ = lean_nat_sub(v_fuel_1375_, v_one_1392_);
v___x_1394_ = lean_nat_dec_eq(v_x_1388_, v_x_1390_);
if (v___x_1394_ == 0)
{
uint8_t v___x_1395_; 
v___x_1395_ = l_Nat_blt(v_x_1388_, v_x_1390_);
if (v___x_1395_ == 0)
{
uint8_t v___x_1396_; 
v___x_1396_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1393_, v_m_u2081_1376_, v_m_1387_);
lean_dec(v_n_1393_);
if (v___x_1396_ == 1)
{
uint8_t v___x_1397_; 
v___x_1397_ = 2;
return v___x_1397_;
}
else
{
return v___x_1396_;
}
}
else
{
uint8_t v___x_1398_; 
v___x_1398_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1393_, v_m_1386_, v_m_u2082_1377_);
lean_dec(v_n_1393_);
if (v___x_1398_ == 1)
{
uint8_t v___x_1399_; 
v___x_1399_ = 0;
return v___x_1399_;
}
else
{
return v___x_1398_;
}
}
}
else
{
uint8_t v___x_1400_; 
v___x_1400_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1393_, v_m_1386_, v_m_1387_);
lean_dec(v_n_1393_);
if (v___x_1400_ == 1)
{
uint8_t v___x_1401_; 
v___x_1401_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1389_, v_k_1391_);
return v___x_1401_;
}
else
{
return v___x_1400_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexFuel___boxed(lean_object* v_fuel_1402_, lean_object* v_m_u2081_1403_, lean_object* v_m_u2082_1404_){
_start:
{
uint8_t v_res_1405_; lean_object* v_r_1406_; 
v_res_1405_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_fuel_1402_, v_m_u2081_1403_, v_m_u2082_1404_);
lean_dec(v_m_u2082_1404_);
lean_dec(v_m_u2081_1403_);
lean_dec(v_fuel_1402_);
v_r_1406_ = lean_box(v_res_1405_);
return v_r_1406_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlex(lean_object* v_m_u2081_1407_, lean_object* v_m_u2082_1408_){
_start:
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = lean_unsigned_to_nat(1000000u);
v___x_1410_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v___x_1409_, v_m_u2081_1407_, v_m_u2082_1408_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlex___boxed(lean_object* v_m_u2081_1411_, lean_object* v_m_u2082_1412_){
_start:
{
uint8_t v_res_1413_; lean_object* v_r_1414_; 
v_res_1413_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1411_, v_m_u2082_1412_);
lean_dec(v_m_u2082_1412_);
lean_dec(v_m_u2081_1411_);
v_r_1414_ = lean_box(v_res_1413_);
return v_r_1414_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object* v_m_u2081_1415_, lean_object* v_m_u2082_1416_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1417_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2081_1415_);
v___x_1418_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2082_1416_);
v___x_1419_ = lean_nat_dec_lt(v___x_1417_, v___x_1418_);
if (v___x_1419_ == 0)
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_nat_dec_eq(v___x_1417_, v___x_1418_);
lean_dec(v___x_1418_);
lean_dec(v___x_1417_);
if (v___x_1420_ == 0)
{
uint8_t v___x_1421_; 
v___x_1421_ = 2;
return v___x_1421_;
}
else
{
uint8_t v___x_1422_; 
v___x_1422_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1415_, v_m_u2082_1416_);
return v___x_1422_;
}
}
else
{
uint8_t v___x_1423_; 
lean_dec(v___x_1418_);
lean_dec(v___x_1417_);
v___x_1423_ = 0;
return v___x_1423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_grevlex___boxed(lean_object* v_m_u2081_1424_, lean_object* v_m_u2082_1425_){
_start:
{
uint8_t v_res_1426_; lean_object* v_r_1427_; 
v_res_1426_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_u2081_1424_, v_m_u2082_1425_);
lean_dec(v_m_u2082_1425_);
lean_dec(v_m_u2081_1424_);
v_r_1427_ = lean_box(v_res_1426_);
return v_r_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___impl(lean_object* v_x_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_obj_tag_nat(v_x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___impl___boxed(lean_object* v_x_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_Grind_CommRing_Poly_ctorIdx___impl(v_x_1430_);
lean_dec_ref(v_x_1430_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___redArg(lean_object* v_t_1432_, lean_object* v_k_1433_){
_start:
{
if (lean_obj_tag(v_t_1432_) == 0)
{
lean_object* v_k_1434_; lean_object* v___x_1435_; 
v_k_1434_ = lean_ctor_get(v_t_1432_, 0);
lean_inc(v_k_1434_);
lean_dec_ref_known(v_t_1432_, 1);
v___x_1435_ = lean_apply_1(v_k_1433_, v_k_1434_);
return v___x_1435_;
}
else
{
lean_object* v_k_1436_; lean_object* v_v_1437_; lean_object* v_p_1438_; lean_object* v___x_1439_; 
v_k_1436_ = lean_ctor_get(v_t_1432_, 0);
lean_inc(v_k_1436_);
v_v_1437_ = lean_ctor_get(v_t_1432_, 1);
lean_inc(v_v_1437_);
v_p_1438_ = lean_ctor_get(v_t_1432_, 2);
lean_inc_ref(v_p_1438_);
lean_dec_ref_known(v_t_1432_, 3);
v___x_1439_ = lean_apply_3(v_k_1433_, v_k_1436_, v_v_1437_, v_p_1438_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim(lean_object* v_motive_1440_, lean_object* v_ctorIdx_1441_, lean_object* v_t_1442_, lean_object* v_h_1443_, lean_object* v_k_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1442_, v_k_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___boxed(lean_object* v_motive_1446_, lean_object* v_ctorIdx_1447_, lean_object* v_t_1448_, lean_object* v_h_1449_, lean_object* v_k_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Grind_CommRing_Poly_ctorElim(v_motive_1446_, v_ctorIdx_1447_, v_t_1448_, v_h_1449_, v_k_1450_);
lean_dec(v_ctorIdx_1447_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim___redArg(lean_object* v_t_1452_, lean_object* v_num_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1452_, v_num_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim(lean_object* v_motive_1455_, lean_object* v_t_1456_, lean_object* v_h_1457_, lean_object* v_num_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1456_, v_num_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim___redArg(lean_object* v_t_1460_, lean_object* v_add_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1460_, v_add_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim(lean_object* v_motive_1463_, lean_object* v_t_1464_, lean_object* v_h_1465_, lean_object* v_add_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1464_, v_add_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPoly_beq(lean_object* v_x_1468_, lean_object* v_x_1469_){
_start:
{
if (lean_obj_tag(v_x_1468_) == 0)
{
if (lean_obj_tag(v_x_1469_) == 0)
{
lean_object* v_k_1470_; lean_object* v_k_1471_; uint8_t v___x_1472_; 
v_k_1470_ = lean_ctor_get(v_x_1468_, 0);
v_k_1471_ = lean_ctor_get(v_x_1469_, 0);
v___x_1472_ = lean_int_dec_eq(v_k_1470_, v_k_1471_);
return v___x_1472_;
}
else
{
uint8_t v___x_1473_; 
v___x_1473_ = 0;
return v___x_1473_;
}
}
else
{
if (lean_obj_tag(v_x_1469_) == 1)
{
lean_object* v_k_1474_; lean_object* v_v_1475_; lean_object* v_p_1476_; lean_object* v_k_1477_; lean_object* v_v_1478_; lean_object* v_p_1479_; uint8_t v___x_1480_; 
v_k_1474_ = lean_ctor_get(v_x_1468_, 0);
v_v_1475_ = lean_ctor_get(v_x_1468_, 1);
v_p_1476_ = lean_ctor_get(v_x_1468_, 2);
v_k_1477_ = lean_ctor_get(v_x_1469_, 0);
v_v_1478_ = lean_ctor_get(v_x_1469_, 1);
v_p_1479_ = lean_ctor_get(v_x_1469_, 2);
v___x_1480_ = lean_int_dec_eq(v_k_1474_, v_k_1477_);
if (v___x_1480_ == 0)
{
return v___x_1480_;
}
else
{
uint8_t v___x_1481_; 
v___x_1481_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_v_1475_, v_v_1478_);
if (v___x_1481_ == 0)
{
return v___x_1481_;
}
else
{
v_x_1468_ = v_p_1476_;
v_x_1469_ = v_p_1479_;
goto _start;
}
}
}
else
{
uint8_t v___x_1483_; 
v___x_1483_ = 0;
return v___x_1483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPoly_beq___boxed(lean_object* v_x_1484_, lean_object* v_x_1485_){
_start:
{
uint8_t v_res_1486_; lean_object* v_r_1487_; 
v_res_1486_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_x_1484_, v_x_1485_);
lean_dec_ref(v_x_1485_);
lean_dec_ref(v_x_1484_);
v_r_1487_ = lean_box(v_res_1486_);
return v_r_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_1490_, lean_object* v_x_1491_, lean_object* v_h__1_1492_, lean_object* v_h__2_1493_, lean_object* v_h__3_1494_){
_start:
{
if (lean_obj_tag(v_x_1490_) == 0)
{
lean_dec(v_h__2_1493_);
if (lean_obj_tag(v_x_1491_) == 0)
{
lean_object* v_k_1495_; lean_object* v_k_1496_; lean_object* v___x_1497_; 
lean_dec(v_h__3_1494_);
v_k_1495_ = lean_ctor_get(v_x_1490_, 0);
lean_inc(v_k_1495_);
lean_dec_ref_known(v_x_1490_, 1);
v_k_1496_ = lean_ctor_get(v_x_1491_, 0);
lean_inc(v_k_1496_);
lean_dec_ref_known(v_x_1491_, 1);
v___x_1497_ = lean_apply_2(v_h__1_1492_, v_k_1495_, v_k_1496_);
return v___x_1497_;
}
else
{
lean_object* v___x_1498_; 
lean_dec(v_h__1_1492_);
v___x_1498_ = lean_apply_4(v_h__3_1494_, v_x_1490_, v_x_1491_, lean_box(0), lean_box(0));
return v___x_1498_;
}
}
else
{
lean_dec(v_h__1_1492_);
if (lean_obj_tag(v_x_1491_) == 1)
{
lean_object* v_k_1499_; lean_object* v_v_1500_; lean_object* v_p_1501_; lean_object* v_k_1502_; lean_object* v_v_1503_; lean_object* v_p_1504_; lean_object* v___x_1505_; 
lean_dec(v_h__3_1494_);
v_k_1499_ = lean_ctor_get(v_x_1490_, 0);
lean_inc(v_k_1499_);
v_v_1500_ = lean_ctor_get(v_x_1490_, 1);
lean_inc(v_v_1500_);
v_p_1501_ = lean_ctor_get(v_x_1490_, 2);
lean_inc_ref(v_p_1501_);
lean_dec_ref_known(v_x_1490_, 3);
v_k_1502_ = lean_ctor_get(v_x_1491_, 0);
lean_inc(v_k_1502_);
v_v_1503_ = lean_ctor_get(v_x_1491_, 1);
lean_inc(v_v_1503_);
v_p_1504_ = lean_ctor_get(v_x_1491_, 2);
lean_inc_ref(v_p_1504_);
lean_dec_ref_known(v_x_1491_, 3);
v___x_1505_ = lean_apply_6(v_h__2_1493_, v_k_1499_, v_v_1500_, v_p_1501_, v_k_1502_, v_v_1503_, v_p_1504_);
return v___x_1505_;
}
else
{
lean_object* v___x_1506_; 
lean_dec(v_h__2_1493_);
v___x_1506_ = lean_apply_4(v_h__3_1494_, v_x_1490_, v_x_1491_, lean_box(0), lean_box(0));
return v___x_1506_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_, lean_object* v_h__1_1510_, lean_object* v_h__2_1511_, lean_object* v_h__3_1512_){
_start:
{
if (lean_obj_tag(v_x_1508_) == 0)
{
lean_dec(v_h__2_1511_);
if (lean_obj_tag(v_x_1509_) == 0)
{
lean_object* v_k_1513_; lean_object* v_k_1514_; lean_object* v___x_1515_; 
lean_dec(v_h__3_1512_);
v_k_1513_ = lean_ctor_get(v_x_1508_, 0);
lean_inc(v_k_1513_);
lean_dec_ref_known(v_x_1508_, 1);
v_k_1514_ = lean_ctor_get(v_x_1509_, 0);
lean_inc(v_k_1514_);
lean_dec_ref_known(v_x_1509_, 1);
v___x_1515_ = lean_apply_2(v_h__1_1510_, v_k_1513_, v_k_1514_);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; 
lean_dec(v_h__1_1510_);
v___x_1516_ = lean_apply_4(v_h__3_1512_, v_x_1508_, v_x_1509_, lean_box(0), lean_box(0));
return v___x_1516_;
}
}
else
{
lean_dec(v_h__1_1510_);
if (lean_obj_tag(v_x_1509_) == 1)
{
lean_object* v_k_1517_; lean_object* v_v_1518_; lean_object* v_p_1519_; lean_object* v_k_1520_; lean_object* v_v_1521_; lean_object* v_p_1522_; lean_object* v___x_1523_; 
lean_dec(v_h__3_1512_);
v_k_1517_ = lean_ctor_get(v_x_1508_, 0);
lean_inc(v_k_1517_);
v_v_1518_ = lean_ctor_get(v_x_1508_, 1);
lean_inc(v_v_1518_);
v_p_1519_ = lean_ctor_get(v_x_1508_, 2);
lean_inc_ref(v_p_1519_);
lean_dec_ref_known(v_x_1508_, 3);
v_k_1520_ = lean_ctor_get(v_x_1509_, 0);
lean_inc(v_k_1520_);
v_v_1521_ = lean_ctor_get(v_x_1509_, 1);
lean_inc(v_v_1521_);
v_p_1522_ = lean_ctor_get(v_x_1509_, 2);
lean_inc_ref(v_p_1522_);
lean_dec_ref_known(v_x_1509_, 3);
v___x_1523_ = lean_apply_6(v_h__2_1511_, v_k_1517_, v_v_1518_, v_p_1519_, v_k_1520_, v_v_1521_, v_p_1522_);
return v___x_1523_;
}
else
{
lean_object* v___x_1524_; 
lean_dec(v_h__2_1511_);
v___x_1524_ = lean_apply_4(v_h__3_1512_, v_x_1508_, v_x_1509_, lean_box(0), lean_box(0));
return v___x_1524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr(lean_object* v_x_1537_, lean_object* v_prec_1538_){
_start:
{
lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; 
if (lean_obj_tag(v_x_1537_) == 0)
{
lean_object* v_k_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1571_; 
v_k_1548_ = lean_ctor_get(v_x_1537_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_x_1537_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1550_ = v_x_1537_;
v_isShared_1551_ = v_isSharedCheck_1571_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_k_1548_);
lean_dec(v_x_1537_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1571_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___y_1553_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = lean_unsigned_to_nat(1024u);
v___x_1568_ = lean_nat_dec_le(v___x_1567_, v_prec_1538_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1553_ = v___x_1569_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1553_ = v___x_1570_;
goto v___jp_1552_;
}
v___jp_1552_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1554_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__2));
v___x_1555_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1556_ = lean_int_dec_lt(v_k_1548_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = l_Int_repr(v_k_1548_);
lean_dec(v_k_1548_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set_tag(v___x_1550_, 3);
lean_ctor_set(v___x_1550_, 0, v___x_1557_);
v___x_1559_ = v___x_1550_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
v___y_1540_ = v___y_1553_;
v___y_1541_ = v___x_1554_;
v___y_1542_ = v___x_1559_;
goto v___jp_1539_;
}
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1561_ = lean_unsigned_to_nat(1024u);
v___x_1562_ = l_Int_repr(v_k_1548_);
lean_dec(v_k_1548_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set_tag(v___x_1550_, 3);
lean_ctor_set(v___x_1550_, 0, v___x_1562_);
v___x_1564_ = v___x_1550_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Repr_addAppParen(v___x_1564_, v___x_1561_);
v___y_1540_ = v___y_1553_;
v___y_1541_ = v___x_1554_;
v___y_1542_ = v___x_1565_;
goto v___jp_1539_;
}
}
}
}
}
else
{
lean_object* v_k_1572_; lean_object* v_v_1573_; lean_object* v_p_1574_; lean_object* v___x_1575_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1593_; uint8_t v___x_1603_; 
v_k_1572_ = lean_ctor_get(v_x_1537_, 0);
lean_inc(v_k_1572_);
v_v_1573_ = lean_ctor_get(v_x_1537_, 1);
lean_inc(v_v_1573_);
v_p_1574_ = lean_ctor_get(v_x_1537_, 2);
lean_inc_ref(v_p_1574_);
lean_dec_ref_known(v_x_1537_, 3);
v___x_1575_ = lean_unsigned_to_nat(1024u);
v___x_1603_ = lean_nat_dec_le(v___x_1575_, v_prec_1538_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1593_ = v___x_1604_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1593_ = v___x_1605_;
goto v___jp_1592_;
}
v___jp_1576_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_inc(v___y_1578_);
v___x_1581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___y_1578_);
lean_ctor_set(v___x_1581_, 1, v___y_1580_);
lean_inc_n(v___y_1577_, 2);
v___x_1582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v___y_1577_);
v___x_1583_ = l_Lean_Grind_CommRing_instReprMon_repr(v_v_1573_, v___x_1575_);
v___x_1584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v___y_1577_);
v___x_1586_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_p_1574_, v___x_1575_);
v___x_1587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
lean_inc(v___y_1579_);
v___x_1588_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___y_1579_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = 0;
v___x_1590_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set_uint8(v___x_1590_, sizeof(void*)*1, v___x_1589_);
v___x_1591_ = l_Repr_addAppParen(v___x_1590_, v_prec_1538_);
return v___x_1591_;
}
v___jp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1594_ = lean_box(1);
v___x_1595_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__5));
v___x_1596_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1597_ = lean_int_dec_lt(v_k_1572_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = l_Int_repr(v_k_1572_);
lean_dec(v_k_1572_);
v___x_1599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
v___y_1577_ = v___x_1594_;
v___y_1578_ = v___x_1595_;
v___y_1579_ = v___y_1593_;
v___y_1580_ = v___x_1599_;
goto v___jp_1576_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = l_Int_repr(v_k_1572_);
lean_dec(v_k_1572_);
v___x_1601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
v___x_1602_ = l_Repr_addAppParen(v___x_1601_, v___x_1575_);
v___y_1577_ = v___x_1594_;
v___y_1578_ = v___x_1595_;
v___y_1579_ = v___y_1593_;
v___y_1580_ = v___x_1602_;
goto v___jp_1576_;
}
}
}
v___jp_1539_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_inc(v___y_1541_);
v___x_1543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___y_1541_);
lean_ctor_set(v___x_1543_, 1, v___y_1542_);
lean_inc(v___y_1540_);
v___x_1544_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___y_1540_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = 0;
v___x_1546_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set_uint8(v___x_1546_, sizeof(void*)*1, v___x_1545_);
v___x_1547_ = l_Repr_addAppParen(v___x_1546_, v_prec_1538_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___boxed(lean_object* v_x_1606_, lean_object* v_prec_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_x_1606_, v_prec_1607_);
lean_dec(v_prec_1607_);
return v_res_1608_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
return v___x_1612_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default(void){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_1613_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly(void){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
return v___x_1614_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePoly_hash(lean_object* v_x_1615_){
_start:
{
if (lean_obj_tag(v_x_1615_) == 0)
{
lean_object* v_k_1616_; uint64_t v___x_1617_; lean_object* v_intZero_1618_; uint8_t v_isNeg_1619_; 
v_k_1616_ = lean_ctor_get(v_x_1615_, 0);
v___x_1617_ = 0ULL;
v_intZero_1618_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1619_ = lean_int_dec_lt(v_k_1616_, v_intZero_1618_);
if (v_isNeg_1619_ == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint64_t v___x_1623_; uint64_t v___x_1624_; 
v_a_1620_ = lean_nat_abs(v_k_1616_);
v___x_1621_ = lean_unsigned_to_nat(2u);
v___x_1622_ = lean_nat_mul(v___x_1621_, v_a_1620_);
lean_dec(v_a_1620_);
v___x_1623_ = lean_uint64_of_nat(v___x_1622_);
lean_dec(v___x_1622_);
v___x_1624_ = lean_uint64_mix_hash(v___x_1617_, v___x_1623_);
return v___x_1624_;
}
else
{
lean_object* v_abs_1625_; lean_object* v_one_1626_; lean_object* v_a_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint64_t v___x_1631_; uint64_t v___x_1632_; 
v_abs_1625_ = lean_nat_abs(v_k_1616_);
v_one_1626_ = lean_unsigned_to_nat(1u);
v_a_1627_ = lean_nat_sub(v_abs_1625_, v_one_1626_);
lean_dec(v_abs_1625_);
v___x_1628_ = lean_unsigned_to_nat(2u);
v___x_1629_ = lean_nat_mul(v___x_1628_, v_a_1627_);
lean_dec(v_a_1627_);
v___x_1630_ = lean_nat_add(v___x_1629_, v_one_1626_);
lean_dec(v___x_1629_);
v___x_1631_ = lean_uint64_of_nat(v___x_1630_);
lean_dec(v___x_1630_);
v___x_1632_ = lean_uint64_mix_hash(v___x_1617_, v___x_1631_);
return v___x_1632_;
}
}
else
{
lean_object* v_k_1633_; lean_object* v_v_1634_; lean_object* v_p_1635_; uint64_t v___x_1636_; uint64_t v___y_1638_; lean_object* v_intZero_1644_; uint8_t v_isNeg_1645_; 
v_k_1633_ = lean_ctor_get(v_x_1615_, 0);
v_v_1634_ = lean_ctor_get(v_x_1615_, 1);
v_p_1635_ = lean_ctor_get(v_x_1615_, 2);
v___x_1636_ = 1ULL;
v_intZero_1644_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1645_ = lean_int_dec_lt(v_k_1633_, v_intZero_1644_);
if (v_isNeg_1645_ == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; uint64_t v___x_1649_; 
v_a_1646_ = lean_nat_abs(v_k_1633_);
v___x_1647_ = lean_unsigned_to_nat(2u);
v___x_1648_ = lean_nat_mul(v___x_1647_, v_a_1646_);
lean_dec(v_a_1646_);
v___x_1649_ = lean_uint64_of_nat(v___x_1648_);
lean_dec(v___x_1648_);
v___y_1638_ = v___x_1649_;
goto v___jp_1637_;
}
else
{
lean_object* v_abs_1650_; lean_object* v_one_1651_; lean_object* v_a_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint64_t v___x_1656_; 
v_abs_1650_ = lean_nat_abs(v_k_1633_);
v_one_1651_ = lean_unsigned_to_nat(1u);
v_a_1652_ = lean_nat_sub(v_abs_1650_, v_one_1651_);
lean_dec(v_abs_1650_);
v___x_1653_ = lean_unsigned_to_nat(2u);
v___x_1654_ = lean_nat_mul(v___x_1653_, v_a_1652_);
lean_dec(v_a_1652_);
v___x_1655_ = lean_nat_add(v___x_1654_, v_one_1651_);
lean_dec(v___x_1654_);
v___x_1656_ = lean_uint64_of_nat(v___x_1655_);
lean_dec(v___x_1655_);
v___y_1638_ = v___x_1656_;
goto v___jp_1637_;
}
v___jp_1637_:
{
uint64_t v___x_1639_; uint64_t v___x_1640_; uint64_t v___x_1641_; uint64_t v___x_1642_; uint64_t v___x_1643_; 
v___x_1639_ = lean_uint64_mix_hash(v___x_1636_, v___y_1638_);
v___x_1640_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_v_1634_);
v___x_1641_ = lean_uint64_mix_hash(v___x_1639_, v___x_1640_);
v___x_1642_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_p_1635_);
v___x_1643_ = lean_uint64_mix_hash(v___x_1641_, v___x_1642_);
return v___x_1643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePoly_hash___boxed(lean_object* v_x_1657_){
_start:
{
uint64_t v_res_1658_; lean_object* v_r_1659_; 
v_res_1658_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_x_1657_);
lean_dec_ref(v_x_1657_);
v_r_1659_ = lean_box_uint64(v_res_1658_);
return v_r_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg(lean_object* v_inst_1662_, lean_object* v_ctx_1663_, lean_object* v_p_1664_){
_start:
{
lean_object* v_toSemiring_1665_; lean_object* v_intCast_1666_; lean_object* v_toAdd_1667_; lean_object* v___x_1668_; 
v_toSemiring_1665_ = lean_ctor_get(v_inst_1662_, 0);
v_intCast_1666_ = lean_ctor_get(v_inst_1662_, 3);
v_toAdd_1667_ = lean_ctor_get(v_toSemiring_1665_, 0);
lean_inc(v_toAdd_1667_);
lean_inc_ref(v_inst_1662_);
v___x_1668_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1662_);
if (lean_obj_tag(v_p_1664_) == 0)
{
lean_object* v_k_1669_; lean_object* v___x_1670_; 
lean_inc(v_intCast_1666_);
lean_dec_ref(v___x_1668_);
lean_dec(v_toAdd_1667_);
lean_dec_ref(v_inst_1662_);
v_k_1669_ = lean_ctor_get(v_p_1664_, 0);
lean_inc(v_k_1669_);
lean_dec_ref_known(v_p_1664_, 1);
v___x_1670_ = lean_apply_1(v_intCast_1666_, v_k_1669_);
return v___x_1670_;
}
else
{
lean_object* v_zsmul_1671_; lean_object* v_k_1672_; lean_object* v_v_1673_; lean_object* v_p_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v_zsmul_1671_ = lean_ctor_get(v___x_1668_, 2);
lean_inc(v_zsmul_1671_);
lean_dec_ref(v___x_1668_);
v_k_1672_ = lean_ctor_get(v_p_1664_, 0);
lean_inc(v_k_1672_);
v_v_1673_ = lean_ctor_get(v_p_1664_, 1);
lean_inc(v_v_1673_);
v_p_1674_ = lean_ctor_get(v_p_1664_, 2);
lean_inc_ref(v_p_1674_);
lean_dec_ref_known(v_p_1664_, 3);
lean_inc_ref(v_toSemiring_1665_);
v___x_1675_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_toSemiring_1665_, v_ctx_1663_, v_v_1673_);
v___x_1676_ = lean_apply_2(v_zsmul_1671_, v_k_1672_, v___x_1675_);
v___x_1677_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1662_, v_ctx_1663_, v_p_1674_);
v___x_1678_ = lean_apply_2(v_toAdd_1667_, v___x_1676_, v___x_1677_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg___boxed(lean_object* v_inst_1679_, lean_object* v_ctx_1680_, lean_object* v_p_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1679_, v_ctx_1680_, v_p_1681_);
lean_dec_ref(v_ctx_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote(lean_object* v_00_u03b1_1683_, lean_object* v_inst_1684_, lean_object* v_ctx_1685_, lean_object* v_p_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1684_, v_ctx_1685_, v_p_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___boxed(lean_object* v_00_u03b1_1688_, lean_object* v_inst_1689_, lean_object* v_ctx_1690_, lean_object* v_p_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Grind_CommRing_Poly_denote(v_00_u03b1_1688_, v_inst_1689_, v_ctx_1690_, v_p_1691_);
lean_dec_ref(v_ctx_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg(lean_object* v_inst_1693_, lean_object* v_ctx_1694_, lean_object* v_k_1695_, lean_object* v_m_1696_){
_start:
{
lean_object* v_toSemiring_1697_; lean_object* v___x_1698_; lean_object* v_zsmul_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
v_toSemiring_1697_ = lean_ctor_get(v_inst_1693_, 0);
lean_inc_ref(v_toSemiring_1697_);
v___x_1698_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1693_);
v_zsmul_1699_ = lean_ctor_get(v___x_1698_, 2);
lean_inc(v_zsmul_1699_);
lean_dec_ref(v___x_1698_);
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1702_ = lean_int_dec_eq(v_k_1695_, v___x_1701_);
if (v___x_1702_ == 0)
{
if (lean_obj_tag(v_m_1696_) == 0)
{
lean_object* v_ofNat_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_ofNat_1703_ = lean_ctor_get(v_toSemiring_1697_, 3);
lean_inc(v_ofNat_1703_);
lean_dec_ref(v_toSemiring_1697_);
v___x_1704_ = lean_apply_1(v_ofNat_1703_, v___x_1700_);
v___x_1705_ = lean_apply_2(v_zsmul_1699_, v_k_1695_, v___x_1704_);
return v___x_1705_;
}
else
{
lean_object* v_p_1706_; lean_object* v_m_1707_; lean_object* v_ofNat_1708_; lean_object* v_npow_1709_; lean_object* v_x_1710_; lean_object* v_k_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v_p_1706_ = lean_ctor_get(v_m_1696_, 0);
lean_inc_ref(v_p_1706_);
v_m_1707_ = lean_ctor_get(v_m_1696_, 1);
lean_inc(v_m_1707_);
lean_dec_ref_known(v_m_1696_, 2);
v_ofNat_1708_ = lean_ctor_get(v_toSemiring_1697_, 3);
v_npow_1709_ = lean_ctor_get(v_toSemiring_1697_, 5);
v_x_1710_ = lean_ctor_get(v_p_1706_, 0);
lean_inc(v_x_1710_);
v_k_1711_ = lean_ctor_get(v_p_1706_, 1);
lean_inc(v_k_1711_);
lean_dec_ref(v_p_1706_);
v___x_1712_ = lean_unsigned_to_nat(0u);
v___x_1713_ = lean_nat_dec_eq(v_k_1711_, v___x_1712_);
if (v___x_1713_ == 0)
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_nat_dec_eq(v_k_1711_, v___x_1700_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1715_ = l_Lean_RArray_getImpl___redArg(v_ctx_1694_, v_x_1710_);
lean_dec(v_x_1710_);
lean_inc(v_npow_1709_);
v___x_1716_ = lean_apply_2(v_npow_1709_, v___x_1715_, v_k_1711_);
v___x_1717_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1697_, v_ctx_1694_, v_m_1707_, v___x_1716_);
v___x_1718_ = lean_apply_2(v_zsmul_1699_, v_k_1695_, v___x_1717_);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_dec(v_k_1711_);
v___x_1719_ = l_Lean_RArray_getImpl___redArg(v_ctx_1694_, v_x_1710_);
lean_dec(v_x_1710_);
v___x_1720_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1697_, v_ctx_1694_, v_m_1707_, v___x_1719_);
v___x_1721_ = lean_apply_2(v_zsmul_1699_, v_k_1695_, v___x_1720_);
return v___x_1721_;
}
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec(v_k_1711_);
lean_dec(v_x_1710_);
lean_inc(v_ofNat_1708_);
v___x_1722_ = lean_apply_1(v_ofNat_1708_, v___x_1700_);
v___x_1723_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1697_, v_ctx_1694_, v_m_1707_, v___x_1722_);
v___x_1724_ = lean_apply_2(v_zsmul_1699_, v_k_1695_, v___x_1723_);
return v___x_1724_;
}
}
}
else
{
lean_dec(v_zsmul_1699_);
lean_dec(v_k_1695_);
if (lean_obj_tag(v_m_1696_) == 0)
{
lean_object* v_ofNat_1725_; lean_object* v___x_1726_; 
v_ofNat_1725_ = lean_ctor_get(v_toSemiring_1697_, 3);
lean_inc(v_ofNat_1725_);
lean_dec_ref(v_toSemiring_1697_);
v___x_1726_ = lean_apply_1(v_ofNat_1725_, v___x_1700_);
return v___x_1726_;
}
else
{
lean_object* v_p_1727_; lean_object* v_m_1728_; lean_object* v_ofNat_1729_; lean_object* v_npow_1730_; lean_object* v_x_1731_; lean_object* v_k_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; 
v_p_1727_ = lean_ctor_get(v_m_1696_, 0);
lean_inc_ref(v_p_1727_);
v_m_1728_ = lean_ctor_get(v_m_1696_, 1);
lean_inc(v_m_1728_);
lean_dec_ref_known(v_m_1696_, 2);
v_ofNat_1729_ = lean_ctor_get(v_toSemiring_1697_, 3);
v_npow_1730_ = lean_ctor_get(v_toSemiring_1697_, 5);
v_x_1731_ = lean_ctor_get(v_p_1727_, 0);
lean_inc(v_x_1731_);
v_k_1732_ = lean_ctor_get(v_p_1727_, 1);
lean_inc(v_k_1732_);
lean_dec_ref(v_p_1727_);
v___x_1733_ = lean_unsigned_to_nat(0u);
v___x_1734_ = lean_nat_dec_eq(v_k_1732_, v___x_1733_);
if (v___x_1734_ == 0)
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_nat_dec_eq(v_k_1732_, v___x_1700_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = l_Lean_RArray_getImpl___redArg(v_ctx_1694_, v_x_1731_);
lean_dec(v_x_1731_);
lean_inc(v_npow_1730_);
v___x_1737_ = lean_apply_2(v_npow_1730_, v___x_1736_, v_k_1732_);
v___x_1738_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1697_, v_ctx_1694_, v_m_1728_, v___x_1737_);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec(v_k_1732_);
v___x_1739_ = l_Lean_RArray_getImpl___redArg(v_ctx_1694_, v_x_1731_);
lean_dec(v_x_1731_);
v___x_1740_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1697_, v_ctx_1694_, v_m_1728_, v___x_1739_);
return v___x_1740_;
}
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_dec(v_k_1732_);
lean_dec(v_x_1731_);
lean_inc(v_ofNat_1729_);
v___x_1741_ = lean_apply_1(v_ofNat_1729_, v___x_1700_);
v___x_1742_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1697_, v_ctx_1694_, v_m_1728_, v___x_1741_);
return v___x_1742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg___boxed(lean_object* v_inst_1743_, lean_object* v_ctx_1744_, lean_object* v_k_1745_, lean_object* v_m_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Grind_CommRing_denoteTerm___redArg(v_inst_1743_, v_ctx_1744_, v_k_1745_, v_m_1746_);
lean_dec_ref(v_ctx_1744_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm(lean_object* v_00_u03b1_1748_, lean_object* v_inst_1749_, lean_object* v_ctx_1750_, lean_object* v_k_1751_, lean_object* v_m_1752_){
_start:
{
lean_object* v_toSemiring_1753_; lean_object* v___x_1754_; lean_object* v_zsmul_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v_toSemiring_1753_ = lean_ctor_get(v_inst_1749_, 0);
lean_inc_ref(v_toSemiring_1753_);
v___x_1754_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1749_);
v_zsmul_1755_ = lean_ctor_get(v___x_1754_, 2);
lean_inc(v_zsmul_1755_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = lean_unsigned_to_nat(1u);
v___x_1757_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1758_ = lean_int_dec_eq(v_k_1751_, v___x_1757_);
if (v___x_1758_ == 0)
{
if (lean_obj_tag(v_m_1752_) == 0)
{
lean_object* v_ofNat_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_ofNat_1759_ = lean_ctor_get(v_toSemiring_1753_, 3);
lean_inc(v_ofNat_1759_);
lean_dec_ref(v_toSemiring_1753_);
v___x_1760_ = lean_apply_1(v_ofNat_1759_, v___x_1756_);
v___x_1761_ = lean_apply_2(v_zsmul_1755_, v_k_1751_, v___x_1760_);
return v___x_1761_;
}
else
{
lean_object* v_p_1762_; lean_object* v_m_1763_; lean_object* v_ofNat_1764_; lean_object* v_npow_1765_; lean_object* v_x_1766_; lean_object* v_k_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_p_1762_ = lean_ctor_get(v_m_1752_, 0);
lean_inc_ref(v_p_1762_);
v_m_1763_ = lean_ctor_get(v_m_1752_, 1);
lean_inc(v_m_1763_);
lean_dec_ref_known(v_m_1752_, 2);
v_ofNat_1764_ = lean_ctor_get(v_toSemiring_1753_, 3);
v_npow_1765_ = lean_ctor_get(v_toSemiring_1753_, 5);
v_x_1766_ = lean_ctor_get(v_p_1762_, 0);
lean_inc(v_x_1766_);
v_k_1767_ = lean_ctor_get(v_p_1762_, 1);
lean_inc(v_k_1767_);
lean_dec_ref(v_p_1762_);
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = lean_nat_dec_eq(v_k_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
uint8_t v___x_1770_; 
v___x_1770_ = lean_nat_dec_eq(v_k_1767_, v___x_1756_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1771_ = l_Lean_RArray_getImpl___redArg(v_ctx_1750_, v_x_1766_);
lean_dec(v_x_1766_);
lean_inc(v_npow_1765_);
v___x_1772_ = lean_apply_2(v_npow_1765_, v___x_1771_, v_k_1767_);
v___x_1773_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1753_, v_ctx_1750_, v_m_1763_, v___x_1772_);
v___x_1774_ = lean_apply_2(v_zsmul_1755_, v_k_1751_, v___x_1773_);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec(v_k_1767_);
v___x_1775_ = l_Lean_RArray_getImpl___redArg(v_ctx_1750_, v_x_1766_);
lean_dec(v_x_1766_);
v___x_1776_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1753_, v_ctx_1750_, v_m_1763_, v___x_1775_);
v___x_1777_ = lean_apply_2(v_zsmul_1755_, v_k_1751_, v___x_1776_);
return v___x_1777_;
}
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec(v_k_1767_);
lean_dec(v_x_1766_);
lean_inc(v_ofNat_1764_);
v___x_1778_ = lean_apply_1(v_ofNat_1764_, v___x_1756_);
v___x_1779_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1753_, v_ctx_1750_, v_m_1763_, v___x_1778_);
v___x_1780_ = lean_apply_2(v_zsmul_1755_, v_k_1751_, v___x_1779_);
return v___x_1780_;
}
}
}
else
{
lean_dec(v_zsmul_1755_);
lean_dec(v_k_1751_);
if (lean_obj_tag(v_m_1752_) == 0)
{
lean_object* v_ofNat_1781_; lean_object* v___x_1782_; 
v_ofNat_1781_ = lean_ctor_get(v_toSemiring_1753_, 3);
lean_inc(v_ofNat_1781_);
lean_dec_ref(v_toSemiring_1753_);
v___x_1782_ = lean_apply_1(v_ofNat_1781_, v___x_1756_);
return v___x_1782_;
}
else
{
lean_object* v_p_1783_; lean_object* v_m_1784_; lean_object* v_ofNat_1785_; lean_object* v_npow_1786_; lean_object* v_x_1787_; lean_object* v_k_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_p_1783_ = lean_ctor_get(v_m_1752_, 0);
lean_inc_ref(v_p_1783_);
v_m_1784_ = lean_ctor_get(v_m_1752_, 1);
lean_inc(v_m_1784_);
lean_dec_ref_known(v_m_1752_, 2);
v_ofNat_1785_ = lean_ctor_get(v_toSemiring_1753_, 3);
v_npow_1786_ = lean_ctor_get(v_toSemiring_1753_, 5);
v_x_1787_ = lean_ctor_get(v_p_1783_, 0);
lean_inc(v_x_1787_);
v_k_1788_ = lean_ctor_get(v_p_1783_, 1);
lean_inc(v_k_1788_);
lean_dec_ref(v_p_1783_);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_nat_dec_eq(v_k_1788_, v___x_1789_);
if (v___x_1790_ == 0)
{
uint8_t v___x_1791_; 
v___x_1791_ = lean_nat_dec_eq(v_k_1788_, v___x_1756_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = l_Lean_RArray_getImpl___redArg(v_ctx_1750_, v_x_1787_);
lean_dec(v_x_1787_);
lean_inc(v_npow_1786_);
v___x_1793_ = lean_apply_2(v_npow_1786_, v___x_1792_, v_k_1788_);
v___x_1794_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1753_, v_ctx_1750_, v_m_1784_, v___x_1793_);
return v___x_1794_;
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v_k_1788_);
v___x_1795_ = l_Lean_RArray_getImpl___redArg(v_ctx_1750_, v_x_1787_);
lean_dec(v_x_1787_);
v___x_1796_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1753_, v_ctx_1750_, v_m_1784_, v___x_1795_);
return v___x_1796_;
}
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_dec(v_k_1788_);
lean_dec(v_x_1787_);
lean_inc(v_ofNat_1785_);
v___x_1797_ = lean_apply_1(v_ofNat_1785_, v___x_1756_);
v___x_1798_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1753_, v_ctx_1750_, v_m_1784_, v___x_1797_);
return v___x_1798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___boxed(lean_object* v_00_u03b1_1799_, lean_object* v_inst_1800_, lean_object* v_ctx_1801_, lean_object* v_k_1802_, lean_object* v_m_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_Grind_CommRing_denoteTerm(v_00_u03b1_1799_, v_inst_1800_, v_ctx_1801_, v_k_1802_, v_m_1803_);
lean_dec_ref(v_ctx_1801_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(lean_object* v_inst_1805_, lean_object* v_ctx_1806_, lean_object* v_p_1807_, lean_object* v_acc_1808_){
_start:
{
if (lean_obj_tag(v_p_1807_) == 0)
{
lean_object* v_toSemiring_1809_; lean_object* v_intCast_1810_; lean_object* v_toAdd_1811_; lean_object* v_k_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v_toSemiring_1809_ = lean_ctor_get(v_inst_1805_, 0);
lean_inc_ref(v_toSemiring_1809_);
v_intCast_1810_ = lean_ctor_get(v_inst_1805_, 3);
lean_inc(v_intCast_1810_);
lean_dec_ref(v_inst_1805_);
v_toAdd_1811_ = lean_ctor_get(v_toSemiring_1809_, 0);
lean_inc(v_toAdd_1811_);
lean_dec_ref(v_toSemiring_1809_);
v_k_1812_ = lean_ctor_get(v_p_1807_, 0);
lean_inc(v_k_1812_);
lean_dec_ref_known(v_p_1807_, 1);
v___x_1813_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1814_ = lean_int_dec_eq(v_k_1812_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_apply_1(v_intCast_1810_, v_k_1812_);
v___x_1816_ = lean_apply_2(v_toAdd_1811_, v_acc_1808_, v___x_1815_);
return v___x_1816_;
}
else
{
lean_dec(v_k_1812_);
lean_dec(v_toAdd_1811_);
lean_dec(v_intCast_1810_);
return v_acc_1808_;
}
}
else
{
lean_object* v_toSemiring_1817_; lean_object* v_toAdd_1818_; lean_object* v_ofNat_1819_; lean_object* v_npow_1820_; lean_object* v_k_1821_; lean_object* v_v_1822_; lean_object* v_p_1823_; lean_object* v___y_1825_; lean_object* v___x_1828_; lean_object* v_zsmul_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v_toSemiring_1817_ = lean_ctor_get(v_inst_1805_, 0);
v_toAdd_1818_ = lean_ctor_get(v_toSemiring_1817_, 0);
v_ofNat_1819_ = lean_ctor_get(v_toSemiring_1817_, 3);
v_npow_1820_ = lean_ctor_get(v_toSemiring_1817_, 5);
v_k_1821_ = lean_ctor_get(v_p_1807_, 0);
lean_inc(v_k_1821_);
v_v_1822_ = lean_ctor_get(v_p_1807_, 1);
lean_inc(v_v_1822_);
v_p_1823_ = lean_ctor_get(v_p_1807_, 2);
lean_inc_ref(v_p_1823_);
lean_dec_ref_known(v_p_1807_, 3);
lean_inc_ref(v_inst_1805_);
v___x_1828_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1805_);
v_zsmul_1829_ = lean_ctor_get(v___x_1828_, 2);
lean_inc(v_zsmul_1829_);
lean_dec_ref(v___x_1828_);
v___x_1830_ = lean_unsigned_to_nat(1u);
v___x_1831_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1832_ = lean_int_dec_eq(v_k_1821_, v___x_1831_);
if (v___x_1832_ == 0)
{
if (lean_obj_tag(v_v_1822_) == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_inc(v_ofNat_1819_);
v___x_1833_ = lean_apply_1(v_ofNat_1819_, v___x_1830_);
v___x_1834_ = lean_apply_2(v_zsmul_1829_, v_k_1821_, v___x_1833_);
v___y_1825_ = v___x_1834_;
goto v___jp_1824_;
}
else
{
lean_object* v_p_1835_; lean_object* v_m_1836_; lean_object* v_x_1837_; lean_object* v_k_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v_p_1835_ = lean_ctor_get(v_v_1822_, 0);
lean_inc_ref(v_p_1835_);
v_m_1836_ = lean_ctor_get(v_v_1822_, 1);
lean_inc(v_m_1836_);
lean_dec_ref_known(v_v_1822_, 2);
v_x_1837_ = lean_ctor_get(v_p_1835_, 0);
lean_inc(v_x_1837_);
v_k_1838_ = lean_ctor_get(v_p_1835_, 1);
lean_inc(v_k_1838_);
lean_dec_ref(v_p_1835_);
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_nat_dec_eq(v_k_1838_, v___x_1839_);
if (v___x_1840_ == 0)
{
uint8_t v___x_1841_; 
v___x_1841_ = lean_nat_dec_eq(v_k_1838_, v___x_1830_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1842_ = l_Lean_RArray_getImpl___redArg(v_ctx_1806_, v_x_1837_);
lean_dec(v_x_1837_);
lean_inc(v_npow_1820_);
v___x_1843_ = lean_apply_2(v_npow_1820_, v___x_1842_, v_k_1838_);
lean_inc_ref(v_toSemiring_1817_);
v___x_1844_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1817_, v_ctx_1806_, v_m_1836_, v___x_1843_);
v___x_1845_ = lean_apply_2(v_zsmul_1829_, v_k_1821_, v___x_1844_);
v___y_1825_ = v___x_1845_;
goto v___jp_1824_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec(v_k_1838_);
v___x_1846_ = l_Lean_RArray_getImpl___redArg(v_ctx_1806_, v_x_1837_);
lean_dec(v_x_1837_);
lean_inc_ref(v_toSemiring_1817_);
v___x_1847_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1817_, v_ctx_1806_, v_m_1836_, v___x_1846_);
v___x_1848_ = lean_apply_2(v_zsmul_1829_, v_k_1821_, v___x_1847_);
v___y_1825_ = v___x_1848_;
goto v___jp_1824_;
}
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec(v_k_1838_);
lean_dec(v_x_1837_);
lean_inc(v_ofNat_1819_);
v___x_1849_ = lean_apply_1(v_ofNat_1819_, v___x_1830_);
lean_inc_ref(v_toSemiring_1817_);
v___x_1850_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1817_, v_ctx_1806_, v_m_1836_, v___x_1849_);
v___x_1851_ = lean_apply_2(v_zsmul_1829_, v_k_1821_, v___x_1850_);
v___y_1825_ = v___x_1851_;
goto v___jp_1824_;
}
}
}
else
{
lean_dec(v_zsmul_1829_);
lean_dec(v_k_1821_);
if (lean_obj_tag(v_v_1822_) == 0)
{
lean_object* v___x_1852_; 
lean_inc(v_ofNat_1819_);
v___x_1852_ = lean_apply_1(v_ofNat_1819_, v___x_1830_);
v___y_1825_ = v___x_1852_;
goto v___jp_1824_;
}
else
{
lean_object* v_p_1853_; lean_object* v_m_1854_; lean_object* v_x_1855_; lean_object* v_k_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v_p_1853_ = lean_ctor_get(v_v_1822_, 0);
lean_inc_ref(v_p_1853_);
v_m_1854_ = lean_ctor_get(v_v_1822_, 1);
lean_inc(v_m_1854_);
lean_dec_ref_known(v_v_1822_, 2);
v_x_1855_ = lean_ctor_get(v_p_1853_, 0);
lean_inc(v_x_1855_);
v_k_1856_ = lean_ctor_get(v_p_1853_, 1);
lean_inc(v_k_1856_);
lean_dec_ref(v_p_1853_);
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = lean_nat_dec_eq(v_k_1856_, v___x_1857_);
if (v___x_1858_ == 0)
{
uint8_t v___x_1859_; 
v___x_1859_ = lean_nat_dec_eq(v_k_1856_, v___x_1830_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = l_Lean_RArray_getImpl___redArg(v_ctx_1806_, v_x_1855_);
lean_dec(v_x_1855_);
lean_inc(v_npow_1820_);
v___x_1861_ = lean_apply_2(v_npow_1820_, v___x_1860_, v_k_1856_);
lean_inc_ref(v_toSemiring_1817_);
v___x_1862_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1817_, v_ctx_1806_, v_m_1854_, v___x_1861_);
v___y_1825_ = v___x_1862_;
goto v___jp_1824_;
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec(v_k_1856_);
v___x_1863_ = l_Lean_RArray_getImpl___redArg(v_ctx_1806_, v_x_1855_);
lean_dec(v_x_1855_);
lean_inc_ref(v_toSemiring_1817_);
v___x_1864_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1817_, v_ctx_1806_, v_m_1854_, v___x_1863_);
v___y_1825_ = v___x_1864_;
goto v___jp_1824_;
}
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
lean_dec(v_k_1856_);
lean_dec(v_x_1855_);
lean_inc(v_ofNat_1819_);
v___x_1865_ = lean_apply_1(v_ofNat_1819_, v___x_1830_);
lean_inc_ref(v_toSemiring_1817_);
v___x_1866_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1817_, v_ctx_1806_, v_m_1854_, v___x_1865_);
v___y_1825_ = v___x_1866_;
goto v___jp_1824_;
}
}
}
v___jp_1824_:
{
lean_object* v___x_1826_; 
lean_inc(v_toAdd_1818_);
v___x_1826_ = lean_apply_2(v_toAdd_1818_, v_acc_1808_, v___y_1825_);
v_p_1807_ = v_p_1823_;
v_acc_1808_ = v___x_1826_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg___boxed(lean_object* v_inst_1867_, lean_object* v_ctx_1868_, lean_object* v_p_1869_, lean_object* v_acc_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1867_, v_ctx_1868_, v_p_1869_, v_acc_1870_);
lean_dec_ref(v_ctx_1868_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go(lean_object* v_00_u03b1_1872_, lean_object* v_inst_1873_, lean_object* v_ctx_1874_, lean_object* v_p_1875_, lean_object* v_acc_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1873_, v_ctx_1874_, v_p_1875_, v_acc_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___boxed(lean_object* v_00_u03b1_1878_, lean_object* v_inst_1879_, lean_object* v_ctx_1880_, lean_object* v_p_1881_, lean_object* v_acc_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_Grind_CommRing_Poly_denote_x27_go(v_00_u03b1_1878_, v_inst_1879_, v_ctx_1880_, v_p_1881_, v_acc_1882_);
lean_dec_ref(v_ctx_1880_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg(lean_object* v_inst_1884_, lean_object* v_ctx_1885_, lean_object* v_p_1886_){
_start:
{
if (lean_obj_tag(v_p_1886_) == 0)
{
lean_object* v_intCast_1887_; lean_object* v_k_1888_; lean_object* v___x_1889_; 
v_intCast_1887_ = lean_ctor_get(v_inst_1884_, 3);
lean_inc(v_intCast_1887_);
lean_dec_ref(v_inst_1884_);
v_k_1888_ = lean_ctor_get(v_p_1886_, 0);
lean_inc(v_k_1888_);
lean_dec_ref_known(v_p_1886_, 1);
v___x_1889_ = lean_apply_1(v_intCast_1887_, v_k_1888_);
return v___x_1889_;
}
else
{
lean_object* v_toSemiring_1890_; lean_object* v_k_1891_; lean_object* v_v_1892_; lean_object* v_p_1893_; lean_object* v___x_1894_; lean_object* v_zsmul_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v_toSemiring_1890_ = lean_ctor_get(v_inst_1884_, 0);
v_k_1891_ = lean_ctor_get(v_p_1886_, 0);
lean_inc(v_k_1891_);
v_v_1892_ = lean_ctor_get(v_p_1886_, 1);
lean_inc(v_v_1892_);
v_p_1893_ = lean_ctor_get(v_p_1886_, 2);
lean_inc_ref(v_p_1893_);
lean_dec_ref_known(v_p_1886_, 3);
lean_inc_ref(v_inst_1884_);
v___x_1894_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1884_);
v_zsmul_1895_ = lean_ctor_get(v___x_1894_, 2);
lean_inc(v_zsmul_1895_);
lean_dec_ref(v___x_1894_);
v___x_1896_ = lean_unsigned_to_nat(1u);
v___x_1897_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1898_ = lean_int_dec_eq(v_k_1891_, v___x_1897_);
if (v___x_1898_ == 0)
{
if (lean_obj_tag(v_v_1892_) == 0)
{
lean_object* v_ofNat_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v_ofNat_1899_ = lean_ctor_get(v_toSemiring_1890_, 3);
lean_inc(v_ofNat_1899_);
v___x_1900_ = lean_apply_1(v_ofNat_1899_, v___x_1896_);
v___x_1901_ = lean_apply_2(v_zsmul_1895_, v_k_1891_, v___x_1900_);
v___x_1902_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1884_, v_ctx_1885_, v_p_1893_, v___x_1901_);
return v___x_1902_;
}
else
{
lean_object* v_p_1903_; lean_object* v_m_1904_; lean_object* v_ofNat_1905_; lean_object* v_npow_1906_; lean_object* v_x_1907_; lean_object* v_k_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v_p_1903_ = lean_ctor_get(v_v_1892_, 0);
lean_inc_ref(v_p_1903_);
v_m_1904_ = lean_ctor_get(v_v_1892_, 1);
lean_inc(v_m_1904_);
lean_dec_ref_known(v_v_1892_, 2);
v_ofNat_1905_ = lean_ctor_get(v_toSemiring_1890_, 3);
v_npow_1906_ = lean_ctor_get(v_toSemiring_1890_, 5);
v_x_1907_ = lean_ctor_get(v_p_1903_, 0);
lean_inc(v_x_1907_);
v_k_1908_ = lean_ctor_get(v_p_1903_, 1);
lean_inc(v_k_1908_);
lean_dec_ref(v_p_1903_);
v___x_1909_ = lean_unsigned_to_nat(0u);
v___x_1910_ = lean_nat_dec_eq(v_k_1908_, v___x_1909_);
if (v___x_1910_ == 0)
{
uint8_t v___x_1911_; 
v___x_1911_ = lean_nat_dec_eq(v_k_1908_, v___x_1896_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1912_ = l_Lean_RArray_getImpl___redArg(v_ctx_1885_, v_x_1907_);
lean_dec(v_x_1907_);
lean_inc(v_npow_1906_);
v___x_1913_ = lean_apply_2(v_npow_1906_, v___x_1912_, v_k_1908_);
lean_inc_ref(v_toSemiring_1890_);
v___x_1914_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1890_, v_ctx_1885_, v_m_1904_, v___x_1913_);
v___x_1915_ = lean_apply_2(v_zsmul_1895_, v_k_1891_, v___x_1914_);
v___x_1916_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1884_, v_ctx_1885_, v_p_1893_, v___x_1915_);
return v___x_1916_;
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_dec(v_k_1908_);
v___x_1917_ = l_Lean_RArray_getImpl___redArg(v_ctx_1885_, v_x_1907_);
lean_dec(v_x_1907_);
lean_inc_ref(v_toSemiring_1890_);
v___x_1918_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1890_, v_ctx_1885_, v_m_1904_, v___x_1917_);
v___x_1919_ = lean_apply_2(v_zsmul_1895_, v_k_1891_, v___x_1918_);
v___x_1920_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1884_, v_ctx_1885_, v_p_1893_, v___x_1919_);
return v___x_1920_;
}
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
lean_dec(v_k_1908_);
lean_dec(v_x_1907_);
lean_inc(v_ofNat_1905_);
v___x_1921_ = lean_apply_1(v_ofNat_1905_, v___x_1896_);
lean_inc_ref(v_toSemiring_1890_);
v___x_1922_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1890_, v_ctx_1885_, v_m_1904_, v___x_1921_);
v___x_1923_ = lean_apply_2(v_zsmul_1895_, v_k_1891_, v___x_1922_);
v___x_1924_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1884_, v_ctx_1885_, v_p_1893_, v___x_1923_);
return v___x_1924_;
}
}
}
else
{
lean_dec(v_zsmul_1895_);
lean_dec(v_k_1891_);
if (lean_obj_tag(v_v_1892_) == 0)
{
lean_object* v_ofNat_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_ofNat_1925_ = lean_ctor_get(v_toSemiring_1890_, 3);
lean_inc(v_ofNat_1925_);
v___x_1926_ = lean_apply_1(v_ofNat_1925_, v___x_1896_);
v___x_1927_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1884_, v_ctx_1885_, v_p_1893_, v___x_1926_);
return v___x_1927_;
}
else
{
lean_object* v_p_1928_; lean_object* v_m_1929_; lean_object* v_ofNat_1930_; lean_object* v_npow_1931_; lean_object* v_x_1932_; lean_object* v_k_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v_p_1928_ = lean_ctor_get(v_v_1892_, 0);
lean_inc_ref(v_p_1928_);
v_m_1929_ = lean_ctor_get(v_v_1892_, 1);
lean_inc(v_m_1929_);
lean_dec_ref_known(v_v_1892_, 2);
v_ofNat_1930_ = lean_ctor_get(v_toSemiring_1890_, 3);
v_npow_1931_ = lean_ctor_get(v_toSemiring_1890_, 5);
v_x_1932_ = lean_ctor_get(v_p_1928_, 0);
lean_inc(v_x_1932_);
v_k_1933_ = lean_ctor_get(v_p_1928_, 1);
lean_inc(v_k_1933_);
lean_dec_ref(v_p_1928_);
v___x_1934_ = lean_unsigned_to_nat(0u);
v___x_1935_ = lean_nat_dec_eq(v_k_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
uint8_t v___x_1936_; 
v___x_1936_ = lean_nat_dec_eq(v_k_1933_, v___x_1896_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1937_ = l_Lean_RArray_getImpl___redArg(v_ctx_1885_, v_x_1932_);
lean_dec(v_x_1932_);
lean_inc(v_npow_1931_);
v___x_1938_ = lean_apply_2(v_npow_1931_, v___x_1937_, v_k_1933_);
lean_inc_ref(v_toSemiring_1890_);
v___x_1939_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1890_, v_ctx_1885_, v_m_1929_, v___x_1938_);
v___x_1940_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1884_, v_ctx_1885_, v_p_1893_, v___x_1939_);
return v___x_1940_;
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
lean_dec(v_k_1933_);
v___x_1941_ = l_Lean_RArray_getImpl___redArg(v_ctx_1885_, v_x_1932_);
lean_dec(v_x_1932_);
lean_inc_ref(v_toSemiring_1890_);
v___x_1942_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1890_, v_ctx_1885_, v_m_1929_, v___x_1941_);
v___x_1943_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1884_, v_ctx_1885_, v_p_1893_, v___x_1942_);
return v___x_1943_;
}
}
else
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
lean_dec(v_k_1933_);
lean_dec(v_x_1932_);
lean_inc(v_ofNat_1930_);
v___x_1944_ = lean_apply_1(v_ofNat_1930_, v___x_1896_);
lean_inc_ref(v_toSemiring_1890_);
v___x_1945_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1890_, v_ctx_1885_, v_m_1929_, v___x_1944_);
v___x_1946_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1884_, v_ctx_1885_, v_p_1893_, v___x_1945_);
return v___x_1946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg___boxed(lean_object* v_inst_1947_, lean_object* v_ctx_1948_, lean_object* v_p_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_Grind_CommRing_Poly_denote_x27___redArg(v_inst_1947_, v_ctx_1948_, v_p_1949_);
lean_dec_ref(v_ctx_1948_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27(lean_object* v_00_u03b1_1951_, lean_object* v_inst_1952_, lean_object* v_ctx_1953_, lean_object* v_p_1954_){
_start:
{
if (lean_obj_tag(v_p_1954_) == 0)
{
lean_object* v_intCast_1955_; lean_object* v_k_1956_; lean_object* v___x_1957_; 
v_intCast_1955_ = lean_ctor_get(v_inst_1952_, 3);
lean_inc(v_intCast_1955_);
lean_dec_ref(v_inst_1952_);
v_k_1956_ = lean_ctor_get(v_p_1954_, 0);
lean_inc(v_k_1956_);
lean_dec_ref_known(v_p_1954_, 1);
v___x_1957_ = lean_apply_1(v_intCast_1955_, v_k_1956_);
return v___x_1957_;
}
else
{
lean_object* v_toSemiring_1958_; lean_object* v_k_1959_; lean_object* v_v_1960_; lean_object* v_p_1961_; lean_object* v___x_1962_; lean_object* v_zsmul_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v_toSemiring_1958_ = lean_ctor_get(v_inst_1952_, 0);
v_k_1959_ = lean_ctor_get(v_p_1954_, 0);
lean_inc(v_k_1959_);
v_v_1960_ = lean_ctor_get(v_p_1954_, 1);
lean_inc(v_v_1960_);
v_p_1961_ = lean_ctor_get(v_p_1954_, 2);
lean_inc_ref(v_p_1961_);
lean_dec_ref_known(v_p_1954_, 3);
lean_inc_ref(v_inst_1952_);
v___x_1962_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1952_);
v_zsmul_1963_ = lean_ctor_get(v___x_1962_, 2);
lean_inc(v_zsmul_1963_);
lean_dec_ref(v___x_1962_);
v___x_1964_ = lean_unsigned_to_nat(1u);
v___x_1965_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1966_ = lean_int_dec_eq(v_k_1959_, v___x_1965_);
if (v___x_1966_ == 0)
{
if (lean_obj_tag(v_v_1960_) == 0)
{
lean_object* v_ofNat_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_ofNat_1967_ = lean_ctor_get(v_toSemiring_1958_, 3);
lean_inc(v_ofNat_1967_);
v___x_1968_ = lean_apply_1(v_ofNat_1967_, v___x_1964_);
v___x_1969_ = lean_apply_2(v_zsmul_1963_, v_k_1959_, v___x_1968_);
v___x_1970_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1952_, v_ctx_1953_, v_p_1961_, v___x_1969_);
return v___x_1970_;
}
else
{
lean_object* v_p_1971_; lean_object* v_m_1972_; lean_object* v_ofNat_1973_; lean_object* v_npow_1974_; lean_object* v_x_1975_; lean_object* v_k_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v_p_1971_ = lean_ctor_get(v_v_1960_, 0);
lean_inc_ref(v_p_1971_);
v_m_1972_ = lean_ctor_get(v_v_1960_, 1);
lean_inc(v_m_1972_);
lean_dec_ref_known(v_v_1960_, 2);
v_ofNat_1973_ = lean_ctor_get(v_toSemiring_1958_, 3);
v_npow_1974_ = lean_ctor_get(v_toSemiring_1958_, 5);
v_x_1975_ = lean_ctor_get(v_p_1971_, 0);
lean_inc(v_x_1975_);
v_k_1976_ = lean_ctor_get(v_p_1971_, 1);
lean_inc(v_k_1976_);
lean_dec_ref(v_p_1971_);
v___x_1977_ = lean_unsigned_to_nat(0u);
v___x_1978_ = lean_nat_dec_eq(v_k_1976_, v___x_1977_);
if (v___x_1978_ == 0)
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_nat_dec_eq(v_k_1976_, v___x_1964_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1980_ = l_Lean_RArray_getImpl___redArg(v_ctx_1953_, v_x_1975_);
lean_dec(v_x_1975_);
lean_inc(v_npow_1974_);
v___x_1981_ = lean_apply_2(v_npow_1974_, v___x_1980_, v_k_1976_);
lean_inc_ref(v_toSemiring_1958_);
v___x_1982_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1958_, v_ctx_1953_, v_m_1972_, v___x_1981_);
v___x_1983_ = lean_apply_2(v_zsmul_1963_, v_k_1959_, v___x_1982_);
v___x_1984_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1952_, v_ctx_1953_, v_p_1961_, v___x_1983_);
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_dec(v_k_1976_);
v___x_1985_ = l_Lean_RArray_getImpl___redArg(v_ctx_1953_, v_x_1975_);
lean_dec(v_x_1975_);
lean_inc_ref(v_toSemiring_1958_);
v___x_1986_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1958_, v_ctx_1953_, v_m_1972_, v___x_1985_);
v___x_1987_ = lean_apply_2(v_zsmul_1963_, v_k_1959_, v___x_1986_);
v___x_1988_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1952_, v_ctx_1953_, v_p_1961_, v___x_1987_);
return v___x_1988_;
}
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_dec(v_k_1976_);
lean_dec(v_x_1975_);
lean_inc(v_ofNat_1973_);
v___x_1989_ = lean_apply_1(v_ofNat_1973_, v___x_1964_);
lean_inc_ref(v_toSemiring_1958_);
v___x_1990_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1958_, v_ctx_1953_, v_m_1972_, v___x_1989_);
v___x_1991_ = lean_apply_2(v_zsmul_1963_, v_k_1959_, v___x_1990_);
v___x_1992_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1952_, v_ctx_1953_, v_p_1961_, v___x_1991_);
return v___x_1992_;
}
}
}
else
{
lean_dec(v_zsmul_1963_);
lean_dec(v_k_1959_);
if (lean_obj_tag(v_v_1960_) == 0)
{
lean_object* v_ofNat_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_ofNat_1993_ = lean_ctor_get(v_toSemiring_1958_, 3);
lean_inc(v_ofNat_1993_);
v___x_1994_ = lean_apply_1(v_ofNat_1993_, v___x_1964_);
v___x_1995_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1952_, v_ctx_1953_, v_p_1961_, v___x_1994_);
return v___x_1995_;
}
else
{
lean_object* v_p_1996_; lean_object* v_m_1997_; lean_object* v_ofNat_1998_; lean_object* v_npow_1999_; lean_object* v_x_2000_; lean_object* v_k_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v_p_1996_ = lean_ctor_get(v_v_1960_, 0);
lean_inc_ref(v_p_1996_);
v_m_1997_ = lean_ctor_get(v_v_1960_, 1);
lean_inc(v_m_1997_);
lean_dec_ref_known(v_v_1960_, 2);
v_ofNat_1998_ = lean_ctor_get(v_toSemiring_1958_, 3);
v_npow_1999_ = lean_ctor_get(v_toSemiring_1958_, 5);
v_x_2000_ = lean_ctor_get(v_p_1996_, 0);
lean_inc(v_x_2000_);
v_k_2001_ = lean_ctor_get(v_p_1996_, 1);
lean_inc(v_k_2001_);
lean_dec_ref(v_p_1996_);
v___x_2002_ = lean_unsigned_to_nat(0u);
v___x_2003_ = lean_nat_dec_eq(v_k_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_nat_dec_eq(v_k_2001_, v___x_1964_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2005_ = l_Lean_RArray_getImpl___redArg(v_ctx_1953_, v_x_2000_);
lean_dec(v_x_2000_);
lean_inc(v_npow_1999_);
v___x_2006_ = lean_apply_2(v_npow_1999_, v___x_2005_, v_k_2001_);
lean_inc_ref(v_toSemiring_1958_);
v___x_2007_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1958_, v_ctx_1953_, v_m_1997_, v___x_2006_);
v___x_2008_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1952_, v_ctx_1953_, v_p_1961_, v___x_2007_);
return v___x_2008_;
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
lean_dec(v_k_2001_);
v___x_2009_ = l_Lean_RArray_getImpl___redArg(v_ctx_1953_, v_x_2000_);
lean_dec(v_x_2000_);
lean_inc_ref(v_toSemiring_1958_);
v___x_2010_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1958_, v_ctx_1953_, v_m_1997_, v___x_2009_);
v___x_2011_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1952_, v_ctx_1953_, v_p_1961_, v___x_2010_);
return v___x_2011_;
}
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec(v_k_2001_);
lean_dec(v_x_2000_);
lean_inc(v_ofNat_1998_);
v___x_2012_ = lean_apply_1(v_ofNat_1998_, v___x_1964_);
lean_inc_ref(v_toSemiring_1958_);
v___x_2013_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1958_, v_ctx_1953_, v_m_1997_, v___x_2012_);
v___x_2014_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1952_, v_ctx_1953_, v_p_1961_, v___x_2013_);
return v___x_2014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___boxed(lean_object* v_00_u03b1_2015_, lean_object* v_inst_2016_, lean_object* v_ctx_2017_, lean_object* v_p_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_Grind_CommRing_Poly_denote_x27(v_00_u03b1_2015_, v_inst_2016_, v_ctx_2017_, v_p_2018_);
lean_dec_ref(v_ctx_2017_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object* v_m_2020_){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2021_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2022_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2023_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2021_);
lean_ctor_set(v___x_2023_, 1, v_m_2020_);
lean_ctor_set(v___x_2023_, 2, v___x_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object* v_x_2024_){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = l_Lean_Grind_CommRing_Mon_ofVar(v_x_2024_);
v___x_2026_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_isSorted(lean_object* v_x_2027_){
_start:
{
if (lean_obj_tag(v_x_2027_) == 0)
{
uint8_t v___x_2028_; 
v___x_2028_ = 1;
return v___x_2028_;
}
else
{
lean_object* v_p_2029_; 
v_p_2029_ = lean_ctor_get(v_x_2027_, 2);
if (lean_obj_tag(v_p_2029_) == 0)
{
uint8_t v___x_2030_; 
v___x_2030_ = 1;
return v___x_2030_;
}
else
{
lean_object* v_v_2031_; lean_object* v_v_2032_; uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v_v_2031_ = lean_ctor_get(v_x_2027_, 1);
v_v_2032_ = lean_ctor_get(v_p_2029_, 1);
v___x_2033_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2031_, v_v_2032_);
v___x_2034_ = lean_box(v___x_2033_);
v___x_2035_ = lean_obj_tag_nat(v___x_2034_);
lean_dec(v___x_2034_);
v___x_2036_ = lean_unsigned_to_nat(2u);
v___x_2037_ = lean_nat_dec_eq(v___x_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
return v___x_2037_;
}
else
{
v_x_2027_ = v_p_2029_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isSorted___boxed(lean_object* v_x_2039_){
_start:
{
uint8_t v_res_2040_; lean_object* v_r_2041_; 
v_res_2040_ = l_Lean_Grind_CommRing_Poly_isSorted(v_x_2039_);
lean_dec_ref(v_x_2039_);
v_r_2041_ = lean_box(v_res_2040_);
return v_r_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go(lean_object* v_k_2042_, lean_object* v_a_2043_){
_start:
{
if (lean_obj_tag(v_a_2043_) == 0)
{
lean_object* v_k_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2052_; 
v_k_2044_ = lean_ctor_get(v_a_2043_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_a_2043_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2046_ = v_a_2043_;
v_isShared_2047_ = v_isSharedCheck_2052_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_k_2044_);
lean_dec(v_a_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2052_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = lean_int_add(v_k_2044_, v_k_2042_);
lean_dec(v_k_2044_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2048_);
v___x_2050_ = v___x_2046_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
else
{
lean_object* v_k_2053_; lean_object* v_v_2054_; lean_object* v_p_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2063_; 
v_k_2053_ = lean_ctor_get(v_a_2043_, 0);
v_v_2054_ = lean_ctor_get(v_a_2043_, 1);
v_p_2055_ = lean_ctor_get(v_a_2043_, 2);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_a_2043_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2057_ = v_a_2043_;
v_isShared_2058_ = v_isSharedCheck_2063_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_p_2055_);
lean_inc(v_v_2054_);
lean_inc(v_k_2053_);
lean_dec(v_a_2043_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2063_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2042_, v_p_2055_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 2, v___x_2059_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_k_2053_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_v_2054_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go___boxed(lean_object* v_k_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2064_, v_a_2065_);
lean_dec(v_k_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object* v_p_2067_, lean_object* v_k_2068_){
_start:
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2070_ = lean_int_dec_eq(v_k_2068_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2068_, v_p_2067_);
return v___x_2071_;
}
else
{
return v_p_2067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst___boxed(lean_object* v_p_2072_, lean_object* v_k_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2072_, v_k_2073_);
lean_dec(v_k_2073_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert_go(lean_object* v_k_2075_, lean_object* v_m_2076_, lean_object* v_a_2077_){
_start:
{
if (lean_obj_tag(v_a_2077_) == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2078_, 0, v_k_2075_);
lean_ctor_set(v___x_2078_, 1, v_m_2076_);
lean_ctor_set(v___x_2078_, 2, v_a_2077_);
return v___x_2078_;
}
else
{
lean_object* v_k_2079_; lean_object* v_v_2080_; lean_object* v_p_2081_; uint8_t v___x_2082_; 
v_k_2079_ = lean_ctor_get(v_a_2077_, 0);
v_v_2080_ = lean_ctor_get(v_a_2077_, 1);
v_p_2081_ = lean_ctor_get(v_a_2077_, 2);
v___x_2082_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2076_, v_v_2080_);
switch(v___x_2082_)
{
case 0:
{
lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2090_; 
lean_inc_ref(v_p_2081_);
lean_inc(v_v_2080_);
lean_inc(v_k_2079_);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_a_2077_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; lean_object* v_unused_2092_; lean_object* v_unused_2093_; 
v_unused_2091_ = lean_ctor_get(v_a_2077_, 2);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_a_2077_, 1);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v_a_2077_, 0);
lean_dec(v_unused_2093_);
v___x_2084_ = v_a_2077_;
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
else
{
lean_dec(v_a_2077_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2075_, v_m_2076_, v_p_2081_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 2, v___x_2086_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_k_2079_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_v_2080_);
lean_ctor_set(v_reuseFailAlloc_2089_, 2, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
case 1:
{
lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2103_; 
lean_inc_ref(v_p_2081_);
lean_inc(v_k_2079_);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_a_2077_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; lean_object* v_unused_2105_; lean_object* v_unused_2106_; 
v_unused_2104_ = lean_ctor_get(v_a_2077_, 2);
lean_dec(v_unused_2104_);
v_unused_2105_ = lean_ctor_get(v_a_2077_, 1);
lean_dec(v_unused_2105_);
v_unused_2106_ = lean_ctor_get(v_a_2077_, 0);
lean_dec(v_unused_2106_);
v___x_2095_ = v_a_2077_;
v_isShared_2096_ = v_isSharedCheck_2103_;
goto v_resetjp_2094_;
}
else
{
lean_dec(v_a_2077_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2103_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v_k_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_k_2097_ = lean_int_add(v_k_2075_, v_k_2079_);
lean_dec(v_k_2079_);
lean_dec(v_k_2075_);
v___x_2098_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2099_ = lean_int_dec_eq(v_k_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2101_; 
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 1, v_m_2076_);
lean_ctor_set(v___x_2095_, 0, v_k_2097_);
v___x_2101_ = v___x_2095_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_k_2097_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_m_2076_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_p_2081_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
else
{
lean_dec(v_k_2097_);
lean_del_object(v___x_2095_);
lean_dec(v_m_2076_);
return v_p_2081_;
}
}
}
default: 
{
lean_object* v___x_2107_; 
v___x_2107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2107_, 0, v_k_2075_);
lean_ctor_set(v___x_2107_, 1, v_m_2076_);
lean_ctor_set(v___x_2107_, 2, v_a_2077_);
return v___x_2107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert(lean_object* v_k_2108_, lean_object* v_m_2109_, lean_object* v_p_2110_){
_start:
{
lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2111_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2112_ = lean_int_dec_eq(v_k_2108_, v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = lean_box(0);
v___x_2114_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2109_, v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2108_, v_m_2109_, v_p_2110_);
return v___x_2115_;
}
else
{
lean_object* v___x_2116_; 
lean_dec(v_m_2109_);
v___x_2116_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2110_, v_k_2108_);
lean_dec(v_k_2108_);
return v___x_2116_;
}
}
else
{
lean_dec(v_m_2109_);
lean_dec(v_k_2108_);
return v_p_2110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_concat(lean_object* v_p_u2081_2117_, lean_object* v_p_u2082_2118_){
_start:
{
if (lean_obj_tag(v_p_u2081_2117_) == 0)
{
lean_object* v_k_2119_; lean_object* v___x_2120_; 
v_k_2119_ = lean_ctor_get(v_p_u2081_2117_, 0);
lean_inc(v_k_2119_);
lean_dec_ref_known(v_p_u2081_2117_, 1);
v___x_2120_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2118_, v_k_2119_);
lean_dec(v_k_2119_);
return v___x_2120_;
}
else
{
lean_object* v_k_2121_; lean_object* v_v_2122_; lean_object* v_p_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2131_; 
v_k_2121_ = lean_ctor_get(v_p_u2081_2117_, 0);
v_v_2122_ = lean_ctor_get(v_p_u2081_2117_, 1);
v_p_2123_ = lean_ctor_get(v_p_u2081_2117_, 2);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_p_u2081_2117_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2125_ = v_p_u2081_2117_;
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_p_2123_);
lean_inc(v_v_2122_);
lean_inc(v_k_2121_);
lean_dec(v_p_u2081_2117_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = l_Lean_Grind_CommRing_Poly_concat(v_p_2123_, v_p_u2082_2118_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 2, v___x_2127_);
v___x_2129_ = v___x_2125_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_k_2121_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_v_2122_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go(lean_object* v_k_2132_, lean_object* v_a_2133_){
_start:
{
if (lean_obj_tag(v_a_2133_) == 0)
{
lean_object* v_k_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2142_; 
v_k_2134_ = lean_ctor_get(v_a_2133_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_a_2133_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2136_ = v_a_2133_;
v_isShared_2137_ = v_isSharedCheck_2142_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_k_2134_);
lean_dec(v_a_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2142_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2138_ = lean_int_mul(v_k_2132_, v_k_2134_);
lean_dec(v_k_2134_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2138_);
v___x_2140_ = v___x_2136_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
else
{
lean_object* v_k_2143_; lean_object* v_v_2144_; lean_object* v_p_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2154_; 
v_k_2143_ = lean_ctor_get(v_a_2133_, 0);
v_v_2144_ = lean_ctor_get(v_a_2133_, 1);
v_p_2145_ = lean_ctor_get(v_a_2133_, 2);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_a_2133_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2147_ = v_a_2133_;
v_isShared_2148_ = v_isSharedCheck_2154_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_p_2145_);
lean_inc(v_v_2144_);
lean_inc(v_k_2143_);
lean_dec(v_a_2133_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2154_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2149_ = lean_int_mul(v_k_2132_, v_k_2143_);
lean_dec(v_k_2143_);
v___x_2150_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2132_, v_p_2145_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 2, v___x_2150_);
lean_ctor_set(v___x_2147_, 0, v___x_2149_);
v___x_2152_ = v___x_2147_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_v_2144_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go___boxed(lean_object* v_k_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2155_, v_a_2156_);
lean_dec(v_k_2155_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object* v_k_2158_, lean_object* v_p_2159_){
_start:
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2161_ = lean_int_dec_eq(v_k_2158_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2163_ = lean_int_dec_eq(v_k_2158_, v___x_2162_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2158_, v_p_2159_);
return v___x_2164_;
}
else
{
return v_p_2159_;
}
}
else
{
lean_object* v___x_2165_; 
lean_dec_ref(v_p_2159_);
v___x_2165_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst___boxed(lean_object* v_k_2166_, lean_object* v_p_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2166_, v_p_2167_);
lean_dec(v_k_2166_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go(lean_object* v_k_2169_, lean_object* v_m_2170_, lean_object* v_a_2171_){
_start:
{
if (lean_obj_tag(v_a_2171_) == 0)
{
lean_object* v_k_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v_k_2172_ = lean_ctor_get(v_a_2171_, 0);
lean_inc(v_k_2172_);
lean_dec_ref_known(v_a_2171_, 1);
v___x_2173_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2174_ = lean_int_dec_eq(v_k_2172_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = lean_int_mul(v_k_2169_, v_k_2172_);
lean_dec(v_k_2172_);
v___x_2176_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2177_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set(v___x_2177_, 1, v_m_2170_);
lean_ctor_set(v___x_2177_, 2, v___x_2176_);
return v___x_2177_;
}
else
{
lean_object* v___x_2178_; 
lean_dec(v_k_2172_);
lean_dec(v_m_2170_);
v___x_2178_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2178_;
}
}
else
{
lean_object* v_k_2179_; lean_object* v_v_2180_; lean_object* v_p_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2191_; 
v_k_2179_ = lean_ctor_get(v_a_2171_, 0);
v_v_2180_ = lean_ctor_get(v_a_2171_, 1);
v_p_2181_ = lean_ctor_get(v_a_2171_, 2);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_a_2171_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2183_ = v_a_2171_;
v_isShared_2184_ = v_isSharedCheck_2191_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_p_2181_);
lean_inc(v_v_2180_);
lean_inc(v_k_2179_);
lean_dec(v_a_2171_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2191_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2185_ = lean_int_mul(v_k_2169_, v_k_2179_);
lean_dec(v_k_2179_);
lean_inc(v_m_2170_);
v___x_2186_ = l_Lean_Grind_CommRing_Mon_mul(v_m_2170_, v_v_2180_);
v___x_2187_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2169_, v_m_2170_, v_p_2181_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 2, v___x_2187_);
lean_ctor_set(v___x_2183_, 1, v___x_2186_);
lean_ctor_set(v___x_2183_, 0, v___x_2185_);
v___x_2189_ = v___x_2183_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2186_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go___boxed(lean_object* v_k_2192_, lean_object* v_m_2193_, lean_object* v_a_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2192_, v_m_2193_, v_a_2194_);
lean_dec(v_k_2192_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object* v_k_2196_, lean_object* v_m_2197_, lean_object* v_p_2198_){
_start:
{
lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2199_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2200_ = lean_int_dec_eq(v_k_2196_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2201_ = lean_box(0);
v___x_2202_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2197_, v___x_2201_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2196_, v_m_2197_, v_p_2198_);
return v___x_2203_;
}
else
{
lean_object* v___x_2204_; 
lean_dec(v_m_2197_);
v___x_2204_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2196_, v_p_2198_);
return v___x_2204_;
}
}
else
{
lean_object* v___x_2205_; 
lean_dec_ref(v_p_2198_);
lean_dec(v_m_2197_);
v___x_2205_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon___boxed(lean_object* v_k_2206_, lean_object* v_m_2207_, lean_object* v_p_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2206_, v_m_2207_, v_p_2208_);
lean_dec(v_k_2206_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go(lean_object* v_k_2210_, lean_object* v_m_2211_, lean_object* v_p_2212_, lean_object* v_acc_2213_){
_start:
{
if (lean_obj_tag(v_p_2212_) == 0)
{
lean_object* v_k_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v_k_2214_ = lean_ctor_get(v_p_2212_, 0);
lean_inc(v_k_2214_);
lean_dec_ref_known(v_p_2212_, 1);
v___x_2215_ = lean_int_mul(v_k_2210_, v_k_2214_);
lean_dec(v_k_2214_);
v___x_2216_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2215_, v_m_2211_, v_acc_2213_);
return v___x_2216_;
}
else
{
lean_object* v_k_2217_; lean_object* v_v_2218_; lean_object* v_p_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_k_2217_ = lean_ctor_get(v_p_2212_, 0);
lean_inc(v_k_2217_);
v_v_2218_ = lean_ctor_get(v_p_2212_, 1);
lean_inc(v_v_2218_);
v_p_2219_ = lean_ctor_get(v_p_2212_, 2);
lean_inc_ref(v_p_2219_);
lean_dec_ref_known(v_p_2212_, 3);
v___x_2220_ = lean_int_mul(v_k_2210_, v_k_2217_);
lean_dec(v_k_2217_);
lean_inc(v_m_2211_);
v___x_2221_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_2211_, v_v_2218_);
v___x_2222_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2220_, v___x_2221_, v_acc_2213_);
v_p_2212_ = v_p_2219_;
v_acc_2213_ = v___x_2222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go___boxed(lean_object* v_k_2224_, lean_object* v_m_2225_, lean_object* v_p_2226_, lean_object* v_acc_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2224_, v_m_2225_, v_p_2226_, v_acc_2227_);
lean_dec(v_k_2224_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc(lean_object* v_k_2229_, lean_object* v_m_2230_, lean_object* v_p_2231_){
_start:
{
lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2232_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2233_ = lean_int_dec_eq(v_k_2229_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; uint8_t v___x_2235_; 
v___x_2234_ = lean_box(0);
v___x_2235_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2230_, v___x_2234_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2237_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2229_, v_m_2230_, v_p_2231_, v___x_2236_);
return v___x_2237_;
}
else
{
lean_object* v___x_2238_; 
lean_dec(v_m_2230_);
v___x_2238_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2229_, v_p_2231_);
return v___x_2238_;
}
}
else
{
lean_object* v___x_2239_; 
lean_dec_ref(v_p_2231_);
lean_dec(v_m_2230_);
v___x_2239_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc___boxed(lean_object* v_k_2240_, lean_object* v_m_2241_, lean_object* v_p_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2240_, v_m_2241_, v_p_2242_);
lean_dec(v_k_2240_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_go(lean_object* v_fuel_2244_, lean_object* v_p_u2081_2245_, lean_object* v_p_u2082_2246_){
_start:
{
lean_object* v_zero_2247_; uint8_t v_isZero_2248_; 
v_zero_2247_ = lean_unsigned_to_nat(0u);
v_isZero_2248_ = lean_nat_dec_eq(v_fuel_2244_, v_zero_2247_);
if (v_isZero_2248_ == 1)
{
lean_object* v___x_2249_; 
lean_dec(v_fuel_2244_);
v___x_2249_ = l_Lean_Grind_CommRing_Poly_concat(v_p_u2081_2245_, v_p_u2082_2246_);
return v___x_2249_;
}
else
{
if (lean_obj_tag(v_p_u2081_2245_) == 0)
{
lean_dec(v_fuel_2244_);
if (lean_obj_tag(v_p_u2082_2246_) == 0)
{
lean_object* v_k_2250_; lean_object* v_k_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2259_; 
v_k_2250_ = lean_ctor_get(v_p_u2081_2245_, 0);
lean_inc(v_k_2250_);
lean_dec_ref_known(v_p_u2081_2245_, 1);
v_k_2251_ = lean_ctor_get(v_p_u2082_2246_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_p_u2082_2246_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2253_ = v_p_u2082_2246_;
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_k_2251_);
lean_dec(v_p_u2082_2246_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2255_ = lean_int_add(v_k_2250_, v_k_2251_);
lean_dec(v_k_2251_);
lean_dec(v_k_2250_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2255_);
v___x_2257_ = v___x_2253_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
else
{
lean_object* v_k_2260_; lean_object* v___x_2261_; 
v_k_2260_ = lean_ctor_get(v_p_u2081_2245_, 0);
lean_inc(v_k_2260_);
lean_dec_ref_known(v_p_u2081_2245_, 1);
v___x_2261_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2246_, v_k_2260_);
lean_dec(v_k_2260_);
return v___x_2261_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_2246_) == 0)
{
lean_object* v_k_2262_; lean_object* v___x_2263_; 
lean_dec(v_fuel_2244_);
v_k_2262_ = lean_ctor_get(v_p_u2082_2246_, 0);
lean_inc(v_k_2262_);
lean_dec_ref_known(v_p_u2082_2246_, 1);
v___x_2263_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2081_2245_, v_k_2262_);
lean_dec(v_k_2262_);
return v___x_2263_;
}
else
{
lean_object* v_k_2264_; lean_object* v_v_2265_; lean_object* v_p_2266_; lean_object* v_k_2267_; lean_object* v_v_2268_; lean_object* v_p_2269_; lean_object* v_one_2270_; lean_object* v_n_2271_; uint8_t v___x_2272_; 
v_k_2264_ = lean_ctor_get(v_p_u2081_2245_, 0);
v_v_2265_ = lean_ctor_get(v_p_u2081_2245_, 1);
v_p_2266_ = lean_ctor_get(v_p_u2081_2245_, 2);
v_k_2267_ = lean_ctor_get(v_p_u2082_2246_, 0);
v_v_2268_ = lean_ctor_get(v_p_u2082_2246_, 1);
v_p_2269_ = lean_ctor_get(v_p_u2082_2246_, 2);
v_one_2270_ = lean_unsigned_to_nat(1u);
v_n_2271_ = lean_nat_sub(v_fuel_2244_, v_one_2270_);
lean_dec(v_fuel_2244_);
v___x_2272_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2265_, v_v_2268_);
switch(v___x_2272_)
{
case 0:
{
lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2280_; 
lean_inc_ref(v_p_2269_);
lean_inc(v_v_2268_);
lean_inc(v_k_2267_);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_p_u2082_2246_);
if (v_isSharedCheck_2280_ == 0)
{
lean_object* v_unused_2281_; lean_object* v_unused_2282_; lean_object* v_unused_2283_; 
v_unused_2281_ = lean_ctor_get(v_p_u2082_2246_, 2);
lean_dec(v_unused_2281_);
v_unused_2282_ = lean_ctor_get(v_p_u2082_2246_, 1);
lean_dec(v_unused_2282_);
v_unused_2283_ = lean_ctor_get(v_p_u2082_2246_, 0);
lean_dec(v_unused_2283_);
v___x_2274_ = v_p_u2082_2246_;
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
else
{
lean_dec(v_p_u2082_2246_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2276_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2271_, v_p_u2081_2245_, v_p_2269_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 2, v___x_2276_);
v___x_2278_ = v___x_2274_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_k_2267_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_v_2268_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
case 1:
{
lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2295_; 
lean_inc_ref(v_p_2269_);
lean_inc(v_k_2267_);
lean_inc_ref(v_p_2266_);
lean_inc(v_v_2265_);
lean_inc(v_k_2264_);
lean_dec_ref_known(v_p_u2081_2245_, 3);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_p_u2082_2246_);
if (v_isSharedCheck_2295_ == 0)
{
lean_object* v_unused_2296_; lean_object* v_unused_2297_; lean_object* v_unused_2298_; 
v_unused_2296_ = lean_ctor_get(v_p_u2082_2246_, 2);
lean_dec(v_unused_2296_);
v_unused_2297_ = lean_ctor_get(v_p_u2082_2246_, 1);
lean_dec(v_unused_2297_);
v_unused_2298_ = lean_ctor_get(v_p_u2082_2246_, 0);
lean_dec(v_unused_2298_);
v___x_2285_ = v_p_u2082_2246_;
v_isShared_2286_ = v_isSharedCheck_2295_;
goto v_resetjp_2284_;
}
else
{
lean_dec(v_p_u2082_2246_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2295_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v_k_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v_k_2287_ = lean_int_add(v_k_2264_, v_k_2267_);
lean_dec(v_k_2267_);
lean_dec(v_k_2264_);
v___x_2288_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2289_ = lean_int_dec_eq(v_k_2287_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2290_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2271_, v_p_2266_, v_p_2269_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 2, v___x_2290_);
lean_ctor_set(v___x_2285_, 1, v_v_2265_);
lean_ctor_set(v___x_2285_, 0, v_k_2287_);
v___x_2292_ = v___x_2285_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_k_2287_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_v_2265_);
lean_ctor_set(v_reuseFailAlloc_2293_, 2, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
else
{
lean_dec(v_k_2287_);
lean_del_object(v___x_2285_);
lean_dec(v_v_2265_);
v_fuel_2244_ = v_n_2271_;
v_p_u2081_2245_ = v_p_2266_;
v_p_u2082_2246_ = v_p_2269_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2306_; 
lean_inc_ref(v_p_2266_);
lean_inc(v_v_2265_);
lean_inc(v_k_2264_);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_p_u2081_2245_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; lean_object* v_unused_2308_; lean_object* v_unused_2309_; 
v_unused_2307_ = lean_ctor_get(v_p_u2081_2245_, 2);
lean_dec(v_unused_2307_);
v_unused_2308_ = lean_ctor_get(v_p_u2081_2245_, 1);
lean_dec(v_unused_2308_);
v_unused_2309_ = lean_ctor_get(v_p_u2081_2245_, 0);
lean_dec(v_unused_2309_);
v___x_2300_ = v_p_u2081_2245_;
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
else
{
lean_dec(v_p_u2081_2245_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2271_, v_p_2266_, v_p_u2082_2246_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 2, v___x_2302_);
v___x_2304_ = v___x_2300_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_k_2264_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_v_2265_);
lean_ctor_set(v_reuseFailAlloc_2305_, 2, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object* v_p_u2081_2310_, lean_object* v_p_u2082_2311_){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = lean_unsigned_to_nat(1000000u);
v___x_2313_ = l_Lean_Grind_CommRing_Poly_combine_go(v___x_2312_, v_p_u2081_2310_, v_p_u2082_2311_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object* v_p_u2081_2314_, lean_object* v_p_u2082_2315_, lean_object* v_h__1_2316_, lean_object* v_h__2_2317_, lean_object* v_h__3_2318_, lean_object* v_h__4_2319_){
_start:
{
if (lean_obj_tag(v_p_u2081_2314_) == 0)
{
lean_dec(v_h__4_2319_);
lean_dec(v_h__3_2318_);
if (lean_obj_tag(v_p_u2082_2315_) == 0)
{
lean_object* v_k_2320_; lean_object* v_k_2321_; lean_object* v___x_2322_; 
lean_dec(v_h__2_2317_);
v_k_2320_ = lean_ctor_get(v_p_u2081_2314_, 0);
lean_inc(v_k_2320_);
lean_dec_ref_known(v_p_u2081_2314_, 1);
v_k_2321_ = lean_ctor_get(v_p_u2082_2315_, 0);
lean_inc(v_k_2321_);
lean_dec_ref_known(v_p_u2082_2315_, 1);
v___x_2322_ = lean_apply_2(v_h__1_2316_, v_k_2320_, v_k_2321_);
return v___x_2322_;
}
else
{
lean_object* v_k_2323_; lean_object* v_k_2324_; lean_object* v_v_2325_; lean_object* v_p_2326_; lean_object* v___x_2327_; 
lean_dec(v_h__1_2316_);
v_k_2323_ = lean_ctor_get(v_p_u2081_2314_, 0);
lean_inc(v_k_2323_);
lean_dec_ref_known(v_p_u2081_2314_, 1);
v_k_2324_ = lean_ctor_get(v_p_u2082_2315_, 0);
lean_inc(v_k_2324_);
v_v_2325_ = lean_ctor_get(v_p_u2082_2315_, 1);
lean_inc(v_v_2325_);
v_p_2326_ = lean_ctor_get(v_p_u2082_2315_, 2);
lean_inc_ref(v_p_2326_);
lean_dec_ref_known(v_p_u2082_2315_, 3);
v___x_2327_ = lean_apply_4(v_h__2_2317_, v_k_2323_, v_k_2324_, v_v_2325_, v_p_2326_);
return v___x_2327_;
}
}
else
{
lean_dec(v_h__2_2317_);
lean_dec(v_h__1_2316_);
if (lean_obj_tag(v_p_u2082_2315_) == 0)
{
lean_object* v_k_2328_; lean_object* v_v_2329_; lean_object* v_p_2330_; lean_object* v_k_2331_; lean_object* v___x_2332_; 
lean_dec(v_h__4_2319_);
v_k_2328_ = lean_ctor_get(v_p_u2081_2314_, 0);
lean_inc(v_k_2328_);
v_v_2329_ = lean_ctor_get(v_p_u2081_2314_, 1);
lean_inc(v_v_2329_);
v_p_2330_ = lean_ctor_get(v_p_u2081_2314_, 2);
lean_inc_ref(v_p_2330_);
lean_dec_ref_known(v_p_u2081_2314_, 3);
v_k_2331_ = lean_ctor_get(v_p_u2082_2315_, 0);
lean_inc(v_k_2331_);
lean_dec_ref_known(v_p_u2082_2315_, 1);
v___x_2332_ = lean_apply_4(v_h__3_2318_, v_k_2328_, v_v_2329_, v_p_2330_, v_k_2331_);
return v___x_2332_;
}
else
{
lean_object* v_k_2333_; lean_object* v_v_2334_; lean_object* v_p_2335_; lean_object* v_k_2336_; lean_object* v_v_2337_; lean_object* v_p_2338_; lean_object* v___x_2339_; 
lean_dec(v_h__3_2318_);
v_k_2333_ = lean_ctor_get(v_p_u2081_2314_, 0);
lean_inc(v_k_2333_);
v_v_2334_ = lean_ctor_get(v_p_u2081_2314_, 1);
lean_inc(v_v_2334_);
v_p_2335_ = lean_ctor_get(v_p_u2081_2314_, 2);
lean_inc_ref(v_p_2335_);
lean_dec_ref_known(v_p_u2081_2314_, 3);
v_k_2336_ = lean_ctor_get(v_p_u2082_2315_, 0);
lean_inc(v_k_2336_);
v_v_2337_ = lean_ctor_get(v_p_u2082_2315_, 1);
lean_inc(v_v_2337_);
v_p_2338_ = lean_ctor_get(v_p_u2082_2315_, 2);
lean_inc_ref(v_p_2338_);
lean_dec_ref_known(v_p_u2082_2315_, 3);
v___x_2339_ = lean_apply_6(v_h__4_2319_, v_k_2333_, v_v_2334_, v_p_2335_, v_k_2336_, v_v_2337_, v_p_2338_);
return v___x_2339_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object* v_motive_2340_, lean_object* v_p_u2081_2341_, lean_object* v_p_u2082_2342_, lean_object* v_h__1_2343_, lean_object* v_h__2_2344_, lean_object* v_h__3_2345_, lean_object* v_h__4_2346_){
_start:
{
if (lean_obj_tag(v_p_u2081_2341_) == 0)
{
lean_dec(v_h__4_2346_);
lean_dec(v_h__3_2345_);
if (lean_obj_tag(v_p_u2082_2342_) == 0)
{
lean_object* v_k_2347_; lean_object* v_k_2348_; lean_object* v___x_2349_; 
lean_dec(v_h__2_2344_);
v_k_2347_ = lean_ctor_get(v_p_u2081_2341_, 0);
lean_inc(v_k_2347_);
lean_dec_ref_known(v_p_u2081_2341_, 1);
v_k_2348_ = lean_ctor_get(v_p_u2082_2342_, 0);
lean_inc(v_k_2348_);
lean_dec_ref_known(v_p_u2082_2342_, 1);
v___x_2349_ = lean_apply_2(v_h__1_2343_, v_k_2347_, v_k_2348_);
return v___x_2349_;
}
else
{
lean_object* v_k_2350_; lean_object* v_k_2351_; lean_object* v_v_2352_; lean_object* v_p_2353_; lean_object* v___x_2354_; 
lean_dec(v_h__1_2343_);
v_k_2350_ = lean_ctor_get(v_p_u2081_2341_, 0);
lean_inc(v_k_2350_);
lean_dec_ref_known(v_p_u2081_2341_, 1);
v_k_2351_ = lean_ctor_get(v_p_u2082_2342_, 0);
lean_inc(v_k_2351_);
v_v_2352_ = lean_ctor_get(v_p_u2082_2342_, 1);
lean_inc(v_v_2352_);
v_p_2353_ = lean_ctor_get(v_p_u2082_2342_, 2);
lean_inc_ref(v_p_2353_);
lean_dec_ref_known(v_p_u2082_2342_, 3);
v___x_2354_ = lean_apply_4(v_h__2_2344_, v_k_2350_, v_k_2351_, v_v_2352_, v_p_2353_);
return v___x_2354_;
}
}
else
{
lean_dec(v_h__2_2344_);
lean_dec(v_h__1_2343_);
if (lean_obj_tag(v_p_u2082_2342_) == 0)
{
lean_object* v_k_2355_; lean_object* v_v_2356_; lean_object* v_p_2357_; lean_object* v_k_2358_; lean_object* v___x_2359_; 
lean_dec(v_h__4_2346_);
v_k_2355_ = lean_ctor_get(v_p_u2081_2341_, 0);
lean_inc(v_k_2355_);
v_v_2356_ = lean_ctor_get(v_p_u2081_2341_, 1);
lean_inc(v_v_2356_);
v_p_2357_ = lean_ctor_get(v_p_u2081_2341_, 2);
lean_inc_ref(v_p_2357_);
lean_dec_ref_known(v_p_u2081_2341_, 3);
v_k_2358_ = lean_ctor_get(v_p_u2082_2342_, 0);
lean_inc(v_k_2358_);
lean_dec_ref_known(v_p_u2082_2342_, 1);
v___x_2359_ = lean_apply_4(v_h__3_2345_, v_k_2355_, v_v_2356_, v_p_2357_, v_k_2358_);
return v___x_2359_;
}
else
{
lean_object* v_k_2360_; lean_object* v_v_2361_; lean_object* v_p_2362_; lean_object* v_k_2363_; lean_object* v_v_2364_; lean_object* v_p_2365_; lean_object* v___x_2366_; 
lean_dec(v_h__3_2345_);
v_k_2360_ = lean_ctor_get(v_p_u2081_2341_, 0);
lean_inc(v_k_2360_);
v_v_2361_ = lean_ctor_get(v_p_u2081_2341_, 1);
lean_inc(v_v_2361_);
v_p_2362_ = lean_ctor_get(v_p_u2081_2341_, 2);
lean_inc_ref(v_p_2362_);
lean_dec_ref_known(v_p_u2081_2341_, 3);
v_k_2363_ = lean_ctor_get(v_p_u2082_2342_, 0);
lean_inc(v_k_2363_);
v_v_2364_ = lean_ctor_get(v_p_u2082_2342_, 1);
lean_inc(v_v_2364_);
v_p_2365_ = lean_ctor_get(v_p_u2082_2342_, 2);
lean_inc_ref(v_p_2365_);
lean_dec_ref_known(v_p_u2082_2342_, 3);
v___x_2366_ = lean_apply_6(v_h__4_2346_, v_k_2360_, v_v_2361_, v_p_2362_, v_k_2363_, v_v_2364_, v_p_2365_);
return v___x_2366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t v_x_2367_, lean_object* v_h__1_2368_, lean_object* v_h__2_2369_, lean_object* v_h__3_2370_){
_start:
{
switch(v_x_2367_)
{
case 0:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_dec(v_h__2_2369_);
lean_dec(v_h__1_2368_);
v___x_2371_ = lean_box(0);
v___x_2372_ = lean_apply_1(v_h__3_2370_, v___x_2371_);
return v___x_2372_;
}
case 1:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec(v_h__3_2370_);
lean_dec(v_h__2_2369_);
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_apply_1(v_h__1_2368_, v___x_2373_);
return v___x_2374_;
}
default: 
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
lean_dec(v_h__3_2370_);
lean_dec(v_h__1_2368_);
v___x_2375_ = lean_box(0);
v___x_2376_ = lean_apply_1(v_h__2_2369_, v___x_2375_);
return v___x_2376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object* v_x_2377_, lean_object* v_h__1_2378_, lean_object* v_h__2_2379_, lean_object* v_h__3_2380_){
_start:
{
uint8_t v_x_33__boxed_2381_; lean_object* v_res_2382_; 
v_x_33__boxed_2381_ = lean_unbox(v_x_2377_);
v_res_2382_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(v_x_33__boxed_2381_, v_h__1_2378_, v_h__2_2379_, v_h__3_2380_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object* v_motive_2383_, uint8_t v_x_2384_, lean_object* v_h__1_2385_, lean_object* v_h__2_2386_, lean_object* v_h__3_2387_){
_start:
{
switch(v_x_2384_)
{
case 0:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec(v_h__2_2386_);
lean_dec(v_h__1_2385_);
v___x_2388_ = lean_box(0);
v___x_2389_ = lean_apply_1(v_h__3_2387_, v___x_2388_);
return v___x_2389_;
}
case 1:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_dec(v_h__3_2387_);
lean_dec(v_h__2_2386_);
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_apply_1(v_h__1_2385_, v___x_2390_);
return v___x_2391_;
}
default: 
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
lean_dec(v_h__3_2387_);
lean_dec(v_h__1_2385_);
v___x_2392_ = lean_box(0);
v___x_2393_ = lean_apply_1(v_h__2_2386_, v___x_2392_);
return v___x_2393_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object* v_motive_2394_, lean_object* v_x_2395_, lean_object* v_h__1_2396_, lean_object* v_h__2_2397_, lean_object* v_h__3_2398_){
_start:
{
uint8_t v_x_48__boxed_2399_; lean_object* v_res_2400_; 
v_x_48__boxed_2399_ = lean_unbox(v_x_2395_);
v_res_2400_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(v_motive_2394_, v_x_48__boxed_2399_, v_h__1_2396_, v_h__2_2397_, v_h__3_2398_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul_go(lean_object* v_p_u2082_2401_, lean_object* v_p_u2081_2402_, lean_object* v_acc_2403_){
_start:
{
if (lean_obj_tag(v_p_u2081_2402_) == 0)
{
lean_object* v_k_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_k_2404_ = lean_ctor_get(v_p_u2081_2402_, 0);
lean_inc(v_k_2404_);
lean_dec_ref_known(v_p_u2081_2402_, 1);
v___x_2405_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2404_, v_p_u2082_2401_);
lean_dec(v_k_2404_);
v___x_2406_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2403_, v___x_2405_);
return v___x_2406_;
}
else
{
lean_object* v_k_2407_; lean_object* v_v_2408_; lean_object* v_p_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_k_2407_ = lean_ctor_get(v_p_u2081_2402_, 0);
lean_inc(v_k_2407_);
v_v_2408_ = lean_ctor_get(v_p_u2081_2402_, 1);
lean_inc(v_v_2408_);
v_p_2409_ = lean_ctor_get(v_p_u2081_2402_, 2);
lean_inc_ref(v_p_2409_);
lean_dec_ref_known(v_p_u2081_2402_, 3);
lean_inc_ref(v_p_u2082_2401_);
v___x_2410_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2407_, v_v_2408_, v_p_u2082_2401_);
lean_dec(v_k_2407_);
v___x_2411_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2403_, v___x_2410_);
v_p_u2081_2402_ = v_p_2409_;
v_acc_2403_ = v___x_2411_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul(lean_object* v_p_u2081_2413_, lean_object* v_p_u2082_2414_){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2416_ = l_Lean_Grind_CommRing_Poly_mul_go(v_p_u2082_2414_, v_p_u2081_2413_, v___x_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc_go(lean_object* v_p_u2082_2417_, lean_object* v_p_u2081_2418_, lean_object* v_acc_2419_){
_start:
{
if (lean_obj_tag(v_p_u2081_2418_) == 0)
{
lean_object* v_k_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v_k_2420_ = lean_ctor_get(v_p_u2081_2418_, 0);
lean_inc(v_k_2420_);
lean_dec_ref_known(v_p_u2081_2418_, 1);
v___x_2421_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2420_, v_p_u2082_2417_);
lean_dec(v_k_2420_);
v___x_2422_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2419_, v___x_2421_);
return v___x_2422_;
}
else
{
lean_object* v_k_2423_; lean_object* v_v_2424_; lean_object* v_p_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v_k_2423_ = lean_ctor_get(v_p_u2081_2418_, 0);
lean_inc(v_k_2423_);
v_v_2424_ = lean_ctor_get(v_p_u2081_2418_, 1);
lean_inc(v_v_2424_);
v_p_2425_ = lean_ctor_get(v_p_u2081_2418_, 2);
lean_inc_ref(v_p_2425_);
lean_dec_ref_known(v_p_u2081_2418_, 3);
lean_inc_ref(v_p_u2082_2417_);
v___x_2426_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2423_, v_v_2424_, v_p_u2082_2417_);
lean_dec(v_k_2423_);
v___x_2427_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2419_, v___x_2426_);
v_p_u2081_2418_ = v_p_2425_;
v_acc_2419_ = v___x_2427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object* v_p_u2081_2429_, lean_object* v_p_u2082_2430_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2432_ = l_Lean_Grind_CommRing_Poly_mul__nc_go(v_p_u2082_2430_, v_p_u2081_2429_, v___x_2431_);
return v___x_2432_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_pow___closed__0(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow(lean_object* v_p_2435_, lean_object* v_k_2436_){
_start:
{
lean_object* v_zero_2437_; uint8_t v_isZero_2438_; 
v_zero_2437_ = lean_unsigned_to_nat(0u);
v_isZero_2438_ = lean_nat_dec_eq(v_k_2436_, v_zero_2437_);
if (v_isZero_2438_ == 1)
{
lean_object* v___x_2439_; 
lean_dec_ref(v_p_2435_);
v___x_2439_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2439_;
}
else
{
lean_object* v_one_2440_; lean_object* v_n_2441_; uint8_t v___x_2442_; 
v_one_2440_ = lean_unsigned_to_nat(1u);
v_n_2441_ = lean_nat_sub(v_k_2436_, v_one_2440_);
v___x_2442_ = lean_nat_dec_eq(v_n_2441_, v_zero_2437_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
lean_inc_ref(v_p_2435_);
v___x_2443_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2435_, v_n_2441_);
lean_dec(v_n_2441_);
v___x_2444_ = l_Lean_Grind_CommRing_Poly_mul(v_p_2435_, v___x_2443_);
return v___x_2444_;
}
else
{
lean_dec(v_n_2441_);
return v_p_2435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow___boxed(lean_object* v_p_2445_, lean_object* v_k_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2445_, v_k_2446_);
lean_dec(v_k_2446_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc(lean_object* v_p_2448_, lean_object* v_k_2449_){
_start:
{
lean_object* v_zero_2450_; uint8_t v_isZero_2451_; 
v_zero_2450_ = lean_unsigned_to_nat(0u);
v_isZero_2451_ = lean_nat_dec_eq(v_k_2449_, v_zero_2450_);
if (v_isZero_2451_ == 1)
{
lean_object* v___x_2452_; 
lean_dec_ref(v_p_2448_);
v___x_2452_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2452_;
}
else
{
lean_object* v_one_2453_; lean_object* v_n_2454_; uint8_t v___x_2455_; 
v_one_2453_ = lean_unsigned_to_nat(1u);
v_n_2454_ = lean_nat_sub(v_k_2449_, v_one_2453_);
v___x_2455_ = lean_nat_dec_eq(v_n_2454_, v_zero_2450_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
lean_inc_ref(v_p_2448_);
v___x_2456_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2448_, v_n_2454_);
lean_dec(v_n_2454_);
v___x_2457_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2456_, v_p_2448_);
return v___x_2457_;
}
else
{
lean_dec(v_n_2454_);
return v_p_2448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc___boxed(lean_object* v_p_2458_, lean_object* v_k_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2458_, v_k_2459_);
lean_dec(v_k_2459_);
return v_res_2460_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2462_ = lean_int_neg(v___x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object* v_x_2463_){
_start:
{
switch(lean_obj_tag(v_x_2463_))
{
case 0:
{
lean_object* v_k_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
v_k_2464_ = lean_ctor_get(v_x_2463_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_x_2463_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v_x_2463_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_k_2464_);
lean_dec(v_x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_k_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
case 1:
{
lean_object* v_k_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2480_; 
v_k_2472_ = lean_ctor_get(v_x_2463_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_x_2463_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2474_ = v_x_2463_;
v_isShared_2475_ = v_isSharedCheck_2480_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_k_2472_);
lean_dec(v_x_2463_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2480_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2476_ = lean_nat_to_int(v_k_2472_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set_tag(v___x_2474_, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2476_);
v___x_2478_ = v___x_2474_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
case 2:
{
lean_object* v_k_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
v_k_2481_ = lean_ctor_get(v_x_2463_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_x_2463_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v_x_2463_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_k_2481_);
lean_dec(v_x_2463_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
lean_ctor_set_tag(v___x_2483_, 0);
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_k_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
case 3:
{
lean_object* v_i_2489_; lean_object* v___x_2490_; 
v_i_2489_ = lean_ctor_get(v_x_2463_, 0);
lean_inc(v_i_2489_);
lean_dec_ref_known(v_x_2463_, 1);
v___x_2490_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2489_);
return v___x_2490_;
}
case 4:
{
lean_object* v_a_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v_a_2491_ = lean_ctor_get(v_x_2463_, 0);
lean_inc_ref(v_a_2491_);
lean_dec_ref_known(v_x_2463_, 1);
v___x_2492_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2493_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2491_);
v___x_2494_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2492_, v___x_2493_);
return v___x_2494_;
}
case 5:
{
lean_object* v_a_2495_; lean_object* v_b_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v_a_2495_ = lean_ctor_get(v_x_2463_, 0);
lean_inc_ref(v_a_2495_);
v_b_2496_ = lean_ctor_get(v_x_2463_, 1);
lean_inc_ref(v_b_2496_);
lean_dec_ref_known(v_x_2463_, 2);
v___x_2497_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2495_);
v___x_2498_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2496_);
v___x_2499_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2497_, v___x_2498_);
return v___x_2499_;
}
case 6:
{
lean_object* v_a_2500_; lean_object* v_b_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v_a_2500_ = lean_ctor_get(v_x_2463_, 0);
lean_inc_ref(v_a_2500_);
v_b_2501_ = lean_ctor_get(v_x_2463_, 1);
lean_inc_ref(v_b_2501_);
lean_dec_ref_known(v_x_2463_, 2);
v___x_2502_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2500_);
v___x_2503_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2504_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2501_);
v___x_2505_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2503_, v___x_2504_);
v___x_2506_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2502_, v___x_2505_);
return v___x_2506_;
}
case 7:
{
lean_object* v_a_2507_; lean_object* v_b_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_a_2507_ = lean_ctor_get(v_x_2463_, 0);
lean_inc_ref(v_a_2507_);
v_b_2508_ = lean_ctor_get(v_x_2463_, 1);
lean_inc_ref(v_b_2508_);
lean_dec_ref_known(v_x_2463_, 2);
v___x_2509_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2507_);
v___x_2510_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2508_);
v___x_2511_ = l_Lean_Grind_CommRing_Poly_mul(v___x_2509_, v___x_2510_);
return v___x_2511_;
}
default: 
{
lean_object* v_a_2512_; lean_object* v_k_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2545_; 
v_a_2512_ = lean_ctor_get(v_x_2463_, 0);
v_k_2513_ = lean_ctor_get(v_x_2463_, 1);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_x_2463_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2515_ = v_x_2463_;
v_isShared_2516_ = v_isSharedCheck_2545_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_k_2513_);
lean_inc(v_a_2512_);
lean_dec(v_x_2463_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2545_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v_n_2518_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v___x_2521_ = lean_unsigned_to_nat(0u);
v___x_2522_ = lean_nat_dec_eq(v_k_2513_, v___x_2521_);
if (v___x_2522_ == 0)
{
switch(lean_obj_tag(v_a_2512_))
{
case 0:
{
lean_object* v_k_2523_; 
lean_del_object(v___x_2515_);
v_k_2523_ = lean_ctor_get(v_a_2512_, 0);
lean_inc(v_k_2523_);
lean_dec_ref_known(v_a_2512_, 1);
v_n_2518_ = v_k_2523_;
goto v___jp_2517_;
}
case 2:
{
lean_object* v_k_2524_; 
lean_del_object(v___x_2515_);
v_k_2524_ = lean_ctor_get(v_a_2512_, 0);
lean_inc(v_k_2524_);
lean_dec_ref_known(v_a_2512_, 1);
v_n_2518_ = v_k_2524_;
goto v___jp_2517_;
}
case 1:
{
lean_object* v_k_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2534_; 
lean_del_object(v___x_2515_);
v_k_2525_ = lean_ctor_get(v_a_2512_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_a_2512_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2527_ = v_a_2512_;
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_k_2525_);
lean_dec(v_a_2512_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2529_ = lean_nat_to_int(v_k_2525_);
v___x_2530_ = l_Int_pow(v___x_2529_, v_k_2513_);
lean_dec(v_k_2513_);
lean_dec(v___x_2529_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set_tag(v___x_2527_, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2530_);
v___x_2532_ = v___x_2527_;
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
case 3:
{
lean_object* v_i_2535_; lean_object* v___x_2537_; 
v_i_2535_ = lean_ctor_get(v_a_2512_, 0);
lean_inc(v_i_2535_);
lean_dec_ref_known(v_a_2512_, 1);
if (v_isShared_2516_ == 0)
{
lean_ctor_set_tag(v___x_2515_, 0);
lean_ctor_set(v___x_2515_, 0, v_i_2535_);
v___x_2537_ = v___x_2515_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_i_2535_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_k_2513_);
v___x_2537_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2539_);
return v___x_2540_;
}
}
default: 
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_del_object(v___x_2515_);
v___x_2542_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2512_);
v___x_2543_ = l_Lean_Grind_CommRing_Poly_pow(v___x_2542_, v_k_2513_);
lean_dec(v_k_2513_);
return v___x_2543_;
}
}
}
else
{
lean_object* v___x_2544_; 
lean_del_object(v___x_2515_);
lean_dec(v_k_2513_);
lean_dec_ref(v_a_2512_);
v___x_2544_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2544_;
}
v___jp_2517_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = l_Int_pow(v_n_2518_, v_k_2513_);
lean_dec(v_k_2513_);
lean_dec(v_n_2518_);
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
return v___x_2520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf(lean_object* v_m_2546_, lean_object* v_x_2547_){
_start:
{
if (lean_obj_tag(v_m_2546_) == 0)
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_unsigned_to_nat(0u);
return v___x_2548_;
}
else
{
lean_object* v_p_2549_; lean_object* v_m_2550_; lean_object* v_x_2551_; lean_object* v_k_2552_; uint8_t v___x_2553_; 
v_p_2549_ = lean_ctor_get(v_m_2546_, 0);
v_m_2550_ = lean_ctor_get(v_m_2546_, 1);
v_x_2551_ = lean_ctor_get(v_p_2549_, 0);
v_k_2552_ = lean_ctor_get(v_p_2549_, 1);
v___x_2553_ = lean_nat_dec_eq(v_x_2551_, v_x_2547_);
if (v___x_2553_ == 0)
{
v_m_2546_ = v_m_2550_;
goto _start;
}
else
{
lean_inc(v_k_2552_);
return v_k_2552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf___boxed(lean_object* v_m_2555_, lean_object* v_x_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_2555_, v_x_2556_);
lean_dec(v_x_2556_);
lean_dec(v_m_2555_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar(lean_object* v_m_2558_, lean_object* v_x_2559_){
_start:
{
if (lean_obj_tag(v_m_2558_) == 0)
{
return v_m_2558_;
}
else
{
lean_object* v_p_2560_; lean_object* v_m_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2571_; 
v_p_2560_ = lean_ctor_get(v_m_2558_, 0);
v_m_2561_ = lean_ctor_get(v_m_2558_, 1);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_m_2558_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2563_ = v_m_2558_;
v_isShared_2564_ = v_isSharedCheck_2571_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_m_2561_);
lean_inc(v_p_2560_);
lean_dec(v_m_2558_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2571_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v_x_2565_; uint8_t v___x_2566_; 
v_x_2565_ = lean_ctor_get(v_p_2560_, 0);
v___x_2566_ = lean_nat_dec_eq(v_x_2565_, v_x_2559_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2569_; 
v___x_2567_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2561_, v_x_2559_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 1, v___x_2567_);
v___x_2569_ = v___x_2563_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_p_2560_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
else
{
lean_del_object(v___x_2563_);
lean_dec_ref(v_p_2560_);
return v_m_2561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar___boxed(lean_object* v_m_2572_, lean_object* v_x_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2572_, v_x_2573_);
lean_dec(v_x_2573_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27(lean_object* v_c_2575_, lean_object* v_x_2576_, lean_object* v_p_2577_, lean_object* v_acc_2578_){
_start:
{
if (lean_obj_tag(v_p_2577_) == 0)
{
lean_object* v_k_2579_; lean_object* v___x_2580_; 
v_k_2579_ = lean_ctor_get(v_p_2577_, 0);
lean_inc(v_k_2579_);
lean_dec_ref_known(v_p_2577_, 1);
v___x_2580_ = l_Lean_Grind_CommRing_Poly_addConst(v_acc_2578_, v_k_2579_);
lean_dec(v_k_2579_);
return v___x_2580_;
}
else
{
lean_object* v_k_2581_; lean_object* v_v_2582_; lean_object* v_p_2583_; lean_object* v_n_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v_k_2581_ = lean_ctor_get(v_p_2577_, 0);
lean_inc(v_k_2581_);
v_v_2582_ = lean_ctor_get(v_p_2577_, 1);
lean_inc(v_v_2582_);
v_p_2583_ = lean_ctor_get(v_p_2577_, 2);
lean_inc_ref(v_p_2583_);
lean_dec_ref_known(v_p_2577_, 3);
v_n_2587_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_2582_, v_x_2576_);
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_nat_dec_lt(v___x_2588_, v_n_2587_);
if (v___x_2589_ == 0)
{
lean_dec(v_n_2587_);
goto v___jp_2584_;
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2590_ = l_Int_pow(v_c_2575_, v_n_2587_);
lean_dec(v_n_2587_);
v___x_2591_ = lean_int_emod(v_k_2581_, v___x_2590_);
v___x_2592_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2593_ = lean_int_dec_eq(v___x_2591_, v___x_2592_);
lean_dec(v___x_2591_);
if (v___x_2593_ == 0)
{
lean_dec(v___x_2590_);
goto v___jp_2584_;
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = lean_int_ediv(v_k_2581_, v___x_2590_);
lean_dec(v___x_2590_);
lean_dec(v_k_2581_);
v___x_2595_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_v_2582_, v_x_2576_);
v___x_2596_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2594_, v___x_2595_, v_acc_2578_);
v_p_2577_ = v_p_2583_;
v_acc_2578_ = v___x_2596_;
goto _start;
}
}
v___jp_2584_:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_Grind_CommRing_Poly_insert(v_k_2581_, v_v_2582_, v_acc_2578_);
v_p_2577_ = v_p_2583_;
v_acc_2578_ = v___x_2585_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27___boxed(lean_object* v_c_2598_, lean_object* v_x_2599_, lean_object* v_p_2600_, lean_object* v_acc_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2598_, v_x_2599_, v_p_2600_, v_acc_2601_);
lean_dec(v_x_2599_);
lean_dec(v_c_2598_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar(lean_object* v_c_2603_, lean_object* v_x_2604_, lean_object* v_p_2605_){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2607_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2603_, v_x_2604_, v_p_2605_, v___x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar___boxed(lean_object* v_c_2608_, lean_object* v_x_2609_, lean_object* v_p_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_Grind_CommRing_Poly_cancelVar(v_c_2608_, v_x_2609_, v_p_2610_);
lean_dec(v_x_2609_);
lean_dec(v_c_2608_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(lean_object* v_p_2612_, lean_object* v_acc_2613_){
_start:
{
lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2614_ = lean_unsigned_to_nat(1u);
v___x_2615_ = lean_nat_dec_eq(v_acc_2613_, v___x_2614_);
if (v___x_2615_ == 0)
{
if (lean_obj_tag(v_p_2612_) == 0)
{
lean_object* v_k_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_k_2616_ = lean_ctor_get(v_p_2612_, 0);
v___x_2617_ = lean_nat_abs(v_k_2616_);
v___x_2618_ = lean_nat_gcd(v_acc_2613_, v___x_2617_);
lean_dec(v___x_2617_);
lean_dec(v_acc_2613_);
return v___x_2618_;
}
else
{
lean_object* v_k_2619_; lean_object* v_p_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_k_2619_ = lean_ctor_get(v_p_2612_, 0);
v_p_2620_ = lean_ctor_get(v_p_2612_, 2);
v___x_2621_ = lean_nat_abs(v_k_2619_);
v___x_2622_ = lean_nat_gcd(v_acc_2613_, v___x_2621_);
lean_dec(v___x_2621_);
lean_dec(v_acc_2613_);
v_p_2612_ = v_p_2620_;
v_acc_2613_ = v___x_2622_;
goto _start;
}
}
else
{
return v_acc_2613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs_go___boxed(lean_object* v_p_2624_, lean_object* v_acc_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_2624_, v_acc_2625_);
lean_dec_ref(v_p_2624_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs(lean_object* v_x_2627_){
_start:
{
if (lean_obj_tag(v_x_2627_) == 0)
{
lean_object* v_k_2628_; lean_object* v___x_2629_; 
v_k_2628_ = lean_ctor_get(v_x_2627_, 0);
v___x_2629_ = lean_nat_abs(v_k_2628_);
return v___x_2629_;
}
else
{
lean_object* v_k_2630_; lean_object* v_p_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v_k_2630_ = lean_ctor_get(v_x_2627_, 0);
v_p_2631_ = lean_ctor_get(v_x_2627_, 2);
v___x_2632_ = lean_nat_abs(v_k_2630_);
v___x_2633_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_2631_, v___x_2632_);
return v___x_2633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs___boxed(lean_object* v_x_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs(v_x_2634_);
lean_dec_ref(v_x_2634_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst(lean_object* v_p_2636_, lean_object* v_a_2637_){
_start:
{
if (lean_obj_tag(v_p_2636_) == 0)
{
lean_object* v_k_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2646_; 
v_k_2638_ = lean_ctor_get(v_p_2636_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_p_2636_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2640_ = v_p_2636_;
v_isShared_2641_ = v_isSharedCheck_2646_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_k_2638_);
lean_dec(v_p_2636_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2646_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2642_ = lean_int_ediv(v_k_2638_, v_a_2637_);
lean_dec(v_k_2638_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___x_2642_);
v___x_2644_ = v___x_2640_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
else
{
lean_object* v_k_2647_; lean_object* v_v_2648_; lean_object* v_p_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2658_; 
v_k_2647_ = lean_ctor_get(v_p_2636_, 0);
v_v_2648_ = lean_ctor_get(v_p_2636_, 1);
v_p_2649_ = lean_ctor_get(v_p_2636_, 2);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_p_2636_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2651_ = v_p_2636_;
v_isShared_2652_ = v_isSharedCheck_2658_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_p_2649_);
lean_inc(v_v_2648_);
lean_inc(v_k_2647_);
lean_dec(v_p_2636_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2658_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2656_; 
v___x_2653_ = lean_int_ediv(v_k_2647_, v_a_2637_);
lean_dec(v_k_2647_);
v___x_2654_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_2649_, v_a_2637_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 2, v___x_2654_);
lean_ctor_set(v___x_2651_, 0, v___x_2653_);
v___x_2656_ = v___x_2651_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_v_2648_);
lean_ctor_set(v_reuseFailAlloc_2657_, 2, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst___boxed(lean_object* v_p_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_2659_, v_a_2660_);
lean_dec(v_a_2660_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(lean_object* v_x_2662_, lean_object* v_p_2663_, lean_object* v_max_2664_){
_start:
{
if (lean_obj_tag(v_p_2663_) == 0)
{
return v_max_2664_;
}
else
{
lean_object* v_v_2665_; lean_object* v_p_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
v_v_2665_ = lean_ctor_get(v_p_2663_, 1);
v_p_2666_ = lean_ctor_get(v_p_2663_, 2);
v___x_2667_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_2665_, v_x_2662_);
v___x_2668_ = lean_nat_dec_le(v_max_2664_, v___x_2667_);
if (v___x_2668_ == 0)
{
lean_dec(v___x_2667_);
v_p_2663_ = v_p_2666_;
goto _start;
}
else
{
lean_dec(v_max_2664_);
v_p_2663_ = v_p_2666_;
v_max_2664_ = v___x_2667_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf_go___boxed(lean_object* v_x_2671_, lean_object* v_p_2672_, lean_object* v_max_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_2671_, v_p_2672_, v_max_2673_);
lean_dec_ref(v_p_2672_);
lean_dec(v_x_2671_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf(lean_object* v_p_2675_, lean_object* v_x_2676_){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = lean_unsigned_to_nat(0u);
v___x_2678_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_2676_, v_p_2675_, v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf___boxed(lean_object* v_p_2679_, lean_object* v_x_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_2679_, v_x_2680_);
lean_dec(v_x_2680_);
lean_dec_ref(v_p_2679_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(lean_object* v_x_2682_, lean_object* v_h__1_2683_, lean_object* v_h__2_2684_, lean_object* v_h__3_2685_, lean_object* v_h__4_2686_, lean_object* v_h__5_2687_, lean_object* v_h__6_2688_, lean_object* v_h__7_2689_, lean_object* v_h__8_2690_, lean_object* v_h__9_2691_){
_start:
{
switch(lean_obj_tag(v_x_2682_))
{
case 0:
{
lean_object* v_k_2692_; lean_object* v___x_2693_; 
lean_dec(v_h__9_2691_);
lean_dec(v_h__8_2690_);
lean_dec(v_h__7_2689_);
lean_dec(v_h__6_2688_);
lean_dec(v_h__5_2687_);
lean_dec(v_h__4_2686_);
lean_dec(v_h__3_2685_);
lean_dec(v_h__2_2684_);
v_k_2692_ = lean_ctor_get(v_x_2682_, 0);
lean_inc(v_k_2692_);
lean_dec_ref_known(v_x_2682_, 1);
v___x_2693_ = lean_apply_1(v_h__1_2683_, v_k_2692_);
return v___x_2693_;
}
case 1:
{
lean_object* v_k_2694_; lean_object* v___x_2695_; 
lean_dec(v_h__9_2691_);
lean_dec(v_h__8_2690_);
lean_dec(v_h__7_2689_);
lean_dec(v_h__6_2688_);
lean_dec(v_h__5_2687_);
lean_dec(v_h__4_2686_);
lean_dec(v_h__2_2684_);
lean_dec(v_h__1_2683_);
v_k_2694_ = lean_ctor_get(v_x_2682_, 0);
lean_inc(v_k_2694_);
lean_dec_ref_known(v_x_2682_, 1);
v___x_2695_ = lean_apply_1(v_h__3_2685_, v_k_2694_);
return v___x_2695_;
}
case 2:
{
lean_object* v_k_2696_; lean_object* v___x_2697_; 
lean_dec(v_h__9_2691_);
lean_dec(v_h__8_2690_);
lean_dec(v_h__7_2689_);
lean_dec(v_h__6_2688_);
lean_dec(v_h__5_2687_);
lean_dec(v_h__4_2686_);
lean_dec(v_h__3_2685_);
lean_dec(v_h__1_2683_);
v_k_2696_ = lean_ctor_get(v_x_2682_, 0);
lean_inc(v_k_2696_);
lean_dec_ref_known(v_x_2682_, 1);
v___x_2697_ = lean_apply_1(v_h__2_2684_, v_k_2696_);
return v___x_2697_;
}
case 3:
{
lean_object* v_i_2698_; lean_object* v___x_2699_; 
lean_dec(v_h__9_2691_);
lean_dec(v_h__8_2690_);
lean_dec(v_h__7_2689_);
lean_dec(v_h__6_2688_);
lean_dec(v_h__5_2687_);
lean_dec(v_h__3_2685_);
lean_dec(v_h__2_2684_);
lean_dec(v_h__1_2683_);
v_i_2698_ = lean_ctor_get(v_x_2682_, 0);
lean_inc(v_i_2698_);
lean_dec_ref_known(v_x_2682_, 1);
v___x_2699_ = lean_apply_1(v_h__4_2686_, v_i_2698_);
return v___x_2699_;
}
case 4:
{
lean_object* v_a_2700_; lean_object* v___x_2701_; 
lean_dec(v_h__9_2691_);
lean_dec(v_h__8_2690_);
lean_dec(v_h__6_2688_);
lean_dec(v_h__5_2687_);
lean_dec(v_h__4_2686_);
lean_dec(v_h__3_2685_);
lean_dec(v_h__2_2684_);
lean_dec(v_h__1_2683_);
v_a_2700_ = lean_ctor_get(v_x_2682_, 0);
lean_inc_ref(v_a_2700_);
lean_dec_ref_known(v_x_2682_, 1);
v___x_2701_ = lean_apply_1(v_h__7_2689_, v_a_2700_);
return v___x_2701_;
}
case 5:
{
lean_object* v_a_2702_; lean_object* v_b_2703_; lean_object* v___x_2704_; 
lean_dec(v_h__9_2691_);
lean_dec(v_h__8_2690_);
lean_dec(v_h__7_2689_);
lean_dec(v_h__6_2688_);
lean_dec(v_h__4_2686_);
lean_dec(v_h__3_2685_);
lean_dec(v_h__2_2684_);
lean_dec(v_h__1_2683_);
v_a_2702_ = lean_ctor_get(v_x_2682_, 0);
lean_inc_ref(v_a_2702_);
v_b_2703_ = lean_ctor_get(v_x_2682_, 1);
lean_inc_ref(v_b_2703_);
lean_dec_ref_known(v_x_2682_, 2);
v___x_2704_ = lean_apply_2(v_h__5_2687_, v_a_2702_, v_b_2703_);
return v___x_2704_;
}
case 6:
{
lean_object* v_a_2705_; lean_object* v_b_2706_; lean_object* v___x_2707_; 
lean_dec(v_h__9_2691_);
lean_dec(v_h__7_2689_);
lean_dec(v_h__6_2688_);
lean_dec(v_h__5_2687_);
lean_dec(v_h__4_2686_);
lean_dec(v_h__3_2685_);
lean_dec(v_h__2_2684_);
lean_dec(v_h__1_2683_);
v_a_2705_ = lean_ctor_get(v_x_2682_, 0);
lean_inc_ref(v_a_2705_);
v_b_2706_ = lean_ctor_get(v_x_2682_, 1);
lean_inc_ref(v_b_2706_);
lean_dec_ref_known(v_x_2682_, 2);
v___x_2707_ = lean_apply_2(v_h__8_2690_, v_a_2705_, v_b_2706_);
return v___x_2707_;
}
case 7:
{
lean_object* v_a_2708_; lean_object* v_b_2709_; lean_object* v___x_2710_; 
lean_dec(v_h__9_2691_);
lean_dec(v_h__8_2690_);
lean_dec(v_h__7_2689_);
lean_dec(v_h__5_2687_);
lean_dec(v_h__4_2686_);
lean_dec(v_h__3_2685_);
lean_dec(v_h__2_2684_);
lean_dec(v_h__1_2683_);
v_a_2708_ = lean_ctor_get(v_x_2682_, 0);
lean_inc_ref(v_a_2708_);
v_b_2709_ = lean_ctor_get(v_x_2682_, 1);
lean_inc_ref(v_b_2709_);
lean_dec_ref_known(v_x_2682_, 2);
v___x_2710_ = lean_apply_2(v_h__6_2688_, v_a_2708_, v_b_2709_);
return v___x_2710_;
}
default: 
{
lean_object* v_a_2711_; lean_object* v_k_2712_; lean_object* v___x_2713_; 
lean_dec(v_h__8_2690_);
lean_dec(v_h__7_2689_);
lean_dec(v_h__6_2688_);
lean_dec(v_h__5_2687_);
lean_dec(v_h__4_2686_);
lean_dec(v_h__3_2685_);
lean_dec(v_h__2_2684_);
lean_dec(v_h__1_2683_);
v_a_2711_ = lean_ctor_get(v_x_2682_, 0);
lean_inc_ref(v_a_2711_);
v_k_2712_ = lean_ctor_get(v_x_2682_, 1);
lean_inc(v_k_2712_);
lean_dec_ref_known(v_x_2682_, 2);
v___x_2713_ = lean_apply_2(v_h__9_2691_, v_a_2711_, v_k_2712_);
return v___x_2713_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter(lean_object* v_motive_2714_, lean_object* v_x_2715_, lean_object* v_h__1_2716_, lean_object* v_h__2_2717_, lean_object* v_h__3_2718_, lean_object* v_h__4_2719_, lean_object* v_h__5_2720_, lean_object* v_h__6_2721_, lean_object* v_h__7_2722_, lean_object* v_h__8_2723_, lean_object* v_h__9_2724_){
_start:
{
switch(lean_obj_tag(v_x_2715_))
{
case 0:
{
lean_object* v_k_2725_; lean_object* v___x_2726_; 
lean_dec(v_h__9_2724_);
lean_dec(v_h__8_2723_);
lean_dec(v_h__7_2722_);
lean_dec(v_h__6_2721_);
lean_dec(v_h__5_2720_);
lean_dec(v_h__4_2719_);
lean_dec(v_h__3_2718_);
lean_dec(v_h__2_2717_);
v_k_2725_ = lean_ctor_get(v_x_2715_, 0);
lean_inc(v_k_2725_);
lean_dec_ref_known(v_x_2715_, 1);
v___x_2726_ = lean_apply_1(v_h__1_2716_, v_k_2725_);
return v___x_2726_;
}
case 1:
{
lean_object* v_k_2727_; lean_object* v___x_2728_; 
lean_dec(v_h__9_2724_);
lean_dec(v_h__8_2723_);
lean_dec(v_h__7_2722_);
lean_dec(v_h__6_2721_);
lean_dec(v_h__5_2720_);
lean_dec(v_h__4_2719_);
lean_dec(v_h__2_2717_);
lean_dec(v_h__1_2716_);
v_k_2727_ = lean_ctor_get(v_x_2715_, 0);
lean_inc(v_k_2727_);
lean_dec_ref_known(v_x_2715_, 1);
v___x_2728_ = lean_apply_1(v_h__3_2718_, v_k_2727_);
return v___x_2728_;
}
case 2:
{
lean_object* v_k_2729_; lean_object* v___x_2730_; 
lean_dec(v_h__9_2724_);
lean_dec(v_h__8_2723_);
lean_dec(v_h__7_2722_);
lean_dec(v_h__6_2721_);
lean_dec(v_h__5_2720_);
lean_dec(v_h__4_2719_);
lean_dec(v_h__3_2718_);
lean_dec(v_h__1_2716_);
v_k_2729_ = lean_ctor_get(v_x_2715_, 0);
lean_inc(v_k_2729_);
lean_dec_ref_known(v_x_2715_, 1);
v___x_2730_ = lean_apply_1(v_h__2_2717_, v_k_2729_);
return v___x_2730_;
}
case 3:
{
lean_object* v_i_2731_; lean_object* v___x_2732_; 
lean_dec(v_h__9_2724_);
lean_dec(v_h__8_2723_);
lean_dec(v_h__7_2722_);
lean_dec(v_h__6_2721_);
lean_dec(v_h__5_2720_);
lean_dec(v_h__3_2718_);
lean_dec(v_h__2_2717_);
lean_dec(v_h__1_2716_);
v_i_2731_ = lean_ctor_get(v_x_2715_, 0);
lean_inc(v_i_2731_);
lean_dec_ref_known(v_x_2715_, 1);
v___x_2732_ = lean_apply_1(v_h__4_2719_, v_i_2731_);
return v___x_2732_;
}
case 4:
{
lean_object* v_a_2733_; lean_object* v___x_2734_; 
lean_dec(v_h__9_2724_);
lean_dec(v_h__8_2723_);
lean_dec(v_h__6_2721_);
lean_dec(v_h__5_2720_);
lean_dec(v_h__4_2719_);
lean_dec(v_h__3_2718_);
lean_dec(v_h__2_2717_);
lean_dec(v_h__1_2716_);
v_a_2733_ = lean_ctor_get(v_x_2715_, 0);
lean_inc_ref(v_a_2733_);
lean_dec_ref_known(v_x_2715_, 1);
v___x_2734_ = lean_apply_1(v_h__7_2722_, v_a_2733_);
return v___x_2734_;
}
case 5:
{
lean_object* v_a_2735_; lean_object* v_b_2736_; lean_object* v___x_2737_; 
lean_dec(v_h__9_2724_);
lean_dec(v_h__8_2723_);
lean_dec(v_h__7_2722_);
lean_dec(v_h__6_2721_);
lean_dec(v_h__4_2719_);
lean_dec(v_h__3_2718_);
lean_dec(v_h__2_2717_);
lean_dec(v_h__1_2716_);
v_a_2735_ = lean_ctor_get(v_x_2715_, 0);
lean_inc_ref(v_a_2735_);
v_b_2736_ = lean_ctor_get(v_x_2715_, 1);
lean_inc_ref(v_b_2736_);
lean_dec_ref_known(v_x_2715_, 2);
v___x_2737_ = lean_apply_2(v_h__5_2720_, v_a_2735_, v_b_2736_);
return v___x_2737_;
}
case 6:
{
lean_object* v_a_2738_; lean_object* v_b_2739_; lean_object* v___x_2740_; 
lean_dec(v_h__9_2724_);
lean_dec(v_h__7_2722_);
lean_dec(v_h__6_2721_);
lean_dec(v_h__5_2720_);
lean_dec(v_h__4_2719_);
lean_dec(v_h__3_2718_);
lean_dec(v_h__2_2717_);
lean_dec(v_h__1_2716_);
v_a_2738_ = lean_ctor_get(v_x_2715_, 0);
lean_inc_ref(v_a_2738_);
v_b_2739_ = lean_ctor_get(v_x_2715_, 1);
lean_inc_ref(v_b_2739_);
lean_dec_ref_known(v_x_2715_, 2);
v___x_2740_ = lean_apply_2(v_h__8_2723_, v_a_2738_, v_b_2739_);
return v___x_2740_;
}
case 7:
{
lean_object* v_a_2741_; lean_object* v_b_2742_; lean_object* v___x_2743_; 
lean_dec(v_h__9_2724_);
lean_dec(v_h__8_2723_);
lean_dec(v_h__7_2722_);
lean_dec(v_h__5_2720_);
lean_dec(v_h__4_2719_);
lean_dec(v_h__3_2718_);
lean_dec(v_h__2_2717_);
lean_dec(v_h__1_2716_);
v_a_2741_ = lean_ctor_get(v_x_2715_, 0);
lean_inc_ref(v_a_2741_);
v_b_2742_ = lean_ctor_get(v_x_2715_, 1);
lean_inc_ref(v_b_2742_);
lean_dec_ref_known(v_x_2715_, 2);
v___x_2743_ = lean_apply_2(v_h__6_2721_, v_a_2741_, v_b_2742_);
return v___x_2743_;
}
default: 
{
lean_object* v_a_2744_; lean_object* v_k_2745_; lean_object* v___x_2746_; 
lean_dec(v_h__8_2723_);
lean_dec(v_h__7_2722_);
lean_dec(v_h__6_2721_);
lean_dec(v_h__5_2720_);
lean_dec(v_h__4_2719_);
lean_dec(v_h__3_2718_);
lean_dec(v_h__2_2717_);
lean_dec(v_h__1_2716_);
v_a_2744_ = lean_ctor_get(v_x_2715_, 0);
lean_inc_ref(v_a_2744_);
v_k_2745_ = lean_ctor_get(v_x_2715_, 1);
lean_inc(v_k_2745_);
lean_dec_ref_known(v_x_2715_, 2);
v___x_2746_ = lean_apply_2(v_h__9_2724_, v_a_2744_, v_k_2745_);
return v___x_2746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter___redArg(lean_object* v_a_2747_, lean_object* v_h__1_2748_, lean_object* v_h__2_2749_, lean_object* v_h__3_2750_, lean_object* v_h__4_2751_, lean_object* v_h__5_2752_){
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter(lean_object* v_motive_2762_, lean_object* v_a_2763_, lean_object* v_h__1_2764_, lean_object* v_h__2_2765_, lean_object* v_h__3_2766_, lean_object* v_h__4_2767_, lean_object* v_h__5_2768_){
_start:
{
switch(lean_obj_tag(v_a_2763_))
{
case 0:
{
lean_object* v_k_2769_; lean_object* v___x_2770_; 
lean_dec(v_h__5_2768_);
lean_dec(v_h__4_2767_);
lean_dec(v_h__3_2766_);
lean_dec(v_h__2_2765_);
v_k_2769_ = lean_ctor_get(v_a_2763_, 0);
lean_inc(v_k_2769_);
lean_dec_ref_known(v_a_2763_, 1);
v___x_2770_ = lean_apply_1(v_h__1_2764_, v_k_2769_);
return v___x_2770_;
}
case 2:
{
lean_object* v_k_2771_; lean_object* v___x_2772_; 
lean_dec(v_h__5_2768_);
lean_dec(v_h__4_2767_);
lean_dec(v_h__3_2766_);
lean_dec(v_h__1_2764_);
v_k_2771_ = lean_ctor_get(v_a_2763_, 0);
lean_inc(v_k_2771_);
lean_dec_ref_known(v_a_2763_, 1);
v___x_2772_ = lean_apply_1(v_h__2_2765_, v_k_2771_);
return v___x_2772_;
}
case 1:
{
lean_object* v_k_2773_; lean_object* v___x_2774_; 
lean_dec(v_h__5_2768_);
lean_dec(v_h__4_2767_);
lean_dec(v_h__2_2765_);
lean_dec(v_h__1_2764_);
v_k_2773_ = lean_ctor_get(v_a_2763_, 0);
lean_inc(v_k_2773_);
lean_dec_ref_known(v_a_2763_, 1);
v___x_2774_ = lean_apply_1(v_h__3_2766_, v_k_2773_);
return v___x_2774_;
}
case 3:
{
lean_object* v_i_2775_; lean_object* v___x_2776_; 
lean_dec(v_h__5_2768_);
lean_dec(v_h__3_2766_);
lean_dec(v_h__2_2765_);
lean_dec(v_h__1_2764_);
v_i_2775_ = lean_ctor_get(v_a_2763_, 0);
lean_inc(v_i_2775_);
lean_dec_ref_known(v_a_2763_, 1);
v___x_2776_ = lean_apply_1(v_h__4_2767_, v_i_2775_);
return v___x_2776_;
}
default: 
{
lean_object* v___x_2777_; 
lean_dec(v_h__4_2767_);
lean_dec(v_h__3_2766_);
lean_dec(v_h__2_2765_);
lean_dec(v_h__1_2764_);
v___x_2777_ = lean_apply_5(v_h__5_2768_, v_a_2763_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly__nc(lean_object* v_x_2778_){
_start:
{
switch(lean_obj_tag(v_x_2778_))
{
case 0:
{
lean_object* v_k_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
v_k_2779_ = lean_ctor_get(v_x_2778_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_x_2778_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v_x_2778_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_k_2779_);
lean_dec(v_x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_k_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
case 1:
{
lean_object* v_k_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2795_; 
v_k_2787_ = lean_ctor_get(v_x_2778_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_x_2778_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2789_ = v_x_2778_;
v_isShared_2790_ = v_isSharedCheck_2795_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_k_2787_);
lean_dec(v_x_2778_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2795_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2791_ = lean_nat_to_int(v_k_2787_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set_tag(v___x_2789_, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2791_);
v___x_2793_ = v___x_2789_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
case 2:
{
lean_object* v_k_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
v_k_2796_ = lean_ctor_get(v_x_2778_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_x_2778_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v_x_2778_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_k_2796_);
lean_dec(v_x_2778_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set_tag(v___x_2798_, 0);
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_k_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
case 3:
{
lean_object* v_i_2804_; lean_object* v___x_2805_; 
v_i_2804_ = lean_ctor_get(v_x_2778_, 0);
lean_inc(v_i_2804_);
lean_dec_ref_known(v_x_2778_, 1);
v___x_2805_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2804_);
return v___x_2805_;
}
case 4:
{
lean_object* v_a_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v_a_2806_ = lean_ctor_get(v_x_2778_, 0);
lean_inc_ref(v_a_2806_);
lean_dec_ref_known(v_x_2778_, 1);
v___x_2807_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2808_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2806_);
v___x_2809_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2807_, v___x_2808_);
return v___x_2809_;
}
case 5:
{
lean_object* v_a_2810_; lean_object* v_b_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_a_2810_ = lean_ctor_get(v_x_2778_, 0);
lean_inc_ref(v_a_2810_);
v_b_2811_ = lean_ctor_get(v_x_2778_, 1);
lean_inc_ref(v_b_2811_);
lean_dec_ref_known(v_x_2778_, 2);
v___x_2812_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2810_);
v___x_2813_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2811_);
v___x_2814_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2812_, v___x_2813_);
return v___x_2814_;
}
case 6:
{
lean_object* v_a_2815_; lean_object* v_b_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v_a_2815_ = lean_ctor_get(v_x_2778_, 0);
lean_inc_ref(v_a_2815_);
v_b_2816_ = lean_ctor_get(v_x_2778_, 1);
lean_inc_ref(v_b_2816_);
lean_dec_ref_known(v_x_2778_, 2);
v___x_2817_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2815_);
v___x_2818_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2819_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2816_);
v___x_2820_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2818_, v___x_2819_);
v___x_2821_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2817_, v___x_2820_);
return v___x_2821_;
}
case 7:
{
lean_object* v_a_2822_; lean_object* v_b_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_a_2822_ = lean_ctor_get(v_x_2778_, 0);
lean_inc_ref(v_a_2822_);
v_b_2823_ = lean_ctor_get(v_x_2778_, 1);
lean_inc_ref(v_b_2823_);
lean_dec_ref_known(v_x_2778_, 2);
v___x_2824_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2822_);
v___x_2825_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2823_);
v___x_2826_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2824_, v___x_2825_);
return v___x_2826_;
}
default: 
{
lean_object* v_a_2827_; lean_object* v_k_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2860_; 
v_a_2827_ = lean_ctor_get(v_x_2778_, 0);
v_k_2828_ = lean_ctor_get(v_x_2778_, 1);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_x_2778_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2830_ = v_x_2778_;
v_isShared_2831_ = v_isSharedCheck_2860_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_k_2828_);
lean_inc(v_a_2827_);
lean_dec(v_x_2778_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2860_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v_n_2833_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2836_ = lean_unsigned_to_nat(0u);
v___x_2837_ = lean_nat_dec_eq(v_k_2828_, v___x_2836_);
if (v___x_2837_ == 0)
{
switch(lean_obj_tag(v_a_2827_))
{
case 0:
{
lean_object* v_k_2838_; 
lean_del_object(v___x_2830_);
v_k_2838_ = lean_ctor_get(v_a_2827_, 0);
lean_inc(v_k_2838_);
lean_dec_ref_known(v_a_2827_, 1);
v_n_2833_ = v_k_2838_;
goto v___jp_2832_;
}
case 2:
{
lean_object* v_k_2839_; 
lean_del_object(v___x_2830_);
v_k_2839_ = lean_ctor_get(v_a_2827_, 0);
lean_inc(v_k_2839_);
lean_dec_ref_known(v_a_2827_, 1);
v_n_2833_ = v_k_2839_;
goto v___jp_2832_;
}
case 1:
{
lean_object* v_k_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2849_; 
lean_del_object(v___x_2830_);
v_k_2840_ = lean_ctor_get(v_a_2827_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_a_2827_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2842_ = v_a_2827_;
v_isShared_2843_ = v_isSharedCheck_2849_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_k_2840_);
lean_dec(v_a_2827_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2849_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2847_; 
v___x_2844_ = lean_nat_to_int(v_k_2840_);
v___x_2845_ = l_Int_pow(v___x_2844_, v_k_2828_);
lean_dec(v_k_2828_);
lean_dec(v___x_2844_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set_tag(v___x_2842_, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2845_);
v___x_2847_ = v___x_2842_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
case 3:
{
lean_object* v_i_2850_; lean_object* v___x_2852_; 
v_i_2850_ = lean_ctor_get(v_a_2827_, 0);
lean_inc(v_i_2850_);
lean_dec_ref_known(v_a_2827_, 1);
if (v_isShared_2831_ == 0)
{
lean_ctor_set_tag(v___x_2830_, 0);
lean_ctor_set(v___x_2830_, 0, v_i_2850_);
v___x_2852_ = v___x_2830_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_i_2850_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_k_2828_);
v___x_2852_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2853_ = lean_box(0);
v___x_2854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2852_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2854_);
return v___x_2855_;
}
}
default: 
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
lean_del_object(v___x_2830_);
v___x_2857_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2827_);
v___x_2858_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_2857_, v_k_2828_);
lean_dec(v_k_2828_);
return v___x_2858_;
}
}
}
else
{
lean_object* v___x_2859_; 
lean_del_object(v___x_2830_);
lean_dec(v_k_2828_);
lean_dec_ref(v_a_2827_);
v___x_2859_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2859_;
}
v___jp_2832_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = l_Int_pow(v_n_2833_, v_k_2828_);
lean_dec(v_k_2828_);
lean_dec(v_n_2833_);
v___x_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
return v___x_2835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_normEq0(lean_object* v_p_2861_, lean_object* v_c_2862_){
_start:
{
if (lean_obj_tag(v_p_2861_) == 0)
{
lean_object* v_k_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v_k_2863_ = lean_ctor_get(v_p_2861_, 0);
v___x_2864_ = lean_nat_to_int(v_c_2862_);
v___x_2865_ = lean_int_emod(v_k_2863_, v___x_2864_);
lean_dec(v___x_2864_);
v___x_2866_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2867_ = lean_int_dec_eq(v___x_2865_, v___x_2866_);
lean_dec(v___x_2865_);
if (v___x_2867_ == 0)
{
return v_p_2861_;
}
else
{
lean_object* v___x_2868_; 
lean_dec_ref_known(v_p_2861_, 1);
v___x_2868_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2868_;
}
}
else
{
lean_object* v_k_2869_; lean_object* v_v_2870_; lean_object* v_p_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2884_; 
v_k_2869_ = lean_ctor_get(v_p_2861_, 0);
v_v_2870_ = lean_ctor_get(v_p_2861_, 1);
v_p_2871_ = lean_ctor_get(v_p_2861_, 2);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_p_2861_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2873_ = v_p_2861_;
v_isShared_2874_ = v_isSharedCheck_2884_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_p_2871_);
lean_inc(v_v_2870_);
lean_inc(v_k_2869_);
lean_dec(v_p_2861_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2884_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; 
lean_inc(v_c_2862_);
v___x_2875_ = lean_nat_to_int(v_c_2862_);
v___x_2876_ = lean_int_emod(v_k_2869_, v___x_2875_);
lean_dec(v___x_2875_);
v___x_2877_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2878_ = lean_int_dec_eq(v___x_2876_, v___x_2877_);
lean_dec(v___x_2876_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2879_ = l_Lean_Grind_CommRing_Poly_normEq0(v_p_2871_, v_c_2862_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 2, v___x_2879_);
v___x_2881_ = v___x_2873_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_k_2869_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_v_2870_);
lean_ctor_set(v_reuseFailAlloc_2882_, 2, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
else
{
lean_del_object(v___x_2873_);
lean_dec(v_v_2870_);
lean_dec(v_k_2869_);
v_p_2861_ = v_p_2871_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object* v_p_2885_, lean_object* v_k_2886_, lean_object* v_c_2887_){
_start:
{
if (lean_obj_tag(v_p_2885_) == 0)
{
lean_object* v_k_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2898_; 
v_k_2888_ = lean_ctor_get(v_p_2885_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_p_2885_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2890_ = v_p_2885_;
v_isShared_2891_ = v_isSharedCheck_2898_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_k_2888_);
lean_dec(v_p_2885_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2898_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2892_ = lean_int_add(v_k_2888_, v_k_2886_);
lean_dec(v_k_2888_);
v___x_2893_ = lean_nat_to_int(v_c_2887_);
v___x_2894_ = lean_int_emod(v___x_2892_, v___x_2893_);
lean_dec(v___x_2893_);
lean_dec(v___x_2892_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2894_);
v___x_2896_ = v___x_2890_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
else
{
lean_object* v_k_2899_; lean_object* v_v_2900_; lean_object* v_p_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2909_; 
v_k_2899_ = lean_ctor_get(v_p_2885_, 0);
v_v_2900_ = lean_ctor_get(v_p_2885_, 1);
v_p_2901_ = lean_ctor_get(v_p_2885_, 2);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_p_2885_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2903_ = v_p_2885_;
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_p_2901_);
lean_inc(v_v_2900_);
lean_inc(v_k_2899_);
lean_dec(v_p_2885_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2905_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2901_, v_k_2886_, v_c_2887_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 2, v___x_2905_);
v___x_2907_ = v___x_2903_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_k_2899_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_v_2900_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC___boxed(lean_object* v_p_2910_, lean_object* v_k_2911_, lean_object* v_c_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2910_, v_k_2911_, v_c_2912_);
lean_dec(v_k_2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC_go(lean_object* v_m_2914_, lean_object* v_c_2915_, lean_object* v_k_2916_, lean_object* v_a_2917_){
_start:
{
if (lean_obj_tag(v_a_2917_) == 0)
{
lean_object* v___x_2918_; 
lean_dec(v_c_2915_);
v___x_2918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2918_, 0, v_k_2916_);
lean_ctor_set(v___x_2918_, 1, v_m_2914_);
lean_ctor_set(v___x_2918_, 2, v_a_2917_);
return v___x_2918_;
}
else
{
lean_object* v_k_2919_; lean_object* v_v_2920_; lean_object* v_p_2921_; uint8_t v___x_2922_; 
v_k_2919_ = lean_ctor_get(v_a_2917_, 0);
v_v_2920_ = lean_ctor_get(v_a_2917_, 1);
v_p_2921_ = lean_ctor_get(v_a_2917_, 2);
v___x_2922_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2914_, v_v_2920_);
switch(v___x_2922_)
{
case 0:
{
lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2930_; 
lean_inc_ref(v_p_2921_);
lean_inc(v_v_2920_);
lean_inc(v_k_2919_);
v_isSharedCheck_2930_ = !lean_is_exclusive(v_a_2917_);
if (v_isSharedCheck_2930_ == 0)
{
lean_object* v_unused_2931_; lean_object* v_unused_2932_; lean_object* v_unused_2933_; 
v_unused_2931_ = lean_ctor_get(v_a_2917_, 2);
lean_dec(v_unused_2931_);
v_unused_2932_ = lean_ctor_get(v_a_2917_, 1);
lean_dec(v_unused_2932_);
v_unused_2933_ = lean_ctor_get(v_a_2917_, 0);
lean_dec(v_unused_2933_);
v___x_2924_ = v_a_2917_;
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
else
{
lean_dec(v_a_2917_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2926_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_2914_, v_c_2915_, v_k_2916_, v_p_2921_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 2, v___x_2926_);
v___x_2928_ = v___x_2924_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_k_2919_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_v_2920_);
lean_ctor_set(v_reuseFailAlloc_2929_, 2, v___x_2926_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
case 1:
{
lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2945_; 
lean_inc_ref(v_p_2921_);
lean_inc(v_k_2919_);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_a_2917_);
if (v_isSharedCheck_2945_ == 0)
{
lean_object* v_unused_2946_; lean_object* v_unused_2947_; lean_object* v_unused_2948_; 
v_unused_2946_ = lean_ctor_get(v_a_2917_, 2);
lean_dec(v_unused_2946_);
v_unused_2947_ = lean_ctor_get(v_a_2917_, 1);
lean_dec(v_unused_2947_);
v_unused_2948_ = lean_ctor_get(v_a_2917_, 0);
lean_dec(v_unused_2948_);
v___x_2935_ = v_a_2917_;
v_isShared_2936_ = v_isSharedCheck_2945_;
goto v_resetjp_2934_;
}
else
{
lean_dec(v_a_2917_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2945_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v_k_x27_x27_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2937_ = lean_int_add(v_k_2916_, v_k_2919_);
lean_dec(v_k_2919_);
lean_dec(v_k_2916_);
v___x_2938_ = lean_nat_to_int(v_c_2915_);
v_k_x27_x27_2939_ = lean_int_emod(v___x_2937_, v___x_2938_);
lean_dec(v___x_2938_);
lean_dec(v___x_2937_);
v___x_2940_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2941_ = lean_int_dec_eq(v_k_x27_x27_2939_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2943_; 
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v_m_2914_);
lean_ctor_set(v___x_2935_, 0, v_k_x27_x27_2939_);
v___x_2943_ = v___x_2935_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_k_x27_x27_2939_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_m_2914_);
lean_ctor_set(v_reuseFailAlloc_2944_, 2, v_p_2921_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
else
{
lean_dec(v_k_x27_x27_2939_);
lean_del_object(v___x_2935_);
lean_dec(v_m_2914_);
return v_p_2921_;
}
}
}
default: 
{
lean_object* v___x_2949_; 
lean_dec(v_c_2915_);
v___x_2949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2949_, 0, v_k_2916_);
lean_ctor_set(v___x_2949_, 1, v_m_2914_);
lean_ctor_set(v___x_2949_, 2, v_a_2917_);
return v___x_2949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC(lean_object* v_k_2950_, lean_object* v_m_2951_, lean_object* v_p_2952_, lean_object* v_c_2953_){
_start:
{
lean_object* v___x_2954_; lean_object* v_k_2955_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
lean_inc(v_c_2953_);
v___x_2954_ = lean_nat_to_int(v_c_2953_);
v_k_2955_ = lean_int_emod(v_k_2950_, v___x_2954_);
lean_dec(v___x_2954_);
v___x_2956_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2957_ = lean_int_dec_eq(v_k_2955_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_2951_, v_c_2953_, v_k_2955_, v_p_2952_);
return v___x_2958_;
}
else
{
lean_dec(v_k_2955_);
lean_dec(v_c_2953_);
lean_dec(v_m_2951_);
return v_p_2952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC___boxed(lean_object* v_k_2959_, lean_object* v_m_2960_, lean_object* v_p_2961_, lean_object* v_c_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_Grind_CommRing_Poly_insertC(v_k_2959_, v_m_2960_, v_p_2961_, v_c_2962_);
lean_dec(v_k_2959_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go(lean_object* v_k_2964_, lean_object* v_c_2965_, lean_object* v_a_2966_){
_start:
{
if (lean_obj_tag(v_a_2966_) == 0)
{
lean_object* v_k_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2977_; 
v_k_2967_ = lean_ctor_get(v_a_2966_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_a_2966_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2969_ = v_a_2966_;
v_isShared_2970_ = v_isSharedCheck_2977_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_k_2967_);
lean_dec(v_a_2966_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2977_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2971_ = lean_int_mul(v_k_2964_, v_k_2967_);
lean_dec(v_k_2967_);
v___x_2972_ = lean_nat_to_int(v_c_2965_);
v___x_2973_ = lean_int_emod(v___x_2971_, v___x_2972_);
lean_dec(v___x_2972_);
lean_dec(v___x_2971_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2973_);
v___x_2975_ = v___x_2969_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
else
{
lean_object* v_k_2978_; lean_object* v_v_2979_; lean_object* v_p_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2994_; 
v_k_2978_ = lean_ctor_get(v_a_2966_, 0);
v_v_2979_ = lean_ctor_get(v_a_2966_, 1);
v_p_2980_ = lean_ctor_get(v_a_2966_, 2);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_a_2966_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2982_ = v_a_2966_;
v_isShared_2983_ = v_isSharedCheck_2994_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_p_2980_);
lean_inc(v_v_2979_);
lean_inc(v_k_2978_);
lean_dec(v_a_2966_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2994_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v_k_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; 
v___x_2984_ = lean_int_mul(v_k_2964_, v_k_2978_);
lean_dec(v_k_2978_);
lean_inc(v_c_2965_);
v___x_2985_ = lean_nat_to_int(v_c_2965_);
v_k_2986_ = lean_int_emod(v___x_2984_, v___x_2985_);
lean_dec(v___x_2985_);
lean_dec(v___x_2984_);
v___x_2987_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2988_ = lean_int_dec_eq(v_k_2986_, v___x_2987_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2989_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_2964_, v_c_2965_, v_p_2980_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 2, v___x_2989_);
lean_ctor_set(v___x_2982_, 0, v_k_2986_);
v___x_2991_ = v___x_2982_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_k_2986_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_v_2979_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
else
{
lean_dec(v_k_2986_);
lean_del_object(v___x_2982_);
lean_dec(v_v_2979_);
v_a_2966_ = v_p_2980_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go___boxed(lean_object* v_k_2995_, lean_object* v_c_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_2995_, v_c_2996_, v_a_2997_);
lean_dec(v_k_2995_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object* v_k_2999_, lean_object* v_p_3000_, lean_object* v_c_3001_){
_start:
{
lean_object* v___x_3002_; lean_object* v_k_3003_; lean_object* v___x_3004_; uint8_t v___x_3005_; 
lean_inc(v_c_3001_);
v___x_3002_ = lean_nat_to_int(v_c_3001_);
v_k_3003_ = lean_int_emod(v_k_2999_, v___x_3002_);
lean_dec(v___x_3002_);
v___x_3004_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3005_ = lean_int_dec_eq(v_k_3003_, v___x_3004_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_3007_ = lean_int_dec_eq(v_k_3003_, v___x_3006_);
lean_dec(v_k_3003_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_2999_, v_c_3001_, v_p_3000_);
return v___x_3008_;
}
else
{
lean_dec(v_c_3001_);
return v_p_3000_;
}
}
else
{
lean_object* v___x_3009_; 
lean_dec(v_k_3003_);
lean_dec(v_c_3001_);
lean_dec_ref(v_p_3000_);
v___x_3009_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC___boxed(lean_object* v_k_3010_, lean_object* v_p_3011_, lean_object* v_c_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3010_, v_p_3011_, v_c_3012_);
lean_dec(v_k_3010_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go(lean_object* v_k_3014_, lean_object* v_m_3015_, lean_object* v_c_3016_, lean_object* v_a_3017_){
_start:
{
if (lean_obj_tag(v_a_3017_) == 0)
{
lean_object* v_k_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v_k_3021_; lean_object* v___x_3022_; uint8_t v___x_3023_; 
v_k_3018_ = lean_ctor_get(v_a_3017_, 0);
lean_inc(v_k_3018_);
lean_dec_ref_known(v_a_3017_, 1);
v___x_3019_ = lean_int_mul(v_k_3014_, v_k_3018_);
lean_dec(v_k_3018_);
v___x_3020_ = lean_nat_to_int(v_c_3016_);
v_k_3021_ = lean_int_emod(v___x_3019_, v___x_3020_);
lean_dec(v___x_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3023_ = lean_int_dec_eq(v_k_3021_, v___x_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3025_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3025_, 0, v_k_3021_);
lean_ctor_set(v___x_3025_, 1, v_m_3015_);
lean_ctor_set(v___x_3025_, 2, v___x_3024_);
return v___x_3025_;
}
else
{
lean_object* v___x_3026_; 
lean_dec(v_k_3021_);
lean_dec(v_m_3015_);
v___x_3026_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3026_;
}
}
else
{
lean_object* v_k_3027_; lean_object* v_v_3028_; lean_object* v_p_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3044_; 
v_k_3027_ = lean_ctor_get(v_a_3017_, 0);
v_v_3028_ = lean_ctor_get(v_a_3017_, 1);
v_p_3029_ = lean_ctor_get(v_a_3017_, 2);
v_isSharedCheck_3044_ = !lean_is_exclusive(v_a_3017_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3031_ = v_a_3017_;
v_isShared_3032_ = v_isSharedCheck_3044_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_p_3029_);
lean_inc(v_v_3028_);
lean_inc(v_k_3027_);
lean_dec(v_a_3017_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3044_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v_k_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3033_ = lean_int_mul(v_k_3014_, v_k_3027_);
lean_dec(v_k_3027_);
lean_inc(v_c_3016_);
v___x_3034_ = lean_nat_to_int(v_c_3016_);
v_k_3035_ = lean_int_emod(v___x_3033_, v___x_3034_);
lean_dec(v___x_3034_);
lean_dec(v___x_3033_);
v___x_3036_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3037_ = lean_int_dec_eq(v_k_3035_, v___x_3036_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
lean_inc(v_m_3015_);
v___x_3038_ = l_Lean_Grind_CommRing_Mon_mul(v_m_3015_, v_v_3028_);
v___x_3039_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3014_, v_m_3015_, v_c_3016_, v_p_3029_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 2, v___x_3039_);
lean_ctor_set(v___x_3031_, 1, v___x_3038_);
lean_ctor_set(v___x_3031_, 0, v_k_3035_);
v___x_3041_ = v___x_3031_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_k_3035_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3042_, 2, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
else
{
lean_dec(v_k_3035_);
lean_del_object(v___x_3031_);
lean_dec(v_v_3028_);
v_a_3017_ = v_p_3029_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go___boxed(lean_object* v_k_3045_, lean_object* v_m_3046_, lean_object* v_c_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3045_, v_m_3046_, v_c_3047_, v_a_3048_);
lean_dec(v_k_3045_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object* v_k_3050_, lean_object* v_m_3051_, lean_object* v_p_3052_, lean_object* v_c_3053_){
_start:
{
lean_object* v___x_3054_; lean_object* v_k_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; 
lean_inc(v_c_3053_);
v___x_3054_ = lean_nat_to_int(v_c_3053_);
v_k_3055_ = lean_int_emod(v_k_3050_, v___x_3054_);
lean_dec(v___x_3054_);
v___x_3056_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3057_ = lean_int_dec_eq(v_k_3055_, v___x_3056_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; uint8_t v___x_3059_; 
v___x_3058_ = lean_box(0);
v___x_3059_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_3051_, v___x_3058_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; 
lean_dec(v_k_3055_);
v___x_3060_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3050_, v_m_3051_, v_c_3053_, v_p_3052_);
return v___x_3060_;
}
else
{
lean_object* v___x_3061_; 
lean_dec(v_m_3051_);
v___x_3061_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3055_, v_p_3052_, v_c_3053_);
lean_dec(v_k_3055_);
return v___x_3061_;
}
}
else
{
lean_object* v___x_3062_; 
lean_dec(v_k_3055_);
lean_dec(v_c_3053_);
lean_dec_ref(v_p_3052_);
lean_dec(v_m_3051_);
v___x_3062_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC___boxed(lean_object* v_k_3063_, lean_object* v_m_3064_, lean_object* v_p_3065_, lean_object* v_c_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_3063_, v_m_3064_, v_p_3065_, v_c_3066_);
lean_dec(v_k_3063_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(lean_object* v_k_3068_, lean_object* v_m_3069_, lean_object* v_c_3070_, lean_object* v_p_3071_, lean_object* v_acc_3072_){
_start:
{
if (lean_obj_tag(v_p_3071_) == 0)
{
lean_object* v_k_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_k_3073_ = lean_ctor_get(v_p_3071_, 0);
lean_inc(v_k_3073_);
lean_dec_ref_known(v_p_3071_, 1);
v___x_3074_ = lean_int_mul(v_k_3068_, v_k_3073_);
lean_dec(v_k_3073_);
v___x_3075_ = lean_nat_to_int(v_c_3070_);
v___x_3076_ = lean_int_emod(v___x_3074_, v___x_3075_);
lean_dec(v___x_3075_);
lean_dec(v___x_3074_);
v___x_3077_ = l_Lean_Grind_CommRing_Poly_insert(v___x_3076_, v_m_3069_, v_acc_3072_);
return v___x_3077_;
}
else
{
lean_object* v_k_3078_; lean_object* v_v_3079_; lean_object* v_p_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v_k_3078_ = lean_ctor_get(v_p_3071_, 0);
lean_inc(v_k_3078_);
v_v_3079_ = lean_ctor_get(v_p_3071_, 1);
lean_inc(v_v_3079_);
v_p_3080_ = lean_ctor_get(v_p_3071_, 2);
lean_inc_ref(v_p_3080_);
lean_dec_ref_known(v_p_3071_, 3);
v___x_3081_ = lean_int_mul(v_k_3068_, v_k_3078_);
lean_dec(v_k_3078_);
lean_inc(v_c_3070_);
v___x_3082_ = lean_nat_to_int(v_c_3070_);
v___x_3083_ = lean_int_emod(v___x_3081_, v___x_3082_);
lean_dec(v___x_3082_);
lean_dec(v___x_3081_);
lean_inc(v_m_3069_);
v___x_3084_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_3069_, v_v_3079_);
v___x_3085_ = l_Lean_Grind_CommRing_Poly_insert(v___x_3083_, v___x_3084_, v_acc_3072_);
v_p_3071_ = v_p_3080_;
v_acc_3072_ = v___x_3085_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go___boxed(lean_object* v_k_3087_, lean_object* v_m_3088_, lean_object* v_c_3089_, lean_object* v_p_3090_, lean_object* v_acc_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_3087_, v_m_3088_, v_c_3089_, v_p_3090_, v_acc_3091_);
lean_dec(v_k_3087_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc(lean_object* v_k_3093_, lean_object* v_m_3094_, lean_object* v_p_3095_, lean_object* v_c_3096_){
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
lean_object* v___x_3103_; lean_object* v___x_3104_; 
lean_dec(v_k_3098_);
v___x_3103_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3104_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_3093_, v_m_3094_, v_c_3096_, v_p_3095_, v___x_3103_);
return v___x_3104_;
}
else
{
lean_object* v___x_3105_; 
lean_dec(v_m_3094_);
v___x_3105_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3098_, v_p_3095_, v_c_3096_);
lean_dec(v_k_3098_);
return v___x_3105_;
}
}
else
{
lean_object* v___x_3106_; 
lean_dec(v_k_3098_);
lean_dec(v_c_3096_);
lean_dec_ref(v_p_3095_);
lean_dec(v_m_3094_);
v___x_3106_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc___boxed(lean_object* v_k_3107_, lean_object* v_m_3108_, lean_object* v_p_3109_, lean_object* v_c_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3107_, v_m_3108_, v_p_3109_, v_c_3110_);
lean_dec(v_k_3107_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineC(lean_object* v_p_u2081_3112_, lean_object* v_p_u2082_3113_, lean_object* v_c_3114_){
_start:
{
if (lean_obj_tag(v_p_u2081_3112_) == 0)
{
if (lean_obj_tag(v_p_u2082_3113_) == 0)
{
lean_object* v_k_3115_; lean_object* v_k_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3126_; 
v_k_3115_ = lean_ctor_get(v_p_u2081_3112_, 0);
lean_inc(v_k_3115_);
lean_dec_ref_known(v_p_u2081_3112_, 1);
v_k_3116_ = lean_ctor_get(v_p_u2082_3113_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_p_u2082_3113_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3118_ = v_p_u2082_3113_;
v_isShared_3119_ = v_isSharedCheck_3126_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_k_3116_);
lean_dec(v_p_u2082_3113_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3126_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3120_ = lean_int_add(v_k_3115_, v_k_3116_);
lean_dec(v_k_3116_);
lean_dec(v_k_3115_);
v___x_3121_ = lean_nat_to_int(v_c_3114_);
v___x_3122_ = lean_int_emod(v___x_3120_, v___x_3121_);
lean_dec(v___x_3121_);
lean_dec(v___x_3120_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3122_);
v___x_3124_ = v___x_3118_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
else
{
lean_object* v_k_3127_; lean_object* v___x_3128_; 
v_k_3127_ = lean_ctor_get(v_p_u2081_3112_, 0);
lean_inc(v_k_3127_);
lean_dec_ref_known(v_p_u2081_3112_, 1);
v___x_3128_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2082_3113_, v_k_3127_, v_c_3114_);
lean_dec(v_k_3127_);
return v___x_3128_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_3113_) == 0)
{
lean_object* v_k_3129_; lean_object* v___x_3130_; 
v_k_3129_ = lean_ctor_get(v_p_u2082_3113_, 0);
lean_inc(v_k_3129_);
lean_dec_ref_known(v_p_u2082_3113_, 1);
v___x_3130_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2081_3112_, v_k_3129_, v_c_3114_);
lean_dec(v_k_3129_);
return v___x_3130_;
}
else
{
lean_object* v_k_3131_; lean_object* v_v_3132_; lean_object* v_p_3133_; lean_object* v_k_3134_; lean_object* v_v_3135_; lean_object* v_p_3136_; uint8_t v___x_3137_; 
v_k_3131_ = lean_ctor_get(v_p_u2081_3112_, 0);
v_v_3132_ = lean_ctor_get(v_p_u2081_3112_, 1);
v_p_3133_ = lean_ctor_get(v_p_u2081_3112_, 2);
v_k_3134_ = lean_ctor_get(v_p_u2082_3113_, 0);
v_v_3135_ = lean_ctor_get(v_p_u2082_3113_, 1);
v_p_3136_ = lean_ctor_get(v_p_u2082_3113_, 2);
v___x_3137_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_3132_, v_v_3135_);
switch(v___x_3137_)
{
case 0:
{
lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3145_; 
lean_inc_ref(v_p_3136_);
lean_inc(v_v_3135_);
lean_inc(v_k_3134_);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_p_u2082_3113_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; lean_object* v_unused_3147_; lean_object* v_unused_3148_; 
v_unused_3146_ = lean_ctor_get(v_p_u2082_3113_, 2);
lean_dec(v_unused_3146_);
v_unused_3147_ = lean_ctor_get(v_p_u2082_3113_, 1);
lean_dec(v_unused_3147_);
v_unused_3148_ = lean_ctor_get(v_p_u2082_3113_, 0);
lean_dec(v_unused_3148_);
v___x_3139_ = v_p_u2082_3113_;
v_isShared_3140_ = v_isSharedCheck_3145_;
goto v_resetjp_3138_;
}
else
{
lean_dec(v_p_u2082_3113_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3145_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3141_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_u2081_3112_, v_p_3136_, v_c_3114_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 2, v___x_3141_);
v___x_3143_ = v___x_3139_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_k_3134_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_v_3135_);
lean_ctor_set(v_reuseFailAlloc_3144_, 2, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
case 1:
{
lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3162_; 
lean_inc_ref(v_p_3136_);
lean_inc(v_k_3134_);
lean_inc_ref(v_p_3133_);
lean_inc(v_v_3132_);
lean_inc(v_k_3131_);
lean_dec_ref_known(v_p_u2081_3112_, 3);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_p_u2082_3113_);
if (v_isSharedCheck_3162_ == 0)
{
lean_object* v_unused_3163_; lean_object* v_unused_3164_; lean_object* v_unused_3165_; 
v_unused_3163_ = lean_ctor_get(v_p_u2082_3113_, 2);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_p_u2082_3113_, 1);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_p_u2082_3113_, 0);
lean_dec(v_unused_3165_);
v___x_3150_ = v_p_u2082_3113_;
v_isShared_3151_ = v_isSharedCheck_3162_;
goto v_resetjp_3149_;
}
else
{
lean_dec(v_p_u2082_3113_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3162_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v_k_3154_; lean_object* v___x_3155_; uint8_t v___x_3156_; 
v___x_3152_ = lean_int_add(v_k_3131_, v_k_3134_);
lean_dec(v_k_3134_);
lean_dec(v_k_3131_);
lean_inc(v_c_3114_);
v___x_3153_ = lean_nat_to_int(v_c_3114_);
v_k_3154_ = lean_int_emod(v___x_3152_, v___x_3153_);
lean_dec(v___x_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3156_ = lean_int_dec_eq(v_k_3154_, v___x_3155_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3157_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3133_, v_p_3136_, v_c_3114_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 2, v___x_3157_);
lean_ctor_set(v___x_3150_, 1, v_v_3132_);
lean_ctor_set(v___x_3150_, 0, v_k_3154_);
v___x_3159_ = v___x_3150_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_k_3154_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_v_3132_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
else
{
lean_dec(v_k_3154_);
lean_del_object(v___x_3150_);
lean_dec(v_v_3132_);
v_p_u2081_3112_ = v_p_3133_;
v_p_u2082_3113_ = v_p_3136_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3173_; 
lean_inc_ref(v_p_3133_);
lean_inc(v_v_3132_);
lean_inc(v_k_3131_);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_p_u2081_3112_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; lean_object* v_unused_3175_; lean_object* v_unused_3176_; 
v_unused_3174_ = lean_ctor_get(v_p_u2081_3112_, 2);
lean_dec(v_unused_3174_);
v_unused_3175_ = lean_ctor_get(v_p_u2081_3112_, 1);
lean_dec(v_unused_3175_);
v_unused_3176_ = lean_ctor_get(v_p_u2081_3112_, 0);
lean_dec(v_unused_3176_);
v___x_3167_ = v_p_u2081_3112_;
v_isShared_3168_ = v_isSharedCheck_3173_;
goto v_resetjp_3166_;
}
else
{
lean_dec(v_p_u2081_3112_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3173_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3169_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3133_, v_p_u2082_3113_, v_c_3114_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 2, v___x_3169_);
v___x_3171_ = v___x_3167_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_k_3131_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_v_3132_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC_go(lean_object* v_p_u2082_3177_, lean_object* v_c_3178_, lean_object* v_p_u2081_3179_, lean_object* v_acc_3180_){
_start:
{
if (lean_obj_tag(v_p_u2081_3179_) == 0)
{
lean_object* v_k_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v_k_3181_ = lean_ctor_get(v_p_u2081_3179_, 0);
lean_inc(v_k_3181_);
lean_dec_ref_known(v_p_u2081_3179_, 1);
lean_inc(v_c_3178_);
v___x_3182_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3181_, v_p_u2082_3177_, v_c_3178_);
lean_dec(v_k_3181_);
v___x_3183_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3180_, v___x_3182_, v_c_3178_);
return v___x_3183_;
}
else
{
lean_object* v_k_3184_; lean_object* v_v_3185_; lean_object* v_p_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v_k_3184_ = lean_ctor_get(v_p_u2081_3179_, 0);
lean_inc(v_k_3184_);
v_v_3185_ = lean_ctor_get(v_p_u2081_3179_, 1);
lean_inc(v_v_3185_);
v_p_3186_ = lean_ctor_get(v_p_u2081_3179_, 2);
lean_inc_ref(v_p_3186_);
lean_dec_ref_known(v_p_u2081_3179_, 3);
lean_inc_n(v_c_3178_, 2);
lean_inc_ref(v_p_u2082_3177_);
v___x_3187_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_3184_, v_v_3185_, v_p_u2082_3177_, v_c_3178_);
lean_dec(v_k_3184_);
v___x_3188_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3180_, v___x_3187_, v_c_3178_);
v_p_u2081_3179_ = v_p_3186_;
v_acc_3180_ = v___x_3188_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC(lean_object* v_p_u2081_3190_, lean_object* v_p_u2082_3191_, lean_object* v_c_3192_){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3194_ = l_Lean_Grind_CommRing_Poly_mulC_go(v_p_u2082_3191_, v_c_3192_, v_p_u2081_3190_, v___x_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc_go(lean_object* v_p_u2082_3195_, lean_object* v_c_3196_, lean_object* v_p_u2081_3197_, lean_object* v_acc_3198_){
_start:
{
if (lean_obj_tag(v_p_u2081_3197_) == 0)
{
lean_object* v_k_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v_k_3199_ = lean_ctor_get(v_p_u2081_3197_, 0);
lean_inc(v_k_3199_);
lean_dec_ref_known(v_p_u2081_3197_, 1);
lean_inc(v_c_3196_);
v___x_3200_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3199_, v_p_u2082_3195_, v_c_3196_);
lean_dec(v_k_3199_);
v___x_3201_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3198_, v___x_3200_, v_c_3196_);
return v___x_3201_;
}
else
{
lean_object* v_k_3202_; lean_object* v_v_3203_; lean_object* v_p_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v_k_3202_ = lean_ctor_get(v_p_u2081_3197_, 0);
lean_inc(v_k_3202_);
v_v_3203_ = lean_ctor_get(v_p_u2081_3197_, 1);
lean_inc(v_v_3203_);
v_p_3204_ = lean_ctor_get(v_p_u2081_3197_, 2);
lean_inc_ref(v_p_3204_);
lean_dec_ref_known(v_p_u2081_3197_, 3);
lean_inc_n(v_c_3196_, 2);
lean_inc_ref(v_p_u2082_3195_);
v___x_3205_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3202_, v_v_3203_, v_p_u2082_3195_, v_c_3196_);
lean_dec(v_k_3202_);
v___x_3206_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3198_, v___x_3205_, v_c_3196_);
v_p_u2081_3197_ = v_p_3204_;
v_acc_3198_ = v___x_3206_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc(lean_object* v_p_u2081_3208_, lean_object* v_p_u2082_3209_, lean_object* v_c_3210_){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3212_ = l_Lean_Grind_CommRing_Poly_mulC__nc_go(v_p_u2082_3209_, v_c_3210_, v_p_u2081_3208_, v___x_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC(lean_object* v_p_3213_, lean_object* v_k_3214_, lean_object* v_c_3215_){
_start:
{
lean_object* v_zero_3216_; uint8_t v_isZero_3217_; 
v_zero_3216_ = lean_unsigned_to_nat(0u);
v_isZero_3217_ = lean_nat_dec_eq(v_k_3214_, v_zero_3216_);
if (v_isZero_3217_ == 1)
{
lean_object* v___x_3218_; 
lean_dec(v_c_3215_);
lean_dec_ref(v_p_3213_);
v___x_3218_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3218_;
}
else
{
lean_object* v_one_3219_; lean_object* v_n_3220_; uint8_t v___x_3221_; 
v_one_3219_ = lean_unsigned_to_nat(1u);
v_n_3220_ = lean_nat_sub(v_k_3214_, v_one_3219_);
v___x_3221_ = lean_nat_dec_eq(v_n_3220_, v_zero_3216_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_inc(v_c_3215_);
lean_inc_ref(v_p_3213_);
v___x_3222_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3213_, v_n_3220_, v_c_3215_);
lean_dec(v_n_3220_);
v___x_3223_ = l_Lean_Grind_CommRing_Poly_mulC(v_p_3213_, v___x_3222_, v_c_3215_);
return v___x_3223_;
}
else
{
lean_dec(v_n_3220_);
lean_dec(v_c_3215_);
return v_p_3213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC___boxed(lean_object* v_p_3224_, lean_object* v_k_3225_, lean_object* v_c_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3224_, v_k_3225_, v_c_3226_);
lean_dec(v_k_3225_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc(lean_object* v_p_3228_, lean_object* v_k_3229_, lean_object* v_c_3230_){
_start:
{
lean_object* v_zero_3231_; uint8_t v_isZero_3232_; 
v_zero_3231_ = lean_unsigned_to_nat(0u);
v_isZero_3232_ = lean_nat_dec_eq(v_k_3229_, v_zero_3231_);
if (v_isZero_3232_ == 1)
{
lean_object* v___x_3233_; 
lean_dec(v_c_3230_);
lean_dec_ref(v_p_3228_);
v___x_3233_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3233_;
}
else
{
lean_object* v_one_3234_; lean_object* v_n_3235_; uint8_t v___x_3236_; 
v_one_3234_ = lean_unsigned_to_nat(1u);
v_n_3235_ = lean_nat_sub(v_k_3229_, v_one_3234_);
v___x_3236_ = lean_nat_dec_eq(v_n_3235_, v_zero_3231_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_inc(v_c_3230_);
lean_inc_ref(v_p_3228_);
v___x_3237_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3228_, v_n_3235_, v_c_3230_);
lean_dec(v_n_3235_);
v___x_3238_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3237_, v_p_3228_, v_c_3230_);
return v___x_3238_;
}
else
{
lean_dec(v_n_3235_);
lean_dec(v_c_3230_);
return v_p_3228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc___boxed(lean_object* v_p_3239_, lean_object* v_k_3240_, lean_object* v_c_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3239_, v_k_3240_, v_c_3241_);
lean_dec(v_k_3240_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC_go(lean_object* v_c_3243_, lean_object* v_a_3244_){
_start:
{
lean_object* v_k_3246_; 
switch(lean_obj_tag(v_a_3244_))
{
case 1:
{
lean_object* v_k_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3260_; 
v_k_3250_ = lean_ctor_get(v_a_3244_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_a_3244_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3252_ = v_a_3244_;
v_isShared_3253_ = v_isSharedCheck_3260_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_k_3250_);
lean_dec(v_a_3244_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3260_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3258_; 
v___x_3254_ = lean_nat_to_int(v_k_3250_);
v___x_3255_ = lean_nat_to_int(v_c_3243_);
v___x_3256_ = lean_int_emod(v___x_3254_, v___x_3255_);
lean_dec(v___x_3255_);
lean_dec(v___x_3254_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set_tag(v___x_3252_, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3256_);
v___x_3258_ = v___x_3252_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3256_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
case 3:
{
lean_object* v_i_3261_; lean_object* v___x_3262_; 
lean_dec(v_c_3243_);
v_i_3261_ = lean_ctor_get(v_a_3244_, 0);
lean_inc(v_i_3261_);
lean_dec_ref_known(v_a_3244_, 1);
v___x_3262_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3261_);
return v___x_3262_;
}
case 4:
{
lean_object* v_a_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v_a_3263_ = lean_ctor_get(v_a_3244_, 0);
lean_inc_ref(v_a_3263_);
lean_dec_ref_known(v_a_3244_, 1);
v___x_3264_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3243_);
v___x_3265_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3243_, v_a_3263_);
v___x_3266_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3264_, v___x_3265_, v_c_3243_);
return v___x_3266_;
}
case 5:
{
lean_object* v_a_3267_; lean_object* v_b_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v_a_3267_ = lean_ctor_get(v_a_3244_, 0);
lean_inc_ref(v_a_3267_);
v_b_3268_ = lean_ctor_get(v_a_3244_, 1);
lean_inc_ref(v_b_3268_);
lean_dec_ref_known(v_a_3244_, 2);
lean_inc_n(v_c_3243_, 2);
v___x_3269_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3243_, v_a_3267_);
v___x_3270_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3243_, v_b_3268_);
v___x_3271_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3269_, v___x_3270_, v_c_3243_);
return v___x_3271_;
}
case 6:
{
lean_object* v_a_3272_; lean_object* v_b_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v_a_3272_ = lean_ctor_get(v_a_3244_, 0);
lean_inc_ref(v_a_3272_);
v_b_3273_ = lean_ctor_get(v_a_3244_, 1);
lean_inc_ref(v_b_3273_);
lean_dec_ref_known(v_a_3244_, 2);
lean_inc_n(v_c_3243_, 3);
v___x_3274_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3243_, v_a_3272_);
v___x_3275_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_3276_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3243_, v_b_3273_);
v___x_3277_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3275_, v___x_3276_, v_c_3243_);
v___x_3278_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3274_, v___x_3277_, v_c_3243_);
return v___x_3278_;
}
case 7:
{
lean_object* v_a_3279_; lean_object* v_b_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_a_3279_ = lean_ctor_get(v_a_3244_, 0);
lean_inc_ref(v_a_3279_);
v_b_3280_ = lean_ctor_get(v_a_3244_, 1);
lean_inc_ref(v_b_3280_);
lean_dec_ref_known(v_a_3244_, 2);
lean_inc_n(v_c_3243_, 2);
v___x_3281_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3243_, v_a_3279_);
v___x_3282_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3243_, v_b_3280_);
v___x_3283_ = l_Lean_Grind_CommRing_Poly_mulC(v___x_3281_, v___x_3282_, v_c_3243_);
return v___x_3283_;
}
case 8:
{
lean_object* v_a_3284_; lean_object* v_k_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3312_; 
v_a_3284_ = lean_ctor_get(v_a_3244_, 0);
v_k_3285_ = lean_ctor_get(v_a_3244_, 1);
v_isSharedCheck_3312_ = !lean_is_exclusive(v_a_3244_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3287_ = v_a_3244_;
v_isShared_3288_ = v_isSharedCheck_3312_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_k_3285_);
lean_inc(v_a_3284_);
lean_dec(v_a_3244_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3312_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3289_; uint8_t v___x_3290_; 
v___x_3289_ = lean_unsigned_to_nat(0u);
v___x_3290_ = lean_nat_dec_eq(v_k_3285_, v___x_3289_);
if (v___x_3290_ == 0)
{
switch(lean_obj_tag(v_a_3284_))
{
case 0:
{
lean_object* v_k_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3301_; 
lean_del_object(v___x_3287_);
v_k_3291_ = lean_ctor_get(v_a_3284_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v_a_3284_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3293_ = v_a_3284_;
v_isShared_3294_ = v_isSharedCheck_3301_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_k_3291_);
lean_dec(v_a_3284_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3301_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3295_ = l_Int_pow(v_k_3291_, v_k_3285_);
lean_dec(v_k_3285_);
lean_dec(v_k_3291_);
v___x_3296_ = lean_nat_to_int(v_c_3243_);
v___x_3297_ = lean_int_emod(v___x_3295_, v___x_3296_);
lean_dec(v___x_3296_);
lean_dec(v___x_3295_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 0, v___x_3297_);
v___x_3299_ = v___x_3293_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
case 3:
{
lean_object* v_i_3302_; lean_object* v___x_3304_; 
lean_dec(v_c_3243_);
v_i_3302_ = lean_ctor_get(v_a_3284_, 0);
lean_inc(v_i_3302_);
lean_dec_ref_known(v_a_3284_, 1);
if (v_isShared_3288_ == 0)
{
lean_ctor_set_tag(v___x_3287_, 0);
lean_ctor_set(v___x_3287_, 0, v_i_3302_);
v___x_3304_ = v___x_3287_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_i_3302_);
lean_ctor_set(v_reuseFailAlloc_3308_, 1, v_k_3285_);
v___x_3304_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3304_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3306_);
return v___x_3307_;
}
}
default: 
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
lean_del_object(v___x_3287_);
lean_inc(v_c_3243_);
v___x_3309_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3243_, v_a_3284_);
v___x_3310_ = l_Lean_Grind_CommRing_Poly_powC(v___x_3309_, v_k_3285_, v_c_3243_);
lean_dec(v_k_3285_);
return v___x_3310_;
}
}
}
else
{
lean_object* v___x_3311_; 
lean_del_object(v___x_3287_);
lean_dec(v_k_3285_);
lean_dec_ref(v_a_3284_);
lean_dec(v_c_3243_);
v___x_3311_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3311_;
}
}
}
default: 
{
lean_object* v_k_3313_; 
v_k_3313_ = lean_ctor_get(v_a_3244_, 0);
lean_inc(v_k_3313_);
lean_dec_ref(v_a_3244_);
v_k_3246_ = v_k_3313_;
goto v___jp_3245_;
}
}
v___jp_3245_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3247_ = lean_nat_to_int(v_c_3243_);
v___x_3248_ = lean_int_emod(v_k_3246_, v___x_3247_);
lean_dec(v___x_3247_);
lean_dec(v_k_3246_);
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
return v___x_3249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC(lean_object* v_e_3314_, lean_object* v_c_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3315_, v_e_3314_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(lean_object* v_c_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v_k_3320_; 
switch(lean_obj_tag(v_a_3318_))
{
case 1:
{
lean_object* v_k_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3334_; 
v_k_3324_ = lean_ctor_get(v_a_3318_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v_a_3318_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3326_ = v_a_3318_;
v_isShared_3327_ = v_isSharedCheck_3334_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_k_3324_);
lean_dec(v_a_3318_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3334_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3332_; 
v___x_3328_ = lean_nat_to_int(v_k_3324_);
v___x_3329_ = lean_nat_to_int(v_c_3317_);
v___x_3330_ = lean_int_emod(v___x_3328_, v___x_3329_);
lean_dec(v___x_3329_);
lean_dec(v___x_3328_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set_tag(v___x_3326_, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3330_);
v___x_3332_ = v___x_3326_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
case 3:
{
lean_object* v_i_3335_; lean_object* v___x_3336_; 
lean_dec(v_c_3317_);
v_i_3335_ = lean_ctor_get(v_a_3318_, 0);
lean_inc(v_i_3335_);
lean_dec_ref_known(v_a_3318_, 1);
v___x_3336_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3335_);
return v___x_3336_;
}
case 4:
{
lean_object* v_a_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v_a_3337_ = lean_ctor_get(v_a_3318_, 0);
lean_inc_ref(v_a_3337_);
lean_dec_ref_known(v_a_3318_, 1);
v___x_3338_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3317_);
v___x_3339_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3317_, v_a_3337_);
v___x_3340_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3338_, v___x_3339_, v_c_3317_);
return v___x_3340_;
}
case 5:
{
lean_object* v_a_3341_; lean_object* v_b_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v_a_3341_ = lean_ctor_get(v_a_3318_, 0);
lean_inc_ref(v_a_3341_);
v_b_3342_ = lean_ctor_get(v_a_3318_, 1);
lean_inc_ref(v_b_3342_);
lean_dec_ref_known(v_a_3318_, 2);
lean_inc_n(v_c_3317_, 2);
v___x_3343_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3317_, v_a_3341_);
v___x_3344_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3317_, v_b_3342_);
v___x_3345_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3343_, v___x_3344_, v_c_3317_);
return v___x_3345_;
}
case 6:
{
lean_object* v_a_3346_; lean_object* v_b_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v_a_3346_ = lean_ctor_get(v_a_3318_, 0);
lean_inc_ref(v_a_3346_);
v_b_3347_ = lean_ctor_get(v_a_3318_, 1);
lean_inc_ref(v_b_3347_);
lean_dec_ref_known(v_a_3318_, 2);
lean_inc_n(v_c_3317_, 3);
v___x_3348_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3317_, v_a_3346_);
v___x_3349_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_3350_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3317_, v_b_3347_);
v___x_3351_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3349_, v___x_3350_, v_c_3317_);
v___x_3352_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3348_, v___x_3351_, v_c_3317_);
return v___x_3352_;
}
case 7:
{
lean_object* v_a_3353_; lean_object* v_b_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v_a_3353_ = lean_ctor_get(v_a_3318_, 0);
lean_inc_ref(v_a_3353_);
v_b_3354_ = lean_ctor_get(v_a_3318_, 1);
lean_inc_ref(v_b_3354_);
lean_dec_ref_known(v_a_3318_, 2);
lean_inc_n(v_c_3317_, 2);
v___x_3355_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3317_, v_a_3353_);
v___x_3356_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3317_, v_b_3354_);
v___x_3357_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3355_, v___x_3356_, v_c_3317_);
return v___x_3357_;
}
case 8:
{
lean_object* v_a_3358_; lean_object* v_k_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3386_; 
v_a_3358_ = lean_ctor_get(v_a_3318_, 0);
v_k_3359_ = lean_ctor_get(v_a_3318_, 1);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_a_3318_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3361_ = v_a_3318_;
v_isShared_3362_ = v_isSharedCheck_3386_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_k_3359_);
lean_inc(v_a_3358_);
lean_dec(v_a_3318_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3386_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; uint8_t v___x_3364_; 
v___x_3363_ = lean_unsigned_to_nat(0u);
v___x_3364_ = lean_nat_dec_eq(v_k_3359_, v___x_3363_);
if (v___x_3364_ == 0)
{
switch(lean_obj_tag(v_a_3358_))
{
case 0:
{
lean_object* v_k_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3375_; 
lean_del_object(v___x_3361_);
v_k_3365_ = lean_ctor_get(v_a_3358_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_a_3358_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3367_ = v_a_3358_;
v_isShared_3368_ = v_isSharedCheck_3375_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_k_3365_);
lean_dec(v_a_3358_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3375_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3373_; 
v___x_3369_ = l_Int_pow(v_k_3365_, v_k_3359_);
lean_dec(v_k_3359_);
lean_dec(v_k_3365_);
v___x_3370_ = lean_nat_to_int(v_c_3317_);
v___x_3371_ = lean_int_emod(v___x_3369_, v___x_3370_);
lean_dec(v___x_3370_);
lean_dec(v___x_3369_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v___x_3371_);
v___x_3373_ = v___x_3367_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
case 3:
{
lean_object* v_i_3376_; lean_object* v___x_3378_; 
lean_dec(v_c_3317_);
v_i_3376_ = lean_ctor_get(v_a_3358_, 0);
lean_inc(v_i_3376_);
lean_dec_ref_known(v_a_3358_, 1);
if (v_isShared_3362_ == 0)
{
lean_ctor_set_tag(v___x_3361_, 0);
lean_ctor_set(v___x_3361_, 0, v_i_3376_);
v___x_3378_ = v___x_3361_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_i_3376_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_k_3359_);
v___x_3378_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3379_ = lean_box(0);
v___x_3380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3380_);
return v___x_3381_;
}
}
default: 
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
lean_del_object(v___x_3361_);
lean_inc(v_c_3317_);
v___x_3383_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3317_, v_a_3358_);
v___x_3384_ = l_Lean_Grind_CommRing_Poly_powC__nc(v___x_3383_, v_k_3359_, v_c_3317_);
lean_dec(v_k_3359_);
return v___x_3384_;
}
}
}
else
{
lean_object* v___x_3385_; 
lean_del_object(v___x_3361_);
lean_dec(v_k_3359_);
lean_dec_ref(v_a_3358_);
lean_dec(v_c_3317_);
v___x_3385_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3385_;
}
}
}
default: 
{
lean_object* v_k_3387_; 
v_k_3387_ = lean_ctor_get(v_a_3318_, 0);
lean_inc(v_k_3387_);
lean_dec_ref(v_a_3318_);
v_k_3320_ = v_k_3387_;
goto v___jp_3319_;
}
}
v___jp_3319_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_nat_to_int(v_c_3317_);
v___x_3322_ = lean_int_emod(v_k_3320_, v___x_3321_);
lean_dec(v___x_3321_);
lean_dec(v_k_3320_);
v___x_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
return v___x_3323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc(lean_object* v_e_3388_, lean_object* v_c_3389_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3389_, v_e_3388_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(lean_object* v_k_3391_, lean_object* v_h__1_3392_, lean_object* v_h__2_3393_, lean_object* v_h__3_3394_){
_start:
{
lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3395_ = lean_unsigned_to_nat(0u);
v___x_3396_ = lean_nat_dec_eq(v_k_3391_, v___x_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; uint8_t v___x_3398_; 
lean_dec(v_h__1_3392_);
v___x_3397_ = lean_unsigned_to_nat(1u);
v___x_3398_ = lean_nat_dec_eq(v_k_3391_, v___x_3397_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; 
lean_dec(v_h__2_3393_);
v___x_3399_ = lean_apply_3(v_h__3_3394_, v_k_3391_, lean_box(0), lean_box(0));
return v___x_3399_;
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
lean_dec(v_h__3_3394_);
lean_dec(v_k_3391_);
v___x_3400_ = lean_box(0);
v___x_3401_ = lean_apply_1(v_h__2_3393_, v___x_3400_);
return v___x_3401_;
}
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec(v_h__3_3394_);
lean_dec(v_h__2_3393_);
lean_dec(v_k_3391_);
v___x_3402_ = lean_box(0);
v___x_3403_ = lean_apply_1(v_h__1_3392_, v___x_3402_);
return v___x_3403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(lean_object* v_motive_3404_, lean_object* v_k_3405_, lean_object* v_h__1_3406_, lean_object* v_h__2_3407_, lean_object* v_h__3_3408_){
_start:
{
lean_object* v___x_3409_; uint8_t v___x_3410_; 
v___x_3409_ = lean_unsigned_to_nat(0u);
v___x_3410_ = lean_nat_dec_eq(v_k_3405_, v___x_3409_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; uint8_t v___x_3412_; 
lean_dec(v_h__1_3406_);
v___x_3411_ = lean_unsigned_to_nat(1u);
v___x_3412_ = lean_nat_dec_eq(v_k_3405_, v___x_3411_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; 
lean_dec(v_h__2_3407_);
v___x_3413_ = lean_apply_3(v_h__3_3408_, v_k_3405_, lean_box(0), lean_box(0));
return v___x_3413_;
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_dec(v_h__3_3408_);
lean_dec(v_k_3405_);
v___x_3414_ = lean_box(0);
v___x_3415_ = lean_apply_1(v_h__2_3407_, v___x_3414_);
return v___x_3415_;
}
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
lean_dec(v_h__3_3408_);
lean_dec(v_h__2_3407_);
lean_dec(v_k_3405_);
v___x_3416_ = lean_box(0);
v___x_3417_ = lean_apply_1(v_h__1_3406_, v___x_3416_);
return v___x_3417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(lean_object* v_m_u2081_3418_, lean_object* v_h__1_3419_, lean_object* v_h__2_3420_, lean_object* v_h__3_3421_){
_start:
{
if (lean_obj_tag(v_m_u2081_3418_) == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec(v_h__3_3421_);
lean_dec(v_h__2_3420_);
v___x_3422_ = lean_box(0);
v___x_3423_ = lean_apply_1(v_h__1_3419_, v___x_3422_);
return v___x_3423_;
}
else
{
lean_object* v_m_3424_; 
lean_dec(v_h__1_3419_);
v_m_3424_ = lean_ctor_get(v_m_u2081_3418_, 1);
if (lean_obj_tag(v_m_3424_) == 0)
{
lean_object* v_p_3425_; lean_object* v___x_3426_; 
lean_dec(v_h__3_3421_);
v_p_3425_ = lean_ctor_get(v_m_u2081_3418_, 0);
lean_inc_ref(v_p_3425_);
lean_dec_ref_known(v_m_u2081_3418_, 2);
v___x_3426_ = lean_apply_1(v_h__2_3420_, v_p_3425_);
return v___x_3426_;
}
else
{
lean_object* v_p_3427_; lean_object* v___x_3428_; 
lean_inc(v_m_3424_);
lean_dec(v_h__2_3420_);
v_p_3427_ = lean_ctor_get(v_m_u2081_3418_, 0);
lean_inc_ref(v_p_3427_);
lean_dec_ref_known(v_m_u2081_3418_, 2);
v___x_3428_ = lean_apply_3(v_h__3_3421_, v_p_3427_, v_m_3424_, lean_box(0));
return v___x_3428_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(lean_object* v_motive_3429_, lean_object* v_m_u2081_3430_, lean_object* v_h__1_3431_, lean_object* v_h__2_3432_, lean_object* v_h__3_3433_){
_start:
{
if (lean_obj_tag(v_m_u2081_3430_) == 0)
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
lean_dec(v_h__3_3433_);
lean_dec(v_h__2_3432_);
v___x_3434_ = lean_box(0);
v___x_3435_ = lean_apply_1(v_h__1_3431_, v___x_3434_);
return v___x_3435_;
}
else
{
lean_object* v_m_3436_; 
lean_dec(v_h__1_3431_);
v_m_3436_ = lean_ctor_get(v_m_u2081_3430_, 1);
if (lean_obj_tag(v_m_3436_) == 0)
{
lean_object* v_p_3437_; lean_object* v___x_3438_; 
lean_dec(v_h__3_3433_);
v_p_3437_ = lean_ctor_get(v_m_u2081_3430_, 0);
lean_inc_ref(v_p_3437_);
lean_dec_ref_known(v_m_u2081_3430_, 2);
v___x_3438_ = lean_apply_1(v_h__2_3432_, v_p_3437_);
return v___x_3438_;
}
else
{
lean_object* v_p_3439_; lean_object* v___x_3440_; 
lean_inc(v_m_3436_);
lean_dec(v_h__2_3432_);
v_p_3439_ = lean_ctor_get(v_m_u2081_3430_, 0);
lean_inc_ref(v_p_3439_);
lean_dec_ref_known(v_m_u2081_3430_, 2);
v___x_3440_ = lean_apply_3(v_h__3_3433_, v_p_3439_, v_m_3436_, lean_box(0));
return v___x_3440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(uint8_t v_a_3441_, lean_object* v_h__1_3442_, lean_object* v_h__2_3443_){
_start:
{
if (v_a_3441_ == 1)
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_dec(v_h__2_3443_);
v___x_3444_ = lean_box(0);
v___x_3445_ = lean_apply_1(v_h__1_3442_, v___x_3444_);
return v___x_3445_;
}
else
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
lean_dec(v_h__1_3442_);
v___x_3446_ = lean_box(v_a_3441_);
v___x_3447_ = lean_apply_2(v_h__2_3443_, v___x_3446_, lean_box(0));
return v___x_3447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object* v_a_3448_, lean_object* v_h__1_3449_, lean_object* v_h__2_3450_){
_start:
{
uint8_t v_a_13__boxed_3451_; lean_object* v_res_3452_; 
v_a_13__boxed_3451_ = lean_unbox(v_a_3448_);
v_res_3452_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(v_a_13__boxed_3451_, v_h__1_3449_, v_h__2_3450_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(lean_object* v_motive_3453_, uint8_t v_a_3454_, lean_object* v_h__1_3455_, lean_object* v_h__2_3456_){
_start:
{
if (v_a_3454_ == 1)
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
lean_dec(v_h__2_3456_);
v___x_3457_ = lean_box(0);
v___x_3458_ = lean_apply_1(v_h__1_3455_, v___x_3457_);
return v___x_3458_;
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
lean_dec(v_h__1_3455_);
v___x_3459_ = lean_box(v_a_3454_);
v___x_3460_ = lean_apply_2(v_h__2_3456_, v___x_3459_, lean_box(0));
return v___x_3460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___boxed(lean_object* v_motive_3461_, lean_object* v_a_3462_, lean_object* v_h__1_3463_, lean_object* v_h__2_3464_){
_start:
{
uint8_t v_a_24__boxed_3465_; lean_object* v_res_3466_; 
v_a_24__boxed_3465_ = lean_unbox(v_a_3462_);
v_res_3466_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(v_motive_3461_, v_a_24__boxed_3465_, v_h__1_3463_, v_h__2_3464_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(lean_object* v_p_3467_, lean_object* v_h__1_3468_, lean_object* v_h__2_3469_, lean_object* v_h__3_3470_){
_start:
{
if (lean_obj_tag(v_p_3467_) == 0)
{
lean_object* v_k_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
lean_dec(v_h__3_3470_);
v_k_3471_ = lean_ctor_get(v_p_3467_, 0);
lean_inc(v_k_3471_);
lean_dec_ref_known(v_p_3467_, 1);
v___x_3472_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3473_ = lean_int_dec_eq(v_k_3471_, v___x_3472_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; 
lean_dec(v_h__1_3468_);
v___x_3474_ = lean_apply_2(v_h__2_3469_, v_k_3471_, lean_box(0));
return v___x_3474_;
}
else
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
lean_dec(v_k_3471_);
lean_dec(v_h__2_3469_);
v___x_3475_ = lean_box(0);
v___x_3476_ = lean_apply_1(v_h__1_3468_, v___x_3475_);
return v___x_3476_;
}
}
else
{
lean_object* v_k_3477_; lean_object* v_v_3478_; lean_object* v_p_3479_; lean_object* v___x_3480_; 
lean_dec(v_h__2_3469_);
lean_dec(v_h__1_3468_);
v_k_3477_ = lean_ctor_get(v_p_3467_, 0);
lean_inc(v_k_3477_);
v_v_3478_ = lean_ctor_get(v_p_3467_, 1);
lean_inc(v_v_3478_);
v_p_3479_ = lean_ctor_get(v_p_3467_, 2);
lean_inc_ref(v_p_3479_);
lean_dec_ref_known(v_p_3467_, 3);
v___x_3480_ = lean_apply_3(v_h__3_3470_, v_k_3477_, v_v_3478_, v_p_3479_);
return v___x_3480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(lean_object* v_motive_3481_, lean_object* v_p_3482_, lean_object* v_h__1_3483_, lean_object* v_h__2_3484_, lean_object* v_h__3_3485_){
_start:
{
if (lean_obj_tag(v_p_3482_) == 0)
{
lean_object* v_k_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; 
lean_dec(v_h__3_3485_);
v_k_3486_ = lean_ctor_get(v_p_3482_, 0);
lean_inc(v_k_3486_);
lean_dec_ref_known(v_p_3482_, 1);
v___x_3487_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3488_ = lean_int_dec_eq(v_k_3486_, v___x_3487_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; 
lean_dec(v_h__1_3483_);
v___x_3489_ = lean_apply_2(v_h__2_3484_, v_k_3486_, lean_box(0));
return v___x_3489_;
}
else
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
lean_dec(v_k_3486_);
lean_dec(v_h__2_3484_);
v___x_3490_ = lean_box(0);
v___x_3491_ = lean_apply_1(v_h__1_3483_, v___x_3490_);
return v___x_3491_;
}
}
else
{
lean_object* v_k_3492_; lean_object* v_v_3493_; lean_object* v_p_3494_; lean_object* v___x_3495_; 
lean_dec(v_h__2_3484_);
lean_dec(v_h__1_3483_);
v_k_3492_ = lean_ctor_get(v_p_3482_, 0);
lean_inc(v_k_3492_);
v_v_3493_ = lean_ctor_get(v_p_3482_, 1);
lean_inc(v_v_3493_);
v_p_3494_ = lean_ctor_get(v_p_3482_, 2);
lean_inc_ref(v_p_3494_);
lean_dec_ref_known(v_p_3482_, 3);
v___x_3495_ = lean_apply_3(v_h__3_3485_, v_k_3492_, v_v_3493_, v_p_3494_);
return v___x_3495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object* v_p_3496_, lean_object* v_h__1_3497_, lean_object* v_h__2_3498_){
_start:
{
if (lean_obj_tag(v_p_3496_) == 0)
{
lean_object* v_k_3499_; lean_object* v___x_3500_; 
lean_dec(v_h__2_3498_);
v_k_3499_ = lean_ctor_get(v_p_3496_, 0);
lean_inc(v_k_3499_);
lean_dec_ref_known(v_p_3496_, 1);
v___x_3500_ = lean_apply_1(v_h__1_3497_, v_k_3499_);
return v___x_3500_;
}
else
{
lean_object* v_k_3501_; lean_object* v_v_3502_; lean_object* v_p_3503_; lean_object* v___x_3504_; 
lean_dec(v_h__1_3497_);
v_k_3501_ = lean_ctor_get(v_p_3496_, 0);
lean_inc(v_k_3501_);
v_v_3502_ = lean_ctor_get(v_p_3496_, 1);
lean_inc(v_v_3502_);
v_p_3503_ = lean_ctor_get(v_p_3496_, 2);
lean_inc_ref(v_p_3503_);
lean_dec_ref_known(v_p_3496_, 3);
v___x_3504_ = lean_apply_3(v_h__2_3498_, v_k_3501_, v_v_3502_, v_p_3503_);
return v___x_3504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object* v_motive_3505_, lean_object* v_p_3506_, lean_object* v_h__1_3507_, lean_object* v_h__2_3508_){
_start:
{
if (lean_obj_tag(v_p_3506_) == 0)
{
lean_object* v_k_3509_; lean_object* v___x_3510_; 
lean_dec(v_h__2_3508_);
v_k_3509_ = lean_ctor_get(v_p_3506_, 0);
lean_inc(v_k_3509_);
lean_dec_ref_known(v_p_3506_, 1);
v___x_3510_ = lean_apply_1(v_h__1_3507_, v_k_3509_);
return v___x_3510_;
}
else
{
lean_object* v_k_3511_; lean_object* v_v_3512_; lean_object* v_p_3513_; lean_object* v___x_3514_; 
lean_dec(v_h__1_3507_);
v_k_3511_ = lean_ctor_get(v_p_3506_, 0);
lean_inc(v_k_3511_);
v_v_3512_ = lean_ctor_get(v_p_3506_, 1);
lean_inc(v_v_3512_);
v_p_3513_ = lean_ctor_get(v_p_3506_, 2);
lean_inc_ref(v_p_3513_);
lean_dec_ref_known(v_p_3506_, 3);
v___x_3514_ = lean_apply_3(v_h__2_3508_, v_k_3511_, v_v_3512_, v_p_3513_);
return v___x_3514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object* v_k_3515_, lean_object* v_h__1_3516_, lean_object* v_h__2_3517_, lean_object* v_h__3_3518_){
_start:
{
lean_object* v_zero_3519_; uint8_t v_isZero_3520_; 
v_zero_3519_ = lean_unsigned_to_nat(0u);
v_isZero_3520_ = lean_nat_dec_eq(v_k_3515_, v_zero_3519_);
if (v_isZero_3520_ == 1)
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
lean_dec(v_h__3_3518_);
lean_dec(v_h__2_3517_);
v___x_3521_ = lean_box(0);
v___x_3522_ = lean_apply_1(v_h__1_3516_, v___x_3521_);
return v___x_3522_;
}
else
{
lean_object* v_one_3523_; lean_object* v_n_3524_; uint8_t v___x_3525_; 
lean_dec(v_h__1_3516_);
v_one_3523_ = lean_unsigned_to_nat(1u);
v_n_3524_ = lean_nat_sub(v_k_3515_, v_one_3523_);
v___x_3525_ = lean_nat_dec_eq(v_n_3524_, v_zero_3519_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; 
lean_dec(v_h__2_3517_);
v___x_3526_ = lean_apply_2(v_h__3_3518_, v_n_3524_, lean_box(0));
return v___x_3526_;
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
lean_dec(v_n_3524_);
lean_dec(v_h__3_3518_);
v___x_3527_ = lean_box(0);
v___x_3528_ = lean_apply_1(v_h__2_3517_, v___x_3527_);
return v___x_3528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object* v_k_3529_, lean_object* v_h__1_3530_, lean_object* v_h__2_3531_, lean_object* v_h__3_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(v_k_3529_, v_h__1_3530_, v_h__2_3531_, v_h__3_3532_);
lean_dec(v_k_3529_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object* v_motive_3534_, lean_object* v_k_3535_, lean_object* v_h__1_3536_, lean_object* v_h__2_3537_, lean_object* v_h__3_3538_){
_start:
{
lean_object* v_zero_3539_; uint8_t v_isZero_3540_; 
v_zero_3539_ = lean_unsigned_to_nat(0u);
v_isZero_3540_ = lean_nat_dec_eq(v_k_3535_, v_zero_3539_);
if (v_isZero_3540_ == 1)
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
lean_dec(v_h__3_3538_);
lean_dec(v_h__2_3537_);
v___x_3541_ = lean_box(0);
v___x_3542_ = lean_apply_1(v_h__1_3536_, v___x_3541_);
return v___x_3542_;
}
else
{
lean_object* v_one_3543_; lean_object* v_n_3544_; uint8_t v___x_3545_; 
lean_dec(v_h__1_3536_);
v_one_3543_ = lean_unsigned_to_nat(1u);
v_n_3544_ = lean_nat_sub(v_k_3535_, v_one_3543_);
v___x_3545_ = lean_nat_dec_eq(v_n_3544_, v_zero_3539_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3546_; 
lean_dec(v_h__2_3537_);
v___x_3546_ = lean_apply_2(v_h__3_3538_, v_n_3544_, lean_box(0));
return v___x_3546_;
}
else
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
lean_dec(v_n_3544_);
lean_dec(v_h__3_3538_);
v___x_3547_ = lean_box(0);
v___x_3548_ = lean_apply_1(v_h__2_3537_, v___x_3547_);
return v___x_3548_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object* v_motive_3549_, lean_object* v_k_3550_, lean_object* v_h__1_3551_, lean_object* v_h__2_3552_, lean_object* v_h__3_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(v_motive_3549_, v_k_3550_, v_h__1_3551_, v_h__2_3552_, v_h__3_3553_);
lean_dec(v_k_3550_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(lean_object* v_x_3555_, lean_object* v_h__1_3556_, lean_object* v_h__2_3557_, lean_object* v_h__3_3558_, lean_object* v_h__4_3559_, lean_object* v_h__5_3560_, lean_object* v_h__6_3561_, lean_object* v_h__7_3562_, lean_object* v_h__8_3563_, lean_object* v_h__9_3564_){
_start:
{
switch(lean_obj_tag(v_x_3555_))
{
case 0:
{
lean_object* v_k_3565_; lean_object* v___x_3566_; 
lean_dec(v_h__9_3564_);
lean_dec(v_h__8_3563_);
lean_dec(v_h__7_3562_);
lean_dec(v_h__6_3561_);
lean_dec(v_h__5_3560_);
lean_dec(v_h__4_3559_);
lean_dec(v_h__3_3558_);
lean_dec(v_h__2_3557_);
v_k_3565_ = lean_ctor_get(v_x_3555_, 0);
lean_inc(v_k_3565_);
lean_dec_ref_known(v_x_3555_, 1);
v___x_3566_ = lean_apply_1(v_h__1_3556_, v_k_3565_);
return v___x_3566_;
}
case 1:
{
lean_object* v_k_3567_; lean_object* v___x_3568_; 
lean_dec(v_h__9_3564_);
lean_dec(v_h__8_3563_);
lean_dec(v_h__7_3562_);
lean_dec(v_h__6_3561_);
lean_dec(v_h__5_3560_);
lean_dec(v_h__4_3559_);
lean_dec(v_h__3_3558_);
lean_dec(v_h__1_3556_);
v_k_3567_ = lean_ctor_get(v_x_3555_, 0);
lean_inc(v_k_3567_);
lean_dec_ref_known(v_x_3555_, 1);
v___x_3568_ = lean_apply_1(v_h__2_3557_, v_k_3567_);
return v___x_3568_;
}
case 2:
{
lean_object* v_k_3569_; lean_object* v___x_3570_; 
lean_dec(v_h__9_3564_);
lean_dec(v_h__8_3563_);
lean_dec(v_h__7_3562_);
lean_dec(v_h__6_3561_);
lean_dec(v_h__5_3560_);
lean_dec(v_h__4_3559_);
lean_dec(v_h__2_3557_);
lean_dec(v_h__1_3556_);
v_k_3569_ = lean_ctor_get(v_x_3555_, 0);
lean_inc(v_k_3569_);
lean_dec_ref_known(v_x_3555_, 1);
v___x_3570_ = lean_apply_1(v_h__3_3558_, v_k_3569_);
return v___x_3570_;
}
case 3:
{
lean_object* v_i_3571_; lean_object* v___x_3572_; 
lean_dec(v_h__9_3564_);
lean_dec(v_h__8_3563_);
lean_dec(v_h__7_3562_);
lean_dec(v_h__6_3561_);
lean_dec(v_h__5_3560_);
lean_dec(v_h__3_3558_);
lean_dec(v_h__2_3557_);
lean_dec(v_h__1_3556_);
v_i_3571_ = lean_ctor_get(v_x_3555_, 0);
lean_inc(v_i_3571_);
lean_dec_ref_known(v_x_3555_, 1);
v___x_3572_ = lean_apply_1(v_h__4_3559_, v_i_3571_);
return v___x_3572_;
}
case 4:
{
lean_object* v_a_3573_; lean_object* v___x_3574_; 
lean_dec(v_h__9_3564_);
lean_dec(v_h__8_3563_);
lean_dec(v_h__6_3561_);
lean_dec(v_h__5_3560_);
lean_dec(v_h__4_3559_);
lean_dec(v_h__3_3558_);
lean_dec(v_h__2_3557_);
lean_dec(v_h__1_3556_);
v_a_3573_ = lean_ctor_get(v_x_3555_, 0);
lean_inc_ref(v_a_3573_);
lean_dec_ref_known(v_x_3555_, 1);
v___x_3574_ = lean_apply_1(v_h__7_3562_, v_a_3573_);
return v___x_3574_;
}
case 5:
{
lean_object* v_a_3575_; lean_object* v_b_3576_; lean_object* v___x_3577_; 
lean_dec(v_h__9_3564_);
lean_dec(v_h__8_3563_);
lean_dec(v_h__7_3562_);
lean_dec(v_h__6_3561_);
lean_dec(v_h__4_3559_);
lean_dec(v_h__3_3558_);
lean_dec(v_h__2_3557_);
lean_dec(v_h__1_3556_);
v_a_3575_ = lean_ctor_get(v_x_3555_, 0);
lean_inc_ref(v_a_3575_);
v_b_3576_ = lean_ctor_get(v_x_3555_, 1);
lean_inc_ref(v_b_3576_);
lean_dec_ref_known(v_x_3555_, 2);
v___x_3577_ = lean_apply_2(v_h__5_3560_, v_a_3575_, v_b_3576_);
return v___x_3577_;
}
case 6:
{
lean_object* v_a_3578_; lean_object* v_b_3579_; lean_object* v___x_3580_; 
lean_dec(v_h__9_3564_);
lean_dec(v_h__7_3562_);
lean_dec(v_h__6_3561_);
lean_dec(v_h__5_3560_);
lean_dec(v_h__4_3559_);
lean_dec(v_h__3_3558_);
lean_dec(v_h__2_3557_);
lean_dec(v_h__1_3556_);
v_a_3578_ = lean_ctor_get(v_x_3555_, 0);
lean_inc_ref(v_a_3578_);
v_b_3579_ = lean_ctor_get(v_x_3555_, 1);
lean_inc_ref(v_b_3579_);
lean_dec_ref_known(v_x_3555_, 2);
v___x_3580_ = lean_apply_2(v_h__8_3563_, v_a_3578_, v_b_3579_);
return v___x_3580_;
}
case 7:
{
lean_object* v_a_3581_; lean_object* v_b_3582_; lean_object* v___x_3583_; 
lean_dec(v_h__9_3564_);
lean_dec(v_h__8_3563_);
lean_dec(v_h__7_3562_);
lean_dec(v_h__5_3560_);
lean_dec(v_h__4_3559_);
lean_dec(v_h__3_3558_);
lean_dec(v_h__2_3557_);
lean_dec(v_h__1_3556_);
v_a_3581_ = lean_ctor_get(v_x_3555_, 0);
lean_inc_ref(v_a_3581_);
v_b_3582_ = lean_ctor_get(v_x_3555_, 1);
lean_inc_ref(v_b_3582_);
lean_dec_ref_known(v_x_3555_, 2);
v___x_3583_ = lean_apply_2(v_h__6_3561_, v_a_3581_, v_b_3582_);
return v___x_3583_;
}
default: 
{
lean_object* v_a_3584_; lean_object* v_k_3585_; lean_object* v___x_3586_; 
lean_dec(v_h__8_3563_);
lean_dec(v_h__7_3562_);
lean_dec(v_h__6_3561_);
lean_dec(v_h__5_3560_);
lean_dec(v_h__4_3559_);
lean_dec(v_h__3_3558_);
lean_dec(v_h__2_3557_);
lean_dec(v_h__1_3556_);
v_a_3584_ = lean_ctor_get(v_x_3555_, 0);
lean_inc_ref(v_a_3584_);
v_k_3585_ = lean_ctor_get(v_x_3555_, 1);
lean_inc(v_k_3585_);
lean_dec_ref_known(v_x_3555_, 2);
v___x_3586_ = lean_apply_2(v_h__9_3564_, v_a_3584_, v_k_3585_);
return v___x_3586_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter(lean_object* v_motive_3587_, lean_object* v_x_3588_, lean_object* v_h__1_3589_, lean_object* v_h__2_3590_, lean_object* v_h__3_3591_, lean_object* v_h__4_3592_, lean_object* v_h__5_3593_, lean_object* v_h__6_3594_, lean_object* v_h__7_3595_, lean_object* v_h__8_3596_, lean_object* v_h__9_3597_){
_start:
{
switch(lean_obj_tag(v_x_3588_))
{
case 0:
{
lean_object* v_k_3598_; lean_object* v___x_3599_; 
lean_dec(v_h__9_3597_);
lean_dec(v_h__8_3596_);
lean_dec(v_h__7_3595_);
lean_dec(v_h__6_3594_);
lean_dec(v_h__5_3593_);
lean_dec(v_h__4_3592_);
lean_dec(v_h__3_3591_);
lean_dec(v_h__2_3590_);
v_k_3598_ = lean_ctor_get(v_x_3588_, 0);
lean_inc(v_k_3598_);
lean_dec_ref_known(v_x_3588_, 1);
v___x_3599_ = lean_apply_1(v_h__1_3589_, v_k_3598_);
return v___x_3599_;
}
case 1:
{
lean_object* v_k_3600_; lean_object* v___x_3601_; 
lean_dec(v_h__9_3597_);
lean_dec(v_h__8_3596_);
lean_dec(v_h__7_3595_);
lean_dec(v_h__6_3594_);
lean_dec(v_h__5_3593_);
lean_dec(v_h__4_3592_);
lean_dec(v_h__3_3591_);
lean_dec(v_h__1_3589_);
v_k_3600_ = lean_ctor_get(v_x_3588_, 0);
lean_inc(v_k_3600_);
lean_dec_ref_known(v_x_3588_, 1);
v___x_3601_ = lean_apply_1(v_h__2_3590_, v_k_3600_);
return v___x_3601_;
}
case 2:
{
lean_object* v_k_3602_; lean_object* v___x_3603_; 
lean_dec(v_h__9_3597_);
lean_dec(v_h__8_3596_);
lean_dec(v_h__7_3595_);
lean_dec(v_h__6_3594_);
lean_dec(v_h__5_3593_);
lean_dec(v_h__4_3592_);
lean_dec(v_h__2_3590_);
lean_dec(v_h__1_3589_);
v_k_3602_ = lean_ctor_get(v_x_3588_, 0);
lean_inc(v_k_3602_);
lean_dec_ref_known(v_x_3588_, 1);
v___x_3603_ = lean_apply_1(v_h__3_3591_, v_k_3602_);
return v___x_3603_;
}
case 3:
{
lean_object* v_i_3604_; lean_object* v___x_3605_; 
lean_dec(v_h__9_3597_);
lean_dec(v_h__8_3596_);
lean_dec(v_h__7_3595_);
lean_dec(v_h__6_3594_);
lean_dec(v_h__5_3593_);
lean_dec(v_h__3_3591_);
lean_dec(v_h__2_3590_);
lean_dec(v_h__1_3589_);
v_i_3604_ = lean_ctor_get(v_x_3588_, 0);
lean_inc(v_i_3604_);
lean_dec_ref_known(v_x_3588_, 1);
v___x_3605_ = lean_apply_1(v_h__4_3592_, v_i_3604_);
return v___x_3605_;
}
case 4:
{
lean_object* v_a_3606_; lean_object* v___x_3607_; 
lean_dec(v_h__9_3597_);
lean_dec(v_h__8_3596_);
lean_dec(v_h__6_3594_);
lean_dec(v_h__5_3593_);
lean_dec(v_h__4_3592_);
lean_dec(v_h__3_3591_);
lean_dec(v_h__2_3590_);
lean_dec(v_h__1_3589_);
v_a_3606_ = lean_ctor_get(v_x_3588_, 0);
lean_inc_ref(v_a_3606_);
lean_dec_ref_known(v_x_3588_, 1);
v___x_3607_ = lean_apply_1(v_h__7_3595_, v_a_3606_);
return v___x_3607_;
}
case 5:
{
lean_object* v_a_3608_; lean_object* v_b_3609_; lean_object* v___x_3610_; 
lean_dec(v_h__9_3597_);
lean_dec(v_h__8_3596_);
lean_dec(v_h__7_3595_);
lean_dec(v_h__6_3594_);
lean_dec(v_h__4_3592_);
lean_dec(v_h__3_3591_);
lean_dec(v_h__2_3590_);
lean_dec(v_h__1_3589_);
v_a_3608_ = lean_ctor_get(v_x_3588_, 0);
lean_inc_ref(v_a_3608_);
v_b_3609_ = lean_ctor_get(v_x_3588_, 1);
lean_inc_ref(v_b_3609_);
lean_dec_ref_known(v_x_3588_, 2);
v___x_3610_ = lean_apply_2(v_h__5_3593_, v_a_3608_, v_b_3609_);
return v___x_3610_;
}
case 6:
{
lean_object* v_a_3611_; lean_object* v_b_3612_; lean_object* v___x_3613_; 
lean_dec(v_h__9_3597_);
lean_dec(v_h__7_3595_);
lean_dec(v_h__6_3594_);
lean_dec(v_h__5_3593_);
lean_dec(v_h__4_3592_);
lean_dec(v_h__3_3591_);
lean_dec(v_h__2_3590_);
lean_dec(v_h__1_3589_);
v_a_3611_ = lean_ctor_get(v_x_3588_, 0);
lean_inc_ref(v_a_3611_);
v_b_3612_ = lean_ctor_get(v_x_3588_, 1);
lean_inc_ref(v_b_3612_);
lean_dec_ref_known(v_x_3588_, 2);
v___x_3613_ = lean_apply_2(v_h__8_3596_, v_a_3611_, v_b_3612_);
return v___x_3613_;
}
case 7:
{
lean_object* v_a_3614_; lean_object* v_b_3615_; lean_object* v___x_3616_; 
lean_dec(v_h__9_3597_);
lean_dec(v_h__8_3596_);
lean_dec(v_h__7_3595_);
lean_dec(v_h__5_3593_);
lean_dec(v_h__4_3592_);
lean_dec(v_h__3_3591_);
lean_dec(v_h__2_3590_);
lean_dec(v_h__1_3589_);
v_a_3614_ = lean_ctor_get(v_x_3588_, 0);
lean_inc_ref(v_a_3614_);
v_b_3615_ = lean_ctor_get(v_x_3588_, 1);
lean_inc_ref(v_b_3615_);
lean_dec_ref_known(v_x_3588_, 2);
v___x_3616_ = lean_apply_2(v_h__6_3594_, v_a_3614_, v_b_3615_);
return v___x_3616_;
}
default: 
{
lean_object* v_a_3617_; lean_object* v_k_3618_; lean_object* v___x_3619_; 
lean_dec(v_h__8_3596_);
lean_dec(v_h__7_3595_);
lean_dec(v_h__6_3594_);
lean_dec(v_h__5_3593_);
lean_dec(v_h__4_3592_);
lean_dec(v_h__3_3591_);
lean_dec(v_h__2_3590_);
lean_dec(v_h__1_3589_);
v_a_3617_ = lean_ctor_get(v_x_3588_, 0);
lean_inc_ref(v_a_3617_);
v_k_3618_ = lean_ctor_get(v_x_3588_, 1);
lean_inc(v_k_3618_);
lean_dec_ref_known(v_x_3588_, 2);
v___x_3619_ = lean_apply_2(v_h__9_3597_, v_a_3617_, v_k_3618_);
return v___x_3619_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter___redArg(lean_object* v_a_3620_, lean_object* v_h__1_3621_, lean_object* v_h__2_3622_, lean_object* v_h__3_3623_){
_start:
{
switch(lean_obj_tag(v_a_3620_))
{
case 0:
{
lean_object* v_k_3624_; lean_object* v___x_3625_; 
lean_dec(v_h__3_3623_);
lean_dec(v_h__2_3622_);
v_k_3624_ = lean_ctor_get(v_a_3620_, 0);
lean_inc(v_k_3624_);
lean_dec_ref_known(v_a_3620_, 1);
v___x_3625_ = lean_apply_1(v_h__1_3621_, v_k_3624_);
return v___x_3625_;
}
case 3:
{
lean_object* v_i_3626_; lean_object* v___x_3627_; 
lean_dec(v_h__3_3623_);
lean_dec(v_h__1_3621_);
v_i_3626_ = lean_ctor_get(v_a_3620_, 0);
lean_inc(v_i_3626_);
lean_dec_ref_known(v_a_3620_, 1);
v___x_3627_ = lean_apply_1(v_h__2_3622_, v_i_3626_);
return v___x_3627_;
}
default: 
{
lean_object* v___x_3628_; 
lean_dec(v_h__2_3622_);
lean_dec(v_h__1_3621_);
v___x_3628_ = lean_apply_3(v_h__3_3623_, v_a_3620_, lean_box(0), lean_box(0));
return v___x_3628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter(lean_object* v_motive_3629_, lean_object* v_a_3630_, lean_object* v_h__1_3631_, lean_object* v_h__2_3632_, lean_object* v_h__3_3633_){
_start:
{
switch(lean_obj_tag(v_a_3630_))
{
case 0:
{
lean_object* v_k_3634_; lean_object* v___x_3635_; 
lean_dec(v_h__3_3633_);
lean_dec(v_h__2_3632_);
v_k_3634_ = lean_ctor_get(v_a_3630_, 0);
lean_inc(v_k_3634_);
lean_dec_ref_known(v_a_3630_, 1);
v___x_3635_ = lean_apply_1(v_h__1_3631_, v_k_3634_);
return v___x_3635_;
}
case 3:
{
lean_object* v_i_3636_; lean_object* v___x_3637_; 
lean_dec(v_h__3_3633_);
lean_dec(v_h__1_3631_);
v_i_3636_ = lean_ctor_get(v_a_3630_, 0);
lean_inc(v_i_3636_);
lean_dec_ref_known(v_a_3630_, 1);
v___x_3637_ = lean_apply_1(v_h__2_3632_, v_i_3636_);
return v___x_3637_;
}
default: 
{
lean_object* v___x_3638_; 
lean_dec(v_h__2_3632_);
lean_dec(v_h__1_3631_);
v___x_3638_ = lean_apply_3(v_h__3_3633_, v_a_3630_, lean_box(0), lean_box(0));
return v___x_3638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(lean_object* v_inst_3639_, lean_object* v_ctx_3640_, lean_object* v_m_3641_, lean_object* v_acc_3642_){
_start:
{
if (lean_obj_tag(v_m_3641_) == 0)
{
lean_dec_ref(v_inst_3639_);
return v_acc_3642_;
}
else
{
lean_object* v_toSemiring_3643_; lean_object* v_toMul_3644_; lean_object* v_ofNat_3645_; lean_object* v_npow_3646_; lean_object* v_p_3647_; lean_object* v_m_3648_; lean_object* v___y_3650_; lean_object* v_x_3653_; lean_object* v_k_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; 
v_toSemiring_3643_ = lean_ctor_get(v_inst_3639_, 0);
v_toMul_3644_ = lean_ctor_get(v_toSemiring_3643_, 1);
v_ofNat_3645_ = lean_ctor_get(v_toSemiring_3643_, 3);
v_npow_3646_ = lean_ctor_get(v_toSemiring_3643_, 5);
v_p_3647_ = lean_ctor_get(v_m_3641_, 0);
lean_inc_ref(v_p_3647_);
v_m_3648_ = lean_ctor_get(v_m_3641_, 1);
lean_inc(v_m_3648_);
lean_dec_ref_known(v_m_3641_, 2);
v_x_3653_ = lean_ctor_get(v_p_3647_, 0);
lean_inc(v_x_3653_);
v_k_3654_ = lean_ctor_get(v_p_3647_, 1);
lean_inc(v_k_3654_);
lean_dec_ref(v_p_3647_);
v___x_3655_ = lean_unsigned_to_nat(0u);
v___x_3656_ = lean_nat_dec_eq(v_k_3654_, v___x_3655_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; uint8_t v___x_3658_; 
v___x_3657_ = lean_unsigned_to_nat(1u);
v___x_3658_ = lean_nat_dec_eq(v_k_3654_, v___x_3657_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = l_Lean_RArray_getImpl___redArg(v_ctx_3640_, v_x_3653_);
lean_dec(v_x_3653_);
lean_inc(v_npow_3646_);
v___x_3660_ = lean_apply_2(v_npow_3646_, v___x_3659_, v_k_3654_);
v___y_3650_ = v___x_3660_;
goto v___jp_3649_;
}
else
{
lean_object* v___x_3661_; 
lean_dec(v_k_3654_);
v___x_3661_ = l_Lean_RArray_getImpl___redArg(v_ctx_3640_, v_x_3653_);
lean_dec(v_x_3653_);
v___y_3650_ = v___x_3661_;
goto v___jp_3649_;
}
}
else
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
lean_dec(v_k_3654_);
lean_dec(v_x_3653_);
v___x_3662_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3645_);
v___x_3663_ = lean_apply_1(v_ofNat_3645_, v___x_3662_);
v___y_3650_ = v___x_3663_;
goto v___jp_3649_;
}
v___jp_3649_:
{
lean_object* v___x_3651_; 
lean_inc(v_toMul_3644_);
v___x_3651_ = lean_apply_2(v_toMul_3644_, v_acc_3642_, v___y_3650_);
v_m_3641_ = v_m_3648_;
v_acc_3642_ = v___x_3651_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg___boxed(lean_object* v_inst_3664_, lean_object* v_ctx_3665_, lean_object* v_m_3666_, lean_object* v_acc_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3664_, v_ctx_3665_, v_m_3666_, v_acc_3667_);
lean_dec_ref(v_ctx_3665_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(lean_object* v_00_u03b1_3669_, lean_object* v_inst_3670_, lean_object* v_ctx_3671_, lean_object* v_m_3672_, lean_object* v_acc_3673_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3670_, v_ctx_3671_, v_m_3672_, v_acc_3673_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___boxed(lean_object* v_00_u03b1_3675_, lean_object* v_inst_3676_, lean_object* v_ctx_3677_, lean_object* v_m_3678_, lean_object* v_acc_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(v_00_u03b1_3675_, v_inst_3676_, v_ctx_3677_, v_m_3678_, v_acc_3679_);
lean_dec_ref(v_ctx_3677_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(lean_object* v_inst_3681_, lean_object* v_ctx_3682_, lean_object* v_m_3683_){
_start:
{
if (lean_obj_tag(v_m_3683_) == 0)
{
lean_object* v_toSemiring_3684_; lean_object* v_ofNat_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v_toSemiring_3684_ = lean_ctor_get(v_inst_3681_, 0);
lean_inc_ref(v_toSemiring_3684_);
lean_dec_ref(v_inst_3681_);
v_ofNat_3685_ = lean_ctor_get(v_toSemiring_3684_, 3);
lean_inc(v_ofNat_3685_);
lean_dec_ref(v_toSemiring_3684_);
v___x_3686_ = lean_unsigned_to_nat(1u);
v___x_3687_ = lean_apply_1(v_ofNat_3685_, v___x_3686_);
return v___x_3687_;
}
else
{
lean_object* v_toSemiring_3688_; lean_object* v_p_3689_; lean_object* v_m_3690_; lean_object* v_ofNat_3691_; lean_object* v_npow_3692_; lean_object* v_x_3693_; lean_object* v_k_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; 
v_toSemiring_3688_ = lean_ctor_get(v_inst_3681_, 0);
v_p_3689_ = lean_ctor_get(v_m_3683_, 0);
lean_inc_ref(v_p_3689_);
v_m_3690_ = lean_ctor_get(v_m_3683_, 1);
lean_inc(v_m_3690_);
lean_dec_ref_known(v_m_3683_, 2);
v_ofNat_3691_ = lean_ctor_get(v_toSemiring_3688_, 3);
v_npow_3692_ = lean_ctor_get(v_toSemiring_3688_, 5);
v_x_3693_ = lean_ctor_get(v_p_3689_, 0);
lean_inc(v_x_3693_);
v_k_3694_ = lean_ctor_get(v_p_3689_, 1);
lean_inc(v_k_3694_);
lean_dec_ref(v_p_3689_);
v___x_3695_ = lean_unsigned_to_nat(0u);
v___x_3696_ = lean_nat_dec_eq(v_k_3694_, v___x_3695_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3697_; uint8_t v___x_3698_; 
v___x_3697_ = lean_unsigned_to_nat(1u);
v___x_3698_ = lean_nat_dec_eq(v_k_3694_, v___x_3697_);
if (v___x_3698_ == 0)
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3699_ = l_Lean_RArray_getImpl___redArg(v_ctx_3682_, v_x_3693_);
lean_dec(v_x_3693_);
lean_inc(v_npow_3692_);
v___x_3700_ = lean_apply_2(v_npow_3692_, v___x_3699_, v_k_3694_);
v___x_3701_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3681_, v_ctx_3682_, v_m_3690_, v___x_3700_);
return v___x_3701_;
}
else
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
lean_dec(v_k_3694_);
v___x_3702_ = l_Lean_RArray_getImpl___redArg(v_ctx_3682_, v_x_3693_);
lean_dec(v_x_3693_);
v___x_3703_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3681_, v_ctx_3682_, v_m_3690_, v___x_3702_);
return v___x_3703_;
}
}
else
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
lean_dec(v_k_3694_);
lean_dec(v_x_3693_);
v___x_3704_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3691_);
v___x_3705_ = lean_apply_1(v_ofNat_3691_, v___x_3704_);
v___x_3706_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3681_, v_ctx_3682_, v_m_3690_, v___x_3705_);
return v___x_3706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3707_, lean_object* v_ctx_3708_, lean_object* v_m_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3707_, v_ctx_3708_, v_m_3709_);
lean_dec_ref(v_ctx_3708_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule(lean_object* v_00_u03b1_3711_, lean_object* v_inst_3712_, lean_object* v_ctx_3713_, lean_object* v_m_3714_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3712_, v_ctx_3713_, v_m_3714_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3716_, lean_object* v_inst_3717_, lean_object* v_ctx_3718_, lean_object* v_m_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule(v_00_u03b1_3716_, v_inst_3717_, v_ctx_3718_, v_m_3719_);
lean_dec_ref(v_ctx_3718_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(lean_object* v_inst_3721_, lean_object* v_ctx_3722_, lean_object* v_p_3723_){
_start:
{
lean_object* v___x_3724_; 
lean_inc_ref(v_inst_3721_);
v___x_3724_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_3721_);
if (lean_obj_tag(v_p_3723_) == 0)
{
lean_object* v_toSemiring_3725_; lean_object* v_zsmul_3726_; lean_object* v_ofNat_3727_; lean_object* v_k_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_toSemiring_3725_ = lean_ctor_get(v_inst_3721_, 0);
lean_inc_ref(v_toSemiring_3725_);
lean_dec_ref(v_inst_3721_);
v_zsmul_3726_ = lean_ctor_get(v___x_3724_, 2);
lean_inc(v_zsmul_3726_);
lean_dec_ref(v___x_3724_);
v_ofNat_3727_ = lean_ctor_get(v_toSemiring_3725_, 3);
lean_inc(v_ofNat_3727_);
lean_dec_ref(v_toSemiring_3725_);
v_k_3728_ = lean_ctor_get(v_p_3723_, 0);
lean_inc(v_k_3728_);
lean_dec_ref_known(v_p_3723_, 1);
v___x_3729_ = lean_unsigned_to_nat(1u);
v___x_3730_ = lean_apply_1(v_ofNat_3727_, v___x_3729_);
v___x_3731_ = lean_apply_2(v_zsmul_3726_, v_k_3728_, v___x_3730_);
return v___x_3731_;
}
else
{
lean_object* v_toSemiring_3732_; lean_object* v_zsmul_3733_; lean_object* v_toAdd_3734_; lean_object* v_k_3735_; lean_object* v_v_3736_; lean_object* v_p_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v_toSemiring_3732_ = lean_ctor_get(v_inst_3721_, 0);
v_zsmul_3733_ = lean_ctor_get(v___x_3724_, 2);
lean_inc(v_zsmul_3733_);
lean_dec_ref(v___x_3724_);
v_toAdd_3734_ = lean_ctor_get(v_toSemiring_3732_, 0);
lean_inc(v_toAdd_3734_);
v_k_3735_ = lean_ctor_get(v_p_3723_, 0);
lean_inc(v_k_3735_);
v_v_3736_ = lean_ctor_get(v_p_3723_, 1);
lean_inc(v_v_3736_);
v_p_3737_ = lean_ctor_get(v_p_3723_, 2);
lean_inc_ref(v_p_3737_);
lean_dec_ref_known(v_p_3723_, 3);
lean_inc_ref(v_inst_3721_);
v___x_3738_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3721_, v_ctx_3722_, v_v_3736_);
v___x_3739_ = lean_apply_2(v_zsmul_3733_, v_k_3735_, v___x_3738_);
v___x_3740_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3721_, v_ctx_3722_, v_p_3737_);
v___x_3741_ = lean_apply_2(v_toAdd_3734_, v___x_3739_, v___x_3740_);
return v___x_3741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3742_, lean_object* v_ctx_3743_, lean_object* v_p_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3742_, v_ctx_3743_, v_p_3744_);
lean_dec_ref(v_ctx_3743_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule(lean_object* v_00_u03b1_3746_, lean_object* v_inst_3747_, lean_object* v_ctx_3748_, lean_object* v_p_3749_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3747_, v_ctx_3748_, v_p_3749_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3751_, lean_object* v_inst_3752_, lean_object* v_ctx_3753_, lean_object* v_p_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule(v_00_u03b1_3751_, v_inst_3752_, v_ctx_3753_, v_p_3754_);
lean_dec_ref(v_ctx_3753_);
return v_res_3755_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__gcd__cert(lean_object* v_a_3756_, lean_object* v_b_3757_, lean_object* v_p_u2081_3758_, lean_object* v_p_u2082_3759_, lean_object* v_p_3760_){
_start:
{
if (lean_obj_tag(v_p_u2081_3758_) == 0)
{
if (lean_obj_tag(v_p_u2082_3759_) == 0)
{
if (lean_obj_tag(v_p_3760_) == 0)
{
lean_object* v_k_3761_; lean_object* v_k_3762_; lean_object* v_k_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; uint8_t v___x_3767_; 
v_k_3761_ = lean_ctor_get(v_p_u2081_3758_, 0);
v_k_3762_ = lean_ctor_get(v_p_u2082_3759_, 0);
v_k_3763_ = lean_ctor_get(v_p_3760_, 0);
v___x_3764_ = lean_int_mul(v_a_3756_, v_k_3761_);
v___x_3765_ = lean_int_mul(v_b_3757_, v_k_3762_);
v___x_3766_ = lean_int_add(v___x_3764_, v___x_3765_);
lean_dec(v___x_3765_);
lean_dec(v___x_3764_);
v___x_3767_ = lean_int_dec_eq(v_k_3763_, v___x_3766_);
lean_dec(v___x_3766_);
return v___x_3767_;
}
else
{
uint8_t v___x_3768_; 
v___x_3768_ = 0;
return v___x_3768_;
}
}
else
{
uint8_t v___x_3769_; 
v___x_3769_ = 0;
return v___x_3769_;
}
}
else
{
uint8_t v___x_3770_; 
v___x_3770_ = 0;
return v___x_3770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__gcd__cert___boxed(lean_object* v_a_3771_, lean_object* v_b_3772_, lean_object* v_p_u2081_3773_, lean_object* v_p_u2082_3774_, lean_object* v_p_3775_){
_start:
{
uint8_t v_res_3776_; lean_object* v_r_3777_; 
v_res_3776_ = l_Lean_Grind_CommRing_eq__gcd__cert(v_a_3771_, v_b_3772_, v_p_u2081_3773_, v_p_u2082_3774_, v_p_3775_);
lean_dec_ref(v_p_3775_);
lean_dec_ref(v_p_u2082_3774_);
lean_dec_ref(v_p_u2081_3773_);
lean_dec(v_b_3772_);
lean_dec(v_a_3771_);
v_r_3777_ = lean_box(v_res_3776_);
return v_r_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(lean_object* v_p_3778_, lean_object* v_h__1_3779_, lean_object* v_h__2_3780_){
_start:
{
if (lean_obj_tag(v_p_3778_) == 0)
{
lean_object* v_k_3781_; lean_object* v___x_3782_; 
lean_dec(v_h__1_3779_);
v_k_3781_ = lean_ctor_get(v_p_3778_, 0);
lean_inc(v_k_3781_);
lean_dec_ref_known(v_p_3778_, 1);
v___x_3782_ = lean_apply_1(v_h__2_3780_, v_k_3781_);
return v___x_3782_;
}
else
{
lean_object* v_k_3783_; lean_object* v_v_3784_; lean_object* v_p_3785_; lean_object* v___x_3786_; 
lean_dec(v_h__2_3780_);
v_k_3783_ = lean_ctor_get(v_p_3778_, 0);
lean_inc(v_k_3783_);
v_v_3784_ = lean_ctor_get(v_p_3778_, 1);
lean_inc(v_v_3784_);
v_p_3785_ = lean_ctor_get(v_p_3778_, 2);
lean_inc_ref(v_p_3785_);
lean_dec_ref_known(v_p_3778_, 3);
v___x_3786_ = lean_apply_3(v_h__1_3779_, v_k_3783_, v_v_3784_, v_p_3785_);
return v___x_3786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter(lean_object* v_motive_3787_, lean_object* v_p_3788_, lean_object* v_h__1_3789_, lean_object* v_h__2_3790_){
_start:
{
if (lean_obj_tag(v_p_3788_) == 0)
{
lean_object* v_k_3791_; lean_object* v___x_3792_; 
lean_dec(v_h__1_3789_);
v_k_3791_ = lean_ctor_get(v_p_3788_, 0);
lean_inc(v_k_3791_);
lean_dec_ref_known(v_p_3788_, 1);
v___x_3792_ = lean_apply_1(v_h__2_3790_, v_k_3791_);
return v___x_3792_;
}
else
{
lean_object* v_k_3793_; lean_object* v_v_3794_; lean_object* v_p_3795_; lean_object* v___x_3796_; 
lean_dec(v_h__2_3790_);
v_k_3793_ = lean_ctor_get(v_p_3788_, 0);
lean_inc(v_k_3793_);
v_v_3794_ = lean_ctor_get(v_p_3788_, 1);
lean_inc(v_v_3794_);
v_p_3795_ = lean_ctor_get(v_p_3788_, 2);
lean_inc_ref(v_p_3795_);
lean_dec_ref_known(v_p_3788_, 3);
v___x_3796_ = lean_apply_3(v_h__1_3789_, v_k_3793_, v_v_3794_, v_p_3795_);
return v___x_3796_;
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
