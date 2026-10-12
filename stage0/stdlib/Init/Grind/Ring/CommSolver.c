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
uint8_t l_Lean_Grind_CommRing_instBEqExpr_beq(lean_object* v_x_113_, lean_object* v_x_114_){
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
LEAN_EXPORT void l_Lean_Grind_CommRing_instBEqExpr_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_113_ = stack[0].m_obj;
lean_object* v_x_114_ = stack[1].m_obj;
uint8_t v_res_164_;
v_res_164_ = l_Lean_Grind_CommRing_instBEqExpr_beq(v_x_113_, v_x_114_);
stack->m_num = v_res_164_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqExpr_beq___boxed(lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Lean_Grind_CommRing_instBEqExpr_beq(v_x_165_, v_x_166_);
lean_dec_ref(v_x_166_);
lean_dec_ref(v_x_165_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
uint64_t l_Lean_Grind_CommRing_instHashableExpr_hash(lean_object* v_x_171_){
_start:
{
switch(lean_obj_tag(v_x_171_))
{
case 0:
{
lean_object* v_k_172_; uint64_t v___x_173_; lean_object* v_intZero_174_; uint8_t v_isNeg_175_; 
v_k_172_ = lean_ctor_get(v_x_171_, 0);
v___x_173_ = 0ULL;
v_intZero_174_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_175_ = lean_int_dec_lt(v_k_172_, v_intZero_174_);
if (v_isNeg_175_ == 0)
{
lean_object* v_a_176_; lean_object* v___x_177_; lean_object* v___x_178_; uint64_t v___x_179_; uint64_t v___x_180_; 
v_a_176_ = lean_nat_abs(v_k_172_);
v___x_177_ = lean_unsigned_to_nat(2u);
v___x_178_ = lean_nat_mul(v___x_177_, v_a_176_);
lean_dec(v_a_176_);
v___x_179_ = lean_uint64_of_nat(v___x_178_);
lean_dec(v___x_178_);
v___x_180_ = lean_uint64_mix_hash(v___x_173_, v___x_179_);
return v___x_180_;
}
else
{
lean_object* v_abs_181_; lean_object* v_one_182_; lean_object* v_a_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint64_t v___x_187_; uint64_t v___x_188_; 
v_abs_181_ = lean_nat_abs(v_k_172_);
v_one_182_ = lean_unsigned_to_nat(1u);
v_a_183_ = lean_nat_sub(v_abs_181_, v_one_182_);
lean_dec(v_abs_181_);
v___x_184_ = lean_unsigned_to_nat(2u);
v___x_185_ = lean_nat_mul(v___x_184_, v_a_183_);
lean_dec(v_a_183_);
v___x_186_ = lean_nat_add(v___x_185_, v_one_182_);
lean_dec(v___x_185_);
v___x_187_ = lean_uint64_of_nat(v___x_186_);
lean_dec(v___x_186_);
v___x_188_ = lean_uint64_mix_hash(v___x_173_, v___x_187_);
return v___x_188_;
}
}
case 1:
{
lean_object* v_k_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; 
v_k_189_ = lean_ctor_get(v_x_171_, 0);
v___x_190_ = 1ULL;
v___x_191_ = lean_uint64_of_nat(v_k_189_);
v___x_192_ = lean_uint64_mix_hash(v___x_190_, v___x_191_);
return v___x_192_;
}
case 2:
{
lean_object* v_k_193_; uint64_t v___x_194_; lean_object* v_intZero_195_; uint8_t v_isNeg_196_; 
v_k_193_ = lean_ctor_get(v_x_171_, 0);
v___x_194_ = 2ULL;
v_intZero_195_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_196_ = lean_int_dec_lt(v_k_193_, v_intZero_195_);
if (v_isNeg_196_ == 0)
{
lean_object* v_a_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint64_t v___x_200_; uint64_t v___x_201_; 
v_a_197_ = lean_nat_abs(v_k_193_);
v___x_198_ = lean_unsigned_to_nat(2u);
v___x_199_ = lean_nat_mul(v___x_198_, v_a_197_);
lean_dec(v_a_197_);
v___x_200_ = lean_uint64_of_nat(v___x_199_);
lean_dec(v___x_199_);
v___x_201_ = lean_uint64_mix_hash(v___x_194_, v___x_200_);
return v___x_201_;
}
else
{
lean_object* v_abs_202_; lean_object* v_one_203_; lean_object* v_a_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint64_t v___x_208_; uint64_t v___x_209_; 
v_abs_202_ = lean_nat_abs(v_k_193_);
v_one_203_ = lean_unsigned_to_nat(1u);
v_a_204_ = lean_nat_sub(v_abs_202_, v_one_203_);
lean_dec(v_abs_202_);
v___x_205_ = lean_unsigned_to_nat(2u);
v___x_206_ = lean_nat_mul(v___x_205_, v_a_204_);
lean_dec(v_a_204_);
v___x_207_ = lean_nat_add(v___x_206_, v_one_203_);
lean_dec(v___x_206_);
v___x_208_ = lean_uint64_of_nat(v___x_207_);
lean_dec(v___x_207_);
v___x_209_ = lean_uint64_mix_hash(v___x_194_, v___x_208_);
return v___x_209_;
}
}
case 3:
{
lean_object* v_i_210_; uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; 
v_i_210_ = lean_ctor_get(v_x_171_, 0);
v___x_211_ = 3ULL;
v___x_212_ = lean_uint64_of_nat(v_i_210_);
v___x_213_ = lean_uint64_mix_hash(v___x_211_, v___x_212_);
return v___x_213_;
}
case 4:
{
lean_object* v_a_214_; uint64_t v___x_215_; uint64_t v___x_216_; uint64_t v___x_217_; 
v_a_214_ = lean_ctor_get(v_x_171_, 0);
v___x_215_ = 4ULL;
v___x_216_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_214_);
v___x_217_ = lean_uint64_mix_hash(v___x_215_, v___x_216_);
return v___x_217_;
}
case 5:
{
lean_object* v_a_218_; lean_object* v_b_219_; uint64_t v___x_220_; uint64_t v___x_221_; uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v___x_224_; 
v_a_218_ = lean_ctor_get(v_x_171_, 0);
v_b_219_ = lean_ctor_get(v_x_171_, 1);
v___x_220_ = 5ULL;
v___x_221_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_218_);
v___x_222_ = lean_uint64_mix_hash(v___x_220_, v___x_221_);
v___x_223_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_219_);
v___x_224_ = lean_uint64_mix_hash(v___x_222_, v___x_223_);
return v___x_224_;
}
case 6:
{
lean_object* v_a_225_; lean_object* v_b_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v___x_231_; 
v_a_225_ = lean_ctor_get(v_x_171_, 0);
v_b_226_ = lean_ctor_get(v_x_171_, 1);
v___x_227_ = 6ULL;
v___x_228_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_225_);
v___x_229_ = lean_uint64_mix_hash(v___x_227_, v___x_228_);
v___x_230_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_226_);
v___x_231_ = lean_uint64_mix_hash(v___x_229_, v___x_230_);
return v___x_231_;
}
case 7:
{
lean_object* v_a_232_; lean_object* v_b_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; 
v_a_232_ = lean_ctor_get(v_x_171_, 0);
v_b_233_ = lean_ctor_get(v_x_171_, 1);
v___x_234_ = 7ULL;
v___x_235_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_232_);
v___x_236_ = lean_uint64_mix_hash(v___x_234_, v___x_235_);
v___x_237_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_b_233_);
v___x_238_ = lean_uint64_mix_hash(v___x_236_, v___x_237_);
return v___x_238_;
}
default: 
{
lean_object* v_a_239_; lean_object* v_k_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; 
v_a_239_ = lean_ctor_get(v_x_171_, 0);
v_k_240_ = lean_ctor_get(v_x_171_, 1);
v___x_241_ = 8ULL;
v___x_242_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_a_239_);
v___x_243_ = lean_uint64_mix_hash(v___x_241_, v___x_242_);
v___x_244_ = lean_uint64_of_nat(v_k_240_);
v___x_245_ = lean_uint64_mix_hash(v___x_243_, v___x_244_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_instHashableExpr_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_171_ = stack[0].m_obj;
uint64_t v_res_246_;
v_res_246_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_x_171_);
stack->m_num = v_res_246_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableExpr_hash___boxed(lean_object* v_x_247_){
_start:
{
uint64_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Lean_Grind_CommRing_instHashableExpr_hash(v_x_247_);
lean_dec_ref(v_x_247_);
v_r_249_ = lean_box_uint64(v_res_248_);
return v_r_249_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(2u);
v___x_259_ = lean_nat_to_int(v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_nat_to_int(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprExpr_repr(lean_object* v_x_310_, lean_object* v_prec_311_){
_start:
{
lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; 
switch(lean_obj_tag(v_x_310_))
{
case 0:
{
lean_object* v_k_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_353_; 
v_k_330_ = lean_ctor_get(v_x_310_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v_x_310_);
if (v_isSharedCheck_353_ == 0)
{
v___x_332_ = v_x_310_;
v_isShared_333_ = v_isSharedCheck_353_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_k_330_);
lean_dec(v_x_310_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_353_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___y_335_; lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = lean_unsigned_to_nat(1024u);
v___x_350_ = lean_nat_dec_le(v___x_349_, v_prec_311_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; 
v___x_351_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_335_ = v___x_351_;
goto v___jp_334_;
}
else
{
lean_object* v___x_352_; 
v___x_352_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_335_ = v___x_352_;
goto v___jp_334_;
}
v___jp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__2));
v___x_337_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_338_ = lean_int_dec_lt(v_k_330_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_339_ = l_Int_repr(v_k_330_);
lean_dec(v_k_330_);
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 3);
lean_ctor_set(v___x_332_, 0, v___x_339_);
v___x_341_ = v___x_332_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
v___y_322_ = v___x_336_;
v___y_323_ = v___y_335_;
v___y_324_ = v___x_341_;
goto v___jp_321_;
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_343_ = lean_unsigned_to_nat(1024u);
v___x_344_ = l_Int_repr(v_k_330_);
lean_dec(v_k_330_);
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 3);
lean_ctor_set(v___x_332_, 0, v___x_344_);
v___x_346_ = v___x_332_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_348_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; 
v___x_347_ = l_Repr_addAppParen(v___x_346_, v___x_343_);
v___y_322_ = v___x_336_;
v___y_323_ = v___y_335_;
v___y_324_ = v___x_347_;
goto v___jp_321_;
}
}
}
}
}
case 1:
{
lean_object* v_k_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_374_; 
v_k_354_ = lean_ctor_get(v_x_310_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v_x_310_);
if (v_isSharedCheck_374_ == 0)
{
v___x_356_ = v_x_310_;
v_isShared_357_ = v_isSharedCheck_374_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_k_354_);
lean_dec(v_x_310_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_374_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___y_359_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = lean_unsigned_to_nat(1024u);
v___x_371_ = lean_nat_dec_le(v___x_370_, v_prec_311_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
v___x_372_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_359_ = v___x_372_;
goto v___jp_358_;
}
else
{
lean_object* v___x_373_; 
v___x_373_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_359_ = v___x_373_;
goto v___jp_358_;
}
v___jp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_360_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__7));
v___x_361_ = l_Nat_reprFast(v_k_354_);
if (v_isShared_357_ == 0)
{
lean_ctor_set_tag(v___x_356_, 3);
lean_ctor_set(v___x_356_, 0, v___x_361_);
v___x_363_ = v___x_356_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_369_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_360_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
lean_inc(v___y_359_);
v___x_365_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_365_, 0, v___y_359_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = 0;
v___x_367_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1, v___x_366_);
v___x_368_ = l_Repr_addAppParen(v___x_367_, v_prec_311_);
return v___x_368_;
}
}
}
}
case 2:
{
lean_object* v_k_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_398_; 
v_k_375_ = lean_ctor_get(v_x_310_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v_x_310_);
if (v_isSharedCheck_398_ == 0)
{
v___x_377_ = v_x_310_;
v_isShared_378_ = v_isSharedCheck_398_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_k_375_);
lean_dec(v_x_310_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_398_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___y_380_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_unsigned_to_nat(1024u);
v___x_395_ = lean_nat_dec_le(v___x_394_, v_prec_311_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
v___x_396_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_380_ = v___x_396_;
goto v___jp_379_;
}
else
{
lean_object* v___x_397_; 
v___x_397_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_380_ = v___x_397_;
goto v___jp_379_;
}
v___jp_379_:
{
lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_381_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__10));
v___x_382_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_383_ = lean_int_dec_lt(v_k_375_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_384_ = l_Int_repr(v_k_375_);
lean_dec(v_k_375_);
if (v_isShared_378_ == 0)
{
lean_ctor_set_tag(v___x_377_, 3);
lean_ctor_set(v___x_377_, 0, v___x_384_);
v___x_386_ = v___x_377_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
v___y_313_ = v___x_381_;
v___y_314_ = v___y_380_;
v___y_315_ = v___x_386_;
goto v___jp_312_;
}
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_388_ = lean_unsigned_to_nat(1024u);
v___x_389_ = l_Int_repr(v_k_375_);
lean_dec(v_k_375_);
if (v_isShared_378_ == 0)
{
lean_ctor_set_tag(v___x_377_, 3);
lean_ctor_set(v___x_377_, 0, v___x_389_);
v___x_391_ = v___x_377_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_389_);
v___x_391_ = v_reuseFailAlloc_393_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; 
v___x_392_ = l_Repr_addAppParen(v___x_391_, v___x_388_);
v___y_313_ = v___x_381_;
v___y_314_ = v___y_380_;
v___y_315_ = v___x_392_;
goto v___jp_312_;
}
}
}
}
}
case 3:
{
lean_object* v_i_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_419_; 
v_i_399_ = lean_ctor_get(v_x_310_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_x_310_);
if (v_isSharedCheck_419_ == 0)
{
v___x_401_ = v_x_310_;
v_isShared_402_ = v_isSharedCheck_419_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_i_399_);
lean_dec(v_x_310_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_419_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___y_404_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = lean_unsigned_to_nat(1024u);
v___x_416_ = lean_nat_dec_le(v___x_415_, v_prec_311_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
v___x_417_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_404_ = v___x_417_;
goto v___jp_403_;
}
else
{
lean_object* v___x_418_; 
v___x_418_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_404_ = v___x_418_;
goto v___jp_403_;
}
v___jp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_405_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__13));
v___x_406_ = l_Nat_reprFast(v_i_399_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_406_);
v___x_408_ = v___x_401_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_414_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_405_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
lean_inc(v___y_404_);
v___x_410_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_410_, 0, v___y_404_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = 0;
v___x_412_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*1, v___x_411_);
v___x_413_ = l_Repr_addAppParen(v___x_412_, v_prec_311_);
return v___x_413_;
}
}
}
}
case 4:
{
lean_object* v_a_420_; lean_object* v___x_421_; lean_object* v___y_423_; uint8_t v___x_431_; 
v_a_420_ = lean_ctor_get(v_x_310_, 0);
lean_inc_ref(v_a_420_);
lean_dec_ref_known(v_x_310_, 1);
v___x_421_ = lean_unsigned_to_nat(1024u);
v___x_431_ = lean_nat_dec_le(v___x_421_, v_prec_311_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
v___x_432_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_423_ = v___x_432_;
goto v___jp_422_;
}
else
{
lean_object* v___x_433_; 
v___x_433_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_423_ = v___x_433_;
goto v___jp_422_;
}
v___jp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_424_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__16));
v___x_425_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_420_, v___x_421_);
v___x_426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
lean_inc(v___y_423_);
v___x_427_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_427_, 0, v___y_423_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = 0;
v___x_429_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set_uint8(v___x_429_, sizeof(void*)*1, v___x_428_);
v___x_430_ = l_Repr_addAppParen(v___x_429_, v_prec_311_);
return v___x_430_;
}
}
case 5:
{
lean_object* v_a_434_; lean_object* v_b_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_458_; 
v_a_434_ = lean_ctor_get(v_x_310_, 0);
v_b_435_ = lean_ctor_get(v_x_310_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_310_);
if (v_isSharedCheck_458_ == 0)
{
v___x_437_ = v_x_310_;
v_isShared_438_ = v_isSharedCheck_458_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_b_435_);
lean_inc(v_a_434_);
lean_dec(v_x_310_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_458_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___y_441_; uint8_t v___x_455_; 
v___x_439_ = lean_unsigned_to_nat(1024u);
v___x_455_ = lean_nat_dec_le(v___x_439_, v_prec_311_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
v___x_456_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_441_ = v___x_456_;
goto v___jp_440_;
}
else
{
lean_object* v___x_457_; 
v___x_457_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_441_ = v___x_457_;
goto v___jp_440_;
}
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_442_ = lean_box(1);
v___x_443_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__19));
v___x_444_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_434_, v___x_439_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v___x_444_);
lean_ctor_set(v___x_437_, 0, v___x_443_);
v___x_446_ = v___x_437_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___x_444_);
v___x_446_ = v_reuseFailAlloc_454_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_442_);
v___x_448_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_435_, v___x_439_);
v___x_449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
lean_inc(v___y_441_);
v___x_450_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_450_, 0, v___y_441_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = 0;
v___x_452_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set_uint8(v___x_452_, sizeof(void*)*1, v___x_451_);
v___x_453_ = l_Repr_addAppParen(v___x_452_, v_prec_311_);
return v___x_453_;
}
}
}
}
case 6:
{
lean_object* v_a_459_; lean_object* v_b_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_483_; 
v_a_459_ = lean_ctor_get(v_x_310_, 0);
v_b_460_ = lean_ctor_get(v_x_310_, 1);
v_isSharedCheck_483_ = !lean_is_exclusive(v_x_310_);
if (v_isSharedCheck_483_ == 0)
{
v___x_462_ = v_x_310_;
v_isShared_463_ = v_isSharedCheck_483_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_b_460_);
lean_inc(v_a_459_);
lean_dec(v_x_310_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_483_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___y_466_; uint8_t v___x_480_; 
v___x_464_ = lean_unsigned_to_nat(1024u);
v___x_480_ = lean_nat_dec_le(v___x_464_, v_prec_311_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
v___x_481_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_466_ = v___x_481_;
goto v___jp_465_;
}
else
{
lean_object* v___x_482_; 
v___x_482_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_466_ = v___x_482_;
goto v___jp_465_;
}
v___jp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_467_ = lean_box(1);
v___x_468_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__22));
v___x_469_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_459_, v___x_464_);
if (v_isShared_463_ == 0)
{
lean_ctor_set_tag(v___x_462_, 5);
lean_ctor_set(v___x_462_, 1, v___x_469_);
lean_ctor_set(v___x_462_, 0, v___x_468_);
v___x_471_ = v___x_462_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_479_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_467_);
v___x_473_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_460_, v___x_464_);
v___x_474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
lean_inc(v___y_466_);
v___x_475_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_475_, 0, v___y_466_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = 0;
v___x_477_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*1, v___x_476_);
v___x_478_ = l_Repr_addAppParen(v___x_477_, v_prec_311_);
return v___x_478_;
}
}
}
}
case 7:
{
lean_object* v_a_484_; lean_object* v_b_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_508_; 
v_a_484_ = lean_ctor_get(v_x_310_, 0);
v_b_485_ = lean_ctor_get(v_x_310_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_x_310_);
if (v_isSharedCheck_508_ == 0)
{
v___x_487_ = v_x_310_;
v_isShared_488_ = v_isSharedCheck_508_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_b_485_);
lean_inc(v_a_484_);
lean_dec(v_x_310_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_508_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___y_491_; uint8_t v___x_505_; 
v___x_489_ = lean_unsigned_to_nat(1024u);
v___x_505_ = lean_nat_dec_le(v___x_489_, v_prec_311_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
v___x_506_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_491_ = v___x_506_;
goto v___jp_490_;
}
else
{
lean_object* v___x_507_; 
v___x_507_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_491_ = v___x_507_;
goto v___jp_490_;
}
v___jp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_492_ = lean_box(1);
v___x_493_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__25));
v___x_494_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_484_, v___x_489_);
if (v_isShared_488_ == 0)
{
lean_ctor_set_tag(v___x_487_, 5);
lean_ctor_set(v___x_487_, 1, v___x_494_);
lean_ctor_set(v___x_487_, 0, v___x_493_);
v___x_496_ = v___x_487_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_494_);
v___x_496_ = v_reuseFailAlloc_504_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v___x_492_);
v___x_498_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_b_485_, v___x_489_);
v___x_499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
lean_inc(v___y_491_);
v___x_500_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_500_, 0, v___y_491_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = 0;
v___x_502_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*1, v___x_501_);
v___x_503_ = l_Repr_addAppParen(v___x_502_, v_prec_311_);
return v___x_503_;
}
}
}
}
default: 
{
lean_object* v_a_509_; lean_object* v_k_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_534_; 
v_a_509_ = lean_ctor_get(v_x_310_, 0);
v_k_510_ = lean_ctor_get(v_x_310_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_x_310_);
if (v_isSharedCheck_534_ == 0)
{
v___x_512_ = v_x_310_;
v_isShared_513_ = v_isSharedCheck_534_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_k_510_);
lean_inc(v_a_509_);
lean_dec(v_x_310_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_534_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___y_516_; uint8_t v___x_531_; 
v___x_514_ = lean_unsigned_to_nat(1024u);
v___x_531_ = lean_nat_dec_le(v___x_514_, v_prec_311_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_516_ = v___x_532_;
goto v___jp_515_;
}
else
{
lean_object* v___x_533_; 
v___x_533_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_516_ = v___x_533_;
goto v___jp_515_;
}
v___jp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_517_ = lean_box(1);
v___x_518_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprExpr_repr___closed__28));
v___x_519_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_a_509_, v___x_514_);
if (v_isShared_513_ == 0)
{
lean_ctor_set_tag(v___x_512_, 5);
lean_ctor_set(v___x_512_, 1, v___x_519_);
lean_ctor_set(v___x_512_, 0, v___x_518_);
v___x_521_ = v___x_512_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_519_);
v___x_521_ = v_reuseFailAlloc_530_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___x_517_);
v___x_523_ = l_Nat_reprFast(v_k_510_);
v___x_524_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
v___x_525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_522_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
lean_inc(v___y_516_);
v___x_526_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_526_, 0, v___y_516_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = 0;
v___x_528_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*1, v___x_527_);
v___x_529_ = l_Repr_addAppParen(v___x_528_, v_prec_311_);
return v___x_529_;
}
}
}
}
}
v___jp_312_:
{
lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
lean_inc(v___y_313_);
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___y_313_);
lean_ctor_set(v___x_316_, 1, v___y_315_);
lean_inc(v___y_314_);
v___x_317_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_317_, 0, v___y_314_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = 0;
v___x_319_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*1, v___x_318_);
v___x_320_ = l_Repr_addAppParen(v___x_319_, v_prec_311_);
return v___x_320_;
}
v___jp_321_:
{
lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_inc(v___y_322_);
v___x_325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_325_, 0, v___y_322_);
lean_ctor_set(v___x_325_, 1, v___y_324_);
lean_inc(v___y_323_);
v___x_326_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_326_, 0, v___y_323_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = 0;
v___x_328_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set_uint8(v___x_328_, sizeof(void*)*1, v___x_327_);
v___x_329_ = l_Repr_addAppParen(v___x_328_, v_prec_311_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprExpr_repr___boxed(lean_object* v_x_535_, lean_object* v_prec_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Grind_CommRing_instReprExpr_repr(v_x_535_, v_prec_536_);
lean_dec(v_prec_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___redArg(lean_object* v_ctx_540_, lean_object* v_v_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_RArray_getImpl___redArg(v_ctx_540_, v_v_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___redArg___boxed(lean_object* v_ctx_543_, lean_object* v_v_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Grind_CommRing_Var_denote___redArg(v_ctx_543_, v_v_544_);
lean_dec(v_v_544_);
lean_dec_ref(v_ctx_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote(lean_object* v_00_u03b1_546_, lean_object* v_ctx_547_, lean_object* v_v_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_RArray_getImpl___redArg(v_ctx_547_, v_v_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_denote___boxed(lean_object* v_00_u03b1_550_, lean_object* v_ctx_551_, lean_object* v_v_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Grind_CommRing_Var_denote(v_00_u03b1_550_, v_ctx_551_, v_v_552_);
lean_dec(v_v_552_);
lean_dec_ref(v_ctx_551_);
return v_res_553_;
}
}
uint8_t l_Lean_Grind_CommRing_instBEqPower_beq(lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
lean_object* v_x_556_; lean_object* v_k_557_; lean_object* v_x_558_; lean_object* v_k_559_; uint8_t v___x_560_; 
v_x_556_ = lean_ctor_get(v_x_554_, 0);
v_k_557_ = lean_ctor_get(v_x_554_, 1);
v_x_558_ = lean_ctor_get(v_x_555_, 0);
v_k_559_ = lean_ctor_get(v_x_555_, 1);
v___x_560_ = lean_nat_dec_eq(v_x_556_, v_x_558_);
if (v___x_560_ == 0)
{
return v___x_560_;
}
else
{
uint8_t v___x_561_; 
v___x_561_ = lean_nat_dec_eq(v_k_557_, v_k_559_);
return v___x_561_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_instBEqPower_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_554_ = stack[0].m_obj;
lean_object* v_x_555_ = stack[1].m_obj;
uint8_t v_res_562_;
v_res_562_ = l_Lean_Grind_CommRing_instBEqPower_beq(v_x_554_, v_x_555_);
stack->m_num = v_res_562_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPower_beq___boxed(lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
uint8_t v_res_565_; lean_object* v_r_566_; 
v_res_565_ = l_Lean_Grind_CommRing_instBEqPower_beq(v_x_563_, v_x_564_);
lean_dec_ref(v_x_564_);
lean_dec_ref(v_x_563_);
v_r_566_ = lean_box(v_res_565_);
return v_r_566_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_instReprPower_repr_spec__0(lean_object* v_a_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = lean_nat_to_int(v_a_569_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_unsigned_to_nat(5u);
v___x_585_ = lean_nat_to_int(v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__0));
v___x_594_ = lean_string_length(v___x_593_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13, &l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13_once, _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__13);
v___x_596_ = lean_nat_to_int(v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___redArg(lean_object* v_x_601_){
_start:
{
lean_object* v_x_602_; lean_object* v_k_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_637_; 
v_x_602_ = lean_ctor_get(v_x_601_, 0);
v_k_603_ = lean_ctor_get(v_x_601_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v_x_601_);
if (v_isSharedCheck_637_ == 0)
{
v___x_605_ = v_x_601_;
v_isShared_606_ = v_isSharedCheck_637_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_k_603_);
lean_inc(v_x_602_);
lean_dec(v_x_601_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_637_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_607_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__5));
v___x_608_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__6));
v___x_609_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7, &l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7_once, _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__7);
v___x_610_ = l_Nat_reprFast(v_x_602_);
v___x_611_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
if (v_isShared_606_ == 0)
{
lean_ctor_set_tag(v___x_605_, 4);
lean_ctor_set(v___x_605_, 1, v___x_611_);
lean_ctor_set(v___x_605_, 0, v___x_609_);
v___x_613_ = v___x_605_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v___x_611_);
v___x_613_ = v_reuseFailAlloc_636_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_614_ = 0;
v___x_615_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*1, v___x_614_);
v___x_616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_608_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__9));
v___x_618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = lean_box(1);
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__11));
v___x_622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v___x_607_);
v___x_624_ = l_Nat_reprFast(v_k_603_);
v___x_625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
v___x_626_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_609_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set_uint8(v___x_627_, sizeof(void*)*1, v___x_614_);
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_623_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14, &l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14_once, _init_l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__14);
v___x_630_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__15));
v___x_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___x_628_);
v___x_632_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPower_repr___redArg___closed__16));
v___x_633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_629_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*1, v___x_614_);
return v___x_635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr(lean_object* v_x_638_, lean_object* v_prec_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg(v_x_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPower_repr___boxed(lean_object* v_x_641_, lean_object* v_prec_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Grind_CommRing_instReprPower_repr(v_x_641_, v_prec_642_);
lean_dec(v_prec_642_);
return v_res_643_;
}
}
uint64_t l_Lean_Grind_CommRing_instHashablePower_hash(lean_object* v_x_650_){
_start:
{
lean_object* v_x_651_; lean_object* v_k_652_; uint64_t v___x_653_; uint64_t v___x_654_; uint64_t v___x_655_; uint64_t v___x_656_; uint64_t v___x_657_; 
v_x_651_ = lean_ctor_get(v_x_650_, 0);
v_k_652_ = lean_ctor_get(v_x_650_, 1);
v___x_653_ = 0ULL;
v___x_654_ = lean_uint64_of_nat(v_x_651_);
v___x_655_ = lean_uint64_mix_hash(v___x_653_, v___x_654_);
v___x_656_ = lean_uint64_of_nat(v_k_652_);
v___x_657_ = lean_uint64_mix_hash(v___x_655_, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_instHashablePower_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_650_ = stack[0].m_obj;
uint64_t v_res_658_;
v_res_658_ = l_Lean_Grind_CommRing_instHashablePower_hash(v_x_650_);
stack->m_num = v_res_658_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePower_hash___boxed(lean_object* v_x_659_){
_start:
{
uint64_t v_res_660_; lean_object* v_r_661_; 
v_res_660_ = l_Lean_Grind_CommRing_instHashablePower_hash(v_x_659_);
lean_dec_ref(v_x_659_);
v_r_661_ = lean_box_uint64(v_res_660_);
return v_r_661_;
}
}
uint8_t l_Lean_Grind_CommRing_Power_varLt(lean_object* v_p_u2081_664_, lean_object* v_p_u2082_665_){
_start:
{
lean_object* v_x_666_; lean_object* v_x_667_; uint8_t v___x_668_; 
v_x_666_ = lean_ctor_get(v_p_u2081_664_, 0);
v_x_667_ = lean_ctor_get(v_p_u2082_665_, 0);
v___x_668_ = l_Nat_blt(v_x_666_, v_x_667_);
return v___x_668_;
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Power_varLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_664_ = stack[0].m_obj;
lean_object* v_p_u2082_665_ = stack[1].m_obj;
uint8_t v_res_669_;
v_res_669_ = l_Lean_Grind_CommRing_Power_varLt(v_p_u2081_664_, v_p_u2082_665_);
stack->m_num = v_res_669_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_varLt___boxed(lean_object* v_p_u2081_670_, lean_object* v_p_u2082_671_){
_start:
{
uint8_t v_res_672_; lean_object* v_r_673_; 
v_res_672_ = l_Lean_Grind_CommRing_Power_varLt(v_p_u2081_670_, v_p_u2082_671_);
lean_dec_ref(v_p_u2082_671_);
lean_dec_ref(v_p_u2081_670_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg(lean_object* v_inst_674_, lean_object* v_ctx_675_, lean_object* v_x_676_){
_start:
{
lean_object* v_ofNat_677_; lean_object* v_npow_678_; lean_object* v_x_679_; lean_object* v_k_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_ofNat_677_ = lean_ctor_get(v_inst_674_, 3);
lean_inc(v_ofNat_677_);
v_npow_678_ = lean_ctor_get(v_inst_674_, 5);
lean_inc(v_npow_678_);
lean_dec_ref(v_inst_674_);
v_x_679_ = lean_ctor_get(v_x_676_, 0);
lean_inc(v_x_679_);
v_k_680_ = lean_ctor_get(v_x_676_, 1);
lean_inc(v_k_680_);
lean_dec_ref(v_x_676_);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_nat_dec_eq(v_k_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; uint8_t v___x_684_; 
lean_dec(v_ofNat_677_);
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_nat_dec_eq(v_k_680_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = l_Lean_RArray_getImpl___redArg(v_ctx_675_, v_x_679_);
lean_dec(v_x_679_);
v___x_686_ = lean_apply_2(v_npow_678_, v___x_685_, v_k_680_);
return v___x_686_;
}
else
{
lean_object* v___x_687_; 
lean_dec(v_k_680_);
lean_dec(v_npow_678_);
v___x_687_ = l_Lean_RArray_getImpl___redArg(v_ctx_675_, v_x_679_);
lean_dec(v_x_679_);
return v___x_687_;
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec(v_k_680_);
lean_dec(v_x_679_);
lean_dec(v_npow_678_);
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = lean_apply_1(v_ofNat_677_, v___x_688_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___redArg___boxed(lean_object* v_inst_690_, lean_object* v_ctx_691_, lean_object* v_x_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Grind_CommRing_Power_denote___redArg(v_inst_690_, v_ctx_691_, v_x_692_);
lean_dec_ref(v_ctx_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote(lean_object* v_00_u03b1_694_, lean_object* v_inst_695_, lean_object* v_ctx_696_, lean_object* v_x_697_){
_start:
{
lean_object* v_ofNat_698_; lean_object* v_npow_699_; lean_object* v_x_700_; lean_object* v_k_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_ofNat_698_ = lean_ctor_get(v_inst_695_, 3);
lean_inc(v_ofNat_698_);
v_npow_699_ = lean_ctor_get(v_inst_695_, 5);
lean_inc(v_npow_699_);
lean_dec_ref(v_inst_695_);
v_x_700_ = lean_ctor_get(v_x_697_, 0);
lean_inc(v_x_700_);
v_k_701_ = lean_ctor_get(v_x_697_, 1);
lean_inc(v_k_701_);
lean_dec_ref(v_x_697_);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_nat_dec_eq(v_k_701_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; uint8_t v___x_705_; 
lean_dec(v_ofNat_698_);
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_dec_eq(v_k_701_, v___x_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = l_Lean_RArray_getImpl___redArg(v_ctx_696_, v_x_700_);
lean_dec(v_x_700_);
v___x_707_ = lean_apply_2(v_npow_699_, v___x_706_, v_k_701_);
return v___x_707_;
}
else
{
lean_object* v___x_708_; 
lean_dec(v_k_701_);
lean_dec(v_npow_699_);
v___x_708_ = l_Lean_RArray_getImpl___redArg(v_ctx_696_, v_x_700_);
lean_dec(v_x_700_);
return v___x_708_;
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec(v_k_701_);
lean_dec(v_x_700_);
lean_dec(v_npow_699_);
v___x_709_ = lean_unsigned_to_nat(1u);
v___x_710_ = lean_apply_1(v_ofNat_698_, v___x_709_);
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_denote___boxed(lean_object* v_00_u03b1_711_, lean_object* v_inst_712_, lean_object* v_ctx_713_, lean_object* v_x_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Grind_CommRing_Power_denote(v_00_u03b1_711_, v_inst_712_, v_ctx_713_, v_x_714_);
lean_dec_ref(v_ctx_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx___impl(lean_object* v_x_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_obj_tag_nat(v_x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorIdx___impl___boxed(lean_object* v_x_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Grind_CommRing_Mon_ctorIdx___impl(v_x_718_);
lean_dec(v_x_718_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___redArg(lean_object* v_t_720_, lean_object* v_k_721_){
_start:
{
if (lean_obj_tag(v_t_720_) == 0)
{
return v_k_721_;
}
else
{
lean_object* v_p_722_; lean_object* v_m_723_; lean_object* v___x_724_; 
v_p_722_ = lean_ctor_get(v_t_720_, 0);
lean_inc_ref(v_p_722_);
v_m_723_ = lean_ctor_get(v_t_720_, 1);
lean_inc(v_m_723_);
lean_dec_ref_known(v_t_720_, 2);
v___x_724_ = lean_apply_2(v_k_721_, v_p_722_, v_m_723_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim(lean_object* v_motive_725_, lean_object* v_ctorIdx_726_, lean_object* v_t_727_, lean_object* v_h_728_, lean_object* v_k_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_727_, v_k_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ctorElim___boxed(lean_object* v_motive_731_, lean_object* v_ctorIdx_732_, lean_object* v_t_733_, lean_object* v_h_734_, lean_object* v_k_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Grind_CommRing_Mon_ctorElim(v_motive_731_, v_ctorIdx_732_, v_t_733_, v_h_734_, v_k_735_);
lean_dec(v_ctorIdx_732_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim___redArg(lean_object* v_t_737_, lean_object* v_unit_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_737_, v_unit_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_unit_elim(lean_object* v_motive_740_, lean_object* v_t_741_, lean_object* v_h_742_, lean_object* v_unit_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_741_, v_unit_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim___redArg(lean_object* v_t_745_, lean_object* v_mult_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_745_, v_mult_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mult_elim(lean_object* v_motive_748_, lean_object* v_t_749_, lean_object* v_h_750_, lean_object* v_mult_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Grind_CommRing_Mon_ctorElim___redArg(v_t_749_, v_mult_751_);
return v___x_752_;
}
}
uint8_t l_Lean_Grind_CommRing_instBEqMon_beq(lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
if (lean_obj_tag(v_x_754_) == 0)
{
uint8_t v___x_755_; 
v___x_755_ = 1;
return v___x_755_;
}
else
{
uint8_t v___x_756_; 
v___x_756_ = 0;
return v___x_756_;
}
}
else
{
if (lean_obj_tag(v_x_754_) == 1)
{
lean_object* v_p_757_; lean_object* v_m_758_; lean_object* v_p_759_; lean_object* v_m_760_; uint8_t v___x_761_; 
v_p_757_ = lean_ctor_get(v_x_753_, 0);
v_m_758_ = lean_ctor_get(v_x_753_, 1);
v_p_759_ = lean_ctor_get(v_x_754_, 0);
v_m_760_ = lean_ctor_get(v_x_754_, 1);
v___x_761_ = l_Lean_Grind_CommRing_instBEqPower_beq(v_p_757_, v_p_759_);
if (v___x_761_ == 0)
{
return v___x_761_;
}
else
{
v_x_753_ = v_m_758_;
v_x_754_ = v_m_760_;
goto _start;
}
}
else
{
uint8_t v___x_763_; 
v___x_763_ = 0;
return v___x_763_;
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_instBEqMon_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_753_ = stack[0].m_obj;
lean_object* v_x_754_ = stack[1].m_obj;
uint8_t v_res_764_;
v_res_764_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_x_753_, v_x_754_);
stack->m_num = v_res_764_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqMon_beq___boxed(lean_object* v_x_765_, lean_object* v_x_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_x_765_, v_x_766_);
lean_dec(v_x_766_);
lean_dec(v_x_765_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter___redArg(lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_h__1_773_, lean_object* v_h__2_774_, lean_object* v_h__3_775_){
_start:
{
if (lean_obj_tag(v_x_771_) == 0)
{
lean_dec(v_h__2_774_);
if (lean_obj_tag(v_x_772_) == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec(v_h__3_775_);
v___x_776_ = lean_box(0);
v___x_777_ = lean_apply_1(v_h__1_773_, v___x_776_);
return v___x_777_;
}
else
{
lean_object* v___x_778_; 
lean_dec(v_h__1_773_);
v___x_778_ = lean_apply_4(v_h__3_775_, v_x_771_, v_x_772_, lean_box(0), lean_box(0));
return v___x_778_;
}
}
else
{
lean_dec(v_h__1_773_);
if (lean_obj_tag(v_x_772_) == 1)
{
lean_object* v_p_779_; lean_object* v_m_780_; lean_object* v_p_781_; lean_object* v_m_782_; lean_object* v___x_783_; 
lean_dec(v_h__3_775_);
v_p_779_ = lean_ctor_get(v_x_771_, 0);
lean_inc_ref(v_p_779_);
v_m_780_ = lean_ctor_get(v_x_771_, 1);
lean_inc(v_m_780_);
lean_dec_ref_known(v_x_771_, 2);
v_p_781_ = lean_ctor_get(v_x_772_, 0);
lean_inc_ref(v_p_781_);
v_m_782_ = lean_ctor_get(v_x_772_, 1);
lean_inc(v_m_782_);
lean_dec_ref_known(v_x_772_, 2);
v___x_783_ = lean_apply_4(v_h__2_774_, v_p_779_, v_m_780_, v_p_781_, v_m_782_);
return v___x_783_;
}
else
{
lean_object* v___x_784_; 
lean_dec(v_h__2_774_);
v___x_784_ = lean_apply_4(v_h__3_775_, v_x_771_, v_x_772_, lean_box(0), lean_box(0));
return v___x_784_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqMon_beq_match__1_splitter(lean_object* v_motive_785_, lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v_h__1_788_, lean_object* v_h__2_789_, lean_object* v_h__3_790_){
_start:
{
if (lean_obj_tag(v_x_786_) == 0)
{
lean_dec(v_h__2_789_);
if (lean_obj_tag(v_x_787_) == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec(v_h__3_790_);
v___x_791_ = lean_box(0);
v___x_792_ = lean_apply_1(v_h__1_788_, v___x_791_);
return v___x_792_;
}
else
{
lean_object* v___x_793_; 
lean_dec(v_h__1_788_);
v___x_793_ = lean_apply_4(v_h__3_790_, v_x_786_, v_x_787_, lean_box(0), lean_box(0));
return v___x_793_;
}
}
else
{
lean_dec(v_h__1_788_);
if (lean_obj_tag(v_x_787_) == 1)
{
lean_object* v_p_794_; lean_object* v_m_795_; lean_object* v_p_796_; lean_object* v_m_797_; lean_object* v___x_798_; 
lean_dec(v_h__3_790_);
v_p_794_ = lean_ctor_get(v_x_786_, 0);
lean_inc_ref(v_p_794_);
v_m_795_ = lean_ctor_get(v_x_786_, 1);
lean_inc(v_m_795_);
lean_dec_ref_known(v_x_786_, 2);
v_p_796_ = lean_ctor_get(v_x_787_, 0);
lean_inc_ref(v_p_796_);
v_m_797_ = lean_ctor_get(v_x_787_, 1);
lean_inc(v_m_797_);
lean_dec_ref_known(v_x_787_, 2);
v___x_798_ = lean_apply_4(v_h__2_789_, v_p_794_, v_m_795_, v_p_796_, v_m_797_);
return v___x_798_;
}
else
{
lean_object* v___x_799_; 
lean_dec(v_h__2_789_);
v___x_799_ = lean_apply_4(v_h__3_790_, v_x_786_, v_x_787_, lean_box(0), lean_box(0));
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr(lean_object* v_x_809_, lean_object* v_prec_810_){
_start:
{
lean_object* v___y_812_; 
if (lean_obj_tag(v_x_809_) == 0)
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = lean_unsigned_to_nat(1024u);
v___x_819_ = lean_nat_dec_le(v___x_818_, v_prec_810_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
v___x_820_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_812_ = v___x_820_;
goto v___jp_811_;
}
else
{
lean_object* v___x_821_; 
v___x_821_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_812_ = v___x_821_;
goto v___jp_811_;
}
}
else
{
lean_object* v_p_822_; lean_object* v_m_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_846_; 
v_p_822_ = lean_ctor_get(v_x_809_, 0);
v_m_823_ = lean_ctor_get(v_x_809_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v_x_809_);
if (v_isSharedCheck_846_ == 0)
{
v___x_825_ = v_x_809_;
v_isShared_826_ = v_isSharedCheck_846_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_m_823_);
lean_inc(v_p_822_);
lean_dec(v_x_809_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_846_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___y_829_; uint8_t v___x_843_; 
v___x_827_ = lean_unsigned_to_nat(1024u);
v___x_843_ = lean_nat_dec_le(v___x_827_, v_prec_810_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
v___x_844_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_829_ = v___x_844_;
goto v___jp_828_;
}
else
{
lean_object* v___x_845_; 
v___x_845_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_829_ = v___x_845_;
goto v___jp_828_;
}
v___jp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_830_ = lean_box(1);
v___x_831_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprMon_repr___closed__4));
v___x_832_ = l_Lean_Grind_CommRing_instReprPower_repr___redArg(v_p_822_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 5);
lean_ctor_set(v___x_825_, 1, v___x_832_);
lean_ctor_set(v___x_825_, 0, v___x_831_);
v___x_834_ = v___x_825_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_832_);
v___x_834_ = v_reuseFailAlloc_842_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_830_);
v___x_836_ = l_Lean_Grind_CommRing_instReprMon_repr(v_m_823_, v___x_827_);
v___x_837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
lean_inc(v___y_829_);
v___x_838_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_838_, 0, v___y_829_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = 0;
v___x_840_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*1, v___x_839_);
v___x_841_ = l_Repr_addAppParen(v___x_840_, v_prec_810_);
return v___x_841_;
}
}
}
}
v___jp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_813_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprMon_repr___closed__1));
lean_inc(v___y_812_);
v___x_814_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_814_, 0, v___y_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = 0;
v___x_816_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*1, v___x_815_);
v___x_817_ = l_Repr_addAppParen(v___x_816_, v_prec_810_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprMon_repr___boxed(lean_object* v_x_847_, lean_object* v_prec_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Grind_CommRing_instReprMon_repr(v_x_847_, v_prec_848_);
lean_dec(v_prec_848_);
return v_res_849_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedMon_default(void){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = lean_box(0);
return v___x_852_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedMon(void){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_box(0);
return v___x_853_;
}
}
uint64_t l_Lean_Grind_CommRing_instHashableMon_hash(lean_object* v_x_854_){
_start:
{
if (lean_obj_tag(v_x_854_) == 0)
{
uint64_t v___x_855_; 
v___x_855_ = 0ULL;
return v___x_855_;
}
else
{
lean_object* v_p_856_; lean_object* v_m_857_; uint64_t v___x_858_; uint64_t v___x_859_; uint64_t v___x_860_; uint64_t v___x_861_; uint64_t v___x_862_; 
v_p_856_ = lean_ctor_get(v_x_854_, 0);
v_m_857_ = lean_ctor_get(v_x_854_, 1);
v___x_858_ = 1ULL;
v___x_859_ = l_Lean_Grind_CommRing_instHashablePower_hash(v_p_856_);
v___x_860_ = lean_uint64_mix_hash(v___x_858_, v___x_859_);
v___x_861_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_m_857_);
v___x_862_ = lean_uint64_mix_hash(v___x_860_, v___x_861_);
return v___x_862_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_instHashableMon_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_854_ = stack[0].m_obj;
uint64_t v_res_863_;
v_res_863_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_x_854_);
stack->m_num = v_res_863_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashableMon_hash___boxed(lean_object* v_x_864_){
_start:
{
uint64_t v_res_865_; lean_object* v_r_866_; 
v_res_865_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_x_864_);
lean_dec(v_x_864_);
v_r_866_ = lean_box_uint64(v_res_865_);
return v_r_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg(lean_object* v_inst_869_, lean_object* v_ctx_870_, lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_871_) == 0)
{
lean_object* v_ofNat_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_ofNat_872_ = lean_ctor_get(v_inst_869_, 3);
lean_inc(v_ofNat_872_);
lean_dec_ref(v_inst_869_);
v___x_873_ = lean_unsigned_to_nat(1u);
v___x_874_ = lean_apply_1(v_ofNat_872_, v___x_873_);
return v___x_874_;
}
else
{
lean_object* v_toMul_875_; lean_object* v_ofNat_876_; lean_object* v_npow_877_; lean_object* v_p_878_; lean_object* v_m_879_; lean_object* v___y_881_; lean_object* v_x_884_; lean_object* v_k_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v_toMul_875_ = lean_ctor_get(v_inst_869_, 1);
lean_inc(v_toMul_875_);
v_ofNat_876_ = lean_ctor_get(v_inst_869_, 3);
v_npow_877_ = lean_ctor_get(v_inst_869_, 5);
v_p_878_ = lean_ctor_get(v_x_871_, 0);
lean_inc_ref(v_p_878_);
v_m_879_ = lean_ctor_get(v_x_871_, 1);
lean_inc(v_m_879_);
lean_dec_ref_known(v_x_871_, 2);
v_x_884_ = lean_ctor_get(v_p_878_, 0);
lean_inc(v_x_884_);
v_k_885_ = lean_ctor_get(v_p_878_, 1);
lean_inc(v_k_885_);
lean_dec_ref(v_p_878_);
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = lean_nat_dec_eq(v_k_885_, v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = lean_nat_dec_eq(v_k_885_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = l_Lean_RArray_getImpl___redArg(v_ctx_870_, v_x_884_);
lean_dec(v_x_884_);
lean_inc(v_npow_877_);
v___x_891_ = lean_apply_2(v_npow_877_, v___x_890_, v_k_885_);
v___y_881_ = v___x_891_;
goto v___jp_880_;
}
else
{
lean_object* v___x_892_; 
lean_dec(v_k_885_);
v___x_892_ = l_Lean_RArray_getImpl___redArg(v_ctx_870_, v_x_884_);
lean_dec(v_x_884_);
v___y_881_ = v___x_892_;
goto v___jp_880_;
}
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec(v_k_885_);
lean_dec(v_x_884_);
v___x_893_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_876_);
v___x_894_ = lean_apply_1(v_ofNat_876_, v___x_893_);
v___y_881_ = v___x_894_;
goto v___jp_880_;
}
v___jp_880_:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_869_, v_ctx_870_, v_m_879_);
v___x_883_ = lean_apply_2(v_toMul_875_, v___y_881_, v___x_882_);
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg___boxed(lean_object* v_inst_895_, lean_object* v_ctx_896_, lean_object* v_x_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_895_, v_ctx_896_, v_x_897_);
lean_dec_ref(v_ctx_896_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote(lean_object* v_00_u03b1_899_, lean_object* v_inst_900_, lean_object* v_ctx_901_, lean_object* v_x_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_900_, v_ctx_901_, v_x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote___boxed(lean_object* v_00_u03b1_904_, lean_object* v_inst_905_, lean_object* v_ctx_906_, lean_object* v_x_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Grind_CommRing_Mon_denote(v_00_u03b1_904_, v_inst_905_, v_ctx_906_, v_x_907_);
lean_dec_ref(v_ctx_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(lean_object* v_inst_909_, lean_object* v_ctx_910_, lean_object* v_m_911_, lean_object* v_acc_912_){
_start:
{
if (lean_obj_tag(v_m_911_) == 0)
{
lean_dec_ref(v_inst_909_);
return v_acc_912_;
}
else
{
lean_object* v_toMul_913_; lean_object* v_ofNat_914_; lean_object* v_npow_915_; lean_object* v_p_916_; lean_object* v_m_917_; lean_object* v___y_919_; lean_object* v_x_922_; lean_object* v_k_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_toMul_913_ = lean_ctor_get(v_inst_909_, 1);
v_ofNat_914_ = lean_ctor_get(v_inst_909_, 3);
v_npow_915_ = lean_ctor_get(v_inst_909_, 5);
v_p_916_ = lean_ctor_get(v_m_911_, 0);
lean_inc_ref(v_p_916_);
v_m_917_ = lean_ctor_get(v_m_911_, 1);
lean_inc(v_m_917_);
lean_dec_ref_known(v_m_911_, 2);
v_x_922_ = lean_ctor_get(v_p_916_, 0);
lean_inc(v_x_922_);
v_k_923_ = lean_ctor_get(v_p_916_, 1);
lean_inc(v_k_923_);
lean_dec_ref(v_p_916_);
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = lean_nat_dec_eq(v_k_923_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_nat_dec_eq(v_k_923_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = l_Lean_RArray_getImpl___redArg(v_ctx_910_, v_x_922_);
lean_dec(v_x_922_);
lean_inc(v_npow_915_);
v___x_929_ = lean_apply_2(v_npow_915_, v___x_928_, v_k_923_);
v___y_919_ = v___x_929_;
goto v___jp_918_;
}
else
{
lean_object* v___x_930_; 
lean_dec(v_k_923_);
v___x_930_ = l_Lean_RArray_getImpl___redArg(v_ctx_910_, v_x_922_);
lean_dec(v_x_922_);
v___y_919_ = v___x_930_;
goto v___jp_918_;
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v_k_923_);
lean_dec(v_x_922_);
v___x_931_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_914_);
v___x_932_ = lean_apply_1(v_ofNat_914_, v___x_931_);
v___y_919_ = v___x_932_;
goto v___jp_918_;
}
v___jp_918_:
{
lean_object* v___x_920_; 
lean_inc(v_toMul_913_);
v___x_920_ = lean_apply_2(v_toMul_913_, v_acc_912_, v___y_919_);
v_m_911_ = v_m_917_;
v_acc_912_ = v___x_920_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg___boxed(lean_object* v_inst_933_, lean_object* v_ctx_934_, lean_object* v_m_935_, lean_object* v_acc_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_933_, v_ctx_934_, v_m_935_, v_acc_936_);
lean_dec_ref(v_ctx_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go(lean_object* v_00_u03b1_938_, lean_object* v_inst_939_, lean_object* v_ctx_940_, lean_object* v_m_941_, lean_object* v_acc_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_939_, v_ctx_940_, v_m_941_, v_acc_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27_go___boxed(lean_object* v_00_u03b1_944_, lean_object* v_inst_945_, lean_object* v_ctx_946_, lean_object* v_m_947_, lean_object* v_acc_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Grind_CommRing_Mon_denote_x27_go(v_00_u03b1_944_, v_inst_945_, v_ctx_946_, v_m_947_, v_acc_948_);
lean_dec_ref(v_ctx_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg(lean_object* v_inst_950_, lean_object* v_ctx_951_, lean_object* v_m_952_){
_start:
{
if (lean_obj_tag(v_m_952_) == 0)
{
lean_object* v_ofNat_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_ofNat_953_ = lean_ctor_get(v_inst_950_, 3);
lean_inc(v_ofNat_953_);
lean_dec_ref(v_inst_950_);
v___x_954_ = lean_unsigned_to_nat(1u);
v___x_955_ = lean_apply_1(v_ofNat_953_, v___x_954_);
return v___x_955_;
}
else
{
lean_object* v_p_956_; lean_object* v_m_957_; lean_object* v_ofNat_958_; lean_object* v_npow_959_; lean_object* v_x_960_; lean_object* v_k_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_p_956_ = lean_ctor_get(v_m_952_, 0);
lean_inc_ref(v_p_956_);
v_m_957_ = lean_ctor_get(v_m_952_, 1);
lean_inc(v_m_957_);
lean_dec_ref_known(v_m_952_, 2);
v_ofNat_958_ = lean_ctor_get(v_inst_950_, 3);
v_npow_959_ = lean_ctor_get(v_inst_950_, 5);
v_x_960_ = lean_ctor_get(v_p_956_, 0);
lean_inc(v_x_960_);
v_k_961_ = lean_ctor_get(v_p_956_, 1);
lean_inc(v_k_961_);
lean_dec_ref(v_p_956_);
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = lean_nat_dec_eq(v_k_961_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_964_ = lean_unsigned_to_nat(1u);
v___x_965_ = lean_nat_dec_eq(v_k_961_, v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = l_Lean_RArray_getImpl___redArg(v_ctx_951_, v_x_960_);
lean_dec(v_x_960_);
lean_inc(v_npow_959_);
v___x_967_ = lean_apply_2(v_npow_959_, v___x_966_, v_k_961_);
v___x_968_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_950_, v_ctx_951_, v_m_957_, v___x_967_);
return v___x_968_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec(v_k_961_);
v___x_969_ = l_Lean_RArray_getImpl___redArg(v_ctx_951_, v_x_960_);
lean_dec(v_x_960_);
v___x_970_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_950_, v_ctx_951_, v_m_957_, v___x_969_);
return v___x_970_;
}
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
lean_dec(v_k_961_);
lean_dec(v_x_960_);
v___x_971_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_958_);
v___x_972_ = lean_apply_1(v_ofNat_958_, v___x_971_);
v___x_973_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_950_, v_ctx_951_, v_m_957_, v___x_972_);
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___redArg___boxed(lean_object* v_inst_974_, lean_object* v_ctx_975_, lean_object* v_m_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Grind_CommRing_Mon_denote_x27___redArg(v_inst_974_, v_ctx_975_, v_m_976_);
lean_dec_ref(v_ctx_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27(lean_object* v_00_u03b1_978_, lean_object* v_inst_979_, lean_object* v_ctx_980_, lean_object* v_m_981_){
_start:
{
if (lean_obj_tag(v_m_981_) == 0)
{
lean_object* v_ofNat_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_ofNat_982_ = lean_ctor_get(v_inst_979_, 3);
lean_inc(v_ofNat_982_);
lean_dec_ref(v_inst_979_);
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = lean_apply_1(v_ofNat_982_, v___x_983_);
return v___x_984_;
}
else
{
lean_object* v_p_985_; lean_object* v_m_986_; lean_object* v_ofNat_987_; lean_object* v_npow_988_; lean_object* v_x_989_; lean_object* v_k_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v_p_985_ = lean_ctor_get(v_m_981_, 0);
lean_inc_ref(v_p_985_);
v_m_986_ = lean_ctor_get(v_m_981_, 1);
lean_inc(v_m_986_);
lean_dec_ref_known(v_m_981_, 2);
v_ofNat_987_ = lean_ctor_get(v_inst_979_, 3);
v_npow_988_ = lean_ctor_get(v_inst_979_, 5);
v_x_989_ = lean_ctor_get(v_p_985_, 0);
lean_inc(v_x_989_);
v_k_990_ = lean_ctor_get(v_p_985_, 1);
lean_inc(v_k_990_);
lean_dec_ref(v_p_985_);
v___x_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = lean_nat_dec_eq(v_k_990_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = lean_unsigned_to_nat(1u);
v___x_994_ = lean_nat_dec_eq(v_k_990_, v___x_993_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = l_Lean_RArray_getImpl___redArg(v_ctx_980_, v_x_989_);
lean_dec(v_x_989_);
lean_inc(v_npow_988_);
v___x_996_ = lean_apply_2(v_npow_988_, v___x_995_, v_k_990_);
v___x_997_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_979_, v_ctx_980_, v_m_986_, v___x_996_);
return v___x_997_;
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec(v_k_990_);
v___x_998_ = l_Lean_RArray_getImpl___redArg(v_ctx_980_, v_x_989_);
lean_dec(v_x_989_);
v___x_999_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_979_, v_ctx_980_, v_m_986_, v___x_998_);
return v___x_999_;
}
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_dec(v_k_990_);
lean_dec(v_x_989_);
v___x_1000_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_987_);
v___x_1001_ = lean_apply_1(v_ofNat_987_, v___x_1000_);
v___x_1002_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_inst_979_, v_ctx_980_, v_m_986_, v___x_1001_);
return v___x_1002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denote_x27___boxed(lean_object* v_00_u03b1_1003_, lean_object* v_inst_1004_, lean_object* v_ctx_1005_, lean_object* v_m_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_Grind_CommRing_Mon_denote_x27(v_00_u03b1_1003_, v_inst_1004_, v_ctx_1005_, v_m_1006_);
lean_dec_ref(v_ctx_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_ofVar(lean_object* v_x_1008_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat(lean_object* v_m_u2081_1013_, lean_object* v_m_u2082_1014_){
_start:
{
if (lean_obj_tag(v_m_u2081_1013_) == 0)
{
lean_inc(v_m_u2082_1014_);
return v_m_u2082_1014_;
}
else
{
lean_object* v_p_1015_; lean_object* v_m_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1024_; 
v_p_1015_ = lean_ctor_get(v_m_u2081_1013_, 0);
v_m_1016_ = lean_ctor_get(v_m_u2081_1013_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_m_u2081_1013_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1018_ = v_m_u2081_1013_;
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_m_1016_);
lean_inc(v_p_1015_);
lean_dec(v_m_u2081_1013_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1020_ = l_Lean_Grind_CommRing_Mon_concat(v_m_1016_, v_m_u2082_1014_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v___x_1020_);
v___x_1022_ = v___x_1018_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_p_1015_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_concat___boxed(lean_object* v_m_u2081_1025_, lean_object* v_m_u2082_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_1025_, v_m_u2082_1026_);
lean_dec(v_m_u2082_1026_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow(lean_object* v_pw_1028_, lean_object* v_m_1029_){
_start:
{
if (lean_obj_tag(v_m_1029_) == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1030_, 0, v_pw_1028_);
lean_ctor_set(v___x_1030_, 1, v_m_1029_);
return v___x_1030_;
}
else
{
lean_object* v_p_1031_; lean_object* v_m_1032_; uint8_t v___x_1033_; 
v_p_1031_ = lean_ctor_get(v_m_1029_, 0);
lean_inc_ref(v_p_1031_);
v_m_1032_ = lean_ctor_get(v_m_1029_, 1);
v___x_1033_ = l_Lean_Grind_CommRing_Power_varLt(v_pw_1028_, v_p_1031_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1057_; 
lean_inc(v_m_1032_);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_m_1029_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; lean_object* v_unused_1059_; 
v_unused_1058_ = lean_ctor_get(v_m_1029_, 1);
lean_dec(v_unused_1058_);
v_unused_1059_ = lean_ctor_get(v_m_1029_, 0);
lean_dec(v_unused_1059_);
v___x_1035_ = v_m_1029_;
v_isShared_1036_ = v_isSharedCheck_1057_;
goto v_resetjp_1034_;
}
else
{
lean_dec(v_m_1029_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1057_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
uint8_t v___x_1037_; 
v___x_1037_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1031_, v_pw_1028_);
if (v___x_1037_ == 0)
{
lean_object* v_x_1038_; lean_object* v_k_1039_; lean_object* v_k_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1051_; 
v_x_1038_ = lean_ctor_get(v_pw_1028_, 0);
lean_inc(v_x_1038_);
v_k_1039_ = lean_ctor_get(v_pw_1028_, 1);
lean_inc(v_k_1039_);
lean_dec_ref(v_pw_1028_);
v_k_1040_ = lean_ctor_get(v_p_1031_, 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_p_1031_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v_p_1031_, 0);
lean_dec(v_unused_1052_);
v___x_1042_ = v_p_1031_;
v_isShared_1043_ = v_isSharedCheck_1051_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_k_1040_);
lean_dec(v_p_1031_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1051_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = lean_nat_add(v_k_1039_, v_k_1040_);
lean_dec(v_k_1040_);
lean_dec(v_k_1039_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v___x_1044_);
lean_ctor_set(v___x_1042_, 0, v_x_1038_);
v___x_1046_ = v___x_1042_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_x_1038_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1048_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1046_);
v___x_1048_ = v___x_1035_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_m_1032_);
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
lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = l_Lean_Grind_CommRing_Mon_mulPow(v_pw_1028_, v_m_1032_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v___x_1053_);
v___x_1055_ = v___x_1035_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_p_1031_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v___x_1060_; 
lean_dec_ref(v_p_1031_);
v___x_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_pw_1028_);
lean_ctor_set(v___x_1060_, 1, v_m_1029_);
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mulPow__nc(lean_object* v_pw_1061_, lean_object* v_m_1062_){
_start:
{
if (lean_obj_tag(v_m_1062_) == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1063_, 0, v_pw_1061_);
lean_ctor_set(v___x_1063_, 1, v_m_1062_);
return v___x_1063_;
}
else
{
lean_object* v_p_1064_; lean_object* v_m_1065_; lean_object* v_x_1066_; lean_object* v_k_1067_; lean_object* v_x_1068_; lean_object* v_k_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1088_; 
v_p_1064_ = lean_ctor_get(v_m_1062_, 0);
lean_inc_ref(v_p_1064_);
v_m_1065_ = lean_ctor_get(v_m_1062_, 1);
v_x_1066_ = lean_ctor_get(v_pw_1061_, 0);
v_k_1067_ = lean_ctor_get(v_pw_1061_, 1);
v_x_1068_ = lean_ctor_get(v_p_1064_, 0);
v_k_1069_ = lean_ctor_get(v_p_1064_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_p_1064_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1071_ = v_p_1064_;
v_isShared_1072_ = v_isSharedCheck_1088_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_k_1069_);
lean_inc(v_x_1068_);
lean_dec(v_p_1064_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1088_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_nat_dec_eq(v_x_1066_, v_x_1068_);
lean_dec(v_x_1068_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; 
lean_del_object(v___x_1071_);
lean_dec(v_k_1069_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_pw_1061_);
lean_ctor_set(v___x_1074_, 1, v_m_1062_);
return v___x_1074_;
}
else
{
lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1085_; 
lean_inc(v_k_1067_);
lean_inc(v_x_1066_);
lean_inc(v_m_1065_);
lean_dec_ref(v_pw_1061_);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_m_1062_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; lean_object* v_unused_1087_; 
v_unused_1086_ = lean_ctor_get(v_m_1062_, 1);
lean_dec(v_unused_1086_);
v_unused_1087_ = lean_ctor_get(v_m_1062_, 0);
lean_dec(v_unused_1087_);
v___x_1076_ = v_m_1062_;
v_isShared_1077_ = v_isSharedCheck_1085_;
goto v_resetjp_1075_;
}
else
{
lean_dec(v_m_1062_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1085_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = lean_nat_add(v_k_1067_, v_k_1069_);
lean_dec(v_k_1069_);
lean_dec(v_k_1067_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v___x_1078_);
lean_ctor_set(v___x_1071_, 0, v_x_1066_);
v___x_1080_ = v___x_1071_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_x_1066_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1082_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1080_);
v___x_1082_ = v___x_1076_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_m_1065_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length(lean_object* v_x_1089_){
_start:
{
if (lean_obj_tag(v_x_1089_) == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_unsigned_to_nat(0u);
return v___x_1090_;
}
else
{
lean_object* v_m_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_m_1091_ = lean_ctor_get(v_x_1089_, 1);
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = l_Lean_Grind_CommRing_Mon_length(v_m_1091_);
v___x_1094_ = lean_nat_add(v___x_1092_, v___x_1093_);
lean_dec(v___x_1093_);
return v___x_1094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_length___boxed(lean_object* v_x_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_Grind_CommRing_Mon_length(v_x_1095_);
lean_dec(v_x_1095_);
return v_res_1096_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_hugeFuel(void){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_unsigned_to_nat(1000000u);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go(lean_object* v_fuel_1098_, lean_object* v_m_u2081_1099_, lean_object* v_m_u2082_1100_){
_start:
{
lean_object* v_zero_1101_; uint8_t v_isZero_1102_; 
v_zero_1101_ = lean_unsigned_to_nat(0u);
v_isZero_1102_ = lean_nat_dec_eq(v_fuel_1098_, v_zero_1101_);
if (v_isZero_1102_ == 1)
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_1099_, v_m_u2082_1100_);
lean_dec(v_m_u2082_1100_);
return v___x_1103_;
}
else
{
if (lean_obj_tag(v_m_u2082_1100_) == 0)
{
return v_m_u2081_1099_;
}
else
{
if (lean_obj_tag(v_m_u2081_1099_) == 0)
{
return v_m_u2082_1100_;
}
else
{
lean_object* v_p_1104_; lean_object* v_m_1105_; lean_object* v_p_1106_; lean_object* v_m_1107_; lean_object* v_one_1108_; lean_object* v_n_1109_; uint8_t v___x_1110_; 
v_p_1104_ = lean_ctor_get(v_m_u2082_1100_, 0);
lean_inc_ref(v_p_1104_);
v_m_1105_ = lean_ctor_get(v_m_u2082_1100_, 1);
v_p_1106_ = lean_ctor_get(v_m_u2081_1099_, 0);
v_m_1107_ = lean_ctor_get(v_m_u2081_1099_, 1);
v_one_1108_ = lean_unsigned_to_nat(1u);
v_n_1109_ = lean_nat_sub(v_fuel_1098_, v_one_1108_);
v___x_1110_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1106_, v_p_1104_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1141_; 
lean_inc(v_m_1105_);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_m_u2082_1100_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; lean_object* v_unused_1143_; 
v_unused_1142_ = lean_ctor_get(v_m_u2082_1100_, 1);
lean_dec(v_unused_1142_);
v_unused_1143_ = lean_ctor_get(v_m_u2082_1100_, 0);
lean_dec(v_unused_1143_);
v___x_1112_ = v_m_u2082_1100_;
v_isShared_1113_ = v_isSharedCheck_1141_;
goto v_resetjp_1111_;
}
else
{
lean_dec(v_m_u2082_1100_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1141_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
uint8_t v___x_1114_; 
v___x_1114_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1104_, v_p_1106_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1134_; 
lean_inc(v_m_1107_);
lean_inc_ref(v_p_1106_);
lean_del_object(v___x_1112_);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_m_u2081_1099_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; lean_object* v_unused_1136_; 
v_unused_1135_ = lean_ctor_get(v_m_u2081_1099_, 1);
lean_dec(v_unused_1135_);
v_unused_1136_ = lean_ctor_get(v_m_u2081_1099_, 0);
lean_dec(v_unused_1136_);
v___x_1116_ = v_m_u2081_1099_;
v_isShared_1117_ = v_isSharedCheck_1134_;
goto v_resetjp_1115_;
}
else
{
lean_dec(v_m_u2081_1099_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1134_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_x_1118_; lean_object* v_k_1119_; lean_object* v_k_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1132_; 
v_x_1118_ = lean_ctor_get(v_p_1106_, 0);
lean_inc(v_x_1118_);
v_k_1119_ = lean_ctor_get(v_p_1106_, 1);
lean_inc(v_k_1119_);
lean_dec_ref(v_p_1106_);
v_k_1120_ = lean_ctor_get(v_p_1104_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_p_1104_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; 
v_unused_1133_ = lean_ctor_get(v_p_1104_, 0);
lean_dec(v_unused_1133_);
v___x_1122_ = v_p_1104_;
v_isShared_1123_ = v_isSharedCheck_1132_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_k_1120_);
lean_dec(v_p_1104_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1132_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_nat_add(v_k_1119_, v_k_1120_);
lean_dec(v_k_1120_);
lean_dec(v_k_1119_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 1, v___x_1124_);
lean_ctor_set(v___x_1122_, 0, v_x_1118_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_x_1118_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1109_, v_m_1107_, v_m_1105_);
lean_dec(v_n_1109_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 1, v___x_1127_);
lean_ctor_set(v___x_1116_, 0, v___x_1126_);
v___x_1129_ = v___x_1116_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1109_, v_m_u2081_1099_, v_m_1105_);
lean_dec(v_n_1109_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v___x_1137_);
v___x_1139_ = v___x_1112_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_p_1104_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1151_; 
lean_inc(v_m_1107_);
lean_inc_ref(v_p_1106_);
lean_dec_ref(v_p_1104_);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_m_u2081_1099_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; lean_object* v_unused_1153_; 
v_unused_1152_ = lean_ctor_get(v_m_u2081_1099_, 1);
lean_dec(v_unused_1152_);
v_unused_1153_ = lean_ctor_get(v_m_u2081_1099_, 0);
lean_dec(v_unused_1153_);
v___x_1145_ = v_m_u2081_1099_;
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
else
{
lean_dec(v_m_u2081_1099_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1109_, v_m_1107_, v_m_u2082_1100_);
lean_dec(v_n_1109_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_p_1106_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go___boxed(lean_object* v_fuel_1154_, lean_object* v_m_u2081_1155_, lean_object* v_m_u2082_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Grind_CommRing_Mon_mul_go(v_fuel_1154_, v_m_u2081_1155_, v_m_u2082_1156_);
lean_dec(v_fuel_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul(lean_object* v_m_u2081_1158_, lean_object* v_m_u2082_1159_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_unsigned_to_nat(1000000u);
v___x_1161_ = l_Lean_Grind_CommRing_Mon_mul_go(v___x_1160_, v_m_u2081_1158_, v_m_u2082_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object* v_fuel_1162_, lean_object* v_h__1_1163_, lean_object* v_h__2_1164_){
_start:
{
lean_object* v_zero_1165_; uint8_t v_isZero_1166_; 
v_zero_1165_ = lean_unsigned_to_nat(0u);
v_isZero_1166_ = lean_nat_dec_eq(v_fuel_1162_, v_zero_1165_);
if (v_isZero_1166_ == 1)
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v_h__2_1164_);
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_apply_1(v_h__1_1163_, v___x_1167_);
return v___x_1168_;
}
else
{
lean_object* v_one_1169_; lean_object* v_n_1170_; lean_object* v___x_1171_; 
lean_dec(v_h__1_1163_);
v_one_1169_ = lean_unsigned_to_nat(1u);
v_n_1170_ = lean_nat_sub(v_fuel_1162_, v_one_1169_);
v___x_1171_ = lean_apply_1(v_h__2_1164_, v_n_1170_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object* v_fuel_1172_, lean_object* v_h__1_1173_, lean_object* v_h__2_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(v_fuel_1172_, v_h__1_1173_, v_h__2_1174_);
lean_dec(v_fuel_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object* v_motive_1176_, lean_object* v_fuel_1177_, lean_object* v_h__1_1178_, lean_object* v_h__2_1179_){
_start:
{
lean_object* v_zero_1180_; uint8_t v_isZero_1181_; 
v_zero_1180_ = lean_unsigned_to_nat(0u);
v_isZero_1181_ = lean_nat_dec_eq(v_fuel_1177_, v_zero_1180_);
if (v_isZero_1181_ == 1)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_h__2_1179_);
v___x_1182_ = lean_box(0);
v___x_1183_ = lean_apply_1(v_h__1_1178_, v___x_1182_);
return v___x_1183_;
}
else
{
lean_object* v_one_1184_; lean_object* v_n_1185_; lean_object* v___x_1186_; 
lean_dec(v_h__1_1178_);
v_one_1184_ = lean_unsigned_to_nat(1u);
v_n_1185_ = lean_nat_sub(v_fuel_1177_, v_one_1184_);
v___x_1186_ = lean_apply_1(v_h__2_1179_, v_n_1185_);
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object* v_motive_1187_, lean_object* v_fuel_1188_, lean_object* v_h__1_1189_, lean_object* v_h__2_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(v_motive_1187_, v_fuel_1188_, v_h__1_1189_, v_h__2_1190_);
lean_dec(v_fuel_1188_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter___redArg(lean_object* v_m_u2081_1192_, lean_object* v_m_u2082_1193_, lean_object* v_h__1_1194_, lean_object* v_h__2_1195_, lean_object* v_h__3_1196_){
_start:
{
if (lean_obj_tag(v_m_u2082_1193_) == 0)
{
lean_object* v___x_1197_; 
lean_dec(v_h__3_1196_);
lean_dec(v_h__2_1195_);
v___x_1197_ = lean_apply_1(v_h__1_1194_, v_m_u2081_1192_);
return v___x_1197_;
}
else
{
lean_dec(v_h__1_1194_);
if (lean_obj_tag(v_m_u2081_1192_) == 0)
{
lean_object* v___x_1198_; 
lean_dec(v_h__3_1196_);
v___x_1198_ = lean_apply_2(v_h__2_1195_, v_m_u2082_1193_, lean_box(0));
return v___x_1198_;
}
else
{
lean_object* v_p_1199_; lean_object* v_m_1200_; lean_object* v_p_1201_; lean_object* v_m_1202_; lean_object* v___x_1203_; 
lean_dec(v_h__2_1195_);
v_p_1199_ = lean_ctor_get(v_m_u2082_1193_, 0);
lean_inc_ref(v_p_1199_);
v_m_1200_ = lean_ctor_get(v_m_u2082_1193_, 1);
lean_inc(v_m_1200_);
lean_dec_ref_known(v_m_u2082_1193_, 2);
v_p_1201_ = lean_ctor_get(v_m_u2081_1192_, 0);
lean_inc_ref(v_p_1201_);
v_m_1202_ = lean_ctor_get(v_m_u2081_1192_, 1);
lean_inc(v_m_1202_);
lean_dec_ref_known(v_m_u2081_1192_, 2);
v___x_1203_ = lean_apply_4(v_h__3_1196_, v_p_1201_, v_m_1202_, v_p_1199_, v_m_1200_);
return v___x_1203_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter(lean_object* v_motive_1204_, lean_object* v_m_u2081_1205_, lean_object* v_m_u2082_1206_, lean_object* v_h__1_1207_, lean_object* v_h__2_1208_, lean_object* v_h__3_1209_){
_start:
{
if (lean_obj_tag(v_m_u2082_1206_) == 0)
{
lean_object* v___x_1210_; 
lean_dec(v_h__3_1209_);
lean_dec(v_h__2_1208_);
v___x_1210_ = lean_apply_1(v_h__1_1207_, v_m_u2081_1205_);
return v___x_1210_;
}
else
{
lean_dec(v_h__1_1207_);
if (lean_obj_tag(v_m_u2081_1205_) == 0)
{
lean_object* v___x_1211_; 
lean_dec(v_h__3_1209_);
v___x_1211_ = lean_apply_2(v_h__2_1208_, v_m_u2082_1206_, lean_box(0));
return v___x_1211_;
}
else
{
lean_object* v_p_1212_; lean_object* v_m_1213_; lean_object* v_p_1214_; lean_object* v_m_1215_; lean_object* v___x_1216_; 
lean_dec(v_h__2_1208_);
v_p_1212_ = lean_ctor_get(v_m_u2082_1206_, 0);
lean_inc_ref(v_p_1212_);
v_m_1213_ = lean_ctor_get(v_m_u2082_1206_, 1);
lean_inc(v_m_1213_);
lean_dec_ref_known(v_m_u2082_1206_, 2);
v_p_1214_ = lean_ctor_get(v_m_u2081_1205_, 0);
lean_inc_ref(v_p_1214_);
v_m_1215_ = lean_ctor_get(v_m_u2081_1205_, 1);
lean_inc(v_m_1215_);
lean_dec_ref_known(v_m_u2081_1205_, 2);
v___x_1216_ = lean_apply_4(v_h__3_1209_, v_p_1214_, v_m_1215_, v_p_1212_, v_m_1213_);
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul__nc(lean_object* v_m_u2081_1217_, lean_object* v_m_u2082_1218_){
_start:
{
if (lean_obj_tag(v_m_u2081_1217_) == 0)
{
return v_m_u2082_1218_;
}
else
{
lean_object* v_m_1219_; 
v_m_1219_ = lean_ctor_get(v_m_u2081_1217_, 1);
if (lean_obj_tag(v_m_1219_) == 0)
{
lean_object* v_p_1220_; lean_object* v___x_1221_; 
v_p_1220_ = lean_ctor_get(v_m_u2081_1217_, 0);
lean_inc_ref(v_p_1220_);
lean_dec_ref_known(v_m_u2081_1217_, 2);
v___x_1221_ = l_Lean_Grind_CommRing_Mon_mulPow__nc(v_p_1220_, v_m_u2082_1218_);
return v___x_1221_;
}
else
{
lean_object* v_p_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1230_; 
lean_inc(v_m_1219_);
v_p_1222_ = lean_ctor_get(v_m_u2081_1217_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_m_u2081_1217_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v_m_u2081_1217_, 1);
lean_dec(v_unused_1231_);
v___x_1224_ = v_m_u2081_1217_;
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_p_1222_);
lean_dec(v_m_u2081_1217_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_1219_, v_m_u2082_1218_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v___x_1226_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_p_1222_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object* v_x_1232_){
_start:
{
if (lean_obj_tag(v_x_1232_) == 0)
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_unsigned_to_nat(0u);
return v___x_1233_;
}
else
{
lean_object* v_p_1234_; lean_object* v_m_1235_; lean_object* v_k_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_p_1234_ = lean_ctor_get(v_x_1232_, 0);
v_m_1235_ = lean_ctor_get(v_x_1232_, 1);
v_k_1236_ = lean_ctor_get(v_p_1234_, 1);
v___x_1237_ = l_Lean_Grind_CommRing_Mon_degree(v_m_1235_);
v___x_1238_ = lean_nat_add(v_k_1236_, v___x_1237_);
lean_dec(v___x_1237_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree___boxed(lean_object* v_x_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Grind_CommRing_Mon_degree(v_x_1239_);
lean_dec(v_x_1239_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object* v_x_1241_, lean_object* v_h__1_1242_, lean_object* v_h__2_1243_){
_start:
{
if (lean_obj_tag(v_x_1241_) == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec(v_h__2_1243_);
v___x_1244_ = lean_box(0);
v___x_1245_ = lean_apply_1(v_h__1_1242_, v___x_1244_);
return v___x_1245_;
}
else
{
lean_object* v_p_1246_; lean_object* v_m_1247_; lean_object* v___x_1248_; 
lean_dec(v_h__1_1242_);
v_p_1246_ = lean_ctor_get(v_x_1241_, 0);
lean_inc_ref(v_p_1246_);
v_m_1247_ = lean_ctor_get(v_x_1241_, 1);
lean_inc(v_m_1247_);
lean_dec_ref_known(v_x_1241_, 2);
v___x_1248_ = lean_apply_2(v_h__2_1243_, v_p_1246_, v_m_1247_);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object* v_motive_1249_, lean_object* v_x_1250_, lean_object* v_h__1_1251_, lean_object* v_h__2_1252_){
_start:
{
if (lean_obj_tag(v_x_1250_) == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec(v_h__2_1252_);
v___x_1253_ = lean_box(0);
v___x_1254_ = lean_apply_1(v_h__1_1251_, v___x_1253_);
return v___x_1254_;
}
else
{
lean_object* v_p_1255_; lean_object* v_m_1256_; lean_object* v___x_1257_; 
lean_dec(v_h__1_1251_);
v_p_1255_ = lean_ctor_get(v_x_1250_, 0);
lean_inc_ref(v_p_1255_);
v_m_1256_ = lean_ctor_get(v_x_1250_, 1);
lean_inc(v_m_1256_);
lean_dec_ref_known(v_x_1250_, 2);
v___x_1257_ = lean_apply_2(v_h__2_1252_, v_p_1255_, v_m_1256_);
return v___x_1257_;
}
}
}
uint8_t l_Lean_Grind_CommRing_Var_revlex(lean_object* v_x_1258_, lean_object* v_y_1259_){
_start:
{
uint8_t v___x_1260_; 
v___x_1260_ = l_Nat_blt(v_x_1258_, v_y_1259_);
if (v___x_1260_ == 0)
{
uint8_t v___x_1261_; 
v___x_1261_ = l_Nat_blt(v_y_1259_, v_x_1258_);
if (v___x_1261_ == 0)
{
uint8_t v___x_1262_; 
v___x_1262_ = 1;
return v___x_1262_;
}
else
{
uint8_t v___x_1263_; 
v___x_1263_ = 0;
return v___x_1263_;
}
}
else
{
uint8_t v___x_1264_; 
v___x_1264_ = 2;
return v___x_1264_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Var_revlex_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1258_ = stack[0].m_obj;
lean_object* v_y_1259_ = stack[1].m_obj;
uint8_t v_res_1265_;
v_res_1265_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1258_, v_y_1259_);
stack->m_num = v_res_1265_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_revlex___boxed(lean_object* v_x_1266_, lean_object* v_y_1267_){
_start:
{
uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_res_1268_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1266_, v_y_1267_);
lean_dec(v_y_1267_);
lean_dec(v_x_1266_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
uint8_t l_Lean_Grind_CommRing_powerRevlex(lean_object* v_k_u2081_1270_, lean_object* v_k_u2082_1271_){
_start:
{
uint8_t v___x_1272_; 
v___x_1272_ = l_Nat_blt(v_k_u2081_1270_, v_k_u2082_1271_);
if (v___x_1272_ == 0)
{
uint8_t v___x_1273_; 
v___x_1273_ = l_Nat_blt(v_k_u2082_1271_, v_k_u2081_1270_);
if (v___x_1273_ == 0)
{
uint8_t v___x_1274_; 
v___x_1274_ = 1;
return v___x_1274_;
}
else
{
uint8_t v___x_1275_; 
v___x_1275_ = 0;
return v___x_1275_;
}
}
else
{
uint8_t v___x_1276_; 
v___x_1276_ = 2;
return v___x_1276_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_powerRevlex_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_u2081_1270_ = stack[0].m_obj;
lean_object* v_k_u2082_1271_ = stack[1].m_obj;
uint8_t v_res_1277_;
v_res_1277_ = l_Lean_Grind_CommRing_powerRevlex(v_k_u2081_1270_, v_k_u2082_1271_);
stack->m_num = v_res_1277_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_powerRevlex___boxed(lean_object* v_k_u2081_1278_, lean_object* v_k_u2082_1279_){
_start:
{
uint8_t v_res_1280_; lean_object* v_r_1281_; 
v_res_1280_ = l_Lean_Grind_CommRing_powerRevlex(v_k_u2081_1278_, v_k_u2082_1279_);
lean_dec(v_k_u2082_1279_);
lean_dec(v_k_u2081_1278_);
v_r_1281_ = lean_box(v_res_1280_);
return v_r_1281_;
}
}
lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(uint8_t v_c_1282_, lean_object* v_h__1_1283_, lean_object* v_h__2_1284_){
_start:
{
if (v_c_1282_ == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_dec(v_h__1_1283_);
v___x_1285_ = lean_box(0);
v___x_1286_ = lean_apply_1(v_h__2_1284_, v___x_1285_);
return v___x_1286_;
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec(v_h__2_1284_);
v___x_1287_ = lean_box(0);
v___x_1288_ = lean_apply_1(v_h__1_1283_, v___x_1287_);
return v___x_1288_;
}
}
}
LEAN_EXPORT void l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_1282_ = stack[0].m_num;
lean_object* v_h__1_1283_ = stack[1].m_obj;
lean_object* v_h__2_1284_ = stack[2].m_obj;
lean_object* v_res_1289_;
v_res_1289_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(v_c_1282_, v_h__1_1283_, v_h__2_1284_);
stack->m_obj
 = v_res_1289_;
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg___boxed(lean_object* v_c_1290_, lean_object* v_h__1_1291_, lean_object* v_h__2_1292_){
_start:
{
uint8_t v_c_24__boxed_1293_; lean_object* v_res_1294_; 
v_c_24__boxed_1293_ = lean_unbox(v_c_1290_);
v_res_1294_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(v_c_24__boxed_1293_, v_h__1_1291_, v_h__2_1292_);
return v_res_1294_;
}
}
lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(lean_object* v_motive_1295_, uint8_t v_c_1296_, lean_object* v_h__1_1297_, lean_object* v_h__2_1298_){
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
LEAN_EXPORT void l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_c_1296_ = stack[1].m_num;
lean_object* v_h__1_1297_ = stack[2].m_obj;
lean_object* v_h__2_1298_ = stack[3].m_obj;
lean_object* v_res_1303_;
v_res_1303_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(lean_box(0), v_c_1296_, v_h__1_1297_, v_h__2_1298_);
stack->m_obj
 = v_res_1303_;
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___boxed(lean_object* v_motive_1304_, lean_object* v_c_1305_, lean_object* v_h__1_1306_, lean_object* v_h__2_1307_){
_start:
{
uint8_t v_c_41__boxed_1308_; lean_object* v_res_1309_; 
v_c_41__boxed_1308_ = lean_unbox(v_c_1305_);
v_res_1309_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(v_motive_1304_, v_c_41__boxed_1308_, v_h__1_1306_, v_h__2_1307_);
return v_res_1309_;
}
}
uint8_t l_Lean_Grind_CommRing_Power_revlex(lean_object* v_p_u2081_1310_, lean_object* v_p_u2082_1311_){
_start:
{
lean_object* v_x_1312_; lean_object* v_k_1313_; lean_object* v_x_1314_; lean_object* v_k_1315_; uint8_t v___x_1316_; 
v_x_1312_ = lean_ctor_get(v_p_u2081_1310_, 0);
v_k_1313_ = lean_ctor_get(v_p_u2081_1310_, 1);
v_x_1314_ = lean_ctor_get(v_p_u2082_1311_, 0);
v_k_1315_ = lean_ctor_get(v_p_u2082_1311_, 1);
v___x_1316_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1312_, v_x_1314_);
if (v___x_1316_ == 1)
{
uint8_t v___x_1317_; 
v___x_1317_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1313_, v_k_1315_);
return v___x_1317_;
}
else
{
return v___x_1316_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Power_revlex_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_1310_ = stack[0].m_obj;
lean_object* v_p_u2082_1311_ = stack[1].m_obj;
uint8_t v_res_1318_;
v_res_1318_ = l_Lean_Grind_CommRing_Power_revlex(v_p_u2081_1310_, v_p_u2082_1311_);
stack->m_num = v_res_1318_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_revlex___boxed(lean_object* v_p_u2081_1319_, lean_object* v_p_u2082_1320_){
_start:
{
uint8_t v_res_1321_; lean_object* v_r_1322_; 
v_res_1321_ = l_Lean_Grind_CommRing_Power_revlex(v_p_u2081_1319_, v_p_u2082_1320_);
lean_dec_ref(v_p_u2082_1320_);
lean_dec_ref(v_p_u2081_1319_);
v_r_1322_ = lean_box(v_res_1321_);
return v_r_1322_;
}
}
uint8_t l_Lean_Grind_CommRing_Mon_revlexWF(lean_object* v_m_u2081_1323_, lean_object* v_m_u2082_1324_){
_start:
{
if (lean_obj_tag(v_m_u2081_1323_) == 0)
{
if (lean_obj_tag(v_m_u2082_1324_) == 0)
{
uint8_t v___x_1325_; 
v___x_1325_ = 1;
return v___x_1325_;
}
else
{
uint8_t v___x_1326_; 
v___x_1326_ = 2;
return v___x_1326_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1324_) == 0)
{
uint8_t v___x_1327_; 
v___x_1327_ = 0;
return v___x_1327_;
}
else
{
lean_object* v_p_1328_; lean_object* v_p_1329_; lean_object* v_m_1330_; lean_object* v_m_1331_; lean_object* v_x_1332_; lean_object* v_k_1333_; lean_object* v_x_1334_; lean_object* v_k_1335_; uint8_t v___x_1336_; 
v_p_1328_ = lean_ctor_get(v_m_u2081_1323_, 0);
v_p_1329_ = lean_ctor_get(v_m_u2082_1324_, 0);
v_m_1330_ = lean_ctor_get(v_m_u2081_1323_, 1);
v_m_1331_ = lean_ctor_get(v_m_u2082_1324_, 1);
v_x_1332_ = lean_ctor_get(v_p_1328_, 0);
v_k_1333_ = lean_ctor_get(v_p_1328_, 1);
v_x_1334_ = lean_ctor_get(v_p_1329_, 0);
v_k_1335_ = lean_ctor_get(v_p_1329_, 1);
v___x_1336_ = lean_nat_dec_eq(v_x_1332_, v_x_1334_);
if (v___x_1336_ == 0)
{
uint8_t v___x_1337_; 
v___x_1337_ = l_Nat_blt(v_x_1332_, v_x_1334_);
if (v___x_1337_ == 0)
{
uint8_t v___x_1338_; 
v___x_1338_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1323_, v_m_1331_);
if (v___x_1338_ == 1)
{
uint8_t v___x_1339_; 
v___x_1339_ = 2;
return v___x_1339_;
}
else
{
return v___x_1338_;
}
}
else
{
uint8_t v___x_1340_; 
v___x_1340_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1330_, v_m_u2082_1324_);
if (v___x_1340_ == 1)
{
uint8_t v___x_1341_; 
v___x_1341_ = 0;
return v___x_1341_;
}
else
{
return v___x_1340_;
}
}
}
else
{
uint8_t v___x_1342_; 
v___x_1342_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1330_, v_m_1331_);
if (v___x_1342_ == 1)
{
uint8_t v___x_1343_; 
v___x_1343_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1333_, v_k_1335_);
return v___x_1343_;
}
else
{
return v___x_1342_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Mon_revlexWF_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_u2081_1323_ = stack[0].m_obj;
lean_object* v_m_u2082_1324_ = stack[1].m_obj;
uint8_t v_res_1344_;
v_res_1344_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1323_, v_m_u2082_1324_);
stack->m_num = v_res_1344_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexWF___boxed(lean_object* v_m_u2081_1345_, lean_object* v_m_u2082_1346_){
_start:
{
uint8_t v_res_1347_; lean_object* v_r_1348_; 
v_res_1347_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1345_, v_m_u2082_1346_);
lean_dec(v_m_u2082_1346_);
lean_dec(v_m_u2081_1345_);
v_r_1348_ = lean_box(v_res_1347_);
return v_r_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(lean_object* v_m_u2081_1349_, lean_object* v_m_u2082_1350_, lean_object* v_h__1_1351_, lean_object* v_h__2_1352_, lean_object* v_h__3_1353_, lean_object* v_h__4_1354_){
_start:
{
if (lean_obj_tag(v_m_u2081_1349_) == 0)
{
lean_dec(v_h__4_1354_);
lean_dec(v_h__3_1353_);
if (lean_obj_tag(v_m_u2082_1350_) == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v_h__2_1352_);
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_apply_1(v_h__1_1351_, v___x_1355_);
return v___x_1356_;
}
else
{
lean_object* v_p_1357_; lean_object* v_m_1358_; lean_object* v___x_1359_; 
lean_dec(v_h__1_1351_);
v_p_1357_ = lean_ctor_get(v_m_u2082_1350_, 0);
lean_inc_ref(v_p_1357_);
v_m_1358_ = lean_ctor_get(v_m_u2082_1350_, 1);
lean_inc(v_m_1358_);
lean_dec_ref_known(v_m_u2082_1350_, 2);
v___x_1359_ = lean_apply_2(v_h__2_1352_, v_p_1357_, v_m_1358_);
return v___x_1359_;
}
}
else
{
lean_dec(v_h__2_1352_);
lean_dec(v_h__1_1351_);
if (lean_obj_tag(v_m_u2082_1350_) == 0)
{
lean_object* v_p_1360_; lean_object* v_m_1361_; lean_object* v___x_1362_; 
lean_dec(v_h__4_1354_);
v_p_1360_ = lean_ctor_get(v_m_u2081_1349_, 0);
lean_inc_ref(v_p_1360_);
v_m_1361_ = lean_ctor_get(v_m_u2081_1349_, 1);
lean_inc(v_m_1361_);
lean_dec_ref_known(v_m_u2081_1349_, 2);
v___x_1362_ = lean_apply_2(v_h__3_1353_, v_p_1360_, v_m_1361_);
return v___x_1362_;
}
else
{
lean_object* v_p_1363_; lean_object* v_m_1364_; lean_object* v_p_1365_; lean_object* v_m_1366_; lean_object* v___x_1367_; 
lean_dec(v_h__3_1353_);
v_p_1363_ = lean_ctor_get(v_m_u2081_1349_, 0);
lean_inc_ref(v_p_1363_);
v_m_1364_ = lean_ctor_get(v_m_u2081_1349_, 1);
lean_inc(v_m_1364_);
lean_dec_ref_known(v_m_u2081_1349_, 2);
v_p_1365_ = lean_ctor_get(v_m_u2082_1350_, 0);
lean_inc_ref(v_p_1365_);
v_m_1366_ = lean_ctor_get(v_m_u2082_1350_, 1);
lean_inc(v_m_1366_);
lean_dec_ref_known(v_m_u2082_1350_, 2);
v___x_1367_ = lean_apply_4(v_h__4_1354_, v_p_1363_, v_m_1364_, v_p_1365_, v_m_1366_);
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter(lean_object* v_motive_1368_, lean_object* v_m_u2081_1369_, lean_object* v_m_u2082_1370_, lean_object* v_h__1_1371_, lean_object* v_h__2_1372_, lean_object* v_h__3_1373_, lean_object* v_h__4_1374_){
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
uint8_t l_Lean_Grind_CommRing_Mon_revlexFuel(lean_object* v_fuel_1388_, lean_object* v_m_u2081_1389_, lean_object* v_m_u2082_1390_){
_start:
{
lean_object* v_zero_1391_; uint8_t v_isZero_1392_; 
v_zero_1391_ = lean_unsigned_to_nat(0u);
v_isZero_1392_ = lean_nat_dec_eq(v_fuel_1388_, v_zero_1391_);
if (v_isZero_1392_ == 1)
{
uint8_t v___x_1393_; 
v___x_1393_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1389_, v_m_u2082_1390_);
return v___x_1393_;
}
else
{
if (lean_obj_tag(v_m_u2081_1389_) == 0)
{
if (lean_obj_tag(v_m_u2082_1390_) == 0)
{
uint8_t v___x_1394_; 
v___x_1394_ = 1;
return v___x_1394_;
}
else
{
uint8_t v___x_1395_; 
v___x_1395_ = 2;
return v___x_1395_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1390_) == 0)
{
uint8_t v___x_1396_; 
v___x_1396_ = 0;
return v___x_1396_;
}
else
{
lean_object* v_p_1397_; lean_object* v_p_1398_; lean_object* v_m_1399_; lean_object* v_m_1400_; lean_object* v_x_1401_; lean_object* v_k_1402_; lean_object* v_x_1403_; lean_object* v_k_1404_; lean_object* v_one_1405_; lean_object* v_n_1406_; uint8_t v___x_1407_; 
v_p_1397_ = lean_ctor_get(v_m_u2081_1389_, 0);
v_p_1398_ = lean_ctor_get(v_m_u2082_1390_, 0);
v_m_1399_ = lean_ctor_get(v_m_u2081_1389_, 1);
v_m_1400_ = lean_ctor_get(v_m_u2082_1390_, 1);
v_x_1401_ = lean_ctor_get(v_p_1397_, 0);
v_k_1402_ = lean_ctor_get(v_p_1397_, 1);
v_x_1403_ = lean_ctor_get(v_p_1398_, 0);
v_k_1404_ = lean_ctor_get(v_p_1398_, 1);
v_one_1405_ = lean_unsigned_to_nat(1u);
v_n_1406_ = lean_nat_sub(v_fuel_1388_, v_one_1405_);
v___x_1407_ = lean_nat_dec_eq(v_x_1401_, v_x_1403_);
if (v___x_1407_ == 0)
{
uint8_t v___x_1408_; 
v___x_1408_ = l_Nat_blt(v_x_1401_, v_x_1403_);
if (v___x_1408_ == 0)
{
uint8_t v___x_1409_; 
v___x_1409_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1406_, v_m_u2081_1389_, v_m_1400_);
lean_dec(v_n_1406_);
if (v___x_1409_ == 1)
{
uint8_t v___x_1410_; 
v___x_1410_ = 2;
return v___x_1410_;
}
else
{
return v___x_1409_;
}
}
else
{
uint8_t v___x_1411_; 
v___x_1411_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1406_, v_m_1399_, v_m_u2082_1390_);
lean_dec(v_n_1406_);
if (v___x_1411_ == 1)
{
uint8_t v___x_1412_; 
v___x_1412_ = 0;
return v___x_1412_;
}
else
{
return v___x_1411_;
}
}
}
else
{
uint8_t v___x_1413_; 
v___x_1413_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1406_, v_m_1399_, v_m_1400_);
lean_dec(v_n_1406_);
if (v___x_1413_ == 1)
{
uint8_t v___x_1414_; 
v___x_1414_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1402_, v_k_1404_);
return v___x_1414_;
}
else
{
return v___x_1413_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Mon_revlexFuel_0interp(lean_interpreter_value* stack)
{
lean_object* v_fuel_1388_ = stack[0].m_obj;
lean_object* v_m_u2081_1389_ = stack[1].m_obj;
lean_object* v_m_u2082_1390_ = stack[2].m_obj;
uint8_t v_res_1415_;
v_res_1415_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_fuel_1388_, v_m_u2081_1389_, v_m_u2082_1390_);
stack->m_num = v_res_1415_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexFuel___boxed(lean_object* v_fuel_1416_, lean_object* v_m_u2081_1417_, lean_object* v_m_u2082_1418_){
_start:
{
uint8_t v_res_1419_; lean_object* v_r_1420_; 
v_res_1419_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_fuel_1416_, v_m_u2081_1417_, v_m_u2082_1418_);
lean_dec(v_m_u2082_1418_);
lean_dec(v_m_u2081_1417_);
lean_dec(v_fuel_1416_);
v_r_1420_ = lean_box(v_res_1419_);
return v_r_1420_;
}
}
uint8_t l_Lean_Grind_CommRing_Mon_revlex(lean_object* v_m_u2081_1421_, lean_object* v_m_u2082_1422_){
_start:
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = lean_unsigned_to_nat(1000000u);
v___x_1424_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v___x_1423_, v_m_u2081_1421_, v_m_u2082_1422_);
return v___x_1424_;
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Mon_revlex_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_u2081_1421_ = stack[0].m_obj;
lean_object* v_m_u2082_1422_ = stack[1].m_obj;
uint8_t v_res_1425_;
v_res_1425_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1421_, v_m_u2082_1422_);
stack->m_num = v_res_1425_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlex___boxed(lean_object* v_m_u2081_1426_, lean_object* v_m_u2082_1427_){
_start:
{
uint8_t v_res_1428_; lean_object* v_r_1429_; 
v_res_1428_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1426_, v_m_u2082_1427_);
lean_dec(v_m_u2082_1427_);
lean_dec(v_m_u2081_1426_);
v_r_1429_ = lean_box(v_res_1428_);
return v_r_1429_;
}
}
uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object* v_m_u2081_1430_, lean_object* v_m_u2082_1431_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2081_1430_);
v___x_1433_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2082_1431_);
v___x_1434_ = lean_nat_dec_lt(v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
uint8_t v___x_1435_; 
v___x_1435_ = lean_nat_dec_eq(v___x_1432_, v___x_1433_);
lean_dec(v___x_1433_);
lean_dec(v___x_1432_);
if (v___x_1435_ == 0)
{
uint8_t v___x_1436_; 
v___x_1436_ = 2;
return v___x_1436_;
}
else
{
uint8_t v___x_1437_; 
v___x_1437_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1430_, v_m_u2082_1431_);
return v___x_1437_;
}
}
else
{
uint8_t v___x_1438_; 
lean_dec(v___x_1433_);
lean_dec(v___x_1432_);
v___x_1438_ = 0;
return v___x_1438_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Mon_grevlex_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_u2081_1430_ = stack[0].m_obj;
lean_object* v_m_u2082_1431_ = stack[1].m_obj;
uint8_t v_res_1439_;
v_res_1439_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_u2081_1430_, v_m_u2082_1431_);
stack->m_num = v_res_1439_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_grevlex___boxed(lean_object* v_m_u2081_1440_, lean_object* v_m_u2082_1441_){
_start:
{
uint8_t v_res_1442_; lean_object* v_r_1443_; 
v_res_1442_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_u2081_1440_, v_m_u2082_1441_);
lean_dec(v_m_u2082_1441_);
lean_dec(v_m_u2081_1440_);
v_r_1443_ = lean_box(v_res_1442_);
return v_r_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___impl(lean_object* v_x_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_obj_tag_nat(v_x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___impl___boxed(lean_object* v_x_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Grind_CommRing_Poly_ctorIdx___impl(v_x_1446_);
lean_dec_ref(v_x_1446_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___redArg(lean_object* v_t_1448_, lean_object* v_k_1449_){
_start:
{
if (lean_obj_tag(v_t_1448_) == 0)
{
lean_object* v_k_1450_; lean_object* v___x_1451_; 
v_k_1450_ = lean_ctor_get(v_t_1448_, 0);
lean_inc(v_k_1450_);
lean_dec_ref_known(v_t_1448_, 1);
v___x_1451_ = lean_apply_1(v_k_1449_, v_k_1450_);
return v___x_1451_;
}
else
{
lean_object* v_k_1452_; lean_object* v_v_1453_; lean_object* v_p_1454_; lean_object* v___x_1455_; 
v_k_1452_ = lean_ctor_get(v_t_1448_, 0);
lean_inc(v_k_1452_);
v_v_1453_ = lean_ctor_get(v_t_1448_, 1);
lean_inc(v_v_1453_);
v_p_1454_ = lean_ctor_get(v_t_1448_, 2);
lean_inc_ref(v_p_1454_);
lean_dec_ref_known(v_t_1448_, 3);
v___x_1455_ = lean_apply_3(v_k_1449_, v_k_1452_, v_v_1453_, v_p_1454_);
return v___x_1455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim(lean_object* v_motive_1456_, lean_object* v_ctorIdx_1457_, lean_object* v_t_1458_, lean_object* v_h_1459_, lean_object* v_k_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1458_, v_k_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___boxed(lean_object* v_motive_1462_, lean_object* v_ctorIdx_1463_, lean_object* v_t_1464_, lean_object* v_h_1465_, lean_object* v_k_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Grind_CommRing_Poly_ctorElim(v_motive_1462_, v_ctorIdx_1463_, v_t_1464_, v_h_1465_, v_k_1466_);
lean_dec(v_ctorIdx_1463_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim___redArg(lean_object* v_t_1468_, lean_object* v_num_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1468_, v_num_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim(lean_object* v_motive_1471_, lean_object* v_t_1472_, lean_object* v_h_1473_, lean_object* v_num_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1472_, v_num_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim___redArg(lean_object* v_t_1476_, lean_object* v_add_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1476_, v_add_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim(lean_object* v_motive_1479_, lean_object* v_t_1480_, lean_object* v_h_1481_, lean_object* v_add_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1480_, v_add_1482_);
return v___x_1483_;
}
}
uint8_t l_Lean_Grind_CommRing_instBEqPoly_beq(lean_object* v_x_1484_, lean_object* v_x_1485_){
_start:
{
if (lean_obj_tag(v_x_1484_) == 0)
{
if (lean_obj_tag(v_x_1485_) == 0)
{
lean_object* v_k_1486_; lean_object* v_k_1487_; uint8_t v___x_1488_; 
v_k_1486_ = lean_ctor_get(v_x_1484_, 0);
v_k_1487_ = lean_ctor_get(v_x_1485_, 0);
v___x_1488_ = lean_int_dec_eq(v_k_1486_, v_k_1487_);
return v___x_1488_;
}
else
{
uint8_t v___x_1489_; 
v___x_1489_ = 0;
return v___x_1489_;
}
}
else
{
if (lean_obj_tag(v_x_1485_) == 1)
{
lean_object* v_k_1490_; lean_object* v_v_1491_; lean_object* v_p_1492_; lean_object* v_k_1493_; lean_object* v_v_1494_; lean_object* v_p_1495_; uint8_t v___x_1496_; 
v_k_1490_ = lean_ctor_get(v_x_1484_, 0);
v_v_1491_ = lean_ctor_get(v_x_1484_, 1);
v_p_1492_ = lean_ctor_get(v_x_1484_, 2);
v_k_1493_ = lean_ctor_get(v_x_1485_, 0);
v_v_1494_ = lean_ctor_get(v_x_1485_, 1);
v_p_1495_ = lean_ctor_get(v_x_1485_, 2);
v___x_1496_ = lean_int_dec_eq(v_k_1490_, v_k_1493_);
if (v___x_1496_ == 0)
{
return v___x_1496_;
}
else
{
uint8_t v___x_1497_; 
v___x_1497_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_v_1491_, v_v_1494_);
if (v___x_1497_ == 0)
{
return v___x_1497_;
}
else
{
v_x_1484_ = v_p_1492_;
v_x_1485_ = v_p_1495_;
goto _start;
}
}
}
else
{
uint8_t v___x_1499_; 
v___x_1499_ = 0;
return v___x_1499_;
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_instBEqPoly_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1484_ = stack[0].m_obj;
lean_object* v_x_1485_ = stack[1].m_obj;
uint8_t v_res_1500_;
v_res_1500_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_x_1484_, v_x_1485_);
stack->m_num = v_res_1500_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPoly_beq___boxed(lean_object* v_x_1501_, lean_object* v_x_1502_){
_start:
{
uint8_t v_res_1503_; lean_object* v_r_1504_; 
v_res_1503_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_x_1501_, v_x_1502_);
lean_dec_ref(v_x_1502_);
lean_dec_ref(v_x_1501_);
v_r_1504_ = lean_box(v_res_1503_);
return v_r_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_1507_, lean_object* v_x_1508_, lean_object* v_h__1_1509_, lean_object* v_h__2_1510_, lean_object* v_h__3_1511_){
_start:
{
if (lean_obj_tag(v_x_1507_) == 0)
{
lean_dec(v_h__2_1510_);
if (lean_obj_tag(v_x_1508_) == 0)
{
lean_object* v_k_1512_; lean_object* v_k_1513_; lean_object* v___x_1514_; 
lean_dec(v_h__3_1511_);
v_k_1512_ = lean_ctor_get(v_x_1507_, 0);
lean_inc(v_k_1512_);
lean_dec_ref_known(v_x_1507_, 1);
v_k_1513_ = lean_ctor_get(v_x_1508_, 0);
lean_inc(v_k_1513_);
lean_dec_ref_known(v_x_1508_, 1);
v___x_1514_ = lean_apply_2(v_h__1_1509_, v_k_1512_, v_k_1513_);
return v___x_1514_;
}
else
{
lean_object* v___x_1515_; 
lean_dec(v_h__1_1509_);
v___x_1515_ = lean_apply_4(v_h__3_1511_, v_x_1507_, v_x_1508_, lean_box(0), lean_box(0));
return v___x_1515_;
}
}
else
{
lean_dec(v_h__1_1509_);
if (lean_obj_tag(v_x_1508_) == 1)
{
lean_object* v_k_1516_; lean_object* v_v_1517_; lean_object* v_p_1518_; lean_object* v_k_1519_; lean_object* v_v_1520_; lean_object* v_p_1521_; lean_object* v___x_1522_; 
lean_dec(v_h__3_1511_);
v_k_1516_ = lean_ctor_get(v_x_1507_, 0);
lean_inc(v_k_1516_);
v_v_1517_ = lean_ctor_get(v_x_1507_, 1);
lean_inc(v_v_1517_);
v_p_1518_ = lean_ctor_get(v_x_1507_, 2);
lean_inc_ref(v_p_1518_);
lean_dec_ref_known(v_x_1507_, 3);
v_k_1519_ = lean_ctor_get(v_x_1508_, 0);
lean_inc(v_k_1519_);
v_v_1520_ = lean_ctor_get(v_x_1508_, 1);
lean_inc(v_v_1520_);
v_p_1521_ = lean_ctor_get(v_x_1508_, 2);
lean_inc_ref(v_p_1521_);
lean_dec_ref_known(v_x_1508_, 3);
v___x_1522_ = lean_apply_6(v_h__2_1510_, v_k_1516_, v_v_1517_, v_p_1518_, v_k_1519_, v_v_1520_, v_p_1521_);
return v___x_1522_;
}
else
{
lean_object* v___x_1523_; 
lean_dec(v_h__2_1510_);
v___x_1523_ = lean_apply_4(v_h__3_1511_, v_x_1507_, v_x_1508_, lean_box(0), lean_box(0));
return v___x_1523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_, lean_object* v_h__1_1527_, lean_object* v_h__2_1528_, lean_object* v_h__3_1529_){
_start:
{
if (lean_obj_tag(v_x_1525_) == 0)
{
lean_dec(v_h__2_1528_);
if (lean_obj_tag(v_x_1526_) == 0)
{
lean_object* v_k_1530_; lean_object* v_k_1531_; lean_object* v___x_1532_; 
lean_dec(v_h__3_1529_);
v_k_1530_ = lean_ctor_get(v_x_1525_, 0);
lean_inc(v_k_1530_);
lean_dec_ref_known(v_x_1525_, 1);
v_k_1531_ = lean_ctor_get(v_x_1526_, 0);
lean_inc(v_k_1531_);
lean_dec_ref_known(v_x_1526_, 1);
v___x_1532_ = lean_apply_2(v_h__1_1527_, v_k_1530_, v_k_1531_);
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; 
lean_dec(v_h__1_1527_);
v___x_1533_ = lean_apply_4(v_h__3_1529_, v_x_1525_, v_x_1526_, lean_box(0), lean_box(0));
return v___x_1533_;
}
}
else
{
lean_dec(v_h__1_1527_);
if (lean_obj_tag(v_x_1526_) == 1)
{
lean_object* v_k_1534_; lean_object* v_v_1535_; lean_object* v_p_1536_; lean_object* v_k_1537_; lean_object* v_v_1538_; lean_object* v_p_1539_; lean_object* v___x_1540_; 
lean_dec(v_h__3_1529_);
v_k_1534_ = lean_ctor_get(v_x_1525_, 0);
lean_inc(v_k_1534_);
v_v_1535_ = lean_ctor_get(v_x_1525_, 1);
lean_inc(v_v_1535_);
v_p_1536_ = lean_ctor_get(v_x_1525_, 2);
lean_inc_ref(v_p_1536_);
lean_dec_ref_known(v_x_1525_, 3);
v_k_1537_ = lean_ctor_get(v_x_1526_, 0);
lean_inc(v_k_1537_);
v_v_1538_ = lean_ctor_get(v_x_1526_, 1);
lean_inc(v_v_1538_);
v_p_1539_ = lean_ctor_get(v_x_1526_, 2);
lean_inc_ref(v_p_1539_);
lean_dec_ref_known(v_x_1526_, 3);
v___x_1540_ = lean_apply_6(v_h__2_1528_, v_k_1534_, v_v_1535_, v_p_1536_, v_k_1537_, v_v_1538_, v_p_1539_);
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; 
lean_dec(v_h__2_1528_);
v___x_1541_ = lean_apply_4(v_h__3_1529_, v_x_1525_, v_x_1526_, lean_box(0), lean_box(0));
return v___x_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr(lean_object* v_x_1554_, lean_object* v_prec_1555_){
_start:
{
lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; 
if (lean_obj_tag(v_x_1554_) == 0)
{
lean_object* v_k_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1588_; 
v_k_1565_ = lean_ctor_get(v_x_1554_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_x_1554_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1567_ = v_x_1554_;
v_isShared_1568_ = v_isSharedCheck_1588_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_k_1565_);
lean_dec(v_x_1554_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1588_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___y_1570_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = lean_unsigned_to_nat(1024u);
v___x_1585_ = lean_nat_dec_le(v___x_1584_, v_prec_1555_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1570_ = v___x_1586_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1570_ = v___x_1587_;
goto v___jp_1569_;
}
v___jp_1569_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1571_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__2));
v___x_1572_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1573_ = lean_int_dec_lt(v_k_1565_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = l_Int_repr(v_k_1565_);
lean_dec(v_k_1565_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set_tag(v___x_1567_, 3);
lean_ctor_set(v___x_1567_, 0, v___x_1574_);
v___x_1576_ = v___x_1567_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
v___y_1557_ = v___y_1570_;
v___y_1558_ = v___x_1571_;
v___y_1559_ = v___x_1576_;
goto v___jp_1556_;
}
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1578_ = lean_unsigned_to_nat(1024u);
v___x_1579_ = l_Int_repr(v_k_1565_);
lean_dec(v_k_1565_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set_tag(v___x_1567_, 3);
lean_ctor_set(v___x_1567_, 0, v___x_1579_);
v___x_1581_ = v___x_1567_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Repr_addAppParen(v___x_1581_, v___x_1578_);
v___y_1557_ = v___y_1570_;
v___y_1558_ = v___x_1571_;
v___y_1559_ = v___x_1582_;
goto v___jp_1556_;
}
}
}
}
}
else
{
lean_object* v_k_1589_; lean_object* v_v_1590_; lean_object* v_p_1591_; lean_object* v___x_1592_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1610_; uint8_t v___x_1620_; 
v_k_1589_ = lean_ctor_get(v_x_1554_, 0);
lean_inc(v_k_1589_);
v_v_1590_ = lean_ctor_get(v_x_1554_, 1);
lean_inc(v_v_1590_);
v_p_1591_ = lean_ctor_get(v_x_1554_, 2);
lean_inc_ref(v_p_1591_);
lean_dec_ref_known(v_x_1554_, 3);
v___x_1592_ = lean_unsigned_to_nat(1024u);
v___x_1620_ = lean_nat_dec_le(v___x_1592_, v_prec_1555_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1610_ = v___x_1621_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1610_ = v___x_1622_;
goto v___jp_1609_;
}
v___jp_1593_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_inc(v___y_1595_);
v___x_1598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___y_1595_);
lean_ctor_set(v___x_1598_, 1, v___y_1597_);
lean_inc_n(v___y_1594_, 2);
v___x_1599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v___y_1594_);
v___x_1600_ = l_Lean_Grind_CommRing_instReprMon_repr(v_v_1590_, v___x_1592_);
v___x_1601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v___y_1594_);
v___x_1603_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_p_1591_, v___x_1592_);
v___x_1604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
lean_inc(v___y_1596_);
v___x_1605_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___y_1596_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = 0;
v___x_1607_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1607_, 0, v___x_1605_);
lean_ctor_set_uint8(v___x_1607_, sizeof(void*)*1, v___x_1606_);
v___x_1608_ = l_Repr_addAppParen(v___x_1607_, v_prec_1555_);
return v___x_1608_;
}
v___jp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1611_ = lean_box(1);
v___x_1612_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__5));
v___x_1613_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1614_ = lean_int_dec_lt(v_k_1589_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = l_Int_repr(v_k_1589_);
lean_dec(v_k_1589_);
v___x_1616_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
v___y_1594_ = v___x_1611_;
v___y_1595_ = v___x_1612_;
v___y_1596_ = v___y_1610_;
v___y_1597_ = v___x_1616_;
goto v___jp_1593_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = l_Int_repr(v_k_1589_);
lean_dec(v_k_1589_);
v___x_1618_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
v___x_1619_ = l_Repr_addAppParen(v___x_1618_, v___x_1592_);
v___y_1594_ = v___x_1611_;
v___y_1595_ = v___x_1612_;
v___y_1596_ = v___y_1610_;
v___y_1597_ = v___x_1619_;
goto v___jp_1593_;
}
}
}
v___jp_1556_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_inc(v___y_1558_);
v___x_1560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___y_1558_);
lean_ctor_set(v___x_1560_, 1, v___y_1559_);
lean_inc(v___y_1557_);
v___x_1561_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___y_1557_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = 0;
v___x_1563_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set_uint8(v___x_1563_, sizeof(void*)*1, v___x_1562_);
v___x_1564_ = l_Repr_addAppParen(v___x_1563_, v_prec_1555_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___boxed(lean_object* v_x_1623_, lean_object* v_prec_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_x_1623_, v_prec_1624_);
lean_dec(v_prec_1624_);
return v_res_1625_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default(void){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_1630_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly(void){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
return v___x_1631_;
}
}
uint64_t l_Lean_Grind_CommRing_instHashablePoly_hash(lean_object* v_x_1632_){
_start:
{
if (lean_obj_tag(v_x_1632_) == 0)
{
lean_object* v_k_1633_; uint64_t v___x_1634_; lean_object* v_intZero_1635_; uint8_t v_isNeg_1636_; 
v_k_1633_ = lean_ctor_get(v_x_1632_, 0);
v___x_1634_ = 0ULL;
v_intZero_1635_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1636_ = lean_int_dec_lt(v_k_1633_, v_intZero_1635_);
if (v_isNeg_1636_ == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint64_t v___x_1640_; uint64_t v___x_1641_; 
v_a_1637_ = lean_nat_abs(v_k_1633_);
v___x_1638_ = lean_unsigned_to_nat(2u);
v___x_1639_ = lean_nat_mul(v___x_1638_, v_a_1637_);
lean_dec(v_a_1637_);
v___x_1640_ = lean_uint64_of_nat(v___x_1639_);
lean_dec(v___x_1639_);
v___x_1641_ = lean_uint64_mix_hash(v___x_1634_, v___x_1640_);
return v___x_1641_;
}
else
{
lean_object* v_abs_1642_; lean_object* v_one_1643_; lean_object* v_a_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; uint64_t v___x_1648_; uint64_t v___x_1649_; 
v_abs_1642_ = lean_nat_abs(v_k_1633_);
v_one_1643_ = lean_unsigned_to_nat(1u);
v_a_1644_ = lean_nat_sub(v_abs_1642_, v_one_1643_);
lean_dec(v_abs_1642_);
v___x_1645_ = lean_unsigned_to_nat(2u);
v___x_1646_ = lean_nat_mul(v___x_1645_, v_a_1644_);
lean_dec(v_a_1644_);
v___x_1647_ = lean_nat_add(v___x_1646_, v_one_1643_);
lean_dec(v___x_1646_);
v___x_1648_ = lean_uint64_of_nat(v___x_1647_);
lean_dec(v___x_1647_);
v___x_1649_ = lean_uint64_mix_hash(v___x_1634_, v___x_1648_);
return v___x_1649_;
}
}
else
{
lean_object* v_k_1650_; lean_object* v_v_1651_; lean_object* v_p_1652_; uint64_t v___x_1653_; uint64_t v___y_1655_; lean_object* v_intZero_1661_; uint8_t v_isNeg_1662_; 
v_k_1650_ = lean_ctor_get(v_x_1632_, 0);
v_v_1651_ = lean_ctor_get(v_x_1632_, 1);
v_p_1652_ = lean_ctor_get(v_x_1632_, 2);
v___x_1653_ = 1ULL;
v_intZero_1661_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1662_ = lean_int_dec_lt(v_k_1650_, v_intZero_1661_);
if (v_isNeg_1662_ == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; uint64_t v___x_1666_; 
v_a_1663_ = lean_nat_abs(v_k_1650_);
v___x_1664_ = lean_unsigned_to_nat(2u);
v___x_1665_ = lean_nat_mul(v___x_1664_, v_a_1663_);
lean_dec(v_a_1663_);
v___x_1666_ = lean_uint64_of_nat(v___x_1665_);
lean_dec(v___x_1665_);
v___y_1655_ = v___x_1666_;
goto v___jp_1654_;
}
else
{
lean_object* v_abs_1667_; lean_object* v_one_1668_; lean_object* v_a_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint64_t v___x_1673_; 
v_abs_1667_ = lean_nat_abs(v_k_1650_);
v_one_1668_ = lean_unsigned_to_nat(1u);
v_a_1669_ = lean_nat_sub(v_abs_1667_, v_one_1668_);
lean_dec(v_abs_1667_);
v___x_1670_ = lean_unsigned_to_nat(2u);
v___x_1671_ = lean_nat_mul(v___x_1670_, v_a_1669_);
lean_dec(v_a_1669_);
v___x_1672_ = lean_nat_add(v___x_1671_, v_one_1668_);
lean_dec(v___x_1671_);
v___x_1673_ = lean_uint64_of_nat(v___x_1672_);
lean_dec(v___x_1672_);
v___y_1655_ = v___x_1673_;
goto v___jp_1654_;
}
v___jp_1654_:
{
uint64_t v___x_1656_; uint64_t v___x_1657_; uint64_t v___x_1658_; uint64_t v___x_1659_; uint64_t v___x_1660_; 
v___x_1656_ = lean_uint64_mix_hash(v___x_1653_, v___y_1655_);
v___x_1657_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_v_1651_);
v___x_1658_ = lean_uint64_mix_hash(v___x_1656_, v___x_1657_);
v___x_1659_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_p_1652_);
v___x_1660_ = lean_uint64_mix_hash(v___x_1658_, v___x_1659_);
return v___x_1660_;
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_instHashablePoly_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1632_ = stack[0].m_obj;
uint64_t v_res_1674_;
v_res_1674_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_x_1632_);
stack->m_num = v_res_1674_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePoly_hash___boxed(lean_object* v_x_1675_){
_start:
{
uint64_t v_res_1676_; lean_object* v_r_1677_; 
v_res_1676_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_x_1675_);
lean_dec_ref(v_x_1675_);
v_r_1677_ = lean_box_uint64(v_res_1676_);
return v_r_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg(lean_object* v_inst_1680_, lean_object* v_ctx_1681_, lean_object* v_p_1682_){
_start:
{
lean_object* v_toSemiring_1683_; lean_object* v_intCast_1684_; lean_object* v_toAdd_1685_; lean_object* v___x_1686_; 
v_toSemiring_1683_ = lean_ctor_get(v_inst_1680_, 0);
v_intCast_1684_ = lean_ctor_get(v_inst_1680_, 3);
v_toAdd_1685_ = lean_ctor_get(v_toSemiring_1683_, 0);
lean_inc(v_toAdd_1685_);
lean_inc_ref(v_inst_1680_);
v___x_1686_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1680_);
if (lean_obj_tag(v_p_1682_) == 0)
{
lean_object* v_k_1687_; lean_object* v___x_1688_; 
lean_inc(v_intCast_1684_);
lean_dec_ref(v___x_1686_);
lean_dec(v_toAdd_1685_);
lean_dec_ref(v_inst_1680_);
v_k_1687_ = lean_ctor_get(v_p_1682_, 0);
lean_inc(v_k_1687_);
lean_dec_ref_known(v_p_1682_, 1);
v___x_1688_ = lean_apply_1(v_intCast_1684_, v_k_1687_);
return v___x_1688_;
}
else
{
lean_object* v_zsmul_1689_; lean_object* v_k_1690_; lean_object* v_v_1691_; lean_object* v_p_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_zsmul_1689_ = lean_ctor_get(v___x_1686_, 2);
lean_inc(v_zsmul_1689_);
lean_dec_ref(v___x_1686_);
v_k_1690_ = lean_ctor_get(v_p_1682_, 0);
lean_inc(v_k_1690_);
v_v_1691_ = lean_ctor_get(v_p_1682_, 1);
lean_inc(v_v_1691_);
v_p_1692_ = lean_ctor_get(v_p_1682_, 2);
lean_inc_ref(v_p_1692_);
lean_dec_ref_known(v_p_1682_, 3);
lean_inc_ref(v_toSemiring_1683_);
v___x_1693_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_toSemiring_1683_, v_ctx_1681_, v_v_1691_);
v___x_1694_ = lean_apply_2(v_zsmul_1689_, v_k_1690_, v___x_1693_);
v___x_1695_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1680_, v_ctx_1681_, v_p_1692_);
v___x_1696_ = lean_apply_2(v_toAdd_1685_, v___x_1694_, v___x_1695_);
return v___x_1696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg___boxed(lean_object* v_inst_1697_, lean_object* v_ctx_1698_, lean_object* v_p_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1697_, v_ctx_1698_, v_p_1699_);
lean_dec_ref(v_ctx_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote(lean_object* v_00_u03b1_1701_, lean_object* v_inst_1702_, lean_object* v_ctx_1703_, lean_object* v_p_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1702_, v_ctx_1703_, v_p_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___boxed(lean_object* v_00_u03b1_1706_, lean_object* v_inst_1707_, lean_object* v_ctx_1708_, lean_object* v_p_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_Grind_CommRing_Poly_denote(v_00_u03b1_1706_, v_inst_1707_, v_ctx_1708_, v_p_1709_);
lean_dec_ref(v_ctx_1708_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg(lean_object* v_inst_1711_, lean_object* v_ctx_1712_, lean_object* v_k_1713_, lean_object* v_m_1714_){
_start:
{
lean_object* v_toSemiring_1715_; lean_object* v___x_1716_; lean_object* v_zsmul_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; 
v_toSemiring_1715_ = lean_ctor_get(v_inst_1711_, 0);
lean_inc_ref(v_toSemiring_1715_);
v___x_1716_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1711_);
v_zsmul_1717_ = lean_ctor_get(v___x_1716_, 2);
lean_inc(v_zsmul_1717_);
lean_dec_ref(v___x_1716_);
v___x_1718_ = lean_unsigned_to_nat(1u);
v___x_1719_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1720_ = lean_int_dec_eq(v_k_1713_, v___x_1719_);
if (v___x_1720_ == 0)
{
if (lean_obj_tag(v_m_1714_) == 0)
{
lean_object* v_ofNat_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_ofNat_1721_ = lean_ctor_get(v_toSemiring_1715_, 3);
lean_inc(v_ofNat_1721_);
lean_dec_ref(v_toSemiring_1715_);
v___x_1722_ = lean_apply_1(v_ofNat_1721_, v___x_1718_);
v___x_1723_ = lean_apply_2(v_zsmul_1717_, v_k_1713_, v___x_1722_);
return v___x_1723_;
}
else
{
lean_object* v_p_1724_; lean_object* v_m_1725_; lean_object* v_ofNat_1726_; lean_object* v_npow_1727_; lean_object* v_x_1728_; lean_object* v_k_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v_p_1724_ = lean_ctor_get(v_m_1714_, 0);
lean_inc_ref(v_p_1724_);
v_m_1725_ = lean_ctor_get(v_m_1714_, 1);
lean_inc(v_m_1725_);
lean_dec_ref_known(v_m_1714_, 2);
v_ofNat_1726_ = lean_ctor_get(v_toSemiring_1715_, 3);
v_npow_1727_ = lean_ctor_get(v_toSemiring_1715_, 5);
v_x_1728_ = lean_ctor_get(v_p_1724_, 0);
lean_inc(v_x_1728_);
v_k_1729_ = lean_ctor_get(v_p_1724_, 1);
lean_inc(v_k_1729_);
lean_dec_ref(v_p_1724_);
v___x_1730_ = lean_unsigned_to_nat(0u);
v___x_1731_ = lean_nat_dec_eq(v_k_1729_, v___x_1730_);
if (v___x_1731_ == 0)
{
uint8_t v___x_1732_; 
v___x_1732_ = lean_nat_dec_eq(v_k_1729_, v___x_1718_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1733_ = l_Lean_RArray_getImpl___redArg(v_ctx_1712_, v_x_1728_);
lean_dec(v_x_1728_);
lean_inc(v_npow_1727_);
v___x_1734_ = lean_apply_2(v_npow_1727_, v___x_1733_, v_k_1729_);
v___x_1735_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1715_, v_ctx_1712_, v_m_1725_, v___x_1734_);
v___x_1736_ = lean_apply_2(v_zsmul_1717_, v_k_1713_, v___x_1735_);
return v___x_1736_;
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v_k_1729_);
v___x_1737_ = l_Lean_RArray_getImpl___redArg(v_ctx_1712_, v_x_1728_);
lean_dec(v_x_1728_);
v___x_1738_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1715_, v_ctx_1712_, v_m_1725_, v___x_1737_);
v___x_1739_ = lean_apply_2(v_zsmul_1717_, v_k_1713_, v___x_1738_);
return v___x_1739_;
}
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_dec(v_k_1729_);
lean_dec(v_x_1728_);
lean_inc(v_ofNat_1726_);
v___x_1740_ = lean_apply_1(v_ofNat_1726_, v___x_1718_);
v___x_1741_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1715_, v_ctx_1712_, v_m_1725_, v___x_1740_);
v___x_1742_ = lean_apply_2(v_zsmul_1717_, v_k_1713_, v___x_1741_);
return v___x_1742_;
}
}
}
else
{
lean_dec(v_zsmul_1717_);
lean_dec(v_k_1713_);
if (lean_obj_tag(v_m_1714_) == 0)
{
lean_object* v_ofNat_1743_; lean_object* v___x_1744_; 
v_ofNat_1743_ = lean_ctor_get(v_toSemiring_1715_, 3);
lean_inc(v_ofNat_1743_);
lean_dec_ref(v_toSemiring_1715_);
v___x_1744_ = lean_apply_1(v_ofNat_1743_, v___x_1718_);
return v___x_1744_;
}
else
{
lean_object* v_p_1745_; lean_object* v_m_1746_; lean_object* v_ofNat_1747_; lean_object* v_npow_1748_; lean_object* v_x_1749_; lean_object* v_k_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v_p_1745_ = lean_ctor_get(v_m_1714_, 0);
lean_inc_ref(v_p_1745_);
v_m_1746_ = lean_ctor_get(v_m_1714_, 1);
lean_inc(v_m_1746_);
lean_dec_ref_known(v_m_1714_, 2);
v_ofNat_1747_ = lean_ctor_get(v_toSemiring_1715_, 3);
v_npow_1748_ = lean_ctor_get(v_toSemiring_1715_, 5);
v_x_1749_ = lean_ctor_get(v_p_1745_, 0);
lean_inc(v_x_1749_);
v_k_1750_ = lean_ctor_get(v_p_1745_, 1);
lean_inc(v_k_1750_);
lean_dec_ref(v_p_1745_);
v___x_1751_ = lean_unsigned_to_nat(0u);
v___x_1752_ = lean_nat_dec_eq(v_k_1750_, v___x_1751_);
if (v___x_1752_ == 0)
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_nat_dec_eq(v_k_1750_, v___x_1718_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = l_Lean_RArray_getImpl___redArg(v_ctx_1712_, v_x_1749_);
lean_dec(v_x_1749_);
lean_inc(v_npow_1748_);
v___x_1755_ = lean_apply_2(v_npow_1748_, v___x_1754_, v_k_1750_);
v___x_1756_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1715_, v_ctx_1712_, v_m_1746_, v___x_1755_);
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec(v_k_1750_);
v___x_1757_ = l_Lean_RArray_getImpl___redArg(v_ctx_1712_, v_x_1749_);
lean_dec(v_x_1749_);
v___x_1758_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1715_, v_ctx_1712_, v_m_1746_, v___x_1757_);
return v___x_1758_;
}
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v_k_1750_);
lean_dec(v_x_1749_);
lean_inc(v_ofNat_1747_);
v___x_1759_ = lean_apply_1(v_ofNat_1747_, v___x_1718_);
v___x_1760_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1715_, v_ctx_1712_, v_m_1746_, v___x_1759_);
return v___x_1760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg___boxed(lean_object* v_inst_1761_, lean_object* v_ctx_1762_, lean_object* v_k_1763_, lean_object* v_m_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Grind_CommRing_denoteTerm___redArg(v_inst_1761_, v_ctx_1762_, v_k_1763_, v_m_1764_);
lean_dec_ref(v_ctx_1762_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm(lean_object* v_00_u03b1_1766_, lean_object* v_inst_1767_, lean_object* v_ctx_1768_, lean_object* v_k_1769_, lean_object* v_m_1770_){
_start:
{
lean_object* v_toSemiring_1771_; lean_object* v___x_1772_; lean_object* v_zsmul_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v_toSemiring_1771_ = lean_ctor_get(v_inst_1767_, 0);
lean_inc_ref(v_toSemiring_1771_);
v___x_1772_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1767_);
v_zsmul_1773_ = lean_ctor_get(v___x_1772_, 2);
lean_inc(v_zsmul_1773_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = lean_unsigned_to_nat(1u);
v___x_1775_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1776_ = lean_int_dec_eq(v_k_1769_, v___x_1775_);
if (v___x_1776_ == 0)
{
if (lean_obj_tag(v_m_1770_) == 0)
{
lean_object* v_ofNat_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v_ofNat_1777_ = lean_ctor_get(v_toSemiring_1771_, 3);
lean_inc(v_ofNat_1777_);
lean_dec_ref(v_toSemiring_1771_);
v___x_1778_ = lean_apply_1(v_ofNat_1777_, v___x_1774_);
v___x_1779_ = lean_apply_2(v_zsmul_1773_, v_k_1769_, v___x_1778_);
return v___x_1779_;
}
else
{
lean_object* v_p_1780_; lean_object* v_m_1781_; lean_object* v_ofNat_1782_; lean_object* v_npow_1783_; lean_object* v_x_1784_; lean_object* v_k_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v_p_1780_ = lean_ctor_get(v_m_1770_, 0);
lean_inc_ref(v_p_1780_);
v_m_1781_ = lean_ctor_get(v_m_1770_, 1);
lean_inc(v_m_1781_);
lean_dec_ref_known(v_m_1770_, 2);
v_ofNat_1782_ = lean_ctor_get(v_toSemiring_1771_, 3);
v_npow_1783_ = lean_ctor_get(v_toSemiring_1771_, 5);
v_x_1784_ = lean_ctor_get(v_p_1780_, 0);
lean_inc(v_x_1784_);
v_k_1785_ = lean_ctor_get(v_p_1780_, 1);
lean_inc(v_k_1785_);
lean_dec_ref(v_p_1780_);
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = lean_nat_dec_eq(v_k_1785_, v___x_1786_);
if (v___x_1787_ == 0)
{
uint8_t v___x_1788_; 
v___x_1788_ = lean_nat_dec_eq(v_k_1785_, v___x_1774_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1789_ = l_Lean_RArray_getImpl___redArg(v_ctx_1768_, v_x_1784_);
lean_dec(v_x_1784_);
lean_inc(v_npow_1783_);
v___x_1790_ = lean_apply_2(v_npow_1783_, v___x_1789_, v_k_1785_);
v___x_1791_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1771_, v_ctx_1768_, v_m_1781_, v___x_1790_);
v___x_1792_ = lean_apply_2(v_zsmul_1773_, v_k_1769_, v___x_1791_);
return v___x_1792_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec(v_k_1785_);
v___x_1793_ = l_Lean_RArray_getImpl___redArg(v_ctx_1768_, v_x_1784_);
lean_dec(v_x_1784_);
v___x_1794_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1771_, v_ctx_1768_, v_m_1781_, v___x_1793_);
v___x_1795_ = lean_apply_2(v_zsmul_1773_, v_k_1769_, v___x_1794_);
return v___x_1795_;
}
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_dec(v_k_1785_);
lean_dec(v_x_1784_);
lean_inc(v_ofNat_1782_);
v___x_1796_ = lean_apply_1(v_ofNat_1782_, v___x_1774_);
v___x_1797_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1771_, v_ctx_1768_, v_m_1781_, v___x_1796_);
v___x_1798_ = lean_apply_2(v_zsmul_1773_, v_k_1769_, v___x_1797_);
return v___x_1798_;
}
}
}
else
{
lean_dec(v_zsmul_1773_);
lean_dec(v_k_1769_);
if (lean_obj_tag(v_m_1770_) == 0)
{
lean_object* v_ofNat_1799_; lean_object* v___x_1800_; 
v_ofNat_1799_ = lean_ctor_get(v_toSemiring_1771_, 3);
lean_inc(v_ofNat_1799_);
lean_dec_ref(v_toSemiring_1771_);
v___x_1800_ = lean_apply_1(v_ofNat_1799_, v___x_1774_);
return v___x_1800_;
}
else
{
lean_object* v_p_1801_; lean_object* v_m_1802_; lean_object* v_ofNat_1803_; lean_object* v_npow_1804_; lean_object* v_x_1805_; lean_object* v_k_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v_p_1801_ = lean_ctor_get(v_m_1770_, 0);
lean_inc_ref(v_p_1801_);
v_m_1802_ = lean_ctor_get(v_m_1770_, 1);
lean_inc(v_m_1802_);
lean_dec_ref_known(v_m_1770_, 2);
v_ofNat_1803_ = lean_ctor_get(v_toSemiring_1771_, 3);
v_npow_1804_ = lean_ctor_get(v_toSemiring_1771_, 5);
v_x_1805_ = lean_ctor_get(v_p_1801_, 0);
lean_inc(v_x_1805_);
v_k_1806_ = lean_ctor_get(v_p_1801_, 1);
lean_inc(v_k_1806_);
lean_dec_ref(v_p_1801_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_nat_dec_eq(v_k_1806_, v___x_1807_);
if (v___x_1808_ == 0)
{
uint8_t v___x_1809_; 
v___x_1809_ = lean_nat_dec_eq(v_k_1806_, v___x_1774_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = l_Lean_RArray_getImpl___redArg(v_ctx_1768_, v_x_1805_);
lean_dec(v_x_1805_);
lean_inc(v_npow_1804_);
v___x_1811_ = lean_apply_2(v_npow_1804_, v___x_1810_, v_k_1806_);
v___x_1812_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1771_, v_ctx_1768_, v_m_1802_, v___x_1811_);
return v___x_1812_;
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec(v_k_1806_);
v___x_1813_ = l_Lean_RArray_getImpl___redArg(v_ctx_1768_, v_x_1805_);
lean_dec(v_x_1805_);
v___x_1814_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1771_, v_ctx_1768_, v_m_1802_, v___x_1813_);
return v___x_1814_;
}
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
lean_dec(v_k_1806_);
lean_dec(v_x_1805_);
lean_inc(v_ofNat_1803_);
v___x_1815_ = lean_apply_1(v_ofNat_1803_, v___x_1774_);
v___x_1816_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1771_, v_ctx_1768_, v_m_1802_, v___x_1815_);
return v___x_1816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___boxed(lean_object* v_00_u03b1_1817_, lean_object* v_inst_1818_, lean_object* v_ctx_1819_, lean_object* v_k_1820_, lean_object* v_m_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Grind_CommRing_denoteTerm(v_00_u03b1_1817_, v_inst_1818_, v_ctx_1819_, v_k_1820_, v_m_1821_);
lean_dec_ref(v_ctx_1819_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(lean_object* v_inst_1823_, lean_object* v_ctx_1824_, lean_object* v_p_1825_, lean_object* v_acc_1826_){
_start:
{
if (lean_obj_tag(v_p_1825_) == 0)
{
lean_object* v_toSemiring_1827_; lean_object* v_intCast_1828_; lean_object* v_toAdd_1829_; lean_object* v_k_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v_toSemiring_1827_ = lean_ctor_get(v_inst_1823_, 0);
lean_inc_ref(v_toSemiring_1827_);
v_intCast_1828_ = lean_ctor_get(v_inst_1823_, 3);
lean_inc(v_intCast_1828_);
lean_dec_ref(v_inst_1823_);
v_toAdd_1829_ = lean_ctor_get(v_toSemiring_1827_, 0);
lean_inc(v_toAdd_1829_);
lean_dec_ref(v_toSemiring_1827_);
v_k_1830_ = lean_ctor_get(v_p_1825_, 0);
lean_inc(v_k_1830_);
lean_dec_ref_known(v_p_1825_, 1);
v___x_1831_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1832_ = lean_int_dec_eq(v_k_1830_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_apply_1(v_intCast_1828_, v_k_1830_);
v___x_1834_ = lean_apply_2(v_toAdd_1829_, v_acc_1826_, v___x_1833_);
return v___x_1834_;
}
else
{
lean_dec(v_k_1830_);
lean_dec(v_toAdd_1829_);
lean_dec(v_intCast_1828_);
return v_acc_1826_;
}
}
else
{
lean_object* v_toSemiring_1835_; lean_object* v_toAdd_1836_; lean_object* v_ofNat_1837_; lean_object* v_npow_1838_; lean_object* v_k_1839_; lean_object* v_v_1840_; lean_object* v_p_1841_; lean_object* v___y_1843_; lean_object* v___x_1846_; lean_object* v_zsmul_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v_toSemiring_1835_ = lean_ctor_get(v_inst_1823_, 0);
v_toAdd_1836_ = lean_ctor_get(v_toSemiring_1835_, 0);
v_ofNat_1837_ = lean_ctor_get(v_toSemiring_1835_, 3);
v_npow_1838_ = lean_ctor_get(v_toSemiring_1835_, 5);
v_k_1839_ = lean_ctor_get(v_p_1825_, 0);
lean_inc(v_k_1839_);
v_v_1840_ = lean_ctor_get(v_p_1825_, 1);
lean_inc(v_v_1840_);
v_p_1841_ = lean_ctor_get(v_p_1825_, 2);
lean_inc_ref(v_p_1841_);
lean_dec_ref_known(v_p_1825_, 3);
lean_inc_ref(v_inst_1823_);
v___x_1846_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1823_);
v_zsmul_1847_ = lean_ctor_get(v___x_1846_, 2);
lean_inc(v_zsmul_1847_);
lean_dec_ref(v___x_1846_);
v___x_1848_ = lean_unsigned_to_nat(1u);
v___x_1849_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1850_ = lean_int_dec_eq(v_k_1839_, v___x_1849_);
if (v___x_1850_ == 0)
{
if (lean_obj_tag(v_v_1840_) == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_inc(v_ofNat_1837_);
v___x_1851_ = lean_apply_1(v_ofNat_1837_, v___x_1848_);
v___x_1852_ = lean_apply_2(v_zsmul_1847_, v_k_1839_, v___x_1851_);
v___y_1843_ = v___x_1852_;
goto v___jp_1842_;
}
else
{
lean_object* v_p_1853_; lean_object* v_m_1854_; lean_object* v_x_1855_; lean_object* v_k_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v_p_1853_ = lean_ctor_get(v_v_1840_, 0);
lean_inc_ref(v_p_1853_);
v_m_1854_ = lean_ctor_get(v_v_1840_, 1);
lean_inc(v_m_1854_);
lean_dec_ref_known(v_v_1840_, 2);
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
v___x_1859_ = lean_nat_dec_eq(v_k_1856_, v___x_1848_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1860_ = l_Lean_RArray_getImpl___redArg(v_ctx_1824_, v_x_1855_);
lean_dec(v_x_1855_);
lean_inc(v_npow_1838_);
v___x_1861_ = lean_apply_2(v_npow_1838_, v___x_1860_, v_k_1856_);
lean_inc_ref(v_toSemiring_1835_);
v___x_1862_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1835_, v_ctx_1824_, v_m_1854_, v___x_1861_);
v___x_1863_ = lean_apply_2(v_zsmul_1847_, v_k_1839_, v___x_1862_);
v___y_1843_ = v___x_1863_;
goto v___jp_1842_;
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
lean_dec(v_k_1856_);
v___x_1864_ = l_Lean_RArray_getImpl___redArg(v_ctx_1824_, v_x_1855_);
lean_dec(v_x_1855_);
lean_inc_ref(v_toSemiring_1835_);
v___x_1865_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1835_, v_ctx_1824_, v_m_1854_, v___x_1864_);
v___x_1866_ = lean_apply_2(v_zsmul_1847_, v_k_1839_, v___x_1865_);
v___y_1843_ = v___x_1866_;
goto v___jp_1842_;
}
}
else
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_dec(v_k_1856_);
lean_dec(v_x_1855_);
lean_inc(v_ofNat_1837_);
v___x_1867_ = lean_apply_1(v_ofNat_1837_, v___x_1848_);
lean_inc_ref(v_toSemiring_1835_);
v___x_1868_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1835_, v_ctx_1824_, v_m_1854_, v___x_1867_);
v___x_1869_ = lean_apply_2(v_zsmul_1847_, v_k_1839_, v___x_1868_);
v___y_1843_ = v___x_1869_;
goto v___jp_1842_;
}
}
}
else
{
lean_dec(v_zsmul_1847_);
lean_dec(v_k_1839_);
if (lean_obj_tag(v_v_1840_) == 0)
{
lean_object* v___x_1870_; 
lean_inc(v_ofNat_1837_);
v___x_1870_ = lean_apply_1(v_ofNat_1837_, v___x_1848_);
v___y_1843_ = v___x_1870_;
goto v___jp_1842_;
}
else
{
lean_object* v_p_1871_; lean_object* v_m_1872_; lean_object* v_x_1873_; lean_object* v_k_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v_p_1871_ = lean_ctor_get(v_v_1840_, 0);
lean_inc_ref(v_p_1871_);
v_m_1872_ = lean_ctor_get(v_v_1840_, 1);
lean_inc(v_m_1872_);
lean_dec_ref_known(v_v_1840_, 2);
v_x_1873_ = lean_ctor_get(v_p_1871_, 0);
lean_inc(v_x_1873_);
v_k_1874_ = lean_ctor_get(v_p_1871_, 1);
lean_inc(v_k_1874_);
lean_dec_ref(v_p_1871_);
v___x_1875_ = lean_unsigned_to_nat(0u);
v___x_1876_ = lean_nat_dec_eq(v_k_1874_, v___x_1875_);
if (v___x_1876_ == 0)
{
uint8_t v___x_1877_; 
v___x_1877_ = lean_nat_dec_eq(v_k_1874_, v___x_1848_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1878_ = l_Lean_RArray_getImpl___redArg(v_ctx_1824_, v_x_1873_);
lean_dec(v_x_1873_);
lean_inc(v_npow_1838_);
v___x_1879_ = lean_apply_2(v_npow_1838_, v___x_1878_, v_k_1874_);
lean_inc_ref(v_toSemiring_1835_);
v___x_1880_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1835_, v_ctx_1824_, v_m_1872_, v___x_1879_);
v___y_1843_ = v___x_1880_;
goto v___jp_1842_;
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec(v_k_1874_);
v___x_1881_ = l_Lean_RArray_getImpl___redArg(v_ctx_1824_, v_x_1873_);
lean_dec(v_x_1873_);
lean_inc_ref(v_toSemiring_1835_);
v___x_1882_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1835_, v_ctx_1824_, v_m_1872_, v___x_1881_);
v___y_1843_ = v___x_1882_;
goto v___jp_1842_;
}
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_dec(v_k_1874_);
lean_dec(v_x_1873_);
lean_inc(v_ofNat_1837_);
v___x_1883_ = lean_apply_1(v_ofNat_1837_, v___x_1848_);
lean_inc_ref(v_toSemiring_1835_);
v___x_1884_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1835_, v_ctx_1824_, v_m_1872_, v___x_1883_);
v___y_1843_ = v___x_1884_;
goto v___jp_1842_;
}
}
}
v___jp_1842_:
{
lean_object* v___x_1844_; 
lean_inc(v_toAdd_1836_);
v___x_1844_ = lean_apply_2(v_toAdd_1836_, v_acc_1826_, v___y_1843_);
v_p_1825_ = v_p_1841_;
v_acc_1826_ = v___x_1844_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg___boxed(lean_object* v_inst_1885_, lean_object* v_ctx_1886_, lean_object* v_p_1887_, lean_object* v_acc_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1885_, v_ctx_1886_, v_p_1887_, v_acc_1888_);
lean_dec_ref(v_ctx_1886_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go(lean_object* v_00_u03b1_1890_, lean_object* v_inst_1891_, lean_object* v_ctx_1892_, lean_object* v_p_1893_, lean_object* v_acc_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1891_, v_ctx_1892_, v_p_1893_, v_acc_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___boxed(lean_object* v_00_u03b1_1896_, lean_object* v_inst_1897_, lean_object* v_ctx_1898_, lean_object* v_p_1899_, lean_object* v_acc_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Grind_CommRing_Poly_denote_x27_go(v_00_u03b1_1896_, v_inst_1897_, v_ctx_1898_, v_p_1899_, v_acc_1900_);
lean_dec_ref(v_ctx_1898_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg(lean_object* v_inst_1902_, lean_object* v_ctx_1903_, lean_object* v_p_1904_){
_start:
{
if (lean_obj_tag(v_p_1904_) == 0)
{
lean_object* v_intCast_1905_; lean_object* v_k_1906_; lean_object* v___x_1907_; 
v_intCast_1905_ = lean_ctor_get(v_inst_1902_, 3);
lean_inc(v_intCast_1905_);
lean_dec_ref(v_inst_1902_);
v_k_1906_ = lean_ctor_get(v_p_1904_, 0);
lean_inc(v_k_1906_);
lean_dec_ref_known(v_p_1904_, 1);
v___x_1907_ = lean_apply_1(v_intCast_1905_, v_k_1906_);
return v___x_1907_;
}
else
{
lean_object* v_toSemiring_1908_; lean_object* v_k_1909_; lean_object* v_v_1910_; lean_object* v_p_1911_; lean_object* v___x_1912_; lean_object* v_zsmul_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v_toSemiring_1908_ = lean_ctor_get(v_inst_1902_, 0);
v_k_1909_ = lean_ctor_get(v_p_1904_, 0);
lean_inc(v_k_1909_);
v_v_1910_ = lean_ctor_get(v_p_1904_, 1);
lean_inc(v_v_1910_);
v_p_1911_ = lean_ctor_get(v_p_1904_, 2);
lean_inc_ref(v_p_1911_);
lean_dec_ref_known(v_p_1904_, 3);
lean_inc_ref(v_inst_1902_);
v___x_1912_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1902_);
v_zsmul_1913_ = lean_ctor_get(v___x_1912_, 2);
lean_inc(v_zsmul_1913_);
lean_dec_ref(v___x_1912_);
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1916_ = lean_int_dec_eq(v_k_1909_, v___x_1915_);
if (v___x_1916_ == 0)
{
if (lean_obj_tag(v_v_1910_) == 0)
{
lean_object* v_ofNat_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_ofNat_1917_ = lean_ctor_get(v_toSemiring_1908_, 3);
lean_inc(v_ofNat_1917_);
v___x_1918_ = lean_apply_1(v_ofNat_1917_, v___x_1914_);
v___x_1919_ = lean_apply_2(v_zsmul_1913_, v_k_1909_, v___x_1918_);
v___x_1920_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1902_, v_ctx_1903_, v_p_1911_, v___x_1919_);
return v___x_1920_;
}
else
{
lean_object* v_p_1921_; lean_object* v_m_1922_; lean_object* v_ofNat_1923_; lean_object* v_npow_1924_; lean_object* v_x_1925_; lean_object* v_k_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
v_p_1921_ = lean_ctor_get(v_v_1910_, 0);
lean_inc_ref(v_p_1921_);
v_m_1922_ = lean_ctor_get(v_v_1910_, 1);
lean_inc(v_m_1922_);
lean_dec_ref_known(v_v_1910_, 2);
v_ofNat_1923_ = lean_ctor_get(v_toSemiring_1908_, 3);
v_npow_1924_ = lean_ctor_get(v_toSemiring_1908_, 5);
v_x_1925_ = lean_ctor_get(v_p_1921_, 0);
lean_inc(v_x_1925_);
v_k_1926_ = lean_ctor_get(v_p_1921_, 1);
lean_inc(v_k_1926_);
lean_dec_ref(v_p_1921_);
v___x_1927_ = lean_unsigned_to_nat(0u);
v___x_1928_ = lean_nat_dec_eq(v_k_1926_, v___x_1927_);
if (v___x_1928_ == 0)
{
uint8_t v___x_1929_; 
v___x_1929_ = lean_nat_dec_eq(v_k_1926_, v___x_1914_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1930_ = l_Lean_RArray_getImpl___redArg(v_ctx_1903_, v_x_1925_);
lean_dec(v_x_1925_);
lean_inc(v_npow_1924_);
v___x_1931_ = lean_apply_2(v_npow_1924_, v___x_1930_, v_k_1926_);
lean_inc_ref(v_toSemiring_1908_);
v___x_1932_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1908_, v_ctx_1903_, v_m_1922_, v___x_1931_);
v___x_1933_ = lean_apply_2(v_zsmul_1913_, v_k_1909_, v___x_1932_);
v___x_1934_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1902_, v_ctx_1903_, v_p_1911_, v___x_1933_);
return v___x_1934_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_dec(v_k_1926_);
v___x_1935_ = l_Lean_RArray_getImpl___redArg(v_ctx_1903_, v_x_1925_);
lean_dec(v_x_1925_);
lean_inc_ref(v_toSemiring_1908_);
v___x_1936_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1908_, v_ctx_1903_, v_m_1922_, v___x_1935_);
v___x_1937_ = lean_apply_2(v_zsmul_1913_, v_k_1909_, v___x_1936_);
v___x_1938_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1902_, v_ctx_1903_, v_p_1911_, v___x_1937_);
return v___x_1938_;
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_dec(v_k_1926_);
lean_dec(v_x_1925_);
lean_inc(v_ofNat_1923_);
v___x_1939_ = lean_apply_1(v_ofNat_1923_, v___x_1914_);
lean_inc_ref(v_toSemiring_1908_);
v___x_1940_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1908_, v_ctx_1903_, v_m_1922_, v___x_1939_);
v___x_1941_ = lean_apply_2(v_zsmul_1913_, v_k_1909_, v___x_1940_);
v___x_1942_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1902_, v_ctx_1903_, v_p_1911_, v___x_1941_);
return v___x_1942_;
}
}
}
else
{
lean_dec(v_zsmul_1913_);
lean_dec(v_k_1909_);
if (lean_obj_tag(v_v_1910_) == 0)
{
lean_object* v_ofNat_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v_ofNat_1943_ = lean_ctor_get(v_toSemiring_1908_, 3);
lean_inc(v_ofNat_1943_);
v___x_1944_ = lean_apply_1(v_ofNat_1943_, v___x_1914_);
v___x_1945_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1902_, v_ctx_1903_, v_p_1911_, v___x_1944_);
return v___x_1945_;
}
else
{
lean_object* v_p_1946_; lean_object* v_m_1947_; lean_object* v_ofNat_1948_; lean_object* v_npow_1949_; lean_object* v_x_1950_; lean_object* v_k_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
v_p_1946_ = lean_ctor_get(v_v_1910_, 0);
lean_inc_ref(v_p_1946_);
v_m_1947_ = lean_ctor_get(v_v_1910_, 1);
lean_inc(v_m_1947_);
lean_dec_ref_known(v_v_1910_, 2);
v_ofNat_1948_ = lean_ctor_get(v_toSemiring_1908_, 3);
v_npow_1949_ = lean_ctor_get(v_toSemiring_1908_, 5);
v_x_1950_ = lean_ctor_get(v_p_1946_, 0);
lean_inc(v_x_1950_);
v_k_1951_ = lean_ctor_get(v_p_1946_, 1);
lean_inc(v_k_1951_);
lean_dec_ref(v_p_1946_);
v___x_1952_ = lean_unsigned_to_nat(0u);
v___x_1953_ = lean_nat_dec_eq(v_k_1951_, v___x_1952_);
if (v___x_1953_ == 0)
{
uint8_t v___x_1954_; 
v___x_1954_ = lean_nat_dec_eq(v_k_1951_, v___x_1914_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1955_ = l_Lean_RArray_getImpl___redArg(v_ctx_1903_, v_x_1950_);
lean_dec(v_x_1950_);
lean_inc(v_npow_1949_);
v___x_1956_ = lean_apply_2(v_npow_1949_, v___x_1955_, v_k_1951_);
lean_inc_ref(v_toSemiring_1908_);
v___x_1957_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1908_, v_ctx_1903_, v_m_1947_, v___x_1956_);
v___x_1958_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1902_, v_ctx_1903_, v_p_1911_, v___x_1957_);
return v___x_1958_;
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec(v_k_1951_);
v___x_1959_ = l_Lean_RArray_getImpl___redArg(v_ctx_1903_, v_x_1950_);
lean_dec(v_x_1950_);
lean_inc_ref(v_toSemiring_1908_);
v___x_1960_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1908_, v_ctx_1903_, v_m_1947_, v___x_1959_);
v___x_1961_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1902_, v_ctx_1903_, v_p_1911_, v___x_1960_);
return v___x_1961_;
}
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec(v_k_1951_);
lean_dec(v_x_1950_);
lean_inc(v_ofNat_1948_);
v___x_1962_ = lean_apply_1(v_ofNat_1948_, v___x_1914_);
lean_inc_ref(v_toSemiring_1908_);
v___x_1963_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1908_, v_ctx_1903_, v_m_1947_, v___x_1962_);
v___x_1964_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1902_, v_ctx_1903_, v_p_1911_, v___x_1963_);
return v___x_1964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg___boxed(lean_object* v_inst_1965_, lean_object* v_ctx_1966_, lean_object* v_p_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Grind_CommRing_Poly_denote_x27___redArg(v_inst_1965_, v_ctx_1966_, v_p_1967_);
lean_dec_ref(v_ctx_1966_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27(lean_object* v_00_u03b1_1969_, lean_object* v_inst_1970_, lean_object* v_ctx_1971_, lean_object* v_p_1972_){
_start:
{
if (lean_obj_tag(v_p_1972_) == 0)
{
lean_object* v_intCast_1973_; lean_object* v_k_1974_; lean_object* v___x_1975_; 
v_intCast_1973_ = lean_ctor_get(v_inst_1970_, 3);
lean_inc(v_intCast_1973_);
lean_dec_ref(v_inst_1970_);
v_k_1974_ = lean_ctor_get(v_p_1972_, 0);
lean_inc(v_k_1974_);
lean_dec_ref_known(v_p_1972_, 1);
v___x_1975_ = lean_apply_1(v_intCast_1973_, v_k_1974_);
return v___x_1975_;
}
else
{
lean_object* v_toSemiring_1976_; lean_object* v_k_1977_; lean_object* v_v_1978_; lean_object* v_p_1979_; lean_object* v___x_1980_; lean_object* v_zsmul_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v_toSemiring_1976_ = lean_ctor_get(v_inst_1970_, 0);
v_k_1977_ = lean_ctor_get(v_p_1972_, 0);
lean_inc(v_k_1977_);
v_v_1978_ = lean_ctor_get(v_p_1972_, 1);
lean_inc(v_v_1978_);
v_p_1979_ = lean_ctor_get(v_p_1972_, 2);
lean_inc_ref(v_p_1979_);
lean_dec_ref_known(v_p_1972_, 3);
lean_inc_ref(v_inst_1970_);
v___x_1980_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1970_);
v_zsmul_1981_ = lean_ctor_get(v___x_1980_, 2);
lean_inc(v_zsmul_1981_);
lean_dec_ref(v___x_1980_);
v___x_1982_ = lean_unsigned_to_nat(1u);
v___x_1983_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1984_ = lean_int_dec_eq(v_k_1977_, v___x_1983_);
if (v___x_1984_ == 0)
{
if (lean_obj_tag(v_v_1978_) == 0)
{
lean_object* v_ofNat_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v_ofNat_1985_ = lean_ctor_get(v_toSemiring_1976_, 3);
lean_inc(v_ofNat_1985_);
v___x_1986_ = lean_apply_1(v_ofNat_1985_, v___x_1982_);
v___x_1987_ = lean_apply_2(v_zsmul_1981_, v_k_1977_, v___x_1986_);
v___x_1988_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1970_, v_ctx_1971_, v_p_1979_, v___x_1987_);
return v___x_1988_;
}
else
{
lean_object* v_p_1989_; lean_object* v_m_1990_; lean_object* v_ofNat_1991_; lean_object* v_npow_1992_; lean_object* v_x_1993_; lean_object* v_k_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v_p_1989_ = lean_ctor_get(v_v_1978_, 0);
lean_inc_ref(v_p_1989_);
v_m_1990_ = lean_ctor_get(v_v_1978_, 1);
lean_inc(v_m_1990_);
lean_dec_ref_known(v_v_1978_, 2);
v_ofNat_1991_ = lean_ctor_get(v_toSemiring_1976_, 3);
v_npow_1992_ = lean_ctor_get(v_toSemiring_1976_, 5);
v_x_1993_ = lean_ctor_get(v_p_1989_, 0);
lean_inc(v_x_1993_);
v_k_1994_ = lean_ctor_get(v_p_1989_, 1);
lean_inc(v_k_1994_);
lean_dec_ref(v_p_1989_);
v___x_1995_ = lean_unsigned_to_nat(0u);
v___x_1996_ = lean_nat_dec_eq(v_k_1994_, v___x_1995_);
if (v___x_1996_ == 0)
{
uint8_t v___x_1997_; 
v___x_1997_ = lean_nat_dec_eq(v_k_1994_, v___x_1982_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1998_ = l_Lean_RArray_getImpl___redArg(v_ctx_1971_, v_x_1993_);
lean_dec(v_x_1993_);
lean_inc(v_npow_1992_);
v___x_1999_ = lean_apply_2(v_npow_1992_, v___x_1998_, v_k_1994_);
lean_inc_ref(v_toSemiring_1976_);
v___x_2000_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1976_, v_ctx_1971_, v_m_1990_, v___x_1999_);
v___x_2001_ = lean_apply_2(v_zsmul_1981_, v_k_1977_, v___x_2000_);
v___x_2002_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1970_, v_ctx_1971_, v_p_1979_, v___x_2001_);
return v___x_2002_;
}
else
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec(v_k_1994_);
v___x_2003_ = l_Lean_RArray_getImpl___redArg(v_ctx_1971_, v_x_1993_);
lean_dec(v_x_1993_);
lean_inc_ref(v_toSemiring_1976_);
v___x_2004_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1976_, v_ctx_1971_, v_m_1990_, v___x_2003_);
v___x_2005_ = lean_apply_2(v_zsmul_1981_, v_k_1977_, v___x_2004_);
v___x_2006_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1970_, v_ctx_1971_, v_p_1979_, v___x_2005_);
return v___x_2006_;
}
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec(v_k_1994_);
lean_dec(v_x_1993_);
lean_inc(v_ofNat_1991_);
v___x_2007_ = lean_apply_1(v_ofNat_1991_, v___x_1982_);
lean_inc_ref(v_toSemiring_1976_);
v___x_2008_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1976_, v_ctx_1971_, v_m_1990_, v___x_2007_);
v___x_2009_ = lean_apply_2(v_zsmul_1981_, v_k_1977_, v___x_2008_);
v___x_2010_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1970_, v_ctx_1971_, v_p_1979_, v___x_2009_);
return v___x_2010_;
}
}
}
else
{
lean_dec(v_zsmul_1981_);
lean_dec(v_k_1977_);
if (lean_obj_tag(v_v_1978_) == 0)
{
lean_object* v_ofNat_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v_ofNat_2011_ = lean_ctor_get(v_toSemiring_1976_, 3);
lean_inc(v_ofNat_2011_);
v___x_2012_ = lean_apply_1(v_ofNat_2011_, v___x_1982_);
v___x_2013_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1970_, v_ctx_1971_, v_p_1979_, v___x_2012_);
return v___x_2013_;
}
else
{
lean_object* v_p_2014_; lean_object* v_m_2015_; lean_object* v_ofNat_2016_; lean_object* v_npow_2017_; lean_object* v_x_2018_; lean_object* v_k_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v_p_2014_ = lean_ctor_get(v_v_1978_, 0);
lean_inc_ref(v_p_2014_);
v_m_2015_ = lean_ctor_get(v_v_1978_, 1);
lean_inc(v_m_2015_);
lean_dec_ref_known(v_v_1978_, 2);
v_ofNat_2016_ = lean_ctor_get(v_toSemiring_1976_, 3);
v_npow_2017_ = lean_ctor_get(v_toSemiring_1976_, 5);
v_x_2018_ = lean_ctor_get(v_p_2014_, 0);
lean_inc(v_x_2018_);
v_k_2019_ = lean_ctor_get(v_p_2014_, 1);
lean_inc(v_k_2019_);
lean_dec_ref(v_p_2014_);
v___x_2020_ = lean_unsigned_to_nat(0u);
v___x_2021_ = lean_nat_dec_eq(v_k_2019_, v___x_2020_);
if (v___x_2021_ == 0)
{
uint8_t v___x_2022_; 
v___x_2022_ = lean_nat_dec_eq(v_k_2019_, v___x_1982_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2023_ = l_Lean_RArray_getImpl___redArg(v_ctx_1971_, v_x_2018_);
lean_dec(v_x_2018_);
lean_inc(v_npow_2017_);
v___x_2024_ = lean_apply_2(v_npow_2017_, v___x_2023_, v_k_2019_);
lean_inc_ref(v_toSemiring_1976_);
v___x_2025_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1976_, v_ctx_1971_, v_m_2015_, v___x_2024_);
v___x_2026_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1970_, v_ctx_1971_, v_p_1979_, v___x_2025_);
return v___x_2026_;
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_dec(v_k_2019_);
v___x_2027_ = l_Lean_RArray_getImpl___redArg(v_ctx_1971_, v_x_2018_);
lean_dec(v_x_2018_);
lean_inc_ref(v_toSemiring_1976_);
v___x_2028_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1976_, v_ctx_1971_, v_m_2015_, v___x_2027_);
v___x_2029_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1970_, v_ctx_1971_, v_p_1979_, v___x_2028_);
return v___x_2029_;
}
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_dec(v_k_2019_);
lean_dec(v_x_2018_);
lean_inc(v_ofNat_2016_);
v___x_2030_ = lean_apply_1(v_ofNat_2016_, v___x_1982_);
lean_inc_ref(v_toSemiring_1976_);
v___x_2031_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1976_, v_ctx_1971_, v_m_2015_, v___x_2030_);
v___x_2032_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1970_, v_ctx_1971_, v_p_1979_, v___x_2031_);
return v___x_2032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___boxed(lean_object* v_00_u03b1_2033_, lean_object* v_inst_2034_, lean_object* v_ctx_2035_, lean_object* v_p_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_Grind_CommRing_Poly_denote_x27(v_00_u03b1_2033_, v_inst_2034_, v_ctx_2035_, v_p_2036_);
lean_dec_ref(v_ctx_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object* v_m_2038_){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2040_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2041_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set(v___x_2041_, 1, v_m_2038_);
lean_ctor_set(v___x_2041_, 2, v___x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object* v_x_2042_){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = l_Lean_Grind_CommRing_Mon_ofVar(v_x_2042_);
v___x_2044_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2043_);
return v___x_2044_;
}
}
uint8_t l_Lean_Grind_CommRing_Poly_isSorted(lean_object* v_x_2045_){
_start:
{
if (lean_obj_tag(v_x_2045_) == 0)
{
uint8_t v___x_2046_; 
v___x_2046_ = 1;
return v___x_2046_;
}
else
{
lean_object* v_p_2047_; 
v_p_2047_ = lean_ctor_get(v_x_2045_, 2);
if (lean_obj_tag(v_p_2047_) == 0)
{
uint8_t v___x_2048_; 
v___x_2048_ = 1;
return v___x_2048_;
}
else
{
lean_object* v_v_2049_; lean_object* v_v_2050_; uint8_t v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v_v_2049_ = lean_ctor_get(v_x_2045_, 1);
v_v_2050_ = lean_ctor_get(v_p_2047_, 1);
v___x_2051_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2049_, v_v_2050_);
v___x_2052_ = lean_box(v___x_2051_);
v___x_2053_ = lean_obj_tag_nat(v___x_2052_);
lean_dec(v___x_2052_);
v___x_2054_ = lean_unsigned_to_nat(2u);
v___x_2055_ = lean_nat_dec_eq(v___x_2053_, v___x_2054_);
if (v___x_2055_ == 0)
{
return v___x_2055_;
}
else
{
v_x_2045_ = v_p_2047_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Poly_isSorted_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2045_ = stack[0].m_obj;
uint8_t v_res_2057_;
v_res_2057_ = l_Lean_Grind_CommRing_Poly_isSorted(v_x_2045_);
stack->m_num = v_res_2057_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isSorted___boxed(lean_object* v_x_2058_){
_start:
{
uint8_t v_res_2059_; lean_object* v_r_2060_; 
v_res_2059_ = l_Lean_Grind_CommRing_Poly_isSorted(v_x_2058_);
lean_dec_ref(v_x_2058_);
v_r_2060_ = lean_box(v_res_2059_);
return v_r_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go(lean_object* v_k_2061_, lean_object* v_a_2062_){
_start:
{
if (lean_obj_tag(v_a_2062_) == 0)
{
lean_object* v_k_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2071_; 
v_k_2063_ = lean_ctor_get(v_a_2062_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_a_2062_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2065_ = v_a_2062_;
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_k_2063_);
lean_dec(v_a_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_int_add(v_k_2063_, v_k_2061_);
lean_dec(v_k_2063_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2067_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
else
{
lean_object* v_k_2072_; lean_object* v_v_2073_; lean_object* v_p_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2082_; 
v_k_2072_ = lean_ctor_get(v_a_2062_, 0);
v_v_2073_ = lean_ctor_get(v_a_2062_, 1);
v_p_2074_ = lean_ctor_get(v_a_2062_, 2);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_a_2062_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2076_ = v_a_2062_;
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_p_2074_);
lean_inc(v_v_2073_);
lean_inc(v_k_2072_);
lean_dec(v_a_2062_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2061_, v_p_2074_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 2, v___x_2078_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_k_2072_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_v_2073_);
lean_ctor_set(v_reuseFailAlloc_2081_, 2, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go___boxed(lean_object* v_k_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2083_, v_a_2084_);
lean_dec(v_k_2083_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object* v_p_2086_, lean_object* v_k_2087_){
_start:
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2089_ = lean_int_dec_eq(v_k_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2087_, v_p_2086_);
return v___x_2090_;
}
else
{
return v_p_2086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst___boxed(lean_object* v_p_2091_, lean_object* v_k_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2091_, v_k_2092_);
lean_dec(v_k_2092_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert_go(lean_object* v_k_2094_, lean_object* v_m_2095_, lean_object* v_a_2096_){
_start:
{
if (lean_obj_tag(v_a_2096_) == 0)
{
lean_object* v___x_2097_; 
v___x_2097_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2097_, 0, v_k_2094_);
lean_ctor_set(v___x_2097_, 1, v_m_2095_);
lean_ctor_set(v___x_2097_, 2, v_a_2096_);
return v___x_2097_;
}
else
{
lean_object* v_k_2098_; lean_object* v_v_2099_; lean_object* v_p_2100_; uint8_t v___x_2101_; 
v_k_2098_ = lean_ctor_get(v_a_2096_, 0);
v_v_2099_ = lean_ctor_get(v_a_2096_, 1);
v_p_2100_ = lean_ctor_get(v_a_2096_, 2);
v___x_2101_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2095_, v_v_2099_);
switch(v___x_2101_)
{
case 0:
{
lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2109_; 
lean_inc_ref(v_p_2100_);
lean_inc(v_v_2099_);
lean_inc(v_k_2098_);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_a_2096_);
if (v_isSharedCheck_2109_ == 0)
{
lean_object* v_unused_2110_; lean_object* v_unused_2111_; lean_object* v_unused_2112_; 
v_unused_2110_ = lean_ctor_get(v_a_2096_, 2);
lean_dec(v_unused_2110_);
v_unused_2111_ = lean_ctor_get(v_a_2096_, 1);
lean_dec(v_unused_2111_);
v_unused_2112_ = lean_ctor_get(v_a_2096_, 0);
lean_dec(v_unused_2112_);
v___x_2103_ = v_a_2096_;
v_isShared_2104_ = v_isSharedCheck_2109_;
goto v_resetjp_2102_;
}
else
{
lean_dec(v_a_2096_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2109_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2094_, v_m_2095_, v_p_2100_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 2, v___x_2105_);
v___x_2107_ = v___x_2103_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_k_2098_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_v_2099_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
case 1:
{
lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2122_; 
lean_inc_ref(v_p_2100_);
lean_inc(v_k_2098_);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_a_2096_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; lean_object* v_unused_2124_; lean_object* v_unused_2125_; 
v_unused_2123_ = lean_ctor_get(v_a_2096_, 2);
lean_dec(v_unused_2123_);
v_unused_2124_ = lean_ctor_get(v_a_2096_, 1);
lean_dec(v_unused_2124_);
v_unused_2125_ = lean_ctor_get(v_a_2096_, 0);
lean_dec(v_unused_2125_);
v___x_2114_ = v_a_2096_;
v_isShared_2115_ = v_isSharedCheck_2122_;
goto v_resetjp_2113_;
}
else
{
lean_dec(v_a_2096_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2122_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v_k_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v_k_2116_ = lean_int_add(v_k_2094_, v_k_2098_);
lean_dec(v_k_2098_);
lean_dec(v_k_2094_);
v___x_2117_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2118_ = lean_int_dec_eq(v_k_2116_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2120_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 1, v_m_2095_);
lean_ctor_set(v___x_2114_, 0, v_k_2116_);
v___x_2120_ = v___x_2114_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_k_2116_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_m_2095_);
lean_ctor_set(v_reuseFailAlloc_2121_, 2, v_p_2100_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
else
{
lean_dec(v_k_2116_);
lean_del_object(v___x_2114_);
lean_dec(v_m_2095_);
return v_p_2100_;
}
}
}
default: 
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2126_, 0, v_k_2094_);
lean_ctor_set(v___x_2126_, 1, v_m_2095_);
lean_ctor_set(v___x_2126_, 2, v_a_2096_);
return v___x_2126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert(lean_object* v_k_2127_, lean_object* v_m_2128_, lean_object* v_p_2129_){
_start:
{
lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2130_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2131_ = lean_int_dec_eq(v_k_2127_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = lean_box(0);
v___x_2133_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2128_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2127_, v_m_2128_, v_p_2129_);
return v___x_2134_;
}
else
{
lean_object* v___x_2135_; 
lean_dec(v_m_2128_);
v___x_2135_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2129_, v_k_2127_);
lean_dec(v_k_2127_);
return v___x_2135_;
}
}
else
{
lean_dec(v_m_2128_);
lean_dec(v_k_2127_);
return v_p_2129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_concat(lean_object* v_p_u2081_2136_, lean_object* v_p_u2082_2137_){
_start:
{
if (lean_obj_tag(v_p_u2081_2136_) == 0)
{
lean_object* v_k_2138_; lean_object* v___x_2139_; 
v_k_2138_ = lean_ctor_get(v_p_u2081_2136_, 0);
lean_inc(v_k_2138_);
lean_dec_ref_known(v_p_u2081_2136_, 1);
v___x_2139_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2137_, v_k_2138_);
lean_dec(v_k_2138_);
return v___x_2139_;
}
else
{
lean_object* v_k_2140_; lean_object* v_v_2141_; lean_object* v_p_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2150_; 
v_k_2140_ = lean_ctor_get(v_p_u2081_2136_, 0);
v_v_2141_ = lean_ctor_get(v_p_u2081_2136_, 1);
v_p_2142_ = lean_ctor_get(v_p_u2081_2136_, 2);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_p_u2081_2136_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2144_ = v_p_u2081_2136_;
v_isShared_2145_ = v_isSharedCheck_2150_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_p_2142_);
lean_inc(v_v_2141_);
lean_inc(v_k_2140_);
lean_dec(v_p_u2081_2136_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2150_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2146_ = l_Lean_Grind_CommRing_Poly_concat(v_p_2142_, v_p_u2082_2137_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 2, v___x_2146_);
v___x_2148_ = v___x_2144_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_k_2140_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_v_2141_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go(lean_object* v_k_2151_, lean_object* v_a_2152_){
_start:
{
if (lean_obj_tag(v_a_2152_) == 0)
{
lean_object* v_k_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2161_; 
v_k_2153_ = lean_ctor_get(v_a_2152_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_a_2152_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2155_ = v_a_2152_;
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_k_2153_);
lean_dec(v_a_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = lean_int_mul(v_k_2151_, v_k_2153_);
lean_dec(v_k_2153_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2157_);
v___x_2159_ = v___x_2155_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
else
{
lean_object* v_k_2162_; lean_object* v_v_2163_; lean_object* v_p_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2173_; 
v_k_2162_ = lean_ctor_get(v_a_2152_, 0);
v_v_2163_ = lean_ctor_get(v_a_2152_, 1);
v_p_2164_ = lean_ctor_get(v_a_2152_, 2);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_a_2152_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2166_ = v_a_2152_;
v_isShared_2167_ = v_isSharedCheck_2173_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_p_2164_);
lean_inc(v_v_2163_);
lean_inc(v_k_2162_);
lean_dec(v_a_2152_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2173_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2168_ = lean_int_mul(v_k_2151_, v_k_2162_);
lean_dec(v_k_2162_);
v___x_2169_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2151_, v_p_2164_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 2, v___x_2169_);
lean_ctor_set(v___x_2166_, 0, v___x_2168_);
v___x_2171_ = v___x_2166_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_v_2163_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go___boxed(lean_object* v_k_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2174_, v_a_2175_);
lean_dec(v_k_2174_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object* v_k_2177_, lean_object* v_p_2178_){
_start:
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2180_ = lean_int_dec_eq(v_k_2177_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2182_ = lean_int_dec_eq(v_k_2177_, v___x_2181_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2177_, v_p_2178_);
return v___x_2183_;
}
else
{
return v_p_2178_;
}
}
else
{
lean_object* v___x_2184_; 
lean_dec_ref(v_p_2178_);
v___x_2184_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst___boxed(lean_object* v_k_2185_, lean_object* v_p_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2185_, v_p_2186_);
lean_dec(v_k_2185_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go(lean_object* v_k_2188_, lean_object* v_m_2189_, lean_object* v_a_2190_){
_start:
{
if (lean_obj_tag(v_a_2190_) == 0)
{
lean_object* v_k_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v_k_2191_ = lean_ctor_get(v_a_2190_, 0);
lean_inc(v_k_2191_);
lean_dec_ref_known(v_a_2190_, 1);
v___x_2192_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2193_ = lean_int_dec_eq(v_k_2191_, v___x_2192_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = lean_int_mul(v_k_2188_, v_k_2191_);
lean_dec(v_k_2191_);
v___x_2195_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v_m_2189_);
lean_ctor_set(v___x_2196_, 2, v___x_2195_);
return v___x_2196_;
}
else
{
lean_object* v___x_2197_; 
lean_dec(v_k_2191_);
lean_dec(v_m_2189_);
v___x_2197_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2197_;
}
}
else
{
lean_object* v_k_2198_; lean_object* v_v_2199_; lean_object* v_p_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2210_; 
v_k_2198_ = lean_ctor_get(v_a_2190_, 0);
v_v_2199_ = lean_ctor_get(v_a_2190_, 1);
v_p_2200_ = lean_ctor_get(v_a_2190_, 2);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_a_2190_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2202_ = v_a_2190_;
v_isShared_2203_ = v_isSharedCheck_2210_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_p_2200_);
lean_inc(v_v_2199_);
lean_inc(v_k_2198_);
lean_dec(v_a_2190_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2210_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2204_ = lean_int_mul(v_k_2188_, v_k_2198_);
lean_dec(v_k_2198_);
lean_inc(v_m_2189_);
v___x_2205_ = l_Lean_Grind_CommRing_Mon_mul(v_m_2189_, v_v_2199_);
v___x_2206_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2188_, v_m_2189_, v_p_2200_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 2, v___x_2206_);
lean_ctor_set(v___x_2202_, 1, v___x_2205_);
lean_ctor_set(v___x_2202_, 0, v___x_2204_);
v___x_2208_ = v___x_2202_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go___boxed(lean_object* v_k_2211_, lean_object* v_m_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2211_, v_m_2212_, v_a_2213_);
lean_dec(v_k_2211_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object* v_k_2215_, lean_object* v_m_2216_, lean_object* v_p_2217_){
_start:
{
lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2219_ = lean_int_dec_eq(v_k_2215_, v___x_2218_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; uint8_t v___x_2221_; 
v___x_2220_ = lean_box(0);
v___x_2221_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2216_, v___x_2220_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2215_, v_m_2216_, v_p_2217_);
return v___x_2222_;
}
else
{
lean_object* v___x_2223_; 
lean_dec(v_m_2216_);
v___x_2223_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2215_, v_p_2217_);
return v___x_2223_;
}
}
else
{
lean_object* v___x_2224_; 
lean_dec_ref(v_p_2217_);
lean_dec(v_m_2216_);
v___x_2224_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon___boxed(lean_object* v_k_2225_, lean_object* v_m_2226_, lean_object* v_p_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2225_, v_m_2226_, v_p_2227_);
lean_dec(v_k_2225_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go(lean_object* v_k_2229_, lean_object* v_m_2230_, lean_object* v_p_2231_, lean_object* v_acc_2232_){
_start:
{
if (lean_obj_tag(v_p_2231_) == 0)
{
lean_object* v_k_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_k_2233_ = lean_ctor_get(v_p_2231_, 0);
lean_inc(v_k_2233_);
lean_dec_ref_known(v_p_2231_, 1);
v___x_2234_ = lean_int_mul(v_k_2229_, v_k_2233_);
lean_dec(v_k_2233_);
v___x_2235_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2234_, v_m_2230_, v_acc_2232_);
return v___x_2235_;
}
else
{
lean_object* v_k_2236_; lean_object* v_v_2237_; lean_object* v_p_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_k_2236_ = lean_ctor_get(v_p_2231_, 0);
lean_inc(v_k_2236_);
v_v_2237_ = lean_ctor_get(v_p_2231_, 1);
lean_inc(v_v_2237_);
v_p_2238_ = lean_ctor_get(v_p_2231_, 2);
lean_inc_ref(v_p_2238_);
lean_dec_ref_known(v_p_2231_, 3);
v___x_2239_ = lean_int_mul(v_k_2229_, v_k_2236_);
lean_dec(v_k_2236_);
lean_inc(v_m_2230_);
v___x_2240_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_2230_, v_v_2237_);
v___x_2241_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2239_, v___x_2240_, v_acc_2232_);
v_p_2231_ = v_p_2238_;
v_acc_2232_ = v___x_2241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go___boxed(lean_object* v_k_2243_, lean_object* v_m_2244_, lean_object* v_p_2245_, lean_object* v_acc_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2243_, v_m_2244_, v_p_2245_, v_acc_2246_);
lean_dec(v_k_2243_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc(lean_object* v_k_2248_, lean_object* v_m_2249_, lean_object* v_p_2250_){
_start:
{
lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2252_ = lean_int_dec_eq(v_k_2248_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = lean_box(0);
v___x_2254_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2249_, v___x_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2256_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2248_, v_m_2249_, v_p_2250_, v___x_2255_);
return v___x_2256_;
}
else
{
lean_object* v___x_2257_; 
lean_dec(v_m_2249_);
v___x_2257_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2248_, v_p_2250_);
return v___x_2257_;
}
}
else
{
lean_object* v___x_2258_; 
lean_dec_ref(v_p_2250_);
lean_dec(v_m_2249_);
v___x_2258_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc___boxed(lean_object* v_k_2259_, lean_object* v_m_2260_, lean_object* v_p_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2259_, v_m_2260_, v_p_2261_);
lean_dec(v_k_2259_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_go(lean_object* v_fuel_2263_, lean_object* v_p_u2081_2264_, lean_object* v_p_u2082_2265_){
_start:
{
lean_object* v_zero_2266_; uint8_t v_isZero_2267_; 
v_zero_2266_ = lean_unsigned_to_nat(0u);
v_isZero_2267_ = lean_nat_dec_eq(v_fuel_2263_, v_zero_2266_);
if (v_isZero_2267_ == 1)
{
lean_object* v___x_2268_; 
lean_dec(v_fuel_2263_);
v___x_2268_ = l_Lean_Grind_CommRing_Poly_concat(v_p_u2081_2264_, v_p_u2082_2265_);
return v___x_2268_;
}
else
{
if (lean_obj_tag(v_p_u2081_2264_) == 0)
{
lean_dec(v_fuel_2263_);
if (lean_obj_tag(v_p_u2082_2265_) == 0)
{
lean_object* v_k_2269_; lean_object* v_k_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2278_; 
v_k_2269_ = lean_ctor_get(v_p_u2081_2264_, 0);
lean_inc(v_k_2269_);
lean_dec_ref_known(v_p_u2081_2264_, 1);
v_k_2270_ = lean_ctor_get(v_p_u2082_2265_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_p_u2082_2265_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2272_ = v_p_u2082_2265_;
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_k_2270_);
lean_dec(v_p_u2082_2265_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2274_ = lean_int_add(v_k_2269_, v_k_2270_);
lean_dec(v_k_2270_);
lean_dec(v_k_2269_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2274_);
v___x_2276_ = v___x_2272_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
else
{
lean_object* v_k_2279_; lean_object* v___x_2280_; 
v_k_2279_ = lean_ctor_get(v_p_u2081_2264_, 0);
lean_inc(v_k_2279_);
lean_dec_ref_known(v_p_u2081_2264_, 1);
v___x_2280_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2265_, v_k_2279_);
lean_dec(v_k_2279_);
return v___x_2280_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_2265_) == 0)
{
lean_object* v_k_2281_; lean_object* v___x_2282_; 
lean_dec(v_fuel_2263_);
v_k_2281_ = lean_ctor_get(v_p_u2082_2265_, 0);
lean_inc(v_k_2281_);
lean_dec_ref_known(v_p_u2082_2265_, 1);
v___x_2282_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2081_2264_, v_k_2281_);
lean_dec(v_k_2281_);
return v___x_2282_;
}
else
{
lean_object* v_k_2283_; lean_object* v_v_2284_; lean_object* v_p_2285_; lean_object* v_k_2286_; lean_object* v_v_2287_; lean_object* v_p_2288_; lean_object* v_one_2289_; lean_object* v_n_2290_; uint8_t v___x_2291_; 
v_k_2283_ = lean_ctor_get(v_p_u2081_2264_, 0);
v_v_2284_ = lean_ctor_get(v_p_u2081_2264_, 1);
v_p_2285_ = lean_ctor_get(v_p_u2081_2264_, 2);
v_k_2286_ = lean_ctor_get(v_p_u2082_2265_, 0);
v_v_2287_ = lean_ctor_get(v_p_u2082_2265_, 1);
v_p_2288_ = lean_ctor_get(v_p_u2082_2265_, 2);
v_one_2289_ = lean_unsigned_to_nat(1u);
v_n_2290_ = lean_nat_sub(v_fuel_2263_, v_one_2289_);
lean_dec(v_fuel_2263_);
v___x_2291_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2284_, v_v_2287_);
switch(v___x_2291_)
{
case 0:
{
lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2299_; 
lean_inc_ref(v_p_2288_);
lean_inc(v_v_2287_);
lean_inc(v_k_2286_);
v_isSharedCheck_2299_ = !lean_is_exclusive(v_p_u2082_2265_);
if (v_isSharedCheck_2299_ == 0)
{
lean_object* v_unused_2300_; lean_object* v_unused_2301_; lean_object* v_unused_2302_; 
v_unused_2300_ = lean_ctor_get(v_p_u2082_2265_, 2);
lean_dec(v_unused_2300_);
v_unused_2301_ = lean_ctor_get(v_p_u2082_2265_, 1);
lean_dec(v_unused_2301_);
v_unused_2302_ = lean_ctor_get(v_p_u2082_2265_, 0);
lean_dec(v_unused_2302_);
v___x_2293_ = v_p_u2082_2265_;
v_isShared_2294_ = v_isSharedCheck_2299_;
goto v_resetjp_2292_;
}
else
{
lean_dec(v_p_u2082_2265_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2299_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2295_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2290_, v_p_u2081_2264_, v_p_2288_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 2, v___x_2295_);
v___x_2297_ = v___x_2293_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2298_, 2, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
case 1:
{
lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2314_; 
lean_inc_ref(v_p_2288_);
lean_inc(v_k_2286_);
lean_inc_ref(v_p_2285_);
lean_inc(v_v_2284_);
lean_inc(v_k_2283_);
lean_dec_ref_known(v_p_u2081_2264_, 3);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_p_u2082_2265_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; lean_object* v_unused_2316_; lean_object* v_unused_2317_; 
v_unused_2315_ = lean_ctor_get(v_p_u2082_2265_, 2);
lean_dec(v_unused_2315_);
v_unused_2316_ = lean_ctor_get(v_p_u2082_2265_, 1);
lean_dec(v_unused_2316_);
v_unused_2317_ = lean_ctor_get(v_p_u2082_2265_, 0);
lean_dec(v_unused_2317_);
v___x_2304_ = v_p_u2082_2265_;
v_isShared_2305_ = v_isSharedCheck_2314_;
goto v_resetjp_2303_;
}
else
{
lean_dec(v_p_u2082_2265_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2314_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v_k_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v_k_2306_ = lean_int_add(v_k_2283_, v_k_2286_);
lean_dec(v_k_2286_);
lean_dec(v_k_2283_);
v___x_2307_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2308_ = lean_int_dec_eq(v_k_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
v___x_2309_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2290_, v_p_2285_, v_p_2288_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 2, v___x_2309_);
lean_ctor_set(v___x_2304_, 1, v_v_2284_);
lean_ctor_set(v___x_2304_, 0, v_k_2306_);
v___x_2311_ = v___x_2304_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_k_2306_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
else
{
lean_dec(v_k_2306_);
lean_del_object(v___x_2304_);
lean_dec(v_v_2284_);
v_fuel_2263_ = v_n_2290_;
v_p_u2081_2264_ = v_p_2285_;
v_p_u2082_2265_ = v_p_2288_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2325_; 
lean_inc_ref(v_p_2285_);
lean_inc(v_v_2284_);
lean_inc(v_k_2283_);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_p_u2081_2264_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; lean_object* v_unused_2327_; lean_object* v_unused_2328_; 
v_unused_2326_ = lean_ctor_get(v_p_u2081_2264_, 2);
lean_dec(v_unused_2326_);
v_unused_2327_ = lean_ctor_get(v_p_u2081_2264_, 1);
lean_dec(v_unused_2327_);
v_unused_2328_ = lean_ctor_get(v_p_u2081_2264_, 0);
lean_dec(v_unused_2328_);
v___x_2319_ = v_p_u2081_2264_;
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
else
{
lean_dec(v_p_u2081_2264_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2321_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2290_, v_p_2285_, v_p_u2082_2265_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 2, v___x_2321_);
v___x_2323_ = v___x_2319_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2324_, 2, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object* v_p_u2081_2329_, lean_object* v_p_u2082_2330_){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = lean_unsigned_to_nat(1000000u);
v___x_2332_ = l_Lean_Grind_CommRing_Poly_combine_go(v___x_2331_, v_p_u2081_2329_, v_p_u2082_2330_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object* v_p_u2081_2333_, lean_object* v_p_u2082_2334_, lean_object* v_h__1_2335_, lean_object* v_h__2_2336_, lean_object* v_h__3_2337_, lean_object* v_h__4_2338_){
_start:
{
if (lean_obj_tag(v_p_u2081_2333_) == 0)
{
lean_dec(v_h__4_2338_);
lean_dec(v_h__3_2337_);
if (lean_obj_tag(v_p_u2082_2334_) == 0)
{
lean_object* v_k_2339_; lean_object* v_k_2340_; lean_object* v___x_2341_; 
lean_dec(v_h__2_2336_);
v_k_2339_ = lean_ctor_get(v_p_u2081_2333_, 0);
lean_inc(v_k_2339_);
lean_dec_ref_known(v_p_u2081_2333_, 1);
v_k_2340_ = lean_ctor_get(v_p_u2082_2334_, 0);
lean_inc(v_k_2340_);
lean_dec_ref_known(v_p_u2082_2334_, 1);
v___x_2341_ = lean_apply_2(v_h__1_2335_, v_k_2339_, v_k_2340_);
return v___x_2341_;
}
else
{
lean_object* v_k_2342_; lean_object* v_k_2343_; lean_object* v_v_2344_; lean_object* v_p_2345_; lean_object* v___x_2346_; 
lean_dec(v_h__1_2335_);
v_k_2342_ = lean_ctor_get(v_p_u2081_2333_, 0);
lean_inc(v_k_2342_);
lean_dec_ref_known(v_p_u2081_2333_, 1);
v_k_2343_ = lean_ctor_get(v_p_u2082_2334_, 0);
lean_inc(v_k_2343_);
v_v_2344_ = lean_ctor_get(v_p_u2082_2334_, 1);
lean_inc(v_v_2344_);
v_p_2345_ = lean_ctor_get(v_p_u2082_2334_, 2);
lean_inc_ref(v_p_2345_);
lean_dec_ref_known(v_p_u2082_2334_, 3);
v___x_2346_ = lean_apply_4(v_h__2_2336_, v_k_2342_, v_k_2343_, v_v_2344_, v_p_2345_);
return v___x_2346_;
}
}
else
{
lean_dec(v_h__2_2336_);
lean_dec(v_h__1_2335_);
if (lean_obj_tag(v_p_u2082_2334_) == 0)
{
lean_object* v_k_2347_; lean_object* v_v_2348_; lean_object* v_p_2349_; lean_object* v_k_2350_; lean_object* v___x_2351_; 
lean_dec(v_h__4_2338_);
v_k_2347_ = lean_ctor_get(v_p_u2081_2333_, 0);
lean_inc(v_k_2347_);
v_v_2348_ = lean_ctor_get(v_p_u2081_2333_, 1);
lean_inc(v_v_2348_);
v_p_2349_ = lean_ctor_get(v_p_u2081_2333_, 2);
lean_inc_ref(v_p_2349_);
lean_dec_ref_known(v_p_u2081_2333_, 3);
v_k_2350_ = lean_ctor_get(v_p_u2082_2334_, 0);
lean_inc(v_k_2350_);
lean_dec_ref_known(v_p_u2082_2334_, 1);
v___x_2351_ = lean_apply_4(v_h__3_2337_, v_k_2347_, v_v_2348_, v_p_2349_, v_k_2350_);
return v___x_2351_;
}
else
{
lean_object* v_k_2352_; lean_object* v_v_2353_; lean_object* v_p_2354_; lean_object* v_k_2355_; lean_object* v_v_2356_; lean_object* v_p_2357_; lean_object* v___x_2358_; 
lean_dec(v_h__3_2337_);
v_k_2352_ = lean_ctor_get(v_p_u2081_2333_, 0);
lean_inc(v_k_2352_);
v_v_2353_ = lean_ctor_get(v_p_u2081_2333_, 1);
lean_inc(v_v_2353_);
v_p_2354_ = lean_ctor_get(v_p_u2081_2333_, 2);
lean_inc_ref(v_p_2354_);
lean_dec_ref_known(v_p_u2081_2333_, 3);
v_k_2355_ = lean_ctor_get(v_p_u2082_2334_, 0);
lean_inc(v_k_2355_);
v_v_2356_ = lean_ctor_get(v_p_u2082_2334_, 1);
lean_inc(v_v_2356_);
v_p_2357_ = lean_ctor_get(v_p_u2082_2334_, 2);
lean_inc_ref(v_p_2357_);
lean_dec_ref_known(v_p_u2082_2334_, 3);
v___x_2358_ = lean_apply_6(v_h__4_2338_, v_k_2352_, v_v_2353_, v_p_2354_, v_k_2355_, v_v_2356_, v_p_2357_);
return v___x_2358_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object* v_motive_2359_, lean_object* v_p_u2081_2360_, lean_object* v_p_u2082_2361_, lean_object* v_h__1_2362_, lean_object* v_h__2_2363_, lean_object* v_h__3_2364_, lean_object* v_h__4_2365_){
_start:
{
if (lean_obj_tag(v_p_u2081_2360_) == 0)
{
lean_dec(v_h__4_2365_);
lean_dec(v_h__3_2364_);
if (lean_obj_tag(v_p_u2082_2361_) == 0)
{
lean_object* v_k_2366_; lean_object* v_k_2367_; lean_object* v___x_2368_; 
lean_dec(v_h__2_2363_);
v_k_2366_ = lean_ctor_get(v_p_u2081_2360_, 0);
lean_inc(v_k_2366_);
lean_dec_ref_known(v_p_u2081_2360_, 1);
v_k_2367_ = lean_ctor_get(v_p_u2082_2361_, 0);
lean_inc(v_k_2367_);
lean_dec_ref_known(v_p_u2082_2361_, 1);
v___x_2368_ = lean_apply_2(v_h__1_2362_, v_k_2366_, v_k_2367_);
return v___x_2368_;
}
else
{
lean_object* v_k_2369_; lean_object* v_k_2370_; lean_object* v_v_2371_; lean_object* v_p_2372_; lean_object* v___x_2373_; 
lean_dec(v_h__1_2362_);
v_k_2369_ = lean_ctor_get(v_p_u2081_2360_, 0);
lean_inc(v_k_2369_);
lean_dec_ref_known(v_p_u2081_2360_, 1);
v_k_2370_ = lean_ctor_get(v_p_u2082_2361_, 0);
lean_inc(v_k_2370_);
v_v_2371_ = lean_ctor_get(v_p_u2082_2361_, 1);
lean_inc(v_v_2371_);
v_p_2372_ = lean_ctor_get(v_p_u2082_2361_, 2);
lean_inc_ref(v_p_2372_);
lean_dec_ref_known(v_p_u2082_2361_, 3);
v___x_2373_ = lean_apply_4(v_h__2_2363_, v_k_2369_, v_k_2370_, v_v_2371_, v_p_2372_);
return v___x_2373_;
}
}
else
{
lean_dec(v_h__2_2363_);
lean_dec(v_h__1_2362_);
if (lean_obj_tag(v_p_u2082_2361_) == 0)
{
lean_object* v_k_2374_; lean_object* v_v_2375_; lean_object* v_p_2376_; lean_object* v_k_2377_; lean_object* v___x_2378_; 
lean_dec(v_h__4_2365_);
v_k_2374_ = lean_ctor_get(v_p_u2081_2360_, 0);
lean_inc(v_k_2374_);
v_v_2375_ = lean_ctor_get(v_p_u2081_2360_, 1);
lean_inc(v_v_2375_);
v_p_2376_ = lean_ctor_get(v_p_u2081_2360_, 2);
lean_inc_ref(v_p_2376_);
lean_dec_ref_known(v_p_u2081_2360_, 3);
v_k_2377_ = lean_ctor_get(v_p_u2082_2361_, 0);
lean_inc(v_k_2377_);
lean_dec_ref_known(v_p_u2082_2361_, 1);
v___x_2378_ = lean_apply_4(v_h__3_2364_, v_k_2374_, v_v_2375_, v_p_2376_, v_k_2377_);
return v___x_2378_;
}
else
{
lean_object* v_k_2379_; lean_object* v_v_2380_; lean_object* v_p_2381_; lean_object* v_k_2382_; lean_object* v_v_2383_; lean_object* v_p_2384_; lean_object* v___x_2385_; 
lean_dec(v_h__3_2364_);
v_k_2379_ = lean_ctor_get(v_p_u2081_2360_, 0);
lean_inc(v_k_2379_);
v_v_2380_ = lean_ctor_get(v_p_u2081_2360_, 1);
lean_inc(v_v_2380_);
v_p_2381_ = lean_ctor_get(v_p_u2081_2360_, 2);
lean_inc_ref(v_p_2381_);
lean_dec_ref_known(v_p_u2081_2360_, 3);
v_k_2382_ = lean_ctor_get(v_p_u2082_2361_, 0);
lean_inc(v_k_2382_);
v_v_2383_ = lean_ctor_get(v_p_u2082_2361_, 1);
lean_inc(v_v_2383_);
v_p_2384_ = lean_ctor_get(v_p_u2082_2361_, 2);
lean_inc_ref(v_p_2384_);
lean_dec_ref_known(v_p_u2082_2361_, 3);
v___x_2385_ = lean_apply_6(v_h__4_2365_, v_k_2379_, v_v_2380_, v_p_2381_, v_k_2382_, v_v_2383_, v_p_2384_);
return v___x_2385_;
}
}
}
}
lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t v_x_2386_, lean_object* v_h__1_2387_, lean_object* v_h__2_2388_, lean_object* v_h__3_2389_){
_start:
{
switch(v_x_2386_)
{
case 0:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_dec(v_h__2_2388_);
lean_dec(v_h__1_2387_);
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_apply_1(v_h__3_2389_, v___x_2390_);
return v___x_2391_;
}
case 1:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
lean_dec(v_h__3_2389_);
lean_dec(v_h__2_2388_);
v___x_2392_ = lean_box(0);
v___x_2393_ = lean_apply_1(v_h__1_2387_, v___x_2392_);
return v___x_2393_;
}
default: 
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
lean_dec(v_h__3_2389_);
lean_dec(v_h__1_2387_);
v___x_2394_ = lean_box(0);
v___x_2395_ = lean_apply_1(v_h__2_2388_, v___x_2394_);
return v___x_2395_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2386_ = stack[0].m_num;
lean_object* v_h__1_2387_ = stack[1].m_obj;
lean_object* v_h__2_2388_ = stack[2].m_obj;
lean_object* v_h__3_2389_ = stack[3].m_obj;
lean_object* v_res_2396_;
v_res_2396_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(v_x_2386_, v_h__1_2387_, v_h__2_2388_, v_h__3_2389_);
stack->m_obj
 = v_res_2396_;
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object* v_x_2397_, lean_object* v_h__1_2398_, lean_object* v_h__2_2399_, lean_object* v_h__3_2400_){
_start:
{
uint8_t v_x_33__boxed_2401_; lean_object* v_res_2402_; 
v_x_33__boxed_2401_ = lean_unbox(v_x_2397_);
v_res_2402_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(v_x_33__boxed_2401_, v_h__1_2398_, v_h__2_2399_, v_h__3_2400_);
return v_res_2402_;
}
}
lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object* v_motive_2403_, uint8_t v_x_2404_, lean_object* v_h__1_2405_, lean_object* v_h__2_2406_, lean_object* v_h__3_2407_){
_start:
{
switch(v_x_2404_)
{
case 0:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
lean_dec(v_h__2_2406_);
lean_dec(v_h__1_2405_);
v___x_2408_ = lean_box(0);
v___x_2409_ = lean_apply_1(v_h__3_2407_, v___x_2408_);
return v___x_2409_;
}
case 1:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
lean_dec(v_h__3_2407_);
lean_dec(v_h__2_2406_);
v___x_2410_ = lean_box(0);
v___x_2411_ = lean_apply_1(v_h__1_2405_, v___x_2410_);
return v___x_2411_;
}
default: 
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec(v_h__3_2407_);
lean_dec(v_h__1_2405_);
v___x_2412_ = lean_box(0);
v___x_2413_ = lean_apply_1(v_h__2_2406_, v___x_2412_);
return v___x_2413_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2404_ = stack[1].m_num;
lean_object* v_h__1_2405_ = stack[2].m_obj;
lean_object* v_h__2_2406_ = stack[3].m_obj;
lean_object* v_h__3_2407_ = stack[4].m_obj;
lean_object* v_res_2414_;
v_res_2414_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_box(0), v_x_2404_, v_h__1_2405_, v_h__2_2406_, v_h__3_2407_);
stack->m_obj
 = v_res_2414_;
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object* v_motive_2415_, lean_object* v_x_2416_, lean_object* v_h__1_2417_, lean_object* v_h__2_2418_, lean_object* v_h__3_2419_){
_start:
{
uint8_t v_x_56__boxed_2420_; lean_object* v_res_2421_; 
v_x_56__boxed_2420_ = lean_unbox(v_x_2416_);
v_res_2421_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(v_motive_2415_, v_x_56__boxed_2420_, v_h__1_2417_, v_h__2_2418_, v_h__3_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul_go(lean_object* v_p_u2082_2422_, lean_object* v_p_u2081_2423_, lean_object* v_acc_2424_){
_start:
{
if (lean_obj_tag(v_p_u2081_2423_) == 0)
{
lean_object* v_k_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v_k_2425_ = lean_ctor_get(v_p_u2081_2423_, 0);
lean_inc(v_k_2425_);
lean_dec_ref_known(v_p_u2081_2423_, 1);
v___x_2426_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2425_, v_p_u2082_2422_);
lean_dec(v_k_2425_);
v___x_2427_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2424_, v___x_2426_);
return v___x_2427_;
}
else
{
lean_object* v_k_2428_; lean_object* v_v_2429_; lean_object* v_p_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_k_2428_ = lean_ctor_get(v_p_u2081_2423_, 0);
lean_inc(v_k_2428_);
v_v_2429_ = lean_ctor_get(v_p_u2081_2423_, 1);
lean_inc(v_v_2429_);
v_p_2430_ = lean_ctor_get(v_p_u2081_2423_, 2);
lean_inc_ref(v_p_2430_);
lean_dec_ref_known(v_p_u2081_2423_, 3);
lean_inc_ref(v_p_u2082_2422_);
v___x_2431_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2428_, v_v_2429_, v_p_u2082_2422_);
lean_dec(v_k_2428_);
v___x_2432_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2424_, v___x_2431_);
v_p_u2081_2423_ = v_p_2430_;
v_acc_2424_ = v___x_2432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul(lean_object* v_p_u2081_2434_, lean_object* v_p_u2082_2435_){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2437_ = l_Lean_Grind_CommRing_Poly_mul_go(v_p_u2082_2435_, v_p_u2081_2434_, v___x_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc_go(lean_object* v_p_u2082_2438_, lean_object* v_p_u2081_2439_, lean_object* v_acc_2440_){
_start:
{
if (lean_obj_tag(v_p_u2081_2439_) == 0)
{
lean_object* v_k_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_k_2441_ = lean_ctor_get(v_p_u2081_2439_, 0);
lean_inc(v_k_2441_);
lean_dec_ref_known(v_p_u2081_2439_, 1);
v___x_2442_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2441_, v_p_u2082_2438_);
lean_dec(v_k_2441_);
v___x_2443_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2440_, v___x_2442_);
return v___x_2443_;
}
else
{
lean_object* v_k_2444_; lean_object* v_v_2445_; lean_object* v_p_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_k_2444_ = lean_ctor_get(v_p_u2081_2439_, 0);
lean_inc(v_k_2444_);
v_v_2445_ = lean_ctor_get(v_p_u2081_2439_, 1);
lean_inc(v_v_2445_);
v_p_2446_ = lean_ctor_get(v_p_u2081_2439_, 2);
lean_inc_ref(v_p_2446_);
lean_dec_ref_known(v_p_u2081_2439_, 3);
lean_inc_ref(v_p_u2082_2438_);
v___x_2447_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2444_, v_v_2445_, v_p_u2082_2438_);
lean_dec(v_k_2444_);
v___x_2448_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2440_, v___x_2447_);
v_p_u2081_2439_ = v_p_2446_;
v_acc_2440_ = v___x_2448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object* v_p_u2081_2450_, lean_object* v_p_u2082_2451_){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2453_ = l_Lean_Grind_CommRing_Poly_mul__nc_go(v_p_u2082_2451_, v_p_u2081_2450_, v___x_2452_);
return v___x_2453_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_pow___closed__0(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow(lean_object* v_p_2456_, lean_object* v_k_2457_){
_start:
{
lean_object* v_zero_2458_; uint8_t v_isZero_2459_; 
v_zero_2458_ = lean_unsigned_to_nat(0u);
v_isZero_2459_ = lean_nat_dec_eq(v_k_2457_, v_zero_2458_);
if (v_isZero_2459_ == 1)
{
lean_object* v___x_2460_; 
lean_dec_ref(v_p_2456_);
v___x_2460_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2460_;
}
else
{
lean_object* v_one_2461_; lean_object* v_n_2462_; uint8_t v___x_2463_; 
v_one_2461_ = lean_unsigned_to_nat(1u);
v_n_2462_ = lean_nat_sub(v_k_2457_, v_one_2461_);
v___x_2463_ = lean_nat_dec_eq(v_n_2462_, v_zero_2458_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
lean_inc_ref(v_p_2456_);
v___x_2464_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2456_, v_n_2462_);
lean_dec(v_n_2462_);
v___x_2465_ = l_Lean_Grind_CommRing_Poly_mul(v_p_2456_, v___x_2464_);
return v___x_2465_;
}
else
{
lean_dec(v_n_2462_);
return v_p_2456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow___boxed(lean_object* v_p_2466_, lean_object* v_k_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2466_, v_k_2467_);
lean_dec(v_k_2467_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc(lean_object* v_p_2469_, lean_object* v_k_2470_){
_start:
{
lean_object* v_zero_2471_; uint8_t v_isZero_2472_; 
v_zero_2471_ = lean_unsigned_to_nat(0u);
v_isZero_2472_ = lean_nat_dec_eq(v_k_2470_, v_zero_2471_);
if (v_isZero_2472_ == 1)
{
lean_object* v___x_2473_; 
lean_dec_ref(v_p_2469_);
v___x_2473_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2473_;
}
else
{
lean_object* v_one_2474_; lean_object* v_n_2475_; uint8_t v___x_2476_; 
v_one_2474_ = lean_unsigned_to_nat(1u);
v_n_2475_ = lean_nat_sub(v_k_2470_, v_one_2474_);
v___x_2476_ = lean_nat_dec_eq(v_n_2475_, v_zero_2471_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
lean_inc_ref(v_p_2469_);
v___x_2477_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2469_, v_n_2475_);
lean_dec(v_n_2475_);
v___x_2478_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2477_, v_p_2469_);
return v___x_2478_;
}
else
{
lean_dec(v_n_2475_);
return v_p_2469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc___boxed(lean_object* v_p_2479_, lean_object* v_k_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2479_, v_k_2480_);
lean_dec(v_k_2480_);
return v_res_2481_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2483_ = lean_int_neg(v___x_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object* v_x_2484_){
_start:
{
switch(lean_obj_tag(v_x_2484_))
{
case 0:
{
lean_object* v_k_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
v_k_2485_ = lean_ctor_get(v_x_2484_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_x_2484_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v_x_2484_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_k_2485_);
lean_dec(v_x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_k_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
case 1:
{
lean_object* v_k_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2501_; 
v_k_2493_ = lean_ctor_get(v_x_2484_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v_x_2484_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2495_ = v_x_2484_;
v_isShared_2496_ = v_isSharedCheck_2501_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_k_2493_);
lean_dec(v_x_2484_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2501_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2497_ = lean_nat_to_int(v_k_2493_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set_tag(v___x_2495_, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2497_);
v___x_2499_ = v___x_2495_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
case 2:
{
lean_object* v_k_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
v_k_2502_ = lean_ctor_get(v_x_2484_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v_x_2484_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v_x_2484_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_k_2502_);
lean_dec(v_x_2484_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set_tag(v___x_2504_, 0);
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_k_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
case 3:
{
lean_object* v_i_2510_; lean_object* v___x_2511_; 
v_i_2510_ = lean_ctor_get(v_x_2484_, 0);
lean_inc(v_i_2510_);
lean_dec_ref_known(v_x_2484_, 1);
v___x_2511_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2510_);
return v___x_2511_;
}
case 4:
{
lean_object* v_a_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_a_2512_ = lean_ctor_get(v_x_2484_, 0);
lean_inc_ref(v_a_2512_);
lean_dec_ref_known(v_x_2484_, 1);
v___x_2513_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2514_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2512_);
v___x_2515_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2513_, v___x_2514_);
return v___x_2515_;
}
case 5:
{
lean_object* v_a_2516_; lean_object* v_b_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v_a_2516_ = lean_ctor_get(v_x_2484_, 0);
lean_inc_ref(v_a_2516_);
v_b_2517_ = lean_ctor_get(v_x_2484_, 1);
lean_inc_ref(v_b_2517_);
lean_dec_ref_known(v_x_2484_, 2);
v___x_2518_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2516_);
v___x_2519_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2517_);
v___x_2520_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2518_, v___x_2519_);
return v___x_2520_;
}
case 6:
{
lean_object* v_a_2521_; lean_object* v_b_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v_a_2521_ = lean_ctor_get(v_x_2484_, 0);
lean_inc_ref(v_a_2521_);
v_b_2522_ = lean_ctor_get(v_x_2484_, 1);
lean_inc_ref(v_b_2522_);
lean_dec_ref_known(v_x_2484_, 2);
v___x_2523_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2521_);
v___x_2524_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2525_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2522_);
v___x_2526_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2524_, v___x_2525_);
v___x_2527_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2523_, v___x_2526_);
return v___x_2527_;
}
case 7:
{
lean_object* v_a_2528_; lean_object* v_b_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v_a_2528_ = lean_ctor_get(v_x_2484_, 0);
lean_inc_ref(v_a_2528_);
v_b_2529_ = lean_ctor_get(v_x_2484_, 1);
lean_inc_ref(v_b_2529_);
lean_dec_ref_known(v_x_2484_, 2);
v___x_2530_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2528_);
v___x_2531_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2529_);
v___x_2532_ = l_Lean_Grind_CommRing_Poly_mul(v___x_2530_, v___x_2531_);
return v___x_2532_;
}
default: 
{
lean_object* v_a_2533_; lean_object* v_k_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2566_; 
v_a_2533_ = lean_ctor_get(v_x_2484_, 0);
v_k_2534_ = lean_ctor_get(v_x_2484_, 1);
v_isSharedCheck_2566_ = !lean_is_exclusive(v_x_2484_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2536_ = v_x_2484_;
v_isShared_2537_ = v_isSharedCheck_2566_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_k_2534_);
lean_inc(v_a_2533_);
lean_dec(v_x_2484_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2566_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v_n_2539_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2542_ = lean_unsigned_to_nat(0u);
v___x_2543_ = lean_nat_dec_eq(v_k_2534_, v___x_2542_);
if (v___x_2543_ == 0)
{
switch(lean_obj_tag(v_a_2533_))
{
case 0:
{
lean_object* v_k_2544_; 
lean_del_object(v___x_2536_);
v_k_2544_ = lean_ctor_get(v_a_2533_, 0);
lean_inc(v_k_2544_);
lean_dec_ref_known(v_a_2533_, 1);
v_n_2539_ = v_k_2544_;
goto v___jp_2538_;
}
case 2:
{
lean_object* v_k_2545_; 
lean_del_object(v___x_2536_);
v_k_2545_ = lean_ctor_get(v_a_2533_, 0);
lean_inc(v_k_2545_);
lean_dec_ref_known(v_a_2533_, 1);
v_n_2539_ = v_k_2545_;
goto v___jp_2538_;
}
case 1:
{
lean_object* v_k_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2555_; 
lean_del_object(v___x_2536_);
v_k_2546_ = lean_ctor_get(v_a_2533_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_a_2533_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2548_ = v_a_2533_;
v_isShared_2549_ = v_isSharedCheck_2555_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_k_2546_);
lean_dec(v_a_2533_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2555_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2550_ = lean_nat_to_int(v_k_2546_);
v___x_2551_ = l_Int_pow(v___x_2550_, v_k_2534_);
lean_dec(v_k_2534_);
lean_dec(v___x_2550_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set_tag(v___x_2548_, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2551_);
v___x_2553_ = v___x_2548_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
case 3:
{
lean_object* v_i_2556_; lean_object* v___x_2558_; 
v_i_2556_ = lean_ctor_get(v_a_2533_, 0);
lean_inc(v_i_2556_);
lean_dec_ref_known(v_a_2533_, 1);
if (v_isShared_2537_ == 0)
{
lean_ctor_set_tag(v___x_2536_, 0);
lean_ctor_set(v___x_2536_, 0, v_i_2556_);
v___x_2558_ = v___x_2536_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_i_2556_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_k_2534_);
v___x_2558_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = lean_box(0);
v___x_2560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2558_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2560_);
return v___x_2561_;
}
}
default: 
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
lean_del_object(v___x_2536_);
v___x_2563_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2533_);
v___x_2564_ = l_Lean_Grind_CommRing_Poly_pow(v___x_2563_, v_k_2534_);
lean_dec(v_k_2534_);
return v___x_2564_;
}
}
}
else
{
lean_object* v___x_2565_; 
lean_del_object(v___x_2536_);
lean_dec(v_k_2534_);
lean_dec_ref(v_a_2533_);
v___x_2565_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2565_;
}
v___jp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = l_Int_pow(v_n_2539_, v_k_2534_);
lean_dec(v_k_2534_);
lean_dec(v_n_2539_);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
return v___x_2541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf(lean_object* v_m_2567_, lean_object* v_x_2568_){
_start:
{
if (lean_obj_tag(v_m_2567_) == 0)
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_unsigned_to_nat(0u);
return v___x_2569_;
}
else
{
lean_object* v_p_2570_; lean_object* v_m_2571_; lean_object* v_x_2572_; lean_object* v_k_2573_; uint8_t v___x_2574_; 
v_p_2570_ = lean_ctor_get(v_m_2567_, 0);
v_m_2571_ = lean_ctor_get(v_m_2567_, 1);
v_x_2572_ = lean_ctor_get(v_p_2570_, 0);
v_k_2573_ = lean_ctor_get(v_p_2570_, 1);
v___x_2574_ = lean_nat_dec_eq(v_x_2572_, v_x_2568_);
if (v___x_2574_ == 0)
{
v_m_2567_ = v_m_2571_;
goto _start;
}
else
{
lean_inc(v_k_2573_);
return v_k_2573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf___boxed(lean_object* v_m_2576_, lean_object* v_x_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_2576_, v_x_2577_);
lean_dec(v_x_2577_);
lean_dec(v_m_2576_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar(lean_object* v_m_2579_, lean_object* v_x_2580_){
_start:
{
if (lean_obj_tag(v_m_2579_) == 0)
{
return v_m_2579_;
}
else
{
lean_object* v_p_2581_; lean_object* v_m_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2592_; 
v_p_2581_ = lean_ctor_get(v_m_2579_, 0);
v_m_2582_ = lean_ctor_get(v_m_2579_, 1);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_m_2579_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2584_ = v_m_2579_;
v_isShared_2585_ = v_isSharedCheck_2592_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_m_2582_);
lean_inc(v_p_2581_);
lean_dec(v_m_2579_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2592_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v_x_2586_; uint8_t v___x_2587_; 
v_x_2586_ = lean_ctor_get(v_p_2581_, 0);
v___x_2587_ = lean_nat_dec_eq(v_x_2586_, v_x_2580_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2588_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2582_, v_x_2580_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 1, v___x_2588_);
v___x_2590_ = v___x_2584_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_p_2581_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
else
{
lean_del_object(v___x_2584_);
lean_dec_ref(v_p_2581_);
return v_m_2582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar___boxed(lean_object* v_m_2593_, lean_object* v_x_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2593_, v_x_2594_);
lean_dec(v_x_2594_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27(lean_object* v_c_2596_, lean_object* v_x_2597_, lean_object* v_p_2598_, lean_object* v_acc_2599_){
_start:
{
if (lean_obj_tag(v_p_2598_) == 0)
{
lean_object* v_k_2600_; lean_object* v___x_2601_; 
v_k_2600_ = lean_ctor_get(v_p_2598_, 0);
lean_inc(v_k_2600_);
lean_dec_ref_known(v_p_2598_, 1);
v___x_2601_ = l_Lean_Grind_CommRing_Poly_addConst(v_acc_2599_, v_k_2600_);
lean_dec(v_k_2600_);
return v___x_2601_;
}
else
{
lean_object* v_k_2602_; lean_object* v_v_2603_; lean_object* v_p_2604_; lean_object* v_n_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v_k_2602_ = lean_ctor_get(v_p_2598_, 0);
lean_inc(v_k_2602_);
v_v_2603_ = lean_ctor_get(v_p_2598_, 1);
lean_inc(v_v_2603_);
v_p_2604_ = lean_ctor_get(v_p_2598_, 2);
lean_inc_ref(v_p_2604_);
lean_dec_ref_known(v_p_2598_, 3);
v_n_2608_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_2603_, v_x_2597_);
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = lean_nat_dec_lt(v___x_2609_, v_n_2608_);
if (v___x_2610_ == 0)
{
lean_dec(v_n_2608_);
goto v___jp_2605_;
}
else
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2611_ = l_Int_pow(v_c_2596_, v_n_2608_);
lean_dec(v_n_2608_);
v___x_2612_ = lean_int_emod(v_k_2602_, v___x_2611_);
v___x_2613_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2614_ = lean_int_dec_eq(v___x_2612_, v___x_2613_);
lean_dec(v___x_2612_);
if (v___x_2614_ == 0)
{
lean_dec(v___x_2611_);
goto v___jp_2605_;
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_int_ediv(v_k_2602_, v___x_2611_);
lean_dec(v___x_2611_);
lean_dec(v_k_2602_);
v___x_2616_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_v_2603_, v_x_2597_);
v___x_2617_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2615_, v___x_2616_, v_acc_2599_);
v_p_2598_ = v_p_2604_;
v_acc_2599_ = v___x_2617_;
goto _start;
}
}
v___jp_2605_:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_Grind_CommRing_Poly_insert(v_k_2602_, v_v_2603_, v_acc_2599_);
v_p_2598_ = v_p_2604_;
v_acc_2599_ = v___x_2606_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27___boxed(lean_object* v_c_2619_, lean_object* v_x_2620_, lean_object* v_p_2621_, lean_object* v_acc_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2619_, v_x_2620_, v_p_2621_, v_acc_2622_);
lean_dec(v_x_2620_);
lean_dec(v_c_2619_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar(lean_object* v_c_2624_, lean_object* v_x_2625_, lean_object* v_p_2626_){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2628_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2624_, v_x_2625_, v_p_2626_, v___x_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar___boxed(lean_object* v_c_2629_, lean_object* v_x_2630_, lean_object* v_p_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_Grind_CommRing_Poly_cancelVar(v_c_2629_, v_x_2630_, v_p_2631_);
lean_dec(v_x_2630_);
lean_dec(v_c_2629_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(lean_object* v_p_2633_, lean_object* v_acc_2634_){
_start:
{
lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2635_ = lean_unsigned_to_nat(1u);
v___x_2636_ = lean_nat_dec_eq(v_acc_2634_, v___x_2635_);
if (v___x_2636_ == 0)
{
if (lean_obj_tag(v_p_2633_) == 0)
{
lean_object* v_k_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v_k_2637_ = lean_ctor_get(v_p_2633_, 0);
v___x_2638_ = lean_nat_abs(v_k_2637_);
v___x_2639_ = lean_nat_gcd(v_acc_2634_, v___x_2638_);
lean_dec(v___x_2638_);
lean_dec(v_acc_2634_);
return v___x_2639_;
}
else
{
lean_object* v_k_2640_; lean_object* v_p_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v_k_2640_ = lean_ctor_get(v_p_2633_, 0);
v_p_2641_ = lean_ctor_get(v_p_2633_, 2);
v___x_2642_ = lean_nat_abs(v_k_2640_);
v___x_2643_ = lean_nat_gcd(v_acc_2634_, v___x_2642_);
lean_dec(v___x_2642_);
lean_dec(v_acc_2634_);
v_p_2633_ = v_p_2641_;
v_acc_2634_ = v___x_2643_;
goto _start;
}
}
else
{
return v_acc_2634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs_go___boxed(lean_object* v_p_2645_, lean_object* v_acc_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_2645_, v_acc_2646_);
lean_dec_ref(v_p_2645_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs(lean_object* v_x_2648_){
_start:
{
if (lean_obj_tag(v_x_2648_) == 0)
{
lean_object* v_k_2649_; lean_object* v___x_2650_; 
v_k_2649_ = lean_ctor_get(v_x_2648_, 0);
v___x_2650_ = lean_nat_abs(v_k_2649_);
return v___x_2650_;
}
else
{
lean_object* v_k_2651_; lean_object* v_p_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v_k_2651_ = lean_ctor_get(v_x_2648_, 0);
v_p_2652_ = lean_ctor_get(v_x_2648_, 2);
v___x_2653_ = lean_nat_abs(v_k_2651_);
v___x_2654_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_2652_, v___x_2653_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs___boxed(lean_object* v_x_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs(v_x_2655_);
lean_dec_ref(v_x_2655_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst(lean_object* v_p_2657_, lean_object* v_a_2658_){
_start:
{
if (lean_obj_tag(v_p_2657_) == 0)
{
lean_object* v_k_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2667_; 
v_k_2659_ = lean_ctor_get(v_p_2657_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v_p_2657_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2661_ = v_p_2657_;
v_isShared_2662_ = v_isSharedCheck_2667_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_k_2659_);
lean_dec(v_p_2657_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2667_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2663_ = lean_int_ediv(v_k_2659_, v_a_2658_);
lean_dec(v_k_2659_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2663_);
v___x_2665_ = v___x_2661_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
else
{
lean_object* v_k_2668_; lean_object* v_v_2669_; lean_object* v_p_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2679_; 
v_k_2668_ = lean_ctor_get(v_p_2657_, 0);
v_v_2669_ = lean_ctor_get(v_p_2657_, 1);
v_p_2670_ = lean_ctor_get(v_p_2657_, 2);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_p_2657_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2672_ = v_p_2657_;
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_p_2670_);
lean_inc(v_v_2669_);
lean_inc(v_k_2668_);
lean_dec(v_p_2657_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2674_ = lean_int_ediv(v_k_2668_, v_a_2658_);
lean_dec(v_k_2668_);
v___x_2675_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_2670_, v_a_2658_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 2, v___x_2675_);
lean_ctor_set(v___x_2672_, 0, v___x_2674_);
v___x_2677_ = v___x_2672_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_v_2669_);
lean_ctor_set(v_reuseFailAlloc_2678_, 2, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst___boxed(lean_object* v_p_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_2680_, v_a_2681_);
lean_dec(v_a_2681_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(lean_object* v_x_2683_, lean_object* v_p_2684_, lean_object* v_max_2685_){
_start:
{
if (lean_obj_tag(v_p_2684_) == 0)
{
return v_max_2685_;
}
else
{
lean_object* v_v_2686_; lean_object* v_p_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v_v_2686_ = lean_ctor_get(v_p_2684_, 1);
v_p_2687_ = lean_ctor_get(v_p_2684_, 2);
v___x_2688_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_2686_, v_x_2683_);
v___x_2689_ = lean_nat_dec_le(v_max_2685_, v___x_2688_);
if (v___x_2689_ == 0)
{
lean_dec(v___x_2688_);
v_p_2684_ = v_p_2687_;
goto _start;
}
else
{
lean_dec(v_max_2685_);
v_p_2684_ = v_p_2687_;
v_max_2685_ = v___x_2688_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf_go___boxed(lean_object* v_x_2692_, lean_object* v_p_2693_, lean_object* v_max_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_2692_, v_p_2693_, v_max_2694_);
lean_dec_ref(v_p_2693_);
lean_dec(v_x_2692_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf(lean_object* v_p_2696_, lean_object* v_x_2697_){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_unsigned_to_nat(0u);
v___x_2699_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_2697_, v_p_2696_, v___x_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf___boxed(lean_object* v_p_2700_, lean_object* v_x_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_2700_, v_x_2701_);
lean_dec(v_x_2701_);
lean_dec_ref(v_p_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(lean_object* v_x_2703_, lean_object* v_h__1_2704_, lean_object* v_h__2_2705_, lean_object* v_h__3_2706_, lean_object* v_h__4_2707_, lean_object* v_h__5_2708_, lean_object* v_h__6_2709_, lean_object* v_h__7_2710_, lean_object* v_h__8_2711_, lean_object* v_h__9_2712_){
_start:
{
switch(lean_obj_tag(v_x_2703_))
{
case 0:
{
lean_object* v_k_2713_; lean_object* v___x_2714_; 
lean_dec(v_h__9_2712_);
lean_dec(v_h__8_2711_);
lean_dec(v_h__7_2710_);
lean_dec(v_h__6_2709_);
lean_dec(v_h__5_2708_);
lean_dec(v_h__4_2707_);
lean_dec(v_h__3_2706_);
lean_dec(v_h__2_2705_);
v_k_2713_ = lean_ctor_get(v_x_2703_, 0);
lean_inc(v_k_2713_);
lean_dec_ref_known(v_x_2703_, 1);
v___x_2714_ = lean_apply_1(v_h__1_2704_, v_k_2713_);
return v___x_2714_;
}
case 1:
{
lean_object* v_k_2715_; lean_object* v___x_2716_; 
lean_dec(v_h__9_2712_);
lean_dec(v_h__8_2711_);
lean_dec(v_h__7_2710_);
lean_dec(v_h__6_2709_);
lean_dec(v_h__5_2708_);
lean_dec(v_h__4_2707_);
lean_dec(v_h__2_2705_);
lean_dec(v_h__1_2704_);
v_k_2715_ = lean_ctor_get(v_x_2703_, 0);
lean_inc(v_k_2715_);
lean_dec_ref_known(v_x_2703_, 1);
v___x_2716_ = lean_apply_1(v_h__3_2706_, v_k_2715_);
return v___x_2716_;
}
case 2:
{
lean_object* v_k_2717_; lean_object* v___x_2718_; 
lean_dec(v_h__9_2712_);
lean_dec(v_h__8_2711_);
lean_dec(v_h__7_2710_);
lean_dec(v_h__6_2709_);
lean_dec(v_h__5_2708_);
lean_dec(v_h__4_2707_);
lean_dec(v_h__3_2706_);
lean_dec(v_h__1_2704_);
v_k_2717_ = lean_ctor_get(v_x_2703_, 0);
lean_inc(v_k_2717_);
lean_dec_ref_known(v_x_2703_, 1);
v___x_2718_ = lean_apply_1(v_h__2_2705_, v_k_2717_);
return v___x_2718_;
}
case 3:
{
lean_object* v_i_2719_; lean_object* v___x_2720_; 
lean_dec(v_h__9_2712_);
lean_dec(v_h__8_2711_);
lean_dec(v_h__7_2710_);
lean_dec(v_h__6_2709_);
lean_dec(v_h__5_2708_);
lean_dec(v_h__3_2706_);
lean_dec(v_h__2_2705_);
lean_dec(v_h__1_2704_);
v_i_2719_ = lean_ctor_get(v_x_2703_, 0);
lean_inc(v_i_2719_);
lean_dec_ref_known(v_x_2703_, 1);
v___x_2720_ = lean_apply_1(v_h__4_2707_, v_i_2719_);
return v___x_2720_;
}
case 4:
{
lean_object* v_a_2721_; lean_object* v___x_2722_; 
lean_dec(v_h__9_2712_);
lean_dec(v_h__8_2711_);
lean_dec(v_h__6_2709_);
lean_dec(v_h__5_2708_);
lean_dec(v_h__4_2707_);
lean_dec(v_h__3_2706_);
lean_dec(v_h__2_2705_);
lean_dec(v_h__1_2704_);
v_a_2721_ = lean_ctor_get(v_x_2703_, 0);
lean_inc_ref(v_a_2721_);
lean_dec_ref_known(v_x_2703_, 1);
v___x_2722_ = lean_apply_1(v_h__7_2710_, v_a_2721_);
return v___x_2722_;
}
case 5:
{
lean_object* v_a_2723_; lean_object* v_b_2724_; lean_object* v___x_2725_; 
lean_dec(v_h__9_2712_);
lean_dec(v_h__8_2711_);
lean_dec(v_h__7_2710_);
lean_dec(v_h__6_2709_);
lean_dec(v_h__4_2707_);
lean_dec(v_h__3_2706_);
lean_dec(v_h__2_2705_);
lean_dec(v_h__1_2704_);
v_a_2723_ = lean_ctor_get(v_x_2703_, 0);
lean_inc_ref(v_a_2723_);
v_b_2724_ = lean_ctor_get(v_x_2703_, 1);
lean_inc_ref(v_b_2724_);
lean_dec_ref_known(v_x_2703_, 2);
v___x_2725_ = lean_apply_2(v_h__5_2708_, v_a_2723_, v_b_2724_);
return v___x_2725_;
}
case 6:
{
lean_object* v_a_2726_; lean_object* v_b_2727_; lean_object* v___x_2728_; 
lean_dec(v_h__9_2712_);
lean_dec(v_h__7_2710_);
lean_dec(v_h__6_2709_);
lean_dec(v_h__5_2708_);
lean_dec(v_h__4_2707_);
lean_dec(v_h__3_2706_);
lean_dec(v_h__2_2705_);
lean_dec(v_h__1_2704_);
v_a_2726_ = lean_ctor_get(v_x_2703_, 0);
lean_inc_ref(v_a_2726_);
v_b_2727_ = lean_ctor_get(v_x_2703_, 1);
lean_inc_ref(v_b_2727_);
lean_dec_ref_known(v_x_2703_, 2);
v___x_2728_ = lean_apply_2(v_h__8_2711_, v_a_2726_, v_b_2727_);
return v___x_2728_;
}
case 7:
{
lean_object* v_a_2729_; lean_object* v_b_2730_; lean_object* v___x_2731_; 
lean_dec(v_h__9_2712_);
lean_dec(v_h__8_2711_);
lean_dec(v_h__7_2710_);
lean_dec(v_h__5_2708_);
lean_dec(v_h__4_2707_);
lean_dec(v_h__3_2706_);
lean_dec(v_h__2_2705_);
lean_dec(v_h__1_2704_);
v_a_2729_ = lean_ctor_get(v_x_2703_, 0);
lean_inc_ref(v_a_2729_);
v_b_2730_ = lean_ctor_get(v_x_2703_, 1);
lean_inc_ref(v_b_2730_);
lean_dec_ref_known(v_x_2703_, 2);
v___x_2731_ = lean_apply_2(v_h__6_2709_, v_a_2729_, v_b_2730_);
return v___x_2731_;
}
default: 
{
lean_object* v_a_2732_; lean_object* v_k_2733_; lean_object* v___x_2734_; 
lean_dec(v_h__8_2711_);
lean_dec(v_h__7_2710_);
lean_dec(v_h__6_2709_);
lean_dec(v_h__5_2708_);
lean_dec(v_h__4_2707_);
lean_dec(v_h__3_2706_);
lean_dec(v_h__2_2705_);
lean_dec(v_h__1_2704_);
v_a_2732_ = lean_ctor_get(v_x_2703_, 0);
lean_inc_ref(v_a_2732_);
v_k_2733_ = lean_ctor_get(v_x_2703_, 1);
lean_inc(v_k_2733_);
lean_dec_ref_known(v_x_2703_, 2);
v___x_2734_ = lean_apply_2(v_h__9_2712_, v_a_2732_, v_k_2733_);
return v___x_2734_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter(lean_object* v_motive_2735_, lean_object* v_x_2736_, lean_object* v_h__1_2737_, lean_object* v_h__2_2738_, lean_object* v_h__3_2739_, lean_object* v_h__4_2740_, lean_object* v_h__5_2741_, lean_object* v_h__6_2742_, lean_object* v_h__7_2743_, lean_object* v_h__8_2744_, lean_object* v_h__9_2745_){
_start:
{
switch(lean_obj_tag(v_x_2736_))
{
case 0:
{
lean_object* v_k_2746_; lean_object* v___x_2747_; 
lean_dec(v_h__9_2745_);
lean_dec(v_h__8_2744_);
lean_dec(v_h__7_2743_);
lean_dec(v_h__6_2742_);
lean_dec(v_h__5_2741_);
lean_dec(v_h__4_2740_);
lean_dec(v_h__3_2739_);
lean_dec(v_h__2_2738_);
v_k_2746_ = lean_ctor_get(v_x_2736_, 0);
lean_inc(v_k_2746_);
lean_dec_ref_known(v_x_2736_, 1);
v___x_2747_ = lean_apply_1(v_h__1_2737_, v_k_2746_);
return v___x_2747_;
}
case 1:
{
lean_object* v_k_2748_; lean_object* v___x_2749_; 
lean_dec(v_h__9_2745_);
lean_dec(v_h__8_2744_);
lean_dec(v_h__7_2743_);
lean_dec(v_h__6_2742_);
lean_dec(v_h__5_2741_);
lean_dec(v_h__4_2740_);
lean_dec(v_h__2_2738_);
lean_dec(v_h__1_2737_);
v_k_2748_ = lean_ctor_get(v_x_2736_, 0);
lean_inc(v_k_2748_);
lean_dec_ref_known(v_x_2736_, 1);
v___x_2749_ = lean_apply_1(v_h__3_2739_, v_k_2748_);
return v___x_2749_;
}
case 2:
{
lean_object* v_k_2750_; lean_object* v___x_2751_; 
lean_dec(v_h__9_2745_);
lean_dec(v_h__8_2744_);
lean_dec(v_h__7_2743_);
lean_dec(v_h__6_2742_);
lean_dec(v_h__5_2741_);
lean_dec(v_h__4_2740_);
lean_dec(v_h__3_2739_);
lean_dec(v_h__1_2737_);
v_k_2750_ = lean_ctor_get(v_x_2736_, 0);
lean_inc(v_k_2750_);
lean_dec_ref_known(v_x_2736_, 1);
v___x_2751_ = lean_apply_1(v_h__2_2738_, v_k_2750_);
return v___x_2751_;
}
case 3:
{
lean_object* v_i_2752_; lean_object* v___x_2753_; 
lean_dec(v_h__9_2745_);
lean_dec(v_h__8_2744_);
lean_dec(v_h__7_2743_);
lean_dec(v_h__6_2742_);
lean_dec(v_h__5_2741_);
lean_dec(v_h__3_2739_);
lean_dec(v_h__2_2738_);
lean_dec(v_h__1_2737_);
v_i_2752_ = lean_ctor_get(v_x_2736_, 0);
lean_inc(v_i_2752_);
lean_dec_ref_known(v_x_2736_, 1);
v___x_2753_ = lean_apply_1(v_h__4_2740_, v_i_2752_);
return v___x_2753_;
}
case 4:
{
lean_object* v_a_2754_; lean_object* v___x_2755_; 
lean_dec(v_h__9_2745_);
lean_dec(v_h__8_2744_);
lean_dec(v_h__6_2742_);
lean_dec(v_h__5_2741_);
lean_dec(v_h__4_2740_);
lean_dec(v_h__3_2739_);
lean_dec(v_h__2_2738_);
lean_dec(v_h__1_2737_);
v_a_2754_ = lean_ctor_get(v_x_2736_, 0);
lean_inc_ref(v_a_2754_);
lean_dec_ref_known(v_x_2736_, 1);
v___x_2755_ = lean_apply_1(v_h__7_2743_, v_a_2754_);
return v___x_2755_;
}
case 5:
{
lean_object* v_a_2756_; lean_object* v_b_2757_; lean_object* v___x_2758_; 
lean_dec(v_h__9_2745_);
lean_dec(v_h__8_2744_);
lean_dec(v_h__7_2743_);
lean_dec(v_h__6_2742_);
lean_dec(v_h__4_2740_);
lean_dec(v_h__3_2739_);
lean_dec(v_h__2_2738_);
lean_dec(v_h__1_2737_);
v_a_2756_ = lean_ctor_get(v_x_2736_, 0);
lean_inc_ref(v_a_2756_);
v_b_2757_ = lean_ctor_get(v_x_2736_, 1);
lean_inc_ref(v_b_2757_);
lean_dec_ref_known(v_x_2736_, 2);
v___x_2758_ = lean_apply_2(v_h__5_2741_, v_a_2756_, v_b_2757_);
return v___x_2758_;
}
case 6:
{
lean_object* v_a_2759_; lean_object* v_b_2760_; lean_object* v___x_2761_; 
lean_dec(v_h__9_2745_);
lean_dec(v_h__7_2743_);
lean_dec(v_h__6_2742_);
lean_dec(v_h__5_2741_);
lean_dec(v_h__4_2740_);
lean_dec(v_h__3_2739_);
lean_dec(v_h__2_2738_);
lean_dec(v_h__1_2737_);
v_a_2759_ = lean_ctor_get(v_x_2736_, 0);
lean_inc_ref(v_a_2759_);
v_b_2760_ = lean_ctor_get(v_x_2736_, 1);
lean_inc_ref(v_b_2760_);
lean_dec_ref_known(v_x_2736_, 2);
v___x_2761_ = lean_apply_2(v_h__8_2744_, v_a_2759_, v_b_2760_);
return v___x_2761_;
}
case 7:
{
lean_object* v_a_2762_; lean_object* v_b_2763_; lean_object* v___x_2764_; 
lean_dec(v_h__9_2745_);
lean_dec(v_h__8_2744_);
lean_dec(v_h__7_2743_);
lean_dec(v_h__5_2741_);
lean_dec(v_h__4_2740_);
lean_dec(v_h__3_2739_);
lean_dec(v_h__2_2738_);
lean_dec(v_h__1_2737_);
v_a_2762_ = lean_ctor_get(v_x_2736_, 0);
lean_inc_ref(v_a_2762_);
v_b_2763_ = lean_ctor_get(v_x_2736_, 1);
lean_inc_ref(v_b_2763_);
lean_dec_ref_known(v_x_2736_, 2);
v___x_2764_ = lean_apply_2(v_h__6_2742_, v_a_2762_, v_b_2763_);
return v___x_2764_;
}
default: 
{
lean_object* v_a_2765_; lean_object* v_k_2766_; lean_object* v___x_2767_; 
lean_dec(v_h__8_2744_);
lean_dec(v_h__7_2743_);
lean_dec(v_h__6_2742_);
lean_dec(v_h__5_2741_);
lean_dec(v_h__4_2740_);
lean_dec(v_h__3_2739_);
lean_dec(v_h__2_2738_);
lean_dec(v_h__1_2737_);
v_a_2765_ = lean_ctor_get(v_x_2736_, 0);
lean_inc_ref(v_a_2765_);
v_k_2766_ = lean_ctor_get(v_x_2736_, 1);
lean_inc(v_k_2766_);
lean_dec_ref_known(v_x_2736_, 2);
v___x_2767_ = lean_apply_2(v_h__9_2745_, v_a_2765_, v_k_2766_);
return v___x_2767_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter___redArg(lean_object* v_a_2768_, lean_object* v_h__1_2769_, lean_object* v_h__2_2770_, lean_object* v_h__3_2771_, lean_object* v_h__4_2772_, lean_object* v_h__5_2773_){
_start:
{
switch(lean_obj_tag(v_a_2768_))
{
case 0:
{
lean_object* v_k_2774_; lean_object* v___x_2775_; 
lean_dec(v_h__5_2773_);
lean_dec(v_h__4_2772_);
lean_dec(v_h__3_2771_);
lean_dec(v_h__2_2770_);
v_k_2774_ = lean_ctor_get(v_a_2768_, 0);
lean_inc(v_k_2774_);
lean_dec_ref_known(v_a_2768_, 1);
v___x_2775_ = lean_apply_1(v_h__1_2769_, v_k_2774_);
return v___x_2775_;
}
case 2:
{
lean_object* v_k_2776_; lean_object* v___x_2777_; 
lean_dec(v_h__5_2773_);
lean_dec(v_h__4_2772_);
lean_dec(v_h__3_2771_);
lean_dec(v_h__1_2769_);
v_k_2776_ = lean_ctor_get(v_a_2768_, 0);
lean_inc(v_k_2776_);
lean_dec_ref_known(v_a_2768_, 1);
v___x_2777_ = lean_apply_1(v_h__2_2770_, v_k_2776_);
return v___x_2777_;
}
case 1:
{
lean_object* v_k_2778_; lean_object* v___x_2779_; 
lean_dec(v_h__5_2773_);
lean_dec(v_h__4_2772_);
lean_dec(v_h__2_2770_);
lean_dec(v_h__1_2769_);
v_k_2778_ = lean_ctor_get(v_a_2768_, 0);
lean_inc(v_k_2778_);
lean_dec_ref_known(v_a_2768_, 1);
v___x_2779_ = lean_apply_1(v_h__3_2771_, v_k_2778_);
return v___x_2779_;
}
case 3:
{
lean_object* v_i_2780_; lean_object* v___x_2781_; 
lean_dec(v_h__5_2773_);
lean_dec(v_h__3_2771_);
lean_dec(v_h__2_2770_);
lean_dec(v_h__1_2769_);
v_i_2780_ = lean_ctor_get(v_a_2768_, 0);
lean_inc(v_i_2780_);
lean_dec_ref_known(v_a_2768_, 1);
v___x_2781_ = lean_apply_1(v_h__4_2772_, v_i_2780_);
return v___x_2781_;
}
default: 
{
lean_object* v___x_2782_; 
lean_dec(v_h__4_2772_);
lean_dec(v_h__3_2771_);
lean_dec(v_h__2_2770_);
lean_dec(v_h__1_2769_);
v___x_2782_ = lean_apply_5(v_h__5_2773_, v_a_2768_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2782_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter(lean_object* v_motive_2783_, lean_object* v_a_2784_, lean_object* v_h__1_2785_, lean_object* v_h__2_2786_, lean_object* v_h__3_2787_, lean_object* v_h__4_2788_, lean_object* v_h__5_2789_){
_start:
{
switch(lean_obj_tag(v_a_2784_))
{
case 0:
{
lean_object* v_k_2790_; lean_object* v___x_2791_; 
lean_dec(v_h__5_2789_);
lean_dec(v_h__4_2788_);
lean_dec(v_h__3_2787_);
lean_dec(v_h__2_2786_);
v_k_2790_ = lean_ctor_get(v_a_2784_, 0);
lean_inc(v_k_2790_);
lean_dec_ref_known(v_a_2784_, 1);
v___x_2791_ = lean_apply_1(v_h__1_2785_, v_k_2790_);
return v___x_2791_;
}
case 2:
{
lean_object* v_k_2792_; lean_object* v___x_2793_; 
lean_dec(v_h__5_2789_);
lean_dec(v_h__4_2788_);
lean_dec(v_h__3_2787_);
lean_dec(v_h__1_2785_);
v_k_2792_ = lean_ctor_get(v_a_2784_, 0);
lean_inc(v_k_2792_);
lean_dec_ref_known(v_a_2784_, 1);
v___x_2793_ = lean_apply_1(v_h__2_2786_, v_k_2792_);
return v___x_2793_;
}
case 1:
{
lean_object* v_k_2794_; lean_object* v___x_2795_; 
lean_dec(v_h__5_2789_);
lean_dec(v_h__4_2788_);
lean_dec(v_h__2_2786_);
lean_dec(v_h__1_2785_);
v_k_2794_ = lean_ctor_get(v_a_2784_, 0);
lean_inc(v_k_2794_);
lean_dec_ref_known(v_a_2784_, 1);
v___x_2795_ = lean_apply_1(v_h__3_2787_, v_k_2794_);
return v___x_2795_;
}
case 3:
{
lean_object* v_i_2796_; lean_object* v___x_2797_; 
lean_dec(v_h__5_2789_);
lean_dec(v_h__3_2787_);
lean_dec(v_h__2_2786_);
lean_dec(v_h__1_2785_);
v_i_2796_ = lean_ctor_get(v_a_2784_, 0);
lean_inc(v_i_2796_);
lean_dec_ref_known(v_a_2784_, 1);
v___x_2797_ = lean_apply_1(v_h__4_2788_, v_i_2796_);
return v___x_2797_;
}
default: 
{
lean_object* v___x_2798_; 
lean_dec(v_h__4_2788_);
lean_dec(v_h__3_2787_);
lean_dec(v_h__2_2786_);
lean_dec(v_h__1_2785_);
v___x_2798_ = lean_apply_5(v_h__5_2789_, v_a_2784_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly__nc(lean_object* v_x_2799_){
_start:
{
switch(lean_obj_tag(v_x_2799_))
{
case 0:
{
lean_object* v_k_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
v_k_2800_ = lean_ctor_get(v_x_2799_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_x_2799_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v_x_2799_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_k_2800_);
lean_dec(v_x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_k_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
case 1:
{
lean_object* v_k_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2816_; 
v_k_2808_ = lean_ctor_get(v_x_2799_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_x_2799_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2810_ = v_x_2799_;
v_isShared_2811_ = v_isSharedCheck_2816_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_k_2808_);
lean_dec(v_x_2799_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2816_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2812_ = lean_nat_to_int(v_k_2808_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set_tag(v___x_2810_, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2812_);
v___x_2814_ = v___x_2810_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
case 2:
{
lean_object* v_k_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
v_k_2817_ = lean_ctor_get(v_x_2799_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_x_2799_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v_x_2799_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_k_2817_);
lean_dec(v_x_2799_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set_tag(v___x_2819_, 0);
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_k_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
case 3:
{
lean_object* v_i_2825_; lean_object* v___x_2826_; 
v_i_2825_ = lean_ctor_get(v_x_2799_, 0);
lean_inc(v_i_2825_);
lean_dec_ref_known(v_x_2799_, 1);
v___x_2826_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2825_);
return v___x_2826_;
}
case 4:
{
lean_object* v_a_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v_a_2827_ = lean_ctor_get(v_x_2799_, 0);
lean_inc_ref(v_a_2827_);
lean_dec_ref_known(v_x_2799_, 1);
v___x_2828_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2829_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2827_);
v___x_2830_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2828_, v___x_2829_);
return v___x_2830_;
}
case 5:
{
lean_object* v_a_2831_; lean_object* v_b_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v_a_2831_ = lean_ctor_get(v_x_2799_, 0);
lean_inc_ref(v_a_2831_);
v_b_2832_ = lean_ctor_get(v_x_2799_, 1);
lean_inc_ref(v_b_2832_);
lean_dec_ref_known(v_x_2799_, 2);
v___x_2833_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2831_);
v___x_2834_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2832_);
v___x_2835_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2833_, v___x_2834_);
return v___x_2835_;
}
case 6:
{
lean_object* v_a_2836_; lean_object* v_b_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v_a_2836_ = lean_ctor_get(v_x_2799_, 0);
lean_inc_ref(v_a_2836_);
v_b_2837_ = lean_ctor_get(v_x_2799_, 1);
lean_inc_ref(v_b_2837_);
lean_dec_ref_known(v_x_2799_, 2);
v___x_2838_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2836_);
v___x_2839_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2840_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2837_);
v___x_2841_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2839_, v___x_2840_);
v___x_2842_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2838_, v___x_2841_);
return v___x_2842_;
}
case 7:
{
lean_object* v_a_2843_; lean_object* v_b_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_a_2843_ = lean_ctor_get(v_x_2799_, 0);
lean_inc_ref(v_a_2843_);
v_b_2844_ = lean_ctor_get(v_x_2799_, 1);
lean_inc_ref(v_b_2844_);
lean_dec_ref_known(v_x_2799_, 2);
v___x_2845_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2843_);
v___x_2846_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2844_);
v___x_2847_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2845_, v___x_2846_);
return v___x_2847_;
}
default: 
{
lean_object* v_a_2848_; lean_object* v_k_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2881_; 
v_a_2848_ = lean_ctor_get(v_x_2799_, 0);
v_k_2849_ = lean_ctor_get(v_x_2799_, 1);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_x_2799_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2851_ = v_x_2799_;
v_isShared_2852_ = v_isSharedCheck_2881_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_k_2849_);
lean_inc(v_a_2848_);
lean_dec(v_x_2799_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2881_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v_n_2854_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2857_ = lean_unsigned_to_nat(0u);
v___x_2858_ = lean_nat_dec_eq(v_k_2849_, v___x_2857_);
if (v___x_2858_ == 0)
{
switch(lean_obj_tag(v_a_2848_))
{
case 0:
{
lean_object* v_k_2859_; 
lean_del_object(v___x_2851_);
v_k_2859_ = lean_ctor_get(v_a_2848_, 0);
lean_inc(v_k_2859_);
lean_dec_ref_known(v_a_2848_, 1);
v_n_2854_ = v_k_2859_;
goto v___jp_2853_;
}
case 2:
{
lean_object* v_k_2860_; 
lean_del_object(v___x_2851_);
v_k_2860_ = lean_ctor_get(v_a_2848_, 0);
lean_inc(v_k_2860_);
lean_dec_ref_known(v_a_2848_, 1);
v_n_2854_ = v_k_2860_;
goto v___jp_2853_;
}
case 1:
{
lean_object* v_k_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2870_; 
lean_del_object(v___x_2851_);
v_k_2861_ = lean_ctor_get(v_a_2848_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_a_2848_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2863_ = v_a_2848_;
v_isShared_2864_ = v_isSharedCheck_2870_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_k_2861_);
lean_dec(v_a_2848_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2870_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
v___x_2865_ = lean_nat_to_int(v_k_2861_);
v___x_2866_ = l_Int_pow(v___x_2865_, v_k_2849_);
lean_dec(v_k_2849_);
lean_dec(v___x_2865_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set_tag(v___x_2863_, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2866_);
v___x_2868_ = v___x_2863_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
case 3:
{
lean_object* v_i_2871_; lean_object* v___x_2873_; 
v_i_2871_ = lean_ctor_get(v_a_2848_, 0);
lean_inc(v_i_2871_);
lean_dec_ref_known(v_a_2848_, 1);
if (v_isShared_2852_ == 0)
{
lean_ctor_set_tag(v___x_2851_, 0);
lean_ctor_set(v___x_2851_, 0, v_i_2871_);
v___x_2873_ = v___x_2851_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_i_2871_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_k_2849_);
v___x_2873_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2874_ = lean_box(0);
v___x_2875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2873_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2875_);
return v___x_2876_;
}
}
default: 
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
lean_del_object(v___x_2851_);
v___x_2878_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2848_);
v___x_2879_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_2878_, v_k_2849_);
lean_dec(v_k_2849_);
return v___x_2879_;
}
}
}
else
{
lean_object* v___x_2880_; 
lean_del_object(v___x_2851_);
lean_dec(v_k_2849_);
lean_dec_ref(v_a_2848_);
v___x_2880_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2880_;
}
v___jp_2853_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = l_Int_pow(v_n_2854_, v_k_2849_);
lean_dec(v_k_2849_);
lean_dec(v_n_2854_);
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
return v___x_2856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_normEq0(lean_object* v_p_2882_, lean_object* v_c_2883_){
_start:
{
if (lean_obj_tag(v_p_2882_) == 0)
{
lean_object* v_k_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; 
v_k_2884_ = lean_ctor_get(v_p_2882_, 0);
v___x_2885_ = lean_nat_to_int(v_c_2883_);
v___x_2886_ = lean_int_emod(v_k_2884_, v___x_2885_);
lean_dec(v___x_2885_);
v___x_2887_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2888_ = lean_int_dec_eq(v___x_2886_, v___x_2887_);
lean_dec(v___x_2886_);
if (v___x_2888_ == 0)
{
return v_p_2882_;
}
else
{
lean_object* v___x_2889_; 
lean_dec_ref_known(v_p_2882_, 1);
v___x_2889_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2889_;
}
}
else
{
lean_object* v_k_2890_; lean_object* v_v_2891_; lean_object* v_p_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2905_; 
v_k_2890_ = lean_ctor_get(v_p_2882_, 0);
v_v_2891_ = lean_ctor_get(v_p_2882_, 1);
v_p_2892_ = lean_ctor_get(v_p_2882_, 2);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_p_2882_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2894_ = v_p_2882_;
v_isShared_2895_ = v_isSharedCheck_2905_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_p_2892_);
lean_inc(v_v_2891_);
lean_inc(v_k_2890_);
lean_dec(v_p_2882_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2905_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
lean_inc(v_c_2883_);
v___x_2896_ = lean_nat_to_int(v_c_2883_);
v___x_2897_ = lean_int_emod(v_k_2890_, v___x_2896_);
lean_dec(v___x_2896_);
v___x_2898_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2899_ = lean_int_dec_eq(v___x_2897_, v___x_2898_);
lean_dec(v___x_2897_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; lean_object* v___x_2902_; 
v___x_2900_ = l_Lean_Grind_CommRing_Poly_normEq0(v_p_2892_, v_c_2883_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 2, v___x_2900_);
v___x_2902_ = v___x_2894_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_k_2890_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_v_2891_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
else
{
lean_del_object(v___x_2894_);
lean_dec(v_v_2891_);
lean_dec(v_k_2890_);
v_p_2882_ = v_p_2892_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object* v_p_2906_, lean_object* v_k_2907_, lean_object* v_c_2908_){
_start:
{
if (lean_obj_tag(v_p_2906_) == 0)
{
lean_object* v_k_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2919_; 
v_k_2909_ = lean_ctor_get(v_p_2906_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_p_2906_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2911_ = v_p_2906_;
v_isShared_2912_ = v_isSharedCheck_2919_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_k_2909_);
lean_dec(v_p_2906_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2919_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2913_ = lean_int_add(v_k_2909_, v_k_2907_);
lean_dec(v_k_2909_);
v___x_2914_ = lean_nat_to_int(v_c_2908_);
v___x_2915_ = lean_int_emod(v___x_2913_, v___x_2914_);
lean_dec(v___x_2914_);
lean_dec(v___x_2913_);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v___x_2915_);
v___x_2917_ = v___x_2911_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
else
{
lean_object* v_k_2920_; lean_object* v_v_2921_; lean_object* v_p_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2930_; 
v_k_2920_ = lean_ctor_get(v_p_2906_, 0);
v_v_2921_ = lean_ctor_get(v_p_2906_, 1);
v_p_2922_ = lean_ctor_get(v_p_2906_, 2);
v_isSharedCheck_2930_ = !lean_is_exclusive(v_p_2906_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2924_ = v_p_2906_;
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_p_2922_);
lean_inc(v_v_2921_);
lean_inc(v_k_2920_);
lean_dec(v_p_2906_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2926_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2922_, v_k_2907_, v_c_2908_);
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
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_k_2920_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_v_2921_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC___boxed(lean_object* v_p_2931_, lean_object* v_k_2932_, lean_object* v_c_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2931_, v_k_2932_, v_c_2933_);
lean_dec(v_k_2932_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC_go(lean_object* v_m_2935_, lean_object* v_c_2936_, lean_object* v_k_2937_, lean_object* v_a_2938_){
_start:
{
if (lean_obj_tag(v_a_2938_) == 0)
{
lean_object* v___x_2939_; 
lean_dec(v_c_2936_);
v___x_2939_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2939_, 0, v_k_2937_);
lean_ctor_set(v___x_2939_, 1, v_m_2935_);
lean_ctor_set(v___x_2939_, 2, v_a_2938_);
return v___x_2939_;
}
else
{
lean_object* v_k_2940_; lean_object* v_v_2941_; lean_object* v_p_2942_; uint8_t v___x_2943_; 
v_k_2940_ = lean_ctor_get(v_a_2938_, 0);
v_v_2941_ = lean_ctor_get(v_a_2938_, 1);
v_p_2942_ = lean_ctor_get(v_a_2938_, 2);
v___x_2943_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2935_, v_v_2941_);
switch(v___x_2943_)
{
case 0:
{
lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2951_; 
lean_inc_ref(v_p_2942_);
lean_inc(v_v_2941_);
lean_inc(v_k_2940_);
v_isSharedCheck_2951_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_2951_ == 0)
{
lean_object* v_unused_2952_; lean_object* v_unused_2953_; lean_object* v_unused_2954_; 
v_unused_2952_ = lean_ctor_get(v_a_2938_, 2);
lean_dec(v_unused_2952_);
v_unused_2953_ = lean_ctor_get(v_a_2938_, 1);
lean_dec(v_unused_2953_);
v_unused_2954_ = lean_ctor_get(v_a_2938_, 0);
lean_dec(v_unused_2954_);
v___x_2945_ = v_a_2938_;
v_isShared_2946_ = v_isSharedCheck_2951_;
goto v_resetjp_2944_;
}
else
{
lean_dec(v_a_2938_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2951_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2947_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_2935_, v_c_2936_, v_k_2937_, v_p_2942_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 2, v___x_2947_);
v___x_2949_ = v___x_2945_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_k_2940_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_v_2941_);
lean_ctor_set(v_reuseFailAlloc_2950_, 2, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
case 1:
{
lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2966_; 
lean_inc_ref(v_p_2942_);
lean_inc(v_k_2940_);
v_isSharedCheck_2966_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_2966_ == 0)
{
lean_object* v_unused_2967_; lean_object* v_unused_2968_; lean_object* v_unused_2969_; 
v_unused_2967_ = lean_ctor_get(v_a_2938_, 2);
lean_dec(v_unused_2967_);
v_unused_2968_ = lean_ctor_get(v_a_2938_, 1);
lean_dec(v_unused_2968_);
v_unused_2969_ = lean_ctor_get(v_a_2938_, 0);
lean_dec(v_unused_2969_);
v___x_2956_ = v_a_2938_;
v_isShared_2957_ = v_isSharedCheck_2966_;
goto v_resetjp_2955_;
}
else
{
lean_dec(v_a_2938_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2966_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v_k_x27_x27_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2958_ = lean_int_add(v_k_2937_, v_k_2940_);
lean_dec(v_k_2940_);
lean_dec(v_k_2937_);
v___x_2959_ = lean_nat_to_int(v_c_2936_);
v_k_x27_x27_2960_ = lean_int_emod(v___x_2958_, v___x_2959_);
lean_dec(v___x_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2962_ = lean_int_dec_eq(v_k_x27_x27_2960_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2964_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v_m_2935_);
lean_ctor_set(v___x_2956_, 0, v_k_x27_x27_2960_);
v___x_2964_ = v___x_2956_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_k_x27_x27_2960_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_m_2935_);
lean_ctor_set(v_reuseFailAlloc_2965_, 2, v_p_2942_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
else
{
lean_dec(v_k_x27_x27_2960_);
lean_del_object(v___x_2956_);
lean_dec(v_m_2935_);
return v_p_2942_;
}
}
}
default: 
{
lean_object* v___x_2970_; 
lean_dec(v_c_2936_);
v___x_2970_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2970_, 0, v_k_2937_);
lean_ctor_set(v___x_2970_, 1, v_m_2935_);
lean_ctor_set(v___x_2970_, 2, v_a_2938_);
return v___x_2970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC(lean_object* v_k_2971_, lean_object* v_m_2972_, lean_object* v_p_2973_, lean_object* v_c_2974_){
_start:
{
lean_object* v___x_2975_; lean_object* v_k_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
lean_inc(v_c_2974_);
v___x_2975_ = lean_nat_to_int(v_c_2974_);
v_k_2976_ = lean_int_emod(v_k_2971_, v___x_2975_);
lean_dec(v___x_2975_);
v___x_2977_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2978_ = lean_int_dec_eq(v_k_2976_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_2972_, v_c_2974_, v_k_2976_, v_p_2973_);
return v___x_2979_;
}
else
{
lean_dec(v_k_2976_);
lean_dec(v_c_2974_);
lean_dec(v_m_2972_);
return v_p_2973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC___boxed(lean_object* v_k_2980_, lean_object* v_m_2981_, lean_object* v_p_2982_, lean_object* v_c_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lean_Grind_CommRing_Poly_insertC(v_k_2980_, v_m_2981_, v_p_2982_, v_c_2983_);
lean_dec(v_k_2980_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go(lean_object* v_k_2985_, lean_object* v_c_2986_, lean_object* v_a_2987_){
_start:
{
if (lean_obj_tag(v_a_2987_) == 0)
{
lean_object* v_k_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2998_; 
v_k_2988_ = lean_ctor_get(v_a_2987_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_a_2987_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2990_ = v_a_2987_;
v_isShared_2991_ = v_isSharedCheck_2998_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_k_2988_);
lean_dec(v_a_2987_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2998_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2996_; 
v___x_2992_ = lean_int_mul(v_k_2985_, v_k_2988_);
lean_dec(v_k_2988_);
v___x_2993_ = lean_nat_to_int(v_c_2986_);
v___x_2994_ = lean_int_emod(v___x_2992_, v___x_2993_);
lean_dec(v___x_2993_);
lean_dec(v___x_2992_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v___x_2994_);
v___x_2996_ = v___x_2990_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2994_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
else
{
lean_object* v_k_2999_; lean_object* v_v_3000_; lean_object* v_p_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3015_; 
v_k_2999_ = lean_ctor_get(v_a_2987_, 0);
v_v_3000_ = lean_ctor_get(v_a_2987_, 1);
v_p_3001_ = lean_ctor_get(v_a_2987_, 2);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_a_2987_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3003_ = v_a_2987_;
v_isShared_3004_ = v_isSharedCheck_3015_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_p_3001_);
lean_inc(v_v_3000_);
lean_inc(v_k_2999_);
lean_dec(v_a_2987_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3015_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v_k_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3005_ = lean_int_mul(v_k_2985_, v_k_2999_);
lean_dec(v_k_2999_);
lean_inc(v_c_2986_);
v___x_3006_ = lean_nat_to_int(v_c_2986_);
v_k_3007_ = lean_int_emod(v___x_3005_, v___x_3006_);
lean_dec(v___x_3006_);
lean_dec(v___x_3005_);
v___x_3008_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3009_ = lean_int_dec_eq(v_k_3007_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
v___x_3010_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_2985_, v_c_2986_, v_p_3001_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 2, v___x_3010_);
lean_ctor_set(v___x_3003_, 0, v_k_3007_);
v___x_3012_ = v___x_3003_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_k_3007_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_v_3000_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
else
{
lean_dec(v_k_3007_);
lean_del_object(v___x_3003_);
lean_dec(v_v_3000_);
v_a_2987_ = v_p_3001_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go___boxed(lean_object* v_k_3016_, lean_object* v_c_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_3016_, v_c_3017_, v_a_3018_);
lean_dec(v_k_3016_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object* v_k_3020_, lean_object* v_p_3021_, lean_object* v_c_3022_){
_start:
{
lean_object* v___x_3023_; lean_object* v_k_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; 
lean_inc(v_c_3022_);
v___x_3023_ = lean_nat_to_int(v_c_3022_);
v_k_3024_ = lean_int_emod(v_k_3020_, v___x_3023_);
lean_dec(v___x_3023_);
v___x_3025_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3026_ = lean_int_dec_eq(v_k_3024_, v___x_3025_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; uint8_t v___x_3028_; 
v___x_3027_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_3028_ = lean_int_dec_eq(v_k_3024_, v___x_3027_);
lean_dec(v_k_3024_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_3020_, v_c_3022_, v_p_3021_);
return v___x_3029_;
}
else
{
lean_dec(v_c_3022_);
return v_p_3021_;
}
}
else
{
lean_object* v___x_3030_; 
lean_dec(v_k_3024_);
lean_dec(v_c_3022_);
lean_dec_ref(v_p_3021_);
v___x_3030_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC___boxed(lean_object* v_k_3031_, lean_object* v_p_3032_, lean_object* v_c_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3031_, v_p_3032_, v_c_3033_);
lean_dec(v_k_3031_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go(lean_object* v_k_3035_, lean_object* v_m_3036_, lean_object* v_c_3037_, lean_object* v_a_3038_){
_start:
{
if (lean_obj_tag(v_a_3038_) == 0)
{
lean_object* v_k_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v_k_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
v_k_3039_ = lean_ctor_get(v_a_3038_, 0);
lean_inc(v_k_3039_);
lean_dec_ref_known(v_a_3038_, 1);
v___x_3040_ = lean_int_mul(v_k_3035_, v_k_3039_);
lean_dec(v_k_3039_);
v___x_3041_ = lean_nat_to_int(v_c_3037_);
v_k_3042_ = lean_int_emod(v___x_3040_, v___x_3041_);
lean_dec(v___x_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3044_ = lean_int_dec_eq(v_k_3042_, v___x_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3046_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3046_, 0, v_k_3042_);
lean_ctor_set(v___x_3046_, 1, v_m_3036_);
lean_ctor_set(v___x_3046_, 2, v___x_3045_);
return v___x_3046_;
}
else
{
lean_object* v___x_3047_; 
lean_dec(v_k_3042_);
lean_dec(v_m_3036_);
v___x_3047_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3047_;
}
}
else
{
lean_object* v_k_3048_; lean_object* v_v_3049_; lean_object* v_p_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3065_; 
v_k_3048_ = lean_ctor_get(v_a_3038_, 0);
v_v_3049_ = lean_ctor_get(v_a_3038_, 1);
v_p_3050_ = lean_ctor_get(v_a_3038_, 2);
v_isSharedCheck_3065_ = !lean_is_exclusive(v_a_3038_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3052_ = v_a_3038_;
v_isShared_3053_ = v_isSharedCheck_3065_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_p_3050_);
lean_inc(v_v_3049_);
lean_inc(v_k_3048_);
lean_dec(v_a_3038_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3065_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v_k_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; 
v___x_3054_ = lean_int_mul(v_k_3035_, v_k_3048_);
lean_dec(v_k_3048_);
lean_inc(v_c_3037_);
v___x_3055_ = lean_nat_to_int(v_c_3037_);
v_k_3056_ = lean_int_emod(v___x_3054_, v___x_3055_);
lean_dec(v___x_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3058_ = lean_int_dec_eq(v_k_3056_, v___x_3057_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; 
lean_inc(v_m_3036_);
v___x_3059_ = l_Lean_Grind_CommRing_Mon_mul(v_m_3036_, v_v_3049_);
v___x_3060_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3035_, v_m_3036_, v_c_3037_, v_p_3050_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 2, v___x_3060_);
lean_ctor_set(v___x_3052_, 1, v___x_3059_);
lean_ctor_set(v___x_3052_, 0, v_k_3056_);
v___x_3062_ = v___x_3052_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_k_3056_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___x_3059_);
lean_ctor_set(v_reuseFailAlloc_3063_, 2, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
else
{
lean_dec(v_k_3056_);
lean_del_object(v___x_3052_);
lean_dec(v_v_3049_);
v_a_3038_ = v_p_3050_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go___boxed(lean_object* v_k_3066_, lean_object* v_m_3067_, lean_object* v_c_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3066_, v_m_3067_, v_c_3068_, v_a_3069_);
lean_dec(v_k_3066_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object* v_k_3071_, lean_object* v_m_3072_, lean_object* v_p_3073_, lean_object* v_c_3074_){
_start:
{
lean_object* v___x_3075_; lean_object* v_k_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; 
lean_inc(v_c_3074_);
v___x_3075_ = lean_nat_to_int(v_c_3074_);
v_k_3076_ = lean_int_emod(v_k_3071_, v___x_3075_);
lean_dec(v___x_3075_);
v___x_3077_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3078_ = lean_int_dec_eq(v_k_3076_, v___x_3077_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = lean_box(0);
v___x_3080_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_3072_, v___x_3079_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; 
lean_dec(v_k_3076_);
v___x_3081_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3071_, v_m_3072_, v_c_3074_, v_p_3073_);
return v___x_3081_;
}
else
{
lean_object* v___x_3082_; 
lean_dec(v_m_3072_);
v___x_3082_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3076_, v_p_3073_, v_c_3074_);
lean_dec(v_k_3076_);
return v___x_3082_;
}
}
else
{
lean_object* v___x_3083_; 
lean_dec(v_k_3076_);
lean_dec(v_c_3074_);
lean_dec_ref(v_p_3073_);
lean_dec(v_m_3072_);
v___x_3083_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC___boxed(lean_object* v_k_3084_, lean_object* v_m_3085_, lean_object* v_p_3086_, lean_object* v_c_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_3084_, v_m_3085_, v_p_3086_, v_c_3087_);
lean_dec(v_k_3084_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(lean_object* v_k_3089_, lean_object* v_m_3090_, lean_object* v_c_3091_, lean_object* v_p_3092_, lean_object* v_acc_3093_){
_start:
{
if (lean_obj_tag(v_p_3092_) == 0)
{
lean_object* v_k_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v_k_3094_ = lean_ctor_get(v_p_3092_, 0);
lean_inc(v_k_3094_);
lean_dec_ref_known(v_p_3092_, 1);
v___x_3095_ = lean_int_mul(v_k_3089_, v_k_3094_);
lean_dec(v_k_3094_);
v___x_3096_ = lean_nat_to_int(v_c_3091_);
v___x_3097_ = lean_int_emod(v___x_3095_, v___x_3096_);
lean_dec(v___x_3096_);
lean_dec(v___x_3095_);
v___x_3098_ = l_Lean_Grind_CommRing_Poly_insert(v___x_3097_, v_m_3090_, v_acc_3093_);
return v___x_3098_;
}
else
{
lean_object* v_k_3099_; lean_object* v_v_3100_; lean_object* v_p_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v_k_3099_ = lean_ctor_get(v_p_3092_, 0);
lean_inc(v_k_3099_);
v_v_3100_ = lean_ctor_get(v_p_3092_, 1);
lean_inc(v_v_3100_);
v_p_3101_ = lean_ctor_get(v_p_3092_, 2);
lean_inc_ref(v_p_3101_);
lean_dec_ref_known(v_p_3092_, 3);
v___x_3102_ = lean_int_mul(v_k_3089_, v_k_3099_);
lean_dec(v_k_3099_);
lean_inc(v_c_3091_);
v___x_3103_ = lean_nat_to_int(v_c_3091_);
v___x_3104_ = lean_int_emod(v___x_3102_, v___x_3103_);
lean_dec(v___x_3103_);
lean_dec(v___x_3102_);
lean_inc(v_m_3090_);
v___x_3105_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_3090_, v_v_3100_);
v___x_3106_ = l_Lean_Grind_CommRing_Poly_insert(v___x_3104_, v___x_3105_, v_acc_3093_);
v_p_3092_ = v_p_3101_;
v_acc_3093_ = v___x_3106_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go___boxed(lean_object* v_k_3108_, lean_object* v_m_3109_, lean_object* v_c_3110_, lean_object* v_p_3111_, lean_object* v_acc_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_3108_, v_m_3109_, v_c_3110_, v_p_3111_, v_acc_3112_);
lean_dec(v_k_3108_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc(lean_object* v_k_3114_, lean_object* v_m_3115_, lean_object* v_p_3116_, lean_object* v_c_3117_){
_start:
{
lean_object* v___x_3118_; lean_object* v_k_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
lean_inc(v_c_3117_);
v___x_3118_ = lean_nat_to_int(v_c_3117_);
v_k_3119_ = lean_int_emod(v_k_3114_, v___x_3118_);
lean_dec(v___x_3118_);
v___x_3120_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3121_ = lean_int_dec_eq(v_k_3119_, v___x_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; uint8_t v___x_3123_; 
v___x_3122_ = lean_box(0);
v___x_3123_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_3115_, v___x_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
lean_dec(v_k_3119_);
v___x_3124_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3125_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_3114_, v_m_3115_, v_c_3117_, v_p_3116_, v___x_3124_);
return v___x_3125_;
}
else
{
lean_object* v___x_3126_; 
lean_dec(v_m_3115_);
v___x_3126_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3119_, v_p_3116_, v_c_3117_);
lean_dec(v_k_3119_);
return v___x_3126_;
}
}
else
{
lean_object* v___x_3127_; 
lean_dec(v_k_3119_);
lean_dec(v_c_3117_);
lean_dec_ref(v_p_3116_);
lean_dec(v_m_3115_);
v___x_3127_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc___boxed(lean_object* v_k_3128_, lean_object* v_m_3129_, lean_object* v_p_3130_, lean_object* v_c_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3128_, v_m_3129_, v_p_3130_, v_c_3131_);
lean_dec(v_k_3128_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineC(lean_object* v_p_u2081_3133_, lean_object* v_p_u2082_3134_, lean_object* v_c_3135_){
_start:
{
if (lean_obj_tag(v_p_u2081_3133_) == 0)
{
if (lean_obj_tag(v_p_u2082_3134_) == 0)
{
lean_object* v_k_3136_; lean_object* v_k_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3147_; 
v_k_3136_ = lean_ctor_get(v_p_u2081_3133_, 0);
lean_inc(v_k_3136_);
lean_dec_ref_known(v_p_u2081_3133_, 1);
v_k_3137_ = lean_ctor_get(v_p_u2082_3134_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_p_u2082_3134_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3139_ = v_p_u2082_3134_;
v_isShared_3140_ = v_isSharedCheck_3147_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_k_3137_);
lean_dec(v_p_u2082_3134_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3147_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3141_ = lean_int_add(v_k_3136_, v_k_3137_);
lean_dec(v_k_3137_);
lean_dec(v_k_3136_);
v___x_3142_ = lean_nat_to_int(v_c_3135_);
v___x_3143_ = lean_int_emod(v___x_3141_, v___x_3142_);
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v___x_3143_);
v___x_3145_ = v___x_3139_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
else
{
lean_object* v_k_3148_; lean_object* v___x_3149_; 
v_k_3148_ = lean_ctor_get(v_p_u2081_3133_, 0);
lean_inc(v_k_3148_);
lean_dec_ref_known(v_p_u2081_3133_, 1);
v___x_3149_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2082_3134_, v_k_3148_, v_c_3135_);
lean_dec(v_k_3148_);
return v___x_3149_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_3134_) == 0)
{
lean_object* v_k_3150_; lean_object* v___x_3151_; 
v_k_3150_ = lean_ctor_get(v_p_u2082_3134_, 0);
lean_inc(v_k_3150_);
lean_dec_ref_known(v_p_u2082_3134_, 1);
v___x_3151_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2081_3133_, v_k_3150_, v_c_3135_);
lean_dec(v_k_3150_);
return v___x_3151_;
}
else
{
lean_object* v_k_3152_; lean_object* v_v_3153_; lean_object* v_p_3154_; lean_object* v_k_3155_; lean_object* v_v_3156_; lean_object* v_p_3157_; uint8_t v___x_3158_; 
v_k_3152_ = lean_ctor_get(v_p_u2081_3133_, 0);
v_v_3153_ = lean_ctor_get(v_p_u2081_3133_, 1);
v_p_3154_ = lean_ctor_get(v_p_u2081_3133_, 2);
v_k_3155_ = lean_ctor_get(v_p_u2082_3134_, 0);
v_v_3156_ = lean_ctor_get(v_p_u2082_3134_, 1);
v_p_3157_ = lean_ctor_get(v_p_u2082_3134_, 2);
v___x_3158_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_3153_, v_v_3156_);
switch(v___x_3158_)
{
case 0:
{
lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3166_; 
lean_inc_ref(v_p_3157_);
lean_inc(v_v_3156_);
lean_inc(v_k_3155_);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_p_u2082_3134_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; lean_object* v_unused_3168_; lean_object* v_unused_3169_; 
v_unused_3167_ = lean_ctor_get(v_p_u2082_3134_, 2);
lean_dec(v_unused_3167_);
v_unused_3168_ = lean_ctor_get(v_p_u2082_3134_, 1);
lean_dec(v_unused_3168_);
v_unused_3169_ = lean_ctor_get(v_p_u2082_3134_, 0);
lean_dec(v_unused_3169_);
v___x_3160_ = v_p_u2082_3134_;
v_isShared_3161_ = v_isSharedCheck_3166_;
goto v_resetjp_3159_;
}
else
{
lean_dec(v_p_u2082_3134_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3166_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3162_; lean_object* v___x_3164_; 
v___x_3162_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_u2081_3133_, v_p_3157_, v_c_3135_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 2, v___x_3162_);
v___x_3164_ = v___x_3160_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_k_3155_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_v_3156_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v___x_3162_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
case 1:
{
lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3183_; 
lean_inc_ref(v_p_3157_);
lean_inc(v_k_3155_);
lean_inc_ref(v_p_3154_);
lean_inc(v_v_3153_);
lean_inc(v_k_3152_);
lean_dec_ref_known(v_p_u2081_3133_, 3);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_p_u2082_3134_);
if (v_isSharedCheck_3183_ == 0)
{
lean_object* v_unused_3184_; lean_object* v_unused_3185_; lean_object* v_unused_3186_; 
v_unused_3184_ = lean_ctor_get(v_p_u2082_3134_, 2);
lean_dec(v_unused_3184_);
v_unused_3185_ = lean_ctor_get(v_p_u2082_3134_, 1);
lean_dec(v_unused_3185_);
v_unused_3186_ = lean_ctor_get(v_p_u2082_3134_, 0);
lean_dec(v_unused_3186_);
v___x_3171_ = v_p_u2082_3134_;
v_isShared_3172_ = v_isSharedCheck_3183_;
goto v_resetjp_3170_;
}
else
{
lean_dec(v_p_u2082_3134_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3183_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v_k_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3173_ = lean_int_add(v_k_3152_, v_k_3155_);
lean_dec(v_k_3155_);
lean_dec(v_k_3152_);
lean_inc(v_c_3135_);
v___x_3174_ = lean_nat_to_int(v_c_3135_);
v_k_3175_ = lean_int_emod(v___x_3173_, v___x_3174_);
lean_dec(v___x_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3177_ = lean_int_dec_eq(v_k_3175_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3178_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3154_, v_p_3157_, v_c_3135_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 2, v___x_3178_);
lean_ctor_set(v___x_3171_, 1, v_v_3153_);
lean_ctor_set(v___x_3171_, 0, v_k_3175_);
v___x_3180_ = v___x_3171_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_k_3175_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_v_3153_);
lean_ctor_set(v_reuseFailAlloc_3181_, 2, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
else
{
lean_dec(v_k_3175_);
lean_del_object(v___x_3171_);
lean_dec(v_v_3153_);
v_p_u2081_3133_ = v_p_3154_;
v_p_u2082_3134_ = v_p_3157_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3194_; 
lean_inc_ref(v_p_3154_);
lean_inc(v_v_3153_);
lean_inc(v_k_3152_);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_p_u2081_3133_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; lean_object* v_unused_3196_; lean_object* v_unused_3197_; 
v_unused_3195_ = lean_ctor_get(v_p_u2081_3133_, 2);
lean_dec(v_unused_3195_);
v_unused_3196_ = lean_ctor_get(v_p_u2081_3133_, 1);
lean_dec(v_unused_3196_);
v_unused_3197_ = lean_ctor_get(v_p_u2081_3133_, 0);
lean_dec(v_unused_3197_);
v___x_3188_ = v_p_u2081_3133_;
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
else
{
lean_dec(v_p_u2081_3133_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3190_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3154_, v_p_u2082_3134_, v_c_3135_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 2, v___x_3190_);
v___x_3192_ = v___x_3188_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_k_3152_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_v_3153_);
lean_ctor_set(v_reuseFailAlloc_3193_, 2, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC_go(lean_object* v_p_u2082_3198_, lean_object* v_c_3199_, lean_object* v_p_u2081_3200_, lean_object* v_acc_3201_){
_start:
{
if (lean_obj_tag(v_p_u2081_3200_) == 0)
{
lean_object* v_k_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v_k_3202_ = lean_ctor_get(v_p_u2081_3200_, 0);
lean_inc(v_k_3202_);
lean_dec_ref_known(v_p_u2081_3200_, 1);
lean_inc(v_c_3199_);
v___x_3203_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3202_, v_p_u2082_3198_, v_c_3199_);
lean_dec(v_k_3202_);
v___x_3204_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3201_, v___x_3203_, v_c_3199_);
return v___x_3204_;
}
else
{
lean_object* v_k_3205_; lean_object* v_v_3206_; lean_object* v_p_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v_k_3205_ = lean_ctor_get(v_p_u2081_3200_, 0);
lean_inc(v_k_3205_);
v_v_3206_ = lean_ctor_get(v_p_u2081_3200_, 1);
lean_inc(v_v_3206_);
v_p_3207_ = lean_ctor_get(v_p_u2081_3200_, 2);
lean_inc_ref(v_p_3207_);
lean_dec_ref_known(v_p_u2081_3200_, 3);
lean_inc_n(v_c_3199_, 2);
lean_inc_ref(v_p_u2082_3198_);
v___x_3208_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_3205_, v_v_3206_, v_p_u2082_3198_, v_c_3199_);
lean_dec(v_k_3205_);
v___x_3209_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3201_, v___x_3208_, v_c_3199_);
v_p_u2081_3200_ = v_p_3207_;
v_acc_3201_ = v___x_3209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC(lean_object* v_p_u2081_3211_, lean_object* v_p_u2082_3212_, lean_object* v_c_3213_){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3215_ = l_Lean_Grind_CommRing_Poly_mulC_go(v_p_u2082_3212_, v_c_3213_, v_p_u2081_3211_, v___x_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc_go(lean_object* v_p_u2082_3216_, lean_object* v_c_3217_, lean_object* v_p_u2081_3218_, lean_object* v_acc_3219_){
_start:
{
if (lean_obj_tag(v_p_u2081_3218_) == 0)
{
lean_object* v_k_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_k_3220_ = lean_ctor_get(v_p_u2081_3218_, 0);
lean_inc(v_k_3220_);
lean_dec_ref_known(v_p_u2081_3218_, 1);
lean_inc(v_c_3217_);
v___x_3221_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3220_, v_p_u2082_3216_, v_c_3217_);
lean_dec(v_k_3220_);
v___x_3222_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3219_, v___x_3221_, v_c_3217_);
return v___x_3222_;
}
else
{
lean_object* v_k_3223_; lean_object* v_v_3224_; lean_object* v_p_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v_k_3223_ = lean_ctor_get(v_p_u2081_3218_, 0);
lean_inc(v_k_3223_);
v_v_3224_ = lean_ctor_get(v_p_u2081_3218_, 1);
lean_inc(v_v_3224_);
v_p_3225_ = lean_ctor_get(v_p_u2081_3218_, 2);
lean_inc_ref(v_p_3225_);
lean_dec_ref_known(v_p_u2081_3218_, 3);
lean_inc_n(v_c_3217_, 2);
lean_inc_ref(v_p_u2082_3216_);
v___x_3226_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3223_, v_v_3224_, v_p_u2082_3216_, v_c_3217_);
lean_dec(v_k_3223_);
v___x_3227_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3219_, v___x_3226_, v_c_3217_);
v_p_u2081_3218_ = v_p_3225_;
v_acc_3219_ = v___x_3227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc(lean_object* v_p_u2081_3229_, lean_object* v_p_u2082_3230_, lean_object* v_c_3231_){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3232_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3233_ = l_Lean_Grind_CommRing_Poly_mulC__nc_go(v_p_u2082_3230_, v_c_3231_, v_p_u2081_3229_, v___x_3232_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC(lean_object* v_p_3234_, lean_object* v_k_3235_, lean_object* v_c_3236_){
_start:
{
lean_object* v_zero_3237_; uint8_t v_isZero_3238_; 
v_zero_3237_ = lean_unsigned_to_nat(0u);
v_isZero_3238_ = lean_nat_dec_eq(v_k_3235_, v_zero_3237_);
if (v_isZero_3238_ == 1)
{
lean_object* v___x_3239_; 
lean_dec(v_c_3236_);
lean_dec_ref(v_p_3234_);
v___x_3239_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3239_;
}
else
{
lean_object* v_one_3240_; lean_object* v_n_3241_; uint8_t v___x_3242_; 
v_one_3240_ = lean_unsigned_to_nat(1u);
v_n_3241_ = lean_nat_sub(v_k_3235_, v_one_3240_);
v___x_3242_ = lean_nat_dec_eq(v_n_3241_, v_zero_3237_);
if (v___x_3242_ == 0)
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
lean_inc(v_c_3236_);
lean_inc_ref(v_p_3234_);
v___x_3243_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3234_, v_n_3241_, v_c_3236_);
lean_dec(v_n_3241_);
v___x_3244_ = l_Lean_Grind_CommRing_Poly_mulC(v_p_3234_, v___x_3243_, v_c_3236_);
return v___x_3244_;
}
else
{
lean_dec(v_n_3241_);
lean_dec(v_c_3236_);
return v_p_3234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC___boxed(lean_object* v_p_3245_, lean_object* v_k_3246_, lean_object* v_c_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3245_, v_k_3246_, v_c_3247_);
lean_dec(v_k_3246_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc(lean_object* v_p_3249_, lean_object* v_k_3250_, lean_object* v_c_3251_){
_start:
{
lean_object* v_zero_3252_; uint8_t v_isZero_3253_; 
v_zero_3252_ = lean_unsigned_to_nat(0u);
v_isZero_3253_ = lean_nat_dec_eq(v_k_3250_, v_zero_3252_);
if (v_isZero_3253_ == 1)
{
lean_object* v___x_3254_; 
lean_dec(v_c_3251_);
lean_dec_ref(v_p_3249_);
v___x_3254_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3254_;
}
else
{
lean_object* v_one_3255_; lean_object* v_n_3256_; uint8_t v___x_3257_; 
v_one_3255_ = lean_unsigned_to_nat(1u);
v_n_3256_ = lean_nat_sub(v_k_3250_, v_one_3255_);
v___x_3257_ = lean_nat_dec_eq(v_n_3256_, v_zero_3252_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_inc(v_c_3251_);
lean_inc_ref(v_p_3249_);
v___x_3258_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3249_, v_n_3256_, v_c_3251_);
lean_dec(v_n_3256_);
v___x_3259_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3258_, v_p_3249_, v_c_3251_);
return v___x_3259_;
}
else
{
lean_dec(v_n_3256_);
lean_dec(v_c_3251_);
return v_p_3249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc___boxed(lean_object* v_p_3260_, lean_object* v_k_3261_, lean_object* v_c_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3260_, v_k_3261_, v_c_3262_);
lean_dec(v_k_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC_go(lean_object* v_c_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v_k_3267_; 
switch(lean_obj_tag(v_a_3265_))
{
case 1:
{
lean_object* v_k_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3281_; 
v_k_3271_ = lean_ctor_get(v_a_3265_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v_a_3265_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3273_ = v_a_3265_;
v_isShared_3274_ = v_isSharedCheck_3281_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_k_3271_);
lean_dec(v_a_3265_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3281_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3279_; 
v___x_3275_ = lean_nat_to_int(v_k_3271_);
v___x_3276_ = lean_nat_to_int(v_c_3264_);
v___x_3277_ = lean_int_emod(v___x_3275_, v___x_3276_);
lean_dec(v___x_3276_);
lean_dec(v___x_3275_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set_tag(v___x_3273_, 0);
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
lean_object* v_i_3282_; lean_object* v___x_3283_; 
lean_dec(v_c_3264_);
v_i_3282_ = lean_ctor_get(v_a_3265_, 0);
lean_inc(v_i_3282_);
lean_dec_ref_known(v_a_3265_, 1);
v___x_3283_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3282_);
return v___x_3283_;
}
case 4:
{
lean_object* v_a_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_a_3284_ = lean_ctor_get(v_a_3265_, 0);
lean_inc_ref(v_a_3284_);
lean_dec_ref_known(v_a_3265_, 1);
v___x_3285_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3264_);
v___x_3286_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3264_, v_a_3284_);
v___x_3287_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3285_, v___x_3286_, v_c_3264_);
return v___x_3287_;
}
case 5:
{
lean_object* v_a_3288_; lean_object* v_b_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_a_3288_ = lean_ctor_get(v_a_3265_, 0);
lean_inc_ref(v_a_3288_);
v_b_3289_ = lean_ctor_get(v_a_3265_, 1);
lean_inc_ref(v_b_3289_);
lean_dec_ref_known(v_a_3265_, 2);
lean_inc_n(v_c_3264_, 2);
v___x_3290_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3264_, v_a_3288_);
v___x_3291_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3264_, v_b_3289_);
v___x_3292_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3290_, v___x_3291_, v_c_3264_);
return v___x_3292_;
}
case 6:
{
lean_object* v_a_3293_; lean_object* v_b_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v_a_3293_ = lean_ctor_get(v_a_3265_, 0);
lean_inc_ref(v_a_3293_);
v_b_3294_ = lean_ctor_get(v_a_3265_, 1);
lean_inc_ref(v_b_3294_);
lean_dec_ref_known(v_a_3265_, 2);
lean_inc_n(v_c_3264_, 3);
v___x_3295_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3264_, v_a_3293_);
v___x_3296_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_3297_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3264_, v_b_3294_);
v___x_3298_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3296_, v___x_3297_, v_c_3264_);
v___x_3299_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3295_, v___x_3298_, v_c_3264_);
return v___x_3299_;
}
case 7:
{
lean_object* v_a_3300_; lean_object* v_b_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_a_3300_ = lean_ctor_get(v_a_3265_, 0);
lean_inc_ref(v_a_3300_);
v_b_3301_ = lean_ctor_get(v_a_3265_, 1);
lean_inc_ref(v_b_3301_);
lean_dec_ref_known(v_a_3265_, 2);
lean_inc_n(v_c_3264_, 2);
v___x_3302_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3264_, v_a_3300_);
v___x_3303_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3264_, v_b_3301_);
v___x_3304_ = l_Lean_Grind_CommRing_Poly_mulC(v___x_3302_, v___x_3303_, v_c_3264_);
return v___x_3304_;
}
case 8:
{
lean_object* v_a_3305_; lean_object* v_k_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3333_; 
v_a_3305_ = lean_ctor_get(v_a_3265_, 0);
v_k_3306_ = lean_ctor_get(v_a_3265_, 1);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_a_3265_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3308_ = v_a_3265_;
v_isShared_3309_ = v_isSharedCheck_3333_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_k_3306_);
lean_inc(v_a_3305_);
lean_dec(v_a_3265_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3333_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3310_ = lean_unsigned_to_nat(0u);
v___x_3311_ = lean_nat_dec_eq(v_k_3306_, v___x_3310_);
if (v___x_3311_ == 0)
{
switch(lean_obj_tag(v_a_3305_))
{
case 0:
{
lean_object* v_k_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3322_; 
lean_del_object(v___x_3308_);
v_k_3312_ = lean_ctor_get(v_a_3305_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v_a_3305_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3314_ = v_a_3305_;
v_isShared_3315_ = v_isSharedCheck_3322_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_k_3312_);
lean_dec(v_a_3305_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3322_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3316_ = l_Int_pow(v_k_3312_, v_k_3306_);
lean_dec(v_k_3306_);
lean_dec(v_k_3312_);
v___x_3317_ = lean_nat_to_int(v_c_3264_);
v___x_3318_ = lean_int_emod(v___x_3316_, v___x_3317_);
lean_dec(v___x_3317_);
lean_dec(v___x_3316_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3318_);
v___x_3320_ = v___x_3314_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
case 3:
{
lean_object* v_i_3323_; lean_object* v___x_3325_; 
lean_dec(v_c_3264_);
v_i_3323_ = lean_ctor_get(v_a_3305_, 0);
lean_inc(v_i_3323_);
lean_dec_ref_known(v_a_3305_, 1);
if (v_isShared_3309_ == 0)
{
lean_ctor_set_tag(v___x_3308_, 0);
lean_ctor_set(v___x_3308_, 0, v_i_3323_);
v___x_3325_ = v___x_3308_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_i_3323_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_k_3306_);
v___x_3325_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3325_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3327_);
return v___x_3328_;
}
}
default: 
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
lean_del_object(v___x_3308_);
lean_inc(v_c_3264_);
v___x_3330_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3264_, v_a_3305_);
v___x_3331_ = l_Lean_Grind_CommRing_Poly_powC(v___x_3330_, v_k_3306_, v_c_3264_);
lean_dec(v_k_3306_);
return v___x_3331_;
}
}
}
else
{
lean_object* v___x_3332_; 
lean_del_object(v___x_3308_);
lean_dec(v_k_3306_);
lean_dec_ref(v_a_3305_);
lean_dec(v_c_3264_);
v___x_3332_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3332_;
}
}
}
default: 
{
lean_object* v_k_3334_; 
v_k_3334_ = lean_ctor_get(v_a_3265_, 0);
lean_inc(v_k_3334_);
lean_dec_ref(v_a_3265_);
v_k_3267_ = v_k_3334_;
goto v___jp_3266_;
}
}
v___jp_3266_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3268_ = lean_nat_to_int(v_c_3264_);
v___x_3269_ = lean_int_emod(v_k_3267_, v___x_3268_);
lean_dec(v___x_3268_);
lean_dec(v_k_3267_);
v___x_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
return v___x_3270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC(lean_object* v_e_3335_, lean_object* v_c_3336_){
_start:
{
lean_object* v___x_3337_; 
v___x_3337_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3336_, v_e_3335_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(lean_object* v_c_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_k_3341_; 
switch(lean_obj_tag(v_a_3339_))
{
case 1:
{
lean_object* v_k_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3355_; 
v_k_3345_ = lean_ctor_get(v_a_3339_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v_a_3339_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3347_ = v_a_3339_;
v_isShared_3348_ = v_isSharedCheck_3355_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_k_3345_);
lean_dec(v_a_3339_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3355_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3349_ = lean_nat_to_int(v_k_3345_);
v___x_3350_ = lean_nat_to_int(v_c_3338_);
v___x_3351_ = lean_int_emod(v___x_3349_, v___x_3350_);
lean_dec(v___x_3350_);
lean_dec(v___x_3349_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set_tag(v___x_3347_, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3351_);
v___x_3353_ = v___x_3347_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
case 3:
{
lean_object* v_i_3356_; lean_object* v___x_3357_; 
lean_dec(v_c_3338_);
v_i_3356_ = lean_ctor_get(v_a_3339_, 0);
lean_inc(v_i_3356_);
lean_dec_ref_known(v_a_3339_, 1);
v___x_3357_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3356_);
return v___x_3357_;
}
case 4:
{
lean_object* v_a_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v_a_3358_ = lean_ctor_get(v_a_3339_, 0);
lean_inc_ref(v_a_3358_);
lean_dec_ref_known(v_a_3339_, 1);
v___x_3359_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3338_);
v___x_3360_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3338_, v_a_3358_);
v___x_3361_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3359_, v___x_3360_, v_c_3338_);
return v___x_3361_;
}
case 5:
{
lean_object* v_a_3362_; lean_object* v_b_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v_a_3362_ = lean_ctor_get(v_a_3339_, 0);
lean_inc_ref(v_a_3362_);
v_b_3363_ = lean_ctor_get(v_a_3339_, 1);
lean_inc_ref(v_b_3363_);
lean_dec_ref_known(v_a_3339_, 2);
lean_inc_n(v_c_3338_, 2);
v___x_3364_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3338_, v_a_3362_);
v___x_3365_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3338_, v_b_3363_);
v___x_3366_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3364_, v___x_3365_, v_c_3338_);
return v___x_3366_;
}
case 6:
{
lean_object* v_a_3367_; lean_object* v_b_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_a_3367_ = lean_ctor_get(v_a_3339_, 0);
lean_inc_ref(v_a_3367_);
v_b_3368_ = lean_ctor_get(v_a_3339_, 1);
lean_inc_ref(v_b_3368_);
lean_dec_ref_known(v_a_3339_, 2);
lean_inc_n(v_c_3338_, 3);
v___x_3369_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3338_, v_a_3367_);
v___x_3370_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_3371_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3338_, v_b_3368_);
v___x_3372_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3370_, v___x_3371_, v_c_3338_);
v___x_3373_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3369_, v___x_3372_, v_c_3338_);
return v___x_3373_;
}
case 7:
{
lean_object* v_a_3374_; lean_object* v_b_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_a_3374_ = lean_ctor_get(v_a_3339_, 0);
lean_inc_ref(v_a_3374_);
v_b_3375_ = lean_ctor_get(v_a_3339_, 1);
lean_inc_ref(v_b_3375_);
lean_dec_ref_known(v_a_3339_, 2);
lean_inc_n(v_c_3338_, 2);
v___x_3376_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3338_, v_a_3374_);
v___x_3377_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3338_, v_b_3375_);
v___x_3378_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3376_, v___x_3377_, v_c_3338_);
return v___x_3378_;
}
case 8:
{
lean_object* v_a_3379_; lean_object* v_k_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3407_; 
v_a_3379_ = lean_ctor_get(v_a_3339_, 0);
v_k_3380_ = lean_ctor_get(v_a_3339_, 1);
v_isSharedCheck_3407_ = !lean_is_exclusive(v_a_3339_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3382_ = v_a_3339_;
v_isShared_3383_ = v_isSharedCheck_3407_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_k_3380_);
lean_inc(v_a_3379_);
lean_dec(v_a_3339_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3407_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; uint8_t v___x_3385_; 
v___x_3384_ = lean_unsigned_to_nat(0u);
v___x_3385_ = lean_nat_dec_eq(v_k_3380_, v___x_3384_);
if (v___x_3385_ == 0)
{
switch(lean_obj_tag(v_a_3379_))
{
case 0:
{
lean_object* v_k_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3396_; 
lean_del_object(v___x_3382_);
v_k_3386_ = lean_ctor_get(v_a_3379_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_a_3379_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3388_ = v_a_3379_;
v_isShared_3389_ = v_isSharedCheck_3396_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_k_3386_);
lean_dec(v_a_3379_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3396_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3390_ = l_Int_pow(v_k_3386_, v_k_3380_);
lean_dec(v_k_3380_);
lean_dec(v_k_3386_);
v___x_3391_ = lean_nat_to_int(v_c_3338_);
v___x_3392_ = lean_int_emod(v___x_3390_, v___x_3391_);
lean_dec(v___x_3391_);
lean_dec(v___x_3390_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___x_3392_);
v___x_3394_ = v___x_3388_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
case 3:
{
lean_object* v_i_3397_; lean_object* v___x_3399_; 
lean_dec(v_c_3338_);
v_i_3397_ = lean_ctor_get(v_a_3379_, 0);
lean_inc(v_i_3397_);
lean_dec_ref_known(v_a_3379_, 1);
if (v_isShared_3383_ == 0)
{
lean_ctor_set_tag(v___x_3382_, 0);
lean_ctor_set(v___x_3382_, 0, v_i_3397_);
v___x_3399_ = v___x_3382_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_i_3397_);
lean_ctor_set(v_reuseFailAlloc_3403_, 1, v_k_3380_);
v___x_3399_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = lean_box(0);
v___x_3401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3401_);
return v___x_3402_;
}
}
default: 
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_del_object(v___x_3382_);
lean_inc(v_c_3338_);
v___x_3404_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3338_, v_a_3379_);
v___x_3405_ = l_Lean_Grind_CommRing_Poly_powC__nc(v___x_3404_, v_k_3380_, v_c_3338_);
lean_dec(v_k_3380_);
return v___x_3405_;
}
}
}
else
{
lean_object* v___x_3406_; 
lean_del_object(v___x_3382_);
lean_dec(v_k_3380_);
lean_dec_ref(v_a_3379_);
lean_dec(v_c_3338_);
v___x_3406_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3406_;
}
}
}
default: 
{
lean_object* v_k_3408_; 
v_k_3408_ = lean_ctor_get(v_a_3339_, 0);
lean_inc(v_k_3408_);
lean_dec_ref(v_a_3339_);
v_k_3341_ = v_k_3408_;
goto v___jp_3340_;
}
}
v___jp_3340_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = lean_nat_to_int(v_c_3338_);
v___x_3343_ = lean_int_emod(v_k_3341_, v___x_3342_);
lean_dec(v___x_3342_);
lean_dec(v_k_3341_);
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
return v___x_3344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc(lean_object* v_e_3409_, lean_object* v_c_3410_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3410_, v_e_3409_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(lean_object* v_k_3412_, lean_object* v_h__1_3413_, lean_object* v_h__2_3414_, lean_object* v_h__3_3415_){
_start:
{
lean_object* v___x_3416_; uint8_t v___x_3417_; 
v___x_3416_ = lean_unsigned_to_nat(0u);
v___x_3417_ = lean_nat_dec_eq(v_k_3412_, v___x_3416_);
if (v___x_3417_ == 0)
{
lean_object* v___x_3418_; uint8_t v___x_3419_; 
lean_dec(v_h__1_3413_);
v___x_3418_ = lean_unsigned_to_nat(1u);
v___x_3419_ = lean_nat_dec_eq(v_k_3412_, v___x_3418_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; 
lean_dec(v_h__2_3414_);
v___x_3420_ = lean_apply_3(v_h__3_3415_, v_k_3412_, lean_box(0), lean_box(0));
return v___x_3420_;
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
lean_dec(v_h__3_3415_);
lean_dec(v_k_3412_);
v___x_3421_ = lean_box(0);
v___x_3422_ = lean_apply_1(v_h__2_3414_, v___x_3421_);
return v___x_3422_;
}
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
lean_dec(v_h__3_3415_);
lean_dec(v_h__2_3414_);
lean_dec(v_k_3412_);
v___x_3423_ = lean_box(0);
v___x_3424_ = lean_apply_1(v_h__1_3413_, v___x_3423_);
return v___x_3424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(lean_object* v_motive_3425_, lean_object* v_k_3426_, lean_object* v_h__1_3427_, lean_object* v_h__2_3428_, lean_object* v_h__3_3429_){
_start:
{
lean_object* v___x_3430_; uint8_t v___x_3431_; 
v___x_3430_ = lean_unsigned_to_nat(0u);
v___x_3431_ = lean_nat_dec_eq(v_k_3426_, v___x_3430_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; uint8_t v___x_3433_; 
lean_dec(v_h__1_3427_);
v___x_3432_ = lean_unsigned_to_nat(1u);
v___x_3433_ = lean_nat_dec_eq(v_k_3426_, v___x_3432_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; 
lean_dec(v_h__2_3428_);
v___x_3434_ = lean_apply_3(v_h__3_3429_, v_k_3426_, lean_box(0), lean_box(0));
return v___x_3434_;
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
lean_dec(v_h__3_3429_);
lean_dec(v_k_3426_);
v___x_3435_ = lean_box(0);
v___x_3436_ = lean_apply_1(v_h__2_3428_, v___x_3435_);
return v___x_3436_;
}
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_dec(v_h__3_3429_);
lean_dec(v_h__2_3428_);
lean_dec(v_k_3426_);
v___x_3437_ = lean_box(0);
v___x_3438_ = lean_apply_1(v_h__1_3427_, v___x_3437_);
return v___x_3438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(lean_object* v_m_u2081_3439_, lean_object* v_h__1_3440_, lean_object* v_h__2_3441_, lean_object* v_h__3_3442_){
_start:
{
if (lean_obj_tag(v_m_u2081_3439_) == 0)
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_dec(v_h__3_3442_);
lean_dec(v_h__2_3441_);
v___x_3443_ = lean_box(0);
v___x_3444_ = lean_apply_1(v_h__1_3440_, v___x_3443_);
return v___x_3444_;
}
else
{
lean_object* v_m_3445_; 
lean_dec(v_h__1_3440_);
v_m_3445_ = lean_ctor_get(v_m_u2081_3439_, 1);
if (lean_obj_tag(v_m_3445_) == 0)
{
lean_object* v_p_3446_; lean_object* v___x_3447_; 
lean_dec(v_h__3_3442_);
v_p_3446_ = lean_ctor_get(v_m_u2081_3439_, 0);
lean_inc_ref(v_p_3446_);
lean_dec_ref_known(v_m_u2081_3439_, 2);
v___x_3447_ = lean_apply_1(v_h__2_3441_, v_p_3446_);
return v___x_3447_;
}
else
{
lean_object* v_p_3448_; lean_object* v___x_3449_; 
lean_inc(v_m_3445_);
lean_dec(v_h__2_3441_);
v_p_3448_ = lean_ctor_get(v_m_u2081_3439_, 0);
lean_inc_ref(v_p_3448_);
lean_dec_ref_known(v_m_u2081_3439_, 2);
v___x_3449_ = lean_apply_3(v_h__3_3442_, v_p_3448_, v_m_3445_, lean_box(0));
return v___x_3449_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(lean_object* v_motive_3450_, lean_object* v_m_u2081_3451_, lean_object* v_h__1_3452_, lean_object* v_h__2_3453_, lean_object* v_h__3_3454_){
_start:
{
if (lean_obj_tag(v_m_u2081_3451_) == 0)
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
lean_dec(v_h__3_3454_);
lean_dec(v_h__2_3453_);
v___x_3455_ = lean_box(0);
v___x_3456_ = lean_apply_1(v_h__1_3452_, v___x_3455_);
return v___x_3456_;
}
else
{
lean_object* v_m_3457_; 
lean_dec(v_h__1_3452_);
v_m_3457_ = lean_ctor_get(v_m_u2081_3451_, 1);
if (lean_obj_tag(v_m_3457_) == 0)
{
lean_object* v_p_3458_; lean_object* v___x_3459_; 
lean_dec(v_h__3_3454_);
v_p_3458_ = lean_ctor_get(v_m_u2081_3451_, 0);
lean_inc_ref(v_p_3458_);
lean_dec_ref_known(v_m_u2081_3451_, 2);
v___x_3459_ = lean_apply_1(v_h__2_3453_, v_p_3458_);
return v___x_3459_;
}
else
{
lean_object* v_p_3460_; lean_object* v___x_3461_; 
lean_inc(v_m_3457_);
lean_dec(v_h__2_3453_);
v_p_3460_ = lean_ctor_get(v_m_u2081_3451_, 0);
lean_inc_ref(v_p_3460_);
lean_dec_ref_known(v_m_u2081_3451_, 2);
v___x_3461_ = lean_apply_3(v_h__3_3454_, v_p_3460_, v_m_3457_, lean_box(0));
return v___x_3461_;
}
}
}
}
lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(uint8_t v_a_3462_, lean_object* v_h__1_3463_, lean_object* v_h__2_3464_){
_start:
{
if (v_a_3462_ == 1)
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
lean_dec(v_h__2_3464_);
v___x_3465_ = lean_box(0);
v___x_3466_ = lean_apply_1(v_h__1_3463_, v___x_3465_);
return v___x_3466_;
}
else
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
lean_dec(v_h__1_3463_);
v___x_3467_ = lean_box(v_a_3462_);
v___x_3468_ = lean_apply_2(v_h__2_3464_, v___x_3467_, lean_box(0));
return v___x_3468_;
}
}
}
LEAN_EXPORT void l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_3462_ = stack[0].m_num;
lean_object* v_h__1_3463_ = stack[1].m_obj;
lean_object* v_h__2_3464_ = stack[2].m_obj;
lean_object* v_res_3469_;
v_res_3469_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(v_a_3462_, v_h__1_3463_, v_h__2_3464_);
stack->m_obj
 = v_res_3469_;
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg___boxed(lean_object* v_a_3470_, lean_object* v_h__1_3471_, lean_object* v_h__2_3472_){
_start:
{
uint8_t v_a_13__boxed_3473_; lean_object* v_res_3474_; 
v_a_13__boxed_3473_ = lean_unbox(v_a_3470_);
v_res_3474_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___redArg(v_a_13__boxed_3473_, v_h__1_3471_, v_h__2_3472_);
return v_res_3474_;
}
}
lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(lean_object* v_motive_3475_, uint8_t v_a_3476_, lean_object* v_h__1_3477_, lean_object* v_h__2_3478_){
_start:
{
if (v_a_3476_ == 1)
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
lean_dec(v_h__2_3478_);
v___x_3479_ = lean_box(0);
v___x_3480_ = lean_apply_1(v_h__1_3477_, v___x_3479_);
return v___x_3480_;
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
lean_dec(v_h__1_3477_);
v___x_3481_ = lean_box(v_a_3476_);
v___x_3482_ = lean_apply_2(v_h__2_3478_, v___x_3481_, lean_box(0));
return v___x_3482_;
}
}
}
LEAN_EXPORT void l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_3476_ = stack[1].m_num;
lean_object* v_h__1_3477_ = stack[2].m_obj;
lean_object* v_h__2_3478_ = stack[3].m_obj;
lean_object* v_res_3483_;
v_res_3483_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(lean_box(0), v_a_3476_, v_h__1_3477_, v_h__2_3478_);
stack->m_obj
 = v_res_3483_;
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter___boxed(lean_object* v_motive_3484_, lean_object* v_a_3485_, lean_object* v_h__1_3486_, lean_object* v_h__2_3487_){
_start:
{
uint8_t v_a_30__boxed_3488_; lean_object* v_res_3489_; 
v_a_30__boxed_3488_ = lean_unbox(v_a_3485_);
v_res_3489_ = l___private_Init_Grind_Ring_CommSolver_0__Ordering_then_match__1_splitter(v_motive_3484_, v_a_30__boxed_3488_, v_h__1_3486_, v_h__2_3487_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(lean_object* v_p_3490_, lean_object* v_h__1_3491_, lean_object* v_h__2_3492_, lean_object* v_h__3_3493_){
_start:
{
if (lean_obj_tag(v_p_3490_) == 0)
{
lean_object* v_k_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
lean_dec(v_h__3_3493_);
v_k_3494_ = lean_ctor_get(v_p_3490_, 0);
lean_inc(v_k_3494_);
lean_dec_ref_known(v_p_3490_, 1);
v___x_3495_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3496_ = lean_int_dec_eq(v_k_3494_, v___x_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
lean_dec(v_h__1_3491_);
v___x_3497_ = lean_apply_2(v_h__2_3492_, v_k_3494_, lean_box(0));
return v___x_3497_;
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
lean_dec(v_k_3494_);
lean_dec(v_h__2_3492_);
v___x_3498_ = lean_box(0);
v___x_3499_ = lean_apply_1(v_h__1_3491_, v___x_3498_);
return v___x_3499_;
}
}
else
{
lean_object* v_k_3500_; lean_object* v_v_3501_; lean_object* v_p_3502_; lean_object* v___x_3503_; 
lean_dec(v_h__2_3492_);
lean_dec(v_h__1_3491_);
v_k_3500_ = lean_ctor_get(v_p_3490_, 0);
lean_inc(v_k_3500_);
v_v_3501_ = lean_ctor_get(v_p_3490_, 1);
lean_inc(v_v_3501_);
v_p_3502_ = lean_ctor_get(v_p_3490_, 2);
lean_inc_ref(v_p_3502_);
lean_dec_ref_known(v_p_3490_, 3);
v___x_3503_ = lean_apply_3(v_h__3_3493_, v_k_3500_, v_v_3501_, v_p_3502_);
return v___x_3503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(lean_object* v_motive_3504_, lean_object* v_p_3505_, lean_object* v_h__1_3506_, lean_object* v_h__2_3507_, lean_object* v_h__3_3508_){
_start:
{
if (lean_obj_tag(v_p_3505_) == 0)
{
lean_object* v_k_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; 
lean_dec(v_h__3_3508_);
v_k_3509_ = lean_ctor_get(v_p_3505_, 0);
lean_inc(v_k_3509_);
lean_dec_ref_known(v_p_3505_, 1);
v___x_3510_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3511_ = lean_int_dec_eq(v_k_3509_, v___x_3510_);
if (v___x_3511_ == 0)
{
lean_object* v___x_3512_; 
lean_dec(v_h__1_3506_);
v___x_3512_ = lean_apply_2(v_h__2_3507_, v_k_3509_, lean_box(0));
return v___x_3512_;
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
lean_dec(v_k_3509_);
lean_dec(v_h__2_3507_);
v___x_3513_ = lean_box(0);
v___x_3514_ = lean_apply_1(v_h__1_3506_, v___x_3513_);
return v___x_3514_;
}
}
else
{
lean_object* v_k_3515_; lean_object* v_v_3516_; lean_object* v_p_3517_; lean_object* v___x_3518_; 
lean_dec(v_h__2_3507_);
lean_dec(v_h__1_3506_);
v_k_3515_ = lean_ctor_get(v_p_3505_, 0);
lean_inc(v_k_3515_);
v_v_3516_ = lean_ctor_get(v_p_3505_, 1);
lean_inc(v_v_3516_);
v_p_3517_ = lean_ctor_get(v_p_3505_, 2);
lean_inc_ref(v_p_3517_);
lean_dec_ref_known(v_p_3505_, 3);
v___x_3518_ = lean_apply_3(v_h__3_3508_, v_k_3515_, v_v_3516_, v_p_3517_);
return v___x_3518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object* v_p_3519_, lean_object* v_h__1_3520_, lean_object* v_h__2_3521_){
_start:
{
if (lean_obj_tag(v_p_3519_) == 0)
{
lean_object* v_k_3522_; lean_object* v___x_3523_; 
lean_dec(v_h__2_3521_);
v_k_3522_ = lean_ctor_get(v_p_3519_, 0);
lean_inc(v_k_3522_);
lean_dec_ref_known(v_p_3519_, 1);
v___x_3523_ = lean_apply_1(v_h__1_3520_, v_k_3522_);
return v___x_3523_;
}
else
{
lean_object* v_k_3524_; lean_object* v_v_3525_; lean_object* v_p_3526_; lean_object* v___x_3527_; 
lean_dec(v_h__1_3520_);
v_k_3524_ = lean_ctor_get(v_p_3519_, 0);
lean_inc(v_k_3524_);
v_v_3525_ = lean_ctor_get(v_p_3519_, 1);
lean_inc(v_v_3525_);
v_p_3526_ = lean_ctor_get(v_p_3519_, 2);
lean_inc_ref(v_p_3526_);
lean_dec_ref_known(v_p_3519_, 3);
v___x_3527_ = lean_apply_3(v_h__2_3521_, v_k_3524_, v_v_3525_, v_p_3526_);
return v___x_3527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object* v_motive_3528_, lean_object* v_p_3529_, lean_object* v_h__1_3530_, lean_object* v_h__2_3531_){
_start:
{
if (lean_obj_tag(v_p_3529_) == 0)
{
lean_object* v_k_3532_; lean_object* v___x_3533_; 
lean_dec(v_h__2_3531_);
v_k_3532_ = lean_ctor_get(v_p_3529_, 0);
lean_inc(v_k_3532_);
lean_dec_ref_known(v_p_3529_, 1);
v___x_3533_ = lean_apply_1(v_h__1_3530_, v_k_3532_);
return v___x_3533_;
}
else
{
lean_object* v_k_3534_; lean_object* v_v_3535_; lean_object* v_p_3536_; lean_object* v___x_3537_; 
lean_dec(v_h__1_3530_);
v_k_3534_ = lean_ctor_get(v_p_3529_, 0);
lean_inc(v_k_3534_);
v_v_3535_ = lean_ctor_get(v_p_3529_, 1);
lean_inc(v_v_3535_);
v_p_3536_ = lean_ctor_get(v_p_3529_, 2);
lean_inc_ref(v_p_3536_);
lean_dec_ref_known(v_p_3529_, 3);
v___x_3537_ = lean_apply_3(v_h__2_3531_, v_k_3534_, v_v_3535_, v_p_3536_);
return v___x_3537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object* v_k_3538_, lean_object* v_h__1_3539_, lean_object* v_h__2_3540_, lean_object* v_h__3_3541_){
_start:
{
lean_object* v_zero_3542_; uint8_t v_isZero_3543_; 
v_zero_3542_ = lean_unsigned_to_nat(0u);
v_isZero_3543_ = lean_nat_dec_eq(v_k_3538_, v_zero_3542_);
if (v_isZero_3543_ == 1)
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
lean_dec(v_h__3_3541_);
lean_dec(v_h__2_3540_);
v___x_3544_ = lean_box(0);
v___x_3545_ = lean_apply_1(v_h__1_3539_, v___x_3544_);
return v___x_3545_;
}
else
{
lean_object* v_one_3546_; lean_object* v_n_3547_; uint8_t v___x_3548_; 
lean_dec(v_h__1_3539_);
v_one_3546_ = lean_unsigned_to_nat(1u);
v_n_3547_ = lean_nat_sub(v_k_3538_, v_one_3546_);
v___x_3548_ = lean_nat_dec_eq(v_n_3547_, v_zero_3542_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
lean_dec(v_h__2_3540_);
v___x_3549_ = lean_apply_2(v_h__3_3541_, v_n_3547_, lean_box(0));
return v___x_3549_;
}
else
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_dec(v_n_3547_);
lean_dec(v_h__3_3541_);
v___x_3550_ = lean_box(0);
v___x_3551_ = lean_apply_1(v_h__2_3540_, v___x_3550_);
return v___x_3551_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object* v_k_3552_, lean_object* v_h__1_3553_, lean_object* v_h__2_3554_, lean_object* v_h__3_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(v_k_3552_, v_h__1_3553_, v_h__2_3554_, v_h__3_3555_);
lean_dec(v_k_3552_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object* v_motive_3557_, lean_object* v_k_3558_, lean_object* v_h__1_3559_, lean_object* v_h__2_3560_, lean_object* v_h__3_3561_){
_start:
{
lean_object* v_zero_3562_; uint8_t v_isZero_3563_; 
v_zero_3562_ = lean_unsigned_to_nat(0u);
v_isZero_3563_ = lean_nat_dec_eq(v_k_3558_, v_zero_3562_);
if (v_isZero_3563_ == 1)
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
lean_dec(v_h__3_3561_);
lean_dec(v_h__2_3560_);
v___x_3564_ = lean_box(0);
v___x_3565_ = lean_apply_1(v_h__1_3559_, v___x_3564_);
return v___x_3565_;
}
else
{
lean_object* v_one_3566_; lean_object* v_n_3567_; uint8_t v___x_3568_; 
lean_dec(v_h__1_3559_);
v_one_3566_ = lean_unsigned_to_nat(1u);
v_n_3567_ = lean_nat_sub(v_k_3558_, v_one_3566_);
v___x_3568_ = lean_nat_dec_eq(v_n_3567_, v_zero_3562_);
if (v___x_3568_ == 0)
{
lean_object* v___x_3569_; 
lean_dec(v_h__2_3560_);
v___x_3569_ = lean_apply_2(v_h__3_3561_, v_n_3567_, lean_box(0));
return v___x_3569_;
}
else
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
lean_dec(v_n_3567_);
lean_dec(v_h__3_3561_);
v___x_3570_ = lean_box(0);
v___x_3571_ = lean_apply_1(v_h__2_3560_, v___x_3570_);
return v___x_3571_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object* v_motive_3572_, lean_object* v_k_3573_, lean_object* v_h__1_3574_, lean_object* v_h__2_3575_, lean_object* v_h__3_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(v_motive_3572_, v_k_3573_, v_h__1_3574_, v_h__2_3575_, v_h__3_3576_);
lean_dec(v_k_3573_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(lean_object* v_x_3578_, lean_object* v_h__1_3579_, lean_object* v_h__2_3580_, lean_object* v_h__3_3581_, lean_object* v_h__4_3582_, lean_object* v_h__5_3583_, lean_object* v_h__6_3584_, lean_object* v_h__7_3585_, lean_object* v_h__8_3586_, lean_object* v_h__9_3587_){
_start:
{
switch(lean_obj_tag(v_x_3578_))
{
case 0:
{
lean_object* v_k_3588_; lean_object* v___x_3589_; 
lean_dec(v_h__9_3587_);
lean_dec(v_h__8_3586_);
lean_dec(v_h__7_3585_);
lean_dec(v_h__6_3584_);
lean_dec(v_h__5_3583_);
lean_dec(v_h__4_3582_);
lean_dec(v_h__3_3581_);
lean_dec(v_h__2_3580_);
v_k_3588_ = lean_ctor_get(v_x_3578_, 0);
lean_inc(v_k_3588_);
lean_dec_ref_known(v_x_3578_, 1);
v___x_3589_ = lean_apply_1(v_h__1_3579_, v_k_3588_);
return v___x_3589_;
}
case 1:
{
lean_object* v_k_3590_; lean_object* v___x_3591_; 
lean_dec(v_h__9_3587_);
lean_dec(v_h__8_3586_);
lean_dec(v_h__7_3585_);
lean_dec(v_h__6_3584_);
lean_dec(v_h__5_3583_);
lean_dec(v_h__4_3582_);
lean_dec(v_h__3_3581_);
lean_dec(v_h__1_3579_);
v_k_3590_ = lean_ctor_get(v_x_3578_, 0);
lean_inc(v_k_3590_);
lean_dec_ref_known(v_x_3578_, 1);
v___x_3591_ = lean_apply_1(v_h__2_3580_, v_k_3590_);
return v___x_3591_;
}
case 2:
{
lean_object* v_k_3592_; lean_object* v___x_3593_; 
lean_dec(v_h__9_3587_);
lean_dec(v_h__8_3586_);
lean_dec(v_h__7_3585_);
lean_dec(v_h__6_3584_);
lean_dec(v_h__5_3583_);
lean_dec(v_h__4_3582_);
lean_dec(v_h__2_3580_);
lean_dec(v_h__1_3579_);
v_k_3592_ = lean_ctor_get(v_x_3578_, 0);
lean_inc(v_k_3592_);
lean_dec_ref_known(v_x_3578_, 1);
v___x_3593_ = lean_apply_1(v_h__3_3581_, v_k_3592_);
return v___x_3593_;
}
case 3:
{
lean_object* v_i_3594_; lean_object* v___x_3595_; 
lean_dec(v_h__9_3587_);
lean_dec(v_h__8_3586_);
lean_dec(v_h__7_3585_);
lean_dec(v_h__6_3584_);
lean_dec(v_h__5_3583_);
lean_dec(v_h__3_3581_);
lean_dec(v_h__2_3580_);
lean_dec(v_h__1_3579_);
v_i_3594_ = lean_ctor_get(v_x_3578_, 0);
lean_inc(v_i_3594_);
lean_dec_ref_known(v_x_3578_, 1);
v___x_3595_ = lean_apply_1(v_h__4_3582_, v_i_3594_);
return v___x_3595_;
}
case 4:
{
lean_object* v_a_3596_; lean_object* v___x_3597_; 
lean_dec(v_h__9_3587_);
lean_dec(v_h__8_3586_);
lean_dec(v_h__6_3584_);
lean_dec(v_h__5_3583_);
lean_dec(v_h__4_3582_);
lean_dec(v_h__3_3581_);
lean_dec(v_h__2_3580_);
lean_dec(v_h__1_3579_);
v_a_3596_ = lean_ctor_get(v_x_3578_, 0);
lean_inc_ref(v_a_3596_);
lean_dec_ref_known(v_x_3578_, 1);
v___x_3597_ = lean_apply_1(v_h__7_3585_, v_a_3596_);
return v___x_3597_;
}
case 5:
{
lean_object* v_a_3598_; lean_object* v_b_3599_; lean_object* v___x_3600_; 
lean_dec(v_h__9_3587_);
lean_dec(v_h__8_3586_);
lean_dec(v_h__7_3585_);
lean_dec(v_h__6_3584_);
lean_dec(v_h__4_3582_);
lean_dec(v_h__3_3581_);
lean_dec(v_h__2_3580_);
lean_dec(v_h__1_3579_);
v_a_3598_ = lean_ctor_get(v_x_3578_, 0);
lean_inc_ref(v_a_3598_);
v_b_3599_ = lean_ctor_get(v_x_3578_, 1);
lean_inc_ref(v_b_3599_);
lean_dec_ref_known(v_x_3578_, 2);
v___x_3600_ = lean_apply_2(v_h__5_3583_, v_a_3598_, v_b_3599_);
return v___x_3600_;
}
case 6:
{
lean_object* v_a_3601_; lean_object* v_b_3602_; lean_object* v___x_3603_; 
lean_dec(v_h__9_3587_);
lean_dec(v_h__7_3585_);
lean_dec(v_h__6_3584_);
lean_dec(v_h__5_3583_);
lean_dec(v_h__4_3582_);
lean_dec(v_h__3_3581_);
lean_dec(v_h__2_3580_);
lean_dec(v_h__1_3579_);
v_a_3601_ = lean_ctor_get(v_x_3578_, 0);
lean_inc_ref(v_a_3601_);
v_b_3602_ = lean_ctor_get(v_x_3578_, 1);
lean_inc_ref(v_b_3602_);
lean_dec_ref_known(v_x_3578_, 2);
v___x_3603_ = lean_apply_2(v_h__8_3586_, v_a_3601_, v_b_3602_);
return v___x_3603_;
}
case 7:
{
lean_object* v_a_3604_; lean_object* v_b_3605_; lean_object* v___x_3606_; 
lean_dec(v_h__9_3587_);
lean_dec(v_h__8_3586_);
lean_dec(v_h__7_3585_);
lean_dec(v_h__5_3583_);
lean_dec(v_h__4_3582_);
lean_dec(v_h__3_3581_);
lean_dec(v_h__2_3580_);
lean_dec(v_h__1_3579_);
v_a_3604_ = lean_ctor_get(v_x_3578_, 0);
lean_inc_ref(v_a_3604_);
v_b_3605_ = lean_ctor_get(v_x_3578_, 1);
lean_inc_ref(v_b_3605_);
lean_dec_ref_known(v_x_3578_, 2);
v___x_3606_ = lean_apply_2(v_h__6_3584_, v_a_3604_, v_b_3605_);
return v___x_3606_;
}
default: 
{
lean_object* v_a_3607_; lean_object* v_k_3608_; lean_object* v___x_3609_; 
lean_dec(v_h__8_3586_);
lean_dec(v_h__7_3585_);
lean_dec(v_h__6_3584_);
lean_dec(v_h__5_3583_);
lean_dec(v_h__4_3582_);
lean_dec(v_h__3_3581_);
lean_dec(v_h__2_3580_);
lean_dec(v_h__1_3579_);
v_a_3607_ = lean_ctor_get(v_x_3578_, 0);
lean_inc_ref(v_a_3607_);
v_k_3608_ = lean_ctor_get(v_x_3578_, 1);
lean_inc(v_k_3608_);
lean_dec_ref_known(v_x_3578_, 2);
v___x_3609_ = lean_apply_2(v_h__9_3587_, v_a_3607_, v_k_3608_);
return v___x_3609_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter(lean_object* v_motive_3610_, lean_object* v_x_3611_, lean_object* v_h__1_3612_, lean_object* v_h__2_3613_, lean_object* v_h__3_3614_, lean_object* v_h__4_3615_, lean_object* v_h__5_3616_, lean_object* v_h__6_3617_, lean_object* v_h__7_3618_, lean_object* v_h__8_3619_, lean_object* v_h__9_3620_){
_start:
{
switch(lean_obj_tag(v_x_3611_))
{
case 0:
{
lean_object* v_k_3621_; lean_object* v___x_3622_; 
lean_dec(v_h__9_3620_);
lean_dec(v_h__8_3619_);
lean_dec(v_h__7_3618_);
lean_dec(v_h__6_3617_);
lean_dec(v_h__5_3616_);
lean_dec(v_h__4_3615_);
lean_dec(v_h__3_3614_);
lean_dec(v_h__2_3613_);
v_k_3621_ = lean_ctor_get(v_x_3611_, 0);
lean_inc(v_k_3621_);
lean_dec_ref_known(v_x_3611_, 1);
v___x_3622_ = lean_apply_1(v_h__1_3612_, v_k_3621_);
return v___x_3622_;
}
case 1:
{
lean_object* v_k_3623_; lean_object* v___x_3624_; 
lean_dec(v_h__9_3620_);
lean_dec(v_h__8_3619_);
lean_dec(v_h__7_3618_);
lean_dec(v_h__6_3617_);
lean_dec(v_h__5_3616_);
lean_dec(v_h__4_3615_);
lean_dec(v_h__3_3614_);
lean_dec(v_h__1_3612_);
v_k_3623_ = lean_ctor_get(v_x_3611_, 0);
lean_inc(v_k_3623_);
lean_dec_ref_known(v_x_3611_, 1);
v___x_3624_ = lean_apply_1(v_h__2_3613_, v_k_3623_);
return v___x_3624_;
}
case 2:
{
lean_object* v_k_3625_; lean_object* v___x_3626_; 
lean_dec(v_h__9_3620_);
lean_dec(v_h__8_3619_);
lean_dec(v_h__7_3618_);
lean_dec(v_h__6_3617_);
lean_dec(v_h__5_3616_);
lean_dec(v_h__4_3615_);
lean_dec(v_h__2_3613_);
lean_dec(v_h__1_3612_);
v_k_3625_ = lean_ctor_get(v_x_3611_, 0);
lean_inc(v_k_3625_);
lean_dec_ref_known(v_x_3611_, 1);
v___x_3626_ = lean_apply_1(v_h__3_3614_, v_k_3625_);
return v___x_3626_;
}
case 3:
{
lean_object* v_i_3627_; lean_object* v___x_3628_; 
lean_dec(v_h__9_3620_);
lean_dec(v_h__8_3619_);
lean_dec(v_h__7_3618_);
lean_dec(v_h__6_3617_);
lean_dec(v_h__5_3616_);
lean_dec(v_h__3_3614_);
lean_dec(v_h__2_3613_);
lean_dec(v_h__1_3612_);
v_i_3627_ = lean_ctor_get(v_x_3611_, 0);
lean_inc(v_i_3627_);
lean_dec_ref_known(v_x_3611_, 1);
v___x_3628_ = lean_apply_1(v_h__4_3615_, v_i_3627_);
return v___x_3628_;
}
case 4:
{
lean_object* v_a_3629_; lean_object* v___x_3630_; 
lean_dec(v_h__9_3620_);
lean_dec(v_h__8_3619_);
lean_dec(v_h__6_3617_);
lean_dec(v_h__5_3616_);
lean_dec(v_h__4_3615_);
lean_dec(v_h__3_3614_);
lean_dec(v_h__2_3613_);
lean_dec(v_h__1_3612_);
v_a_3629_ = lean_ctor_get(v_x_3611_, 0);
lean_inc_ref(v_a_3629_);
lean_dec_ref_known(v_x_3611_, 1);
v___x_3630_ = lean_apply_1(v_h__7_3618_, v_a_3629_);
return v___x_3630_;
}
case 5:
{
lean_object* v_a_3631_; lean_object* v_b_3632_; lean_object* v___x_3633_; 
lean_dec(v_h__9_3620_);
lean_dec(v_h__8_3619_);
lean_dec(v_h__7_3618_);
lean_dec(v_h__6_3617_);
lean_dec(v_h__4_3615_);
lean_dec(v_h__3_3614_);
lean_dec(v_h__2_3613_);
lean_dec(v_h__1_3612_);
v_a_3631_ = lean_ctor_get(v_x_3611_, 0);
lean_inc_ref(v_a_3631_);
v_b_3632_ = lean_ctor_get(v_x_3611_, 1);
lean_inc_ref(v_b_3632_);
lean_dec_ref_known(v_x_3611_, 2);
v___x_3633_ = lean_apply_2(v_h__5_3616_, v_a_3631_, v_b_3632_);
return v___x_3633_;
}
case 6:
{
lean_object* v_a_3634_; lean_object* v_b_3635_; lean_object* v___x_3636_; 
lean_dec(v_h__9_3620_);
lean_dec(v_h__7_3618_);
lean_dec(v_h__6_3617_);
lean_dec(v_h__5_3616_);
lean_dec(v_h__4_3615_);
lean_dec(v_h__3_3614_);
lean_dec(v_h__2_3613_);
lean_dec(v_h__1_3612_);
v_a_3634_ = lean_ctor_get(v_x_3611_, 0);
lean_inc_ref(v_a_3634_);
v_b_3635_ = lean_ctor_get(v_x_3611_, 1);
lean_inc_ref(v_b_3635_);
lean_dec_ref_known(v_x_3611_, 2);
v___x_3636_ = lean_apply_2(v_h__8_3619_, v_a_3634_, v_b_3635_);
return v___x_3636_;
}
case 7:
{
lean_object* v_a_3637_; lean_object* v_b_3638_; lean_object* v___x_3639_; 
lean_dec(v_h__9_3620_);
lean_dec(v_h__8_3619_);
lean_dec(v_h__7_3618_);
lean_dec(v_h__5_3616_);
lean_dec(v_h__4_3615_);
lean_dec(v_h__3_3614_);
lean_dec(v_h__2_3613_);
lean_dec(v_h__1_3612_);
v_a_3637_ = lean_ctor_get(v_x_3611_, 0);
lean_inc_ref(v_a_3637_);
v_b_3638_ = lean_ctor_get(v_x_3611_, 1);
lean_inc_ref(v_b_3638_);
lean_dec_ref_known(v_x_3611_, 2);
v___x_3639_ = lean_apply_2(v_h__6_3617_, v_a_3637_, v_b_3638_);
return v___x_3639_;
}
default: 
{
lean_object* v_a_3640_; lean_object* v_k_3641_; lean_object* v___x_3642_; 
lean_dec(v_h__8_3619_);
lean_dec(v_h__7_3618_);
lean_dec(v_h__6_3617_);
lean_dec(v_h__5_3616_);
lean_dec(v_h__4_3615_);
lean_dec(v_h__3_3614_);
lean_dec(v_h__2_3613_);
lean_dec(v_h__1_3612_);
v_a_3640_ = lean_ctor_get(v_x_3611_, 0);
lean_inc_ref(v_a_3640_);
v_k_3641_ = lean_ctor_get(v_x_3611_, 1);
lean_inc(v_k_3641_);
lean_dec_ref_known(v_x_3611_, 2);
v___x_3642_ = lean_apply_2(v_h__9_3620_, v_a_3640_, v_k_3641_);
return v___x_3642_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter___redArg(lean_object* v_a_3643_, lean_object* v_h__1_3644_, lean_object* v_h__2_3645_, lean_object* v_h__3_3646_){
_start:
{
switch(lean_obj_tag(v_a_3643_))
{
case 0:
{
lean_object* v_k_3647_; lean_object* v___x_3648_; 
lean_dec(v_h__3_3646_);
lean_dec(v_h__2_3645_);
v_k_3647_ = lean_ctor_get(v_a_3643_, 0);
lean_inc(v_k_3647_);
lean_dec_ref_known(v_a_3643_, 1);
v___x_3648_ = lean_apply_1(v_h__1_3644_, v_k_3647_);
return v___x_3648_;
}
case 3:
{
lean_object* v_i_3649_; lean_object* v___x_3650_; 
lean_dec(v_h__3_3646_);
lean_dec(v_h__1_3644_);
v_i_3649_ = lean_ctor_get(v_a_3643_, 0);
lean_inc(v_i_3649_);
lean_dec_ref_known(v_a_3643_, 1);
v___x_3650_ = lean_apply_1(v_h__2_3645_, v_i_3649_);
return v___x_3650_;
}
default: 
{
lean_object* v___x_3651_; 
lean_dec(v_h__2_3645_);
lean_dec(v_h__1_3644_);
v___x_3651_ = lean_apply_3(v_h__3_3646_, v_a_3643_, lean_box(0), lean_box(0));
return v___x_3651_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter(lean_object* v_motive_3652_, lean_object* v_a_3653_, lean_object* v_h__1_3654_, lean_object* v_h__2_3655_, lean_object* v_h__3_3656_){
_start:
{
switch(lean_obj_tag(v_a_3653_))
{
case 0:
{
lean_object* v_k_3657_; lean_object* v___x_3658_; 
lean_dec(v_h__3_3656_);
lean_dec(v_h__2_3655_);
v_k_3657_ = lean_ctor_get(v_a_3653_, 0);
lean_inc(v_k_3657_);
lean_dec_ref_known(v_a_3653_, 1);
v___x_3658_ = lean_apply_1(v_h__1_3654_, v_k_3657_);
return v___x_3658_;
}
case 3:
{
lean_object* v_i_3659_; lean_object* v___x_3660_; 
lean_dec(v_h__3_3656_);
lean_dec(v_h__1_3654_);
v_i_3659_ = lean_ctor_get(v_a_3653_, 0);
lean_inc(v_i_3659_);
lean_dec_ref_known(v_a_3653_, 1);
v___x_3660_ = lean_apply_1(v_h__2_3655_, v_i_3659_);
return v___x_3660_;
}
default: 
{
lean_object* v___x_3661_; 
lean_dec(v_h__2_3655_);
lean_dec(v_h__1_3654_);
v___x_3661_ = lean_apply_3(v_h__3_3656_, v_a_3653_, lean_box(0), lean_box(0));
return v___x_3661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(lean_object* v_inst_3662_, lean_object* v_ctx_3663_, lean_object* v_m_3664_, lean_object* v_acc_3665_){
_start:
{
if (lean_obj_tag(v_m_3664_) == 0)
{
lean_dec_ref(v_inst_3662_);
return v_acc_3665_;
}
else
{
lean_object* v_toSemiring_3666_; lean_object* v_toMul_3667_; lean_object* v_ofNat_3668_; lean_object* v_npow_3669_; lean_object* v_p_3670_; lean_object* v_m_3671_; lean_object* v___y_3673_; lean_object* v_x_3676_; lean_object* v_k_3677_; lean_object* v___x_3678_; uint8_t v___x_3679_; 
v_toSemiring_3666_ = lean_ctor_get(v_inst_3662_, 0);
v_toMul_3667_ = lean_ctor_get(v_toSemiring_3666_, 1);
v_ofNat_3668_ = lean_ctor_get(v_toSemiring_3666_, 3);
v_npow_3669_ = lean_ctor_get(v_toSemiring_3666_, 5);
v_p_3670_ = lean_ctor_get(v_m_3664_, 0);
lean_inc_ref(v_p_3670_);
v_m_3671_ = lean_ctor_get(v_m_3664_, 1);
lean_inc(v_m_3671_);
lean_dec_ref_known(v_m_3664_, 2);
v_x_3676_ = lean_ctor_get(v_p_3670_, 0);
lean_inc(v_x_3676_);
v_k_3677_ = lean_ctor_get(v_p_3670_, 1);
lean_inc(v_k_3677_);
lean_dec_ref(v_p_3670_);
v___x_3678_ = lean_unsigned_to_nat(0u);
v___x_3679_ = lean_nat_dec_eq(v_k_3677_, v___x_3678_);
if (v___x_3679_ == 0)
{
lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___x_3680_ = lean_unsigned_to_nat(1u);
v___x_3681_ = lean_nat_dec_eq(v_k_3677_, v___x_3680_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = l_Lean_RArray_getImpl___redArg(v_ctx_3663_, v_x_3676_);
lean_dec(v_x_3676_);
lean_inc(v_npow_3669_);
v___x_3683_ = lean_apply_2(v_npow_3669_, v___x_3682_, v_k_3677_);
v___y_3673_ = v___x_3683_;
goto v___jp_3672_;
}
else
{
lean_object* v___x_3684_; 
lean_dec(v_k_3677_);
v___x_3684_ = l_Lean_RArray_getImpl___redArg(v_ctx_3663_, v_x_3676_);
lean_dec(v_x_3676_);
v___y_3673_ = v___x_3684_;
goto v___jp_3672_;
}
}
else
{
lean_object* v___x_3685_; lean_object* v___x_3686_; 
lean_dec(v_k_3677_);
lean_dec(v_x_3676_);
v___x_3685_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3668_);
v___x_3686_ = lean_apply_1(v_ofNat_3668_, v___x_3685_);
v___y_3673_ = v___x_3686_;
goto v___jp_3672_;
}
v___jp_3672_:
{
lean_object* v___x_3674_; 
lean_inc(v_toMul_3667_);
v___x_3674_ = lean_apply_2(v_toMul_3667_, v_acc_3665_, v___y_3673_);
v_m_3664_ = v_m_3671_;
v_acc_3665_ = v___x_3674_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg___boxed(lean_object* v_inst_3687_, lean_object* v_ctx_3688_, lean_object* v_m_3689_, lean_object* v_acc_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3687_, v_ctx_3688_, v_m_3689_, v_acc_3690_);
lean_dec_ref(v_ctx_3688_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(lean_object* v_00_u03b1_3692_, lean_object* v_inst_3693_, lean_object* v_ctx_3694_, lean_object* v_m_3695_, lean_object* v_acc_3696_){
_start:
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3693_, v_ctx_3694_, v_m_3695_, v_acc_3696_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___boxed(lean_object* v_00_u03b1_3698_, lean_object* v_inst_3699_, lean_object* v_ctx_3700_, lean_object* v_m_3701_, lean_object* v_acc_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(v_00_u03b1_3698_, v_inst_3699_, v_ctx_3700_, v_m_3701_, v_acc_3702_);
lean_dec_ref(v_ctx_3700_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(lean_object* v_inst_3704_, lean_object* v_ctx_3705_, lean_object* v_m_3706_){
_start:
{
if (lean_obj_tag(v_m_3706_) == 0)
{
lean_object* v_toSemiring_3707_; lean_object* v_ofNat_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v_toSemiring_3707_ = lean_ctor_get(v_inst_3704_, 0);
lean_inc_ref(v_toSemiring_3707_);
lean_dec_ref(v_inst_3704_);
v_ofNat_3708_ = lean_ctor_get(v_toSemiring_3707_, 3);
lean_inc(v_ofNat_3708_);
lean_dec_ref(v_toSemiring_3707_);
v___x_3709_ = lean_unsigned_to_nat(1u);
v___x_3710_ = lean_apply_1(v_ofNat_3708_, v___x_3709_);
return v___x_3710_;
}
else
{
lean_object* v_toSemiring_3711_; lean_object* v_p_3712_; lean_object* v_m_3713_; lean_object* v_ofNat_3714_; lean_object* v_npow_3715_; lean_object* v_x_3716_; lean_object* v_k_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v_toSemiring_3711_ = lean_ctor_get(v_inst_3704_, 0);
v_p_3712_ = lean_ctor_get(v_m_3706_, 0);
lean_inc_ref(v_p_3712_);
v_m_3713_ = lean_ctor_get(v_m_3706_, 1);
lean_inc(v_m_3713_);
lean_dec_ref_known(v_m_3706_, 2);
v_ofNat_3714_ = lean_ctor_get(v_toSemiring_3711_, 3);
v_npow_3715_ = lean_ctor_get(v_toSemiring_3711_, 5);
v_x_3716_ = lean_ctor_get(v_p_3712_, 0);
lean_inc(v_x_3716_);
v_k_3717_ = lean_ctor_get(v_p_3712_, 1);
lean_inc(v_k_3717_);
lean_dec_ref(v_p_3712_);
v___x_3718_ = lean_unsigned_to_nat(0u);
v___x_3719_ = lean_nat_dec_eq(v_k_3717_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; uint8_t v___x_3721_; 
v___x_3720_ = lean_unsigned_to_nat(1u);
v___x_3721_ = lean_nat_dec_eq(v_k_3717_, v___x_3720_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3722_ = l_Lean_RArray_getImpl___redArg(v_ctx_3705_, v_x_3716_);
lean_dec(v_x_3716_);
lean_inc(v_npow_3715_);
v___x_3723_ = lean_apply_2(v_npow_3715_, v___x_3722_, v_k_3717_);
v___x_3724_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3704_, v_ctx_3705_, v_m_3713_, v___x_3723_);
return v___x_3724_;
}
else
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
lean_dec(v_k_3717_);
v___x_3725_ = l_Lean_RArray_getImpl___redArg(v_ctx_3705_, v_x_3716_);
lean_dec(v_x_3716_);
v___x_3726_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3704_, v_ctx_3705_, v_m_3713_, v___x_3725_);
return v___x_3726_;
}
}
else
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
lean_dec(v_k_3717_);
lean_dec(v_x_3716_);
v___x_3727_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3714_);
v___x_3728_ = lean_apply_1(v_ofNat_3714_, v___x_3727_);
v___x_3729_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3704_, v_ctx_3705_, v_m_3713_, v___x_3728_);
return v___x_3729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3730_, lean_object* v_ctx_3731_, lean_object* v_m_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3730_, v_ctx_3731_, v_m_3732_);
lean_dec_ref(v_ctx_3731_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule(lean_object* v_00_u03b1_3734_, lean_object* v_inst_3735_, lean_object* v_ctx_3736_, lean_object* v_m_3737_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3735_, v_ctx_3736_, v_m_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3739_, lean_object* v_inst_3740_, lean_object* v_ctx_3741_, lean_object* v_m_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule(v_00_u03b1_3739_, v_inst_3740_, v_ctx_3741_, v_m_3742_);
lean_dec_ref(v_ctx_3741_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(lean_object* v_inst_3744_, lean_object* v_ctx_3745_, lean_object* v_p_3746_){
_start:
{
lean_object* v___x_3747_; 
lean_inc_ref(v_inst_3744_);
v___x_3747_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_3744_);
if (lean_obj_tag(v_p_3746_) == 0)
{
lean_object* v_toSemiring_3748_; lean_object* v_zsmul_3749_; lean_object* v_ofNat_3750_; lean_object* v_k_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v_toSemiring_3748_ = lean_ctor_get(v_inst_3744_, 0);
lean_inc_ref(v_toSemiring_3748_);
lean_dec_ref(v_inst_3744_);
v_zsmul_3749_ = lean_ctor_get(v___x_3747_, 2);
lean_inc(v_zsmul_3749_);
lean_dec_ref(v___x_3747_);
v_ofNat_3750_ = lean_ctor_get(v_toSemiring_3748_, 3);
lean_inc(v_ofNat_3750_);
lean_dec_ref(v_toSemiring_3748_);
v_k_3751_ = lean_ctor_get(v_p_3746_, 0);
lean_inc(v_k_3751_);
lean_dec_ref_known(v_p_3746_, 1);
v___x_3752_ = lean_unsigned_to_nat(1u);
v___x_3753_ = lean_apply_1(v_ofNat_3750_, v___x_3752_);
v___x_3754_ = lean_apply_2(v_zsmul_3749_, v_k_3751_, v___x_3753_);
return v___x_3754_;
}
else
{
lean_object* v_toSemiring_3755_; lean_object* v_zsmul_3756_; lean_object* v_toAdd_3757_; lean_object* v_k_3758_; lean_object* v_v_3759_; lean_object* v_p_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_toSemiring_3755_ = lean_ctor_get(v_inst_3744_, 0);
v_zsmul_3756_ = lean_ctor_get(v___x_3747_, 2);
lean_inc(v_zsmul_3756_);
lean_dec_ref(v___x_3747_);
v_toAdd_3757_ = lean_ctor_get(v_toSemiring_3755_, 0);
lean_inc(v_toAdd_3757_);
v_k_3758_ = lean_ctor_get(v_p_3746_, 0);
lean_inc(v_k_3758_);
v_v_3759_ = lean_ctor_get(v_p_3746_, 1);
lean_inc(v_v_3759_);
v_p_3760_ = lean_ctor_get(v_p_3746_, 2);
lean_inc_ref(v_p_3760_);
lean_dec_ref_known(v_p_3746_, 3);
lean_inc_ref(v_inst_3744_);
v___x_3761_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3744_, v_ctx_3745_, v_v_3759_);
v___x_3762_ = lean_apply_2(v_zsmul_3756_, v_k_3758_, v___x_3761_);
v___x_3763_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3744_, v_ctx_3745_, v_p_3760_);
v___x_3764_ = lean_apply_2(v_toAdd_3757_, v___x_3762_, v___x_3763_);
return v___x_3764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3765_, lean_object* v_ctx_3766_, lean_object* v_p_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3765_, v_ctx_3766_, v_p_3767_);
lean_dec_ref(v_ctx_3766_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule(lean_object* v_00_u03b1_3769_, lean_object* v_inst_3770_, lean_object* v_ctx_3771_, lean_object* v_p_3772_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3770_, v_ctx_3771_, v_p_3772_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3774_, lean_object* v_inst_3775_, lean_object* v_ctx_3776_, lean_object* v_p_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule(v_00_u03b1_3774_, v_inst_3775_, v_ctx_3776_, v_p_3777_);
lean_dec_ref(v_ctx_3776_);
return v_res_3778_;
}
}
uint8_t l_Lean_Grind_CommRing_eq__gcd__cert(lean_object* v_a_3779_, lean_object* v_b_3780_, lean_object* v_p_u2081_3781_, lean_object* v_p_u2082_3782_, lean_object* v_p_3783_){
_start:
{
if (lean_obj_tag(v_p_u2081_3781_) == 0)
{
if (lean_obj_tag(v_p_u2082_3782_) == 0)
{
if (lean_obj_tag(v_p_3783_) == 0)
{
lean_object* v_k_3784_; lean_object* v_k_3785_; lean_object* v_k_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; 
v_k_3784_ = lean_ctor_get(v_p_u2081_3781_, 0);
v_k_3785_ = lean_ctor_get(v_p_u2082_3782_, 0);
v_k_3786_ = lean_ctor_get(v_p_3783_, 0);
v___x_3787_ = lean_int_mul(v_a_3779_, v_k_3784_);
v___x_3788_ = lean_int_mul(v_b_3780_, v_k_3785_);
v___x_3789_ = lean_int_add(v___x_3787_, v___x_3788_);
lean_dec(v___x_3788_);
lean_dec(v___x_3787_);
v___x_3790_ = lean_int_dec_eq(v_k_3786_, v___x_3789_);
lean_dec(v___x_3789_);
return v___x_3790_;
}
else
{
uint8_t v___x_3791_; 
v___x_3791_ = 0;
return v___x_3791_;
}
}
else
{
uint8_t v___x_3792_; 
v___x_3792_ = 0;
return v___x_3792_;
}
}
else
{
uint8_t v___x_3793_; 
v___x_3793_ = 0;
return v___x_3793_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_eq__gcd__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3779_ = stack[0].m_obj;
lean_object* v_b_3780_ = stack[1].m_obj;
lean_object* v_p_u2081_3781_ = stack[2].m_obj;
lean_object* v_p_u2082_3782_ = stack[3].m_obj;
lean_object* v_p_3783_ = stack[4].m_obj;
uint8_t v_res_3794_;
v_res_3794_ = l_Lean_Grind_CommRing_eq__gcd__cert(v_a_3779_, v_b_3780_, v_p_u2081_3781_, v_p_u2082_3782_, v_p_3783_);
stack->m_num = v_res_3794_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__gcd__cert___boxed(lean_object* v_a_3795_, lean_object* v_b_3796_, lean_object* v_p_u2081_3797_, lean_object* v_p_u2082_3798_, lean_object* v_p_3799_){
_start:
{
uint8_t v_res_3800_; lean_object* v_r_3801_; 
v_res_3800_ = l_Lean_Grind_CommRing_eq__gcd__cert(v_a_3795_, v_b_3796_, v_p_u2081_3797_, v_p_u2082_3798_, v_p_3799_);
lean_dec_ref(v_p_3799_);
lean_dec_ref(v_p_u2082_3798_);
lean_dec_ref(v_p_u2081_3797_);
lean_dec(v_b_3796_);
lean_dec(v_a_3795_);
v_r_3801_ = lean_box(v_res_3800_);
return v_r_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(lean_object* v_p_3802_, lean_object* v_h__1_3803_, lean_object* v_h__2_3804_){
_start:
{
if (lean_obj_tag(v_p_3802_) == 0)
{
lean_object* v_k_3805_; lean_object* v___x_3806_; 
lean_dec(v_h__1_3803_);
v_k_3805_ = lean_ctor_get(v_p_3802_, 0);
lean_inc(v_k_3805_);
lean_dec_ref_known(v_p_3802_, 1);
v___x_3806_ = lean_apply_1(v_h__2_3804_, v_k_3805_);
return v___x_3806_;
}
else
{
lean_object* v_k_3807_; lean_object* v_v_3808_; lean_object* v_p_3809_; lean_object* v___x_3810_; 
lean_dec(v_h__2_3804_);
v_k_3807_ = lean_ctor_get(v_p_3802_, 0);
lean_inc(v_k_3807_);
v_v_3808_ = lean_ctor_get(v_p_3802_, 1);
lean_inc(v_v_3808_);
v_p_3809_ = lean_ctor_get(v_p_3802_, 2);
lean_inc_ref(v_p_3809_);
lean_dec_ref_known(v_p_3802_, 3);
v___x_3810_ = lean_apply_3(v_h__1_3803_, v_k_3807_, v_v_3808_, v_p_3809_);
return v___x_3810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter(lean_object* v_motive_3811_, lean_object* v_p_3812_, lean_object* v_h__1_3813_, lean_object* v_h__2_3814_){
_start:
{
if (lean_obj_tag(v_p_3812_) == 0)
{
lean_object* v_k_3815_; lean_object* v___x_3816_; 
lean_dec(v_h__1_3813_);
v_k_3815_ = lean_ctor_get(v_p_3812_, 0);
lean_inc(v_k_3815_);
lean_dec_ref_known(v_p_3812_, 1);
v___x_3816_ = lean_apply_1(v_h__2_3814_, v_k_3815_);
return v___x_3816_;
}
else
{
lean_object* v_k_3817_; lean_object* v_v_3818_; lean_object* v_p_3819_; lean_object* v___x_3820_; 
lean_dec(v_h__2_3814_);
v_k_3817_ = lean_ctor_get(v_p_3812_, 0);
lean_inc(v_k_3817_);
v_v_3818_ = lean_ctor_get(v_p_3812_, 1);
lean_inc(v_v_3818_);
v_p_3819_ = lean_ctor_get(v_p_3812_, 2);
lean_inc_ref(v_p_3819_);
lean_dec_ref_known(v_p_3812_, 3);
v___x_3820_ = lean_apply_3(v_h__1_3813_, v_k_3817_, v_v_3818_, v_p_3819_);
return v___x_3820_;
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
