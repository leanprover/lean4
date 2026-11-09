// Lean compiler output
// Module: Init.Grind.Ring.CommSolver
// Imports: public import Init.Data.Ord.Basic public import Init.Grind.Ring.Field public import Init.Grind.Ordered.Ring public import Init.GrindInstances.Ring.Int import all Init.Data.Ord.Basic import Init.LawfulBEqTactics public import Init.Classical public import Init.Data.Bool public import Init.Data.Int.DivMod.Lemmas public import Init.Data.Int.Kernel public import Init.Data.RArray public import Init.Ext import Init.Data.Hashable import Init.Data.Int.LemmasAux import Init.Data.Nat.Internal.Linear import Init.Grind.Ordered.Order import Init.Omega import Init.WFTactics import Init.Data.Int.Repr public import Init.Data.Nat.Gcd
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul__nc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_toExpr_go(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Mon_toExpr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr_goTerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteList___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denoteList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denoteList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
v___y_320_ = v___y_333_;
v___y_321_ = v___x_334_;
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
v___y_320_ = v___y_333_;
v___y_321_ = v___x_334_;
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
lean_inc(v___y_321_);
v___x_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_323_, 0, v___y_321_);
lean_ctor_set(v___x_323_, 1, v___y_322_);
lean_inc(v___y_320_);
v___x_324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_324_, 0, v___y_320_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go(lean_object* v_fuel_1114_, lean_object* v_m_u2081_1115_, lean_object* v_m_u2082_1116_){
_start:
{
lean_object* v_zero_1117_; uint8_t v_isZero_1118_; 
v_zero_1117_ = lean_unsigned_to_nat(0u);
v_isZero_1118_ = lean_nat_dec_eq(v_fuel_1114_, v_zero_1117_);
if (v_isZero_1118_ == 1)
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_1115_, v_m_u2082_1116_);
lean_dec(v_m_u2082_1116_);
return v___x_1119_;
}
else
{
if (lean_obj_tag(v_m_u2082_1116_) == 0)
{
return v_m_u2081_1115_;
}
else
{
if (lean_obj_tag(v_m_u2081_1115_) == 0)
{
return v_m_u2082_1116_;
}
else
{
lean_object* v_p_1120_; lean_object* v_m_1121_; lean_object* v_p_1122_; lean_object* v_m_1123_; lean_object* v_one_1124_; lean_object* v_n_1125_; uint8_t v___x_1126_; 
v_p_1120_ = lean_ctor_get(v_m_u2082_1116_, 0);
lean_inc_ref(v_p_1120_);
v_m_1121_ = lean_ctor_get(v_m_u2082_1116_, 1);
v_p_1122_ = lean_ctor_get(v_m_u2081_1115_, 0);
v_m_1123_ = lean_ctor_get(v_m_u2081_1115_, 1);
v_one_1124_ = lean_unsigned_to_nat(1u);
v_n_1125_ = lean_nat_sub(v_fuel_1114_, v_one_1124_);
v___x_1126_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1122_, v_p_1120_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1157_; 
lean_inc(v_m_1121_);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_m_u2082_1116_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; lean_object* v_unused_1159_; 
v_unused_1158_ = lean_ctor_get(v_m_u2082_1116_, 1);
lean_dec(v_unused_1158_);
v_unused_1159_ = lean_ctor_get(v_m_u2082_1116_, 0);
lean_dec(v_unused_1159_);
v___x_1128_ = v_m_u2082_1116_;
v_isShared_1129_ = v_isSharedCheck_1157_;
goto v_resetjp_1127_;
}
else
{
lean_dec(v_m_u2082_1116_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1157_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
uint8_t v___x_1130_; 
v___x_1130_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1120_, v_p_1122_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1150_; 
lean_inc(v_m_1123_);
lean_inc_ref(v_p_1122_);
lean_del_object(v___x_1128_);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_m_u2081_1115_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; lean_object* v_unused_1152_; 
v_unused_1151_ = lean_ctor_get(v_m_u2081_1115_, 1);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_m_u2081_1115_, 0);
lean_dec(v_unused_1152_);
v___x_1132_ = v_m_u2081_1115_;
v_isShared_1133_ = v_isSharedCheck_1150_;
goto v_resetjp_1131_;
}
else
{
lean_dec(v_m_u2081_1115_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1150_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_x_1134_; lean_object* v_k_1135_; lean_object* v_k_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1148_; 
v_x_1134_ = lean_ctor_get(v_p_1122_, 0);
lean_inc(v_x_1134_);
v_k_1135_ = lean_ctor_get(v_p_1122_, 1);
lean_inc(v_k_1135_);
lean_dec_ref(v_p_1122_);
v_k_1136_ = lean_ctor_get(v_p_1120_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_p_1120_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v_p_1120_, 0);
lean_dec(v_unused_1149_);
v___x_1138_ = v_p_1120_;
v_isShared_1139_ = v_isSharedCheck_1148_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_k_1136_);
lean_dec(v_p_1120_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1148_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = lean_nat_add(v_k_1135_, v_k_1136_);
lean_dec(v_k_1136_);
lean_dec(v_k_1135_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1140_);
lean_ctor_set(v___x_1138_, 0, v_x_1134_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_x_1134_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1125_, v_m_1123_, v_m_1121_);
lean_dec(v_n_1125_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v___x_1143_);
lean_ctor_set(v___x_1132_, 0, v___x_1142_);
v___x_1145_ = v___x_1132_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1125_, v_m_u2081_1115_, v_m_1121_);
lean_dec(v_n_1125_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 1, v___x_1153_);
v___x_1155_ = v___x_1128_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_p_1120_);
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
else
{
lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1167_; 
lean_inc(v_m_1123_);
lean_inc_ref(v_p_1122_);
lean_dec_ref(v_p_1120_);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_m_u2081_1115_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; lean_object* v_unused_1169_; 
v_unused_1168_ = lean_ctor_get(v_m_u2081_1115_, 1);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_m_u2081_1115_, 0);
lean_dec(v_unused_1169_);
v___x_1161_ = v_m_u2081_1115_;
v_isShared_1162_ = v_isSharedCheck_1167_;
goto v_resetjp_1160_;
}
else
{
lean_dec(v_m_u2081_1115_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1167_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1163_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1125_, v_m_1123_, v_m_u2082_1116_);
lean_dec(v_n_1125_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1163_);
v___x_1165_ = v___x_1161_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_p_1122_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go___boxed(lean_object* v_fuel_1170_, lean_object* v_m_u2081_1171_, lean_object* v_m_u2082_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Grind_CommRing_Mon_mul_go(v_fuel_1170_, v_m_u2081_1171_, v_m_u2082_1172_);
lean_dec(v_fuel_1170_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul(lean_object* v_m_u2081_1174_, lean_object* v_m_u2082_1175_){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1176_ = l_Lean_Grind_CommRing_Mon_length(v_m_u2081_1174_);
v___x_1177_ = l_Lean_Grind_CommRing_Mon_length(v_m_u2082_1175_);
v___x_1178_ = lean_nat_add(v___x_1176_, v___x_1177_);
lean_dec(v___x_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_unsigned_to_nat(1u);
v___x_1180_ = lean_nat_add(v___x_1178_, v___x_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = l_Lean_Grind_CommRing_Mon_mul_go(v___x_1180_, v_m_u2081_1174_, v_m_u2082_1175_);
lean_dec(v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object* v_x_1182_, lean_object* v_h__1_1183_, lean_object* v_h__2_1184_){
_start:
{
if (lean_obj_tag(v_x_1182_) == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v_h__2_1184_);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_apply_1(v_h__1_1183_, v___x_1185_);
return v___x_1186_;
}
else
{
lean_object* v_p_1187_; lean_object* v_m_1188_; lean_object* v___x_1189_; 
lean_dec(v_h__1_1183_);
v_p_1187_ = lean_ctor_get(v_x_1182_, 0);
lean_inc_ref(v_p_1187_);
v_m_1188_ = lean_ctor_get(v_x_1182_, 1);
lean_inc(v_m_1188_);
lean_dec_ref_known(v_x_1182_, 2);
v___x_1189_ = lean_apply_2(v_h__2_1184_, v_p_1187_, v_m_1188_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object* v_motive_1190_, lean_object* v_x_1191_, lean_object* v_h__1_1192_, lean_object* v_h__2_1193_){
_start:
{
if (lean_obj_tag(v_x_1191_) == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec(v_h__2_1193_);
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_apply_1(v_h__1_1192_, v___x_1194_);
return v___x_1195_;
}
else
{
lean_object* v_p_1196_; lean_object* v_m_1197_; lean_object* v___x_1198_; 
lean_dec(v_h__1_1192_);
v_p_1196_ = lean_ctor_get(v_x_1191_, 0);
lean_inc_ref(v_p_1196_);
v_m_1197_ = lean_ctor_get(v_x_1191_, 1);
lean_inc(v_m_1197_);
lean_dec_ref_known(v_x_1191_, 2);
v___x_1198_ = lean_apply_2(v_h__2_1193_, v_p_1196_, v_m_1197_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object* v_fuel_1199_, lean_object* v_h__1_1200_, lean_object* v_h__2_1201_){
_start:
{
lean_object* v_zero_1202_; uint8_t v_isZero_1203_; 
v_zero_1202_ = lean_unsigned_to_nat(0u);
v_isZero_1203_ = lean_nat_dec_eq(v_fuel_1199_, v_zero_1202_);
if (v_isZero_1203_ == 1)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec(v_h__2_1201_);
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_apply_1(v_h__1_1200_, v___x_1204_);
return v___x_1205_;
}
else
{
lean_object* v_one_1206_; lean_object* v_n_1207_; lean_object* v___x_1208_; 
lean_dec(v_h__1_1200_);
v_one_1206_ = lean_unsigned_to_nat(1u);
v_n_1207_ = lean_nat_sub(v_fuel_1199_, v_one_1206_);
v___x_1208_ = lean_apply_1(v_h__2_1201_, v_n_1207_);
return v___x_1208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object* v_fuel_1209_, lean_object* v_h__1_1210_, lean_object* v_h__2_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(v_fuel_1209_, v_h__1_1210_, v_h__2_1211_);
lean_dec(v_fuel_1209_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object* v_motive_1213_, lean_object* v_fuel_1214_, lean_object* v_h__1_1215_, lean_object* v_h__2_1216_){
_start:
{
lean_object* v_zero_1217_; uint8_t v_isZero_1218_; 
v_zero_1217_ = lean_unsigned_to_nat(0u);
v_isZero_1218_ = lean_nat_dec_eq(v_fuel_1214_, v_zero_1217_);
if (v_isZero_1218_ == 1)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec(v_h__2_1216_);
v___x_1219_ = lean_box(0);
v___x_1220_ = lean_apply_1(v_h__1_1215_, v___x_1219_);
return v___x_1220_;
}
else
{
lean_object* v_one_1221_; lean_object* v_n_1222_; lean_object* v___x_1223_; 
lean_dec(v_h__1_1215_);
v_one_1221_ = lean_unsigned_to_nat(1u);
v_n_1222_ = lean_nat_sub(v_fuel_1214_, v_one_1221_);
v___x_1223_ = lean_apply_1(v_h__2_1216_, v_n_1222_);
return v___x_1223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object* v_motive_1224_, lean_object* v_fuel_1225_, lean_object* v_h__1_1226_, lean_object* v_h__2_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(v_motive_1224_, v_fuel_1225_, v_h__1_1226_, v_h__2_1227_);
lean_dec(v_fuel_1225_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter___redArg(lean_object* v_m_u2081_1229_, lean_object* v_m_u2082_1230_, lean_object* v_h__1_1231_, lean_object* v_h__2_1232_, lean_object* v_h__3_1233_){
_start:
{
if (lean_obj_tag(v_m_u2082_1230_) == 0)
{
lean_object* v___x_1234_; 
lean_dec(v_h__3_1233_);
lean_dec(v_h__2_1232_);
v___x_1234_ = lean_apply_1(v_h__1_1231_, v_m_u2081_1229_);
return v___x_1234_;
}
else
{
lean_dec(v_h__1_1231_);
if (lean_obj_tag(v_m_u2081_1229_) == 0)
{
lean_object* v___x_1235_; 
lean_dec(v_h__3_1233_);
v___x_1235_ = lean_apply_2(v_h__2_1232_, v_m_u2082_1230_, lean_box(0));
return v___x_1235_;
}
else
{
lean_object* v_p_1236_; lean_object* v_m_1237_; lean_object* v_p_1238_; lean_object* v_m_1239_; lean_object* v___x_1240_; 
lean_dec(v_h__2_1232_);
v_p_1236_ = lean_ctor_get(v_m_u2082_1230_, 0);
lean_inc_ref(v_p_1236_);
v_m_1237_ = lean_ctor_get(v_m_u2082_1230_, 1);
lean_inc(v_m_1237_);
lean_dec_ref_known(v_m_u2082_1230_, 2);
v_p_1238_ = lean_ctor_get(v_m_u2081_1229_, 0);
lean_inc_ref(v_p_1238_);
v_m_1239_ = lean_ctor_get(v_m_u2081_1229_, 1);
lean_inc(v_m_1239_);
lean_dec_ref_known(v_m_u2081_1229_, 2);
v___x_1240_ = lean_apply_4(v_h__3_1233_, v_p_1238_, v_m_1239_, v_p_1236_, v_m_1237_);
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter(lean_object* v_motive_1241_, lean_object* v_m_u2081_1242_, lean_object* v_m_u2082_1243_, lean_object* v_h__1_1244_, lean_object* v_h__2_1245_, lean_object* v_h__3_1246_){
_start:
{
if (lean_obj_tag(v_m_u2082_1243_) == 0)
{
lean_object* v___x_1247_; 
lean_dec(v_h__3_1246_);
lean_dec(v_h__2_1245_);
v___x_1247_ = lean_apply_1(v_h__1_1244_, v_m_u2081_1242_);
return v___x_1247_;
}
else
{
lean_dec(v_h__1_1244_);
if (lean_obj_tag(v_m_u2081_1242_) == 0)
{
lean_object* v___x_1248_; 
lean_dec(v_h__3_1246_);
v___x_1248_ = lean_apply_2(v_h__2_1245_, v_m_u2082_1243_, lean_box(0));
return v___x_1248_;
}
else
{
lean_object* v_p_1249_; lean_object* v_m_1250_; lean_object* v_p_1251_; lean_object* v_m_1252_; lean_object* v___x_1253_; 
lean_dec(v_h__2_1245_);
v_p_1249_ = lean_ctor_get(v_m_u2082_1243_, 0);
lean_inc_ref(v_p_1249_);
v_m_1250_ = lean_ctor_get(v_m_u2082_1243_, 1);
lean_inc(v_m_1250_);
lean_dec_ref_known(v_m_u2082_1243_, 2);
v_p_1251_ = lean_ctor_get(v_m_u2081_1242_, 0);
lean_inc_ref(v_p_1251_);
v_m_1252_ = lean_ctor_get(v_m_u2081_1242_, 1);
lean_inc(v_m_1252_);
lean_dec_ref_known(v_m_u2081_1242_, 2);
v___x_1253_ = lean_apply_4(v_h__3_1246_, v_p_1251_, v_m_1252_, v_p_1249_, v_m_1250_);
return v___x_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul__nc(lean_object* v_m_u2081_1254_, lean_object* v_m_u2082_1255_){
_start:
{
if (lean_obj_tag(v_m_u2081_1254_) == 0)
{
return v_m_u2082_1255_;
}
else
{
lean_object* v_m_1256_; 
v_m_1256_ = lean_ctor_get(v_m_u2081_1254_, 1);
if (lean_obj_tag(v_m_1256_) == 0)
{
lean_object* v_p_1257_; lean_object* v___x_1258_; 
v_p_1257_ = lean_ctor_get(v_m_u2081_1254_, 0);
lean_inc_ref(v_p_1257_);
lean_dec_ref_known(v_m_u2081_1254_, 2);
v___x_1258_ = l_Lean_Grind_CommRing_Mon_mulPow__nc(v_p_1257_, v_m_u2082_1255_);
return v___x_1258_;
}
else
{
lean_object* v_p_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1267_; 
lean_inc(v_m_1256_);
v_p_1259_ = lean_ctor_get(v_m_u2081_1254_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_m_u2081_1254_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v_m_u2081_1254_, 1);
lean_dec(v_unused_1268_);
v___x_1261_ = v_m_u2081_1254_;
v_isShared_1262_ = v_isSharedCheck_1267_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_p_1259_);
lean_dec(v_m_u2081_1254_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1267_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_1256_, v_m_u2082_1255_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___x_1263_);
v___x_1265_ = v___x_1261_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_p_1259_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object* v_x_1269_){
_start:
{
if (lean_obj_tag(v_x_1269_) == 0)
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_unsigned_to_nat(0u);
return v___x_1270_;
}
else
{
lean_object* v_p_1271_; lean_object* v_m_1272_; lean_object* v_k_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_p_1271_ = lean_ctor_get(v_x_1269_, 0);
v_m_1272_ = lean_ctor_get(v_x_1269_, 1);
v_k_1273_ = lean_ctor_get(v_p_1271_, 1);
v___x_1274_ = l_Lean_Grind_CommRing_Mon_degree(v_m_1272_);
v___x_1275_ = lean_nat_add(v_k_1273_, v___x_1274_);
lean_dec(v___x_1274_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree___boxed(lean_object* v_x_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Grind_CommRing_Mon_degree(v_x_1276_);
lean_dec(v_x_1276_);
return v_res_1277_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Var_revlex(lean_object* v_x_1278_, lean_object* v_y_1279_){
_start:
{
uint8_t v___x_1280_; 
v___x_1280_ = l_Nat_blt(v_x_1278_, v_y_1279_);
if (v___x_1280_ == 0)
{
uint8_t v___x_1281_; 
v___x_1281_ = l_Nat_blt(v_y_1279_, v_x_1278_);
if (v___x_1281_ == 0)
{
uint8_t v___x_1282_; 
v___x_1282_ = 1;
return v___x_1282_;
}
else
{
uint8_t v___x_1283_; 
v___x_1283_ = 0;
return v___x_1283_;
}
}
else
{
uint8_t v___x_1284_; 
v___x_1284_ = 2;
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_revlex___boxed(lean_object* v_x_1285_, lean_object* v_y_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1285_, v_y_1286_);
lean_dec(v_y_1286_);
lean_dec(v_x_1285_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_powerRevlex(lean_object* v_k_u2081_1289_, lean_object* v_k_u2082_1290_){
_start:
{
uint8_t v___x_1291_; 
v___x_1291_ = l_Nat_blt(v_k_u2081_1289_, v_k_u2082_1290_);
if (v___x_1291_ == 0)
{
uint8_t v___x_1292_; 
v___x_1292_ = l_Nat_blt(v_k_u2082_1290_, v_k_u2081_1289_);
if (v___x_1292_ == 0)
{
uint8_t v___x_1293_; 
v___x_1293_ = 1;
return v___x_1293_;
}
else
{
uint8_t v___x_1294_; 
v___x_1294_ = 0;
return v___x_1294_;
}
}
else
{
uint8_t v___x_1295_; 
v___x_1295_ = 2;
return v___x_1295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_powerRevlex___boxed(lean_object* v_k_u2081_1296_, lean_object* v_k_u2082_1297_){
_start:
{
uint8_t v_res_1298_; lean_object* v_r_1299_; 
v_res_1298_ = l_Lean_Grind_CommRing_powerRevlex(v_k_u2081_1296_, v_k_u2082_1297_);
lean_dec(v_k_u2082_1297_);
lean_dec(v_k_u2081_1296_);
v_r_1299_ = lean_box(v_res_1298_);
return v_r_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(uint8_t v_c_1300_, lean_object* v_h__1_1301_, lean_object* v_h__2_1302_){
_start:
{
if (v_c_1300_ == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec(v_h__1_1301_);
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_apply_1(v_h__2_1302_, v___x_1303_);
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec(v_h__2_1302_);
v___x_1305_ = lean_box(0);
v___x_1306_ = lean_apply_1(v_h__1_1301_, v___x_1305_);
return v___x_1306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg___boxed(lean_object* v_c_1307_, lean_object* v_h__1_1308_, lean_object* v_h__2_1309_){
_start:
{
uint8_t v_c_24__boxed_1310_; lean_object* v_res_1311_; 
v_c_24__boxed_1310_ = lean_unbox(v_c_1307_);
v_res_1311_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(v_c_24__boxed_1310_, v_h__1_1308_, v_h__2_1309_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(lean_object* v_motive_1312_, uint8_t v_c_1313_, lean_object* v_h__1_1314_, lean_object* v_h__2_1315_){
_start:
{
if (v_c_1313_ == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec(v_h__1_1314_);
v___x_1316_ = lean_box(0);
v___x_1317_ = lean_apply_1(v_h__2_1315_, v___x_1316_);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec(v_h__2_1315_);
v___x_1318_ = lean_box(0);
v___x_1319_ = lean_apply_1(v_h__1_1314_, v___x_1318_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___boxed(lean_object* v_motive_1320_, lean_object* v_c_1321_, lean_object* v_h__1_1322_, lean_object* v_h__2_1323_){
_start:
{
uint8_t v_c_35__boxed_1324_; lean_object* v_res_1325_; 
v_c_35__boxed_1324_ = lean_unbox(v_c_1321_);
v_res_1325_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(v_motive_1320_, v_c_35__boxed_1324_, v_h__1_1322_, v_h__2_1323_);
return v_res_1325_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_revlex(lean_object* v_p_u2081_1326_, lean_object* v_p_u2082_1327_){
_start:
{
lean_object* v_x_1328_; lean_object* v_k_1329_; lean_object* v_x_1330_; lean_object* v_k_1331_; uint8_t v___x_1332_; 
v_x_1328_ = lean_ctor_get(v_p_u2081_1326_, 0);
v_k_1329_ = lean_ctor_get(v_p_u2081_1326_, 1);
v_x_1330_ = lean_ctor_get(v_p_u2082_1327_, 0);
v_k_1331_ = lean_ctor_get(v_p_u2082_1327_, 1);
v___x_1332_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1328_, v_x_1330_);
if (v___x_1332_ == 1)
{
uint8_t v___x_1333_; 
v___x_1333_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1329_, v_k_1331_);
return v___x_1333_;
}
else
{
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_revlex___boxed(lean_object* v_p_u2081_1334_, lean_object* v_p_u2082_1335_){
_start:
{
uint8_t v_res_1336_; lean_object* v_r_1337_; 
v_res_1336_ = l_Lean_Grind_CommRing_Power_revlex(v_p_u2081_1334_, v_p_u2082_1335_);
lean_dec_ref(v_p_u2082_1335_);
lean_dec_ref(v_p_u2081_1334_);
v_r_1337_ = lean_box(v_res_1336_);
return v_r_1337_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexWF(lean_object* v_m_u2081_1338_, lean_object* v_m_u2082_1339_){
_start:
{
if (lean_obj_tag(v_m_u2081_1338_) == 0)
{
if (lean_obj_tag(v_m_u2082_1339_) == 0)
{
uint8_t v___x_1340_; 
v___x_1340_ = 1;
return v___x_1340_;
}
else
{
uint8_t v___x_1341_; 
v___x_1341_ = 2;
return v___x_1341_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1339_) == 0)
{
uint8_t v___x_1342_; 
v___x_1342_ = 0;
return v___x_1342_;
}
else
{
lean_object* v_p_1343_; lean_object* v_p_1344_; lean_object* v_m_1345_; lean_object* v_m_1346_; lean_object* v_x_1347_; lean_object* v_k_1348_; lean_object* v_x_1349_; lean_object* v_k_1350_; uint8_t v___x_1351_; 
v_p_1343_ = lean_ctor_get(v_m_u2081_1338_, 0);
v_p_1344_ = lean_ctor_get(v_m_u2082_1339_, 0);
v_m_1345_ = lean_ctor_get(v_m_u2081_1338_, 1);
v_m_1346_ = lean_ctor_get(v_m_u2082_1339_, 1);
v_x_1347_ = lean_ctor_get(v_p_1343_, 0);
v_k_1348_ = lean_ctor_get(v_p_1343_, 1);
v_x_1349_ = lean_ctor_get(v_p_1344_, 0);
v_k_1350_ = lean_ctor_get(v_p_1344_, 1);
v___x_1351_ = lean_nat_dec_eq(v_x_1347_, v_x_1349_);
if (v___x_1351_ == 0)
{
uint8_t v___x_1352_; 
v___x_1352_ = l_Nat_blt(v_x_1347_, v_x_1349_);
if (v___x_1352_ == 0)
{
uint8_t v___x_1353_; 
v___x_1353_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1338_, v_m_1346_);
if (v___x_1353_ == 1)
{
uint8_t v___x_1354_; 
v___x_1354_ = 2;
return v___x_1354_;
}
else
{
return v___x_1353_;
}
}
else
{
uint8_t v___x_1355_; 
v___x_1355_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1345_, v_m_u2082_1339_);
if (v___x_1355_ == 1)
{
uint8_t v___x_1356_; 
v___x_1356_ = 0;
return v___x_1356_;
}
else
{
return v___x_1355_;
}
}
}
else
{
uint8_t v___x_1357_; 
v___x_1357_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1345_, v_m_1346_);
if (v___x_1357_ == 1)
{
uint8_t v___x_1358_; 
v___x_1358_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1348_, v_k_1350_);
return v___x_1358_;
}
else
{
return v___x_1357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexWF___boxed(lean_object* v_m_u2081_1359_, lean_object* v_m_u2082_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1359_, v_m_u2082_1360_);
lean_dec(v_m_u2082_1360_);
lean_dec(v_m_u2081_1359_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(lean_object* v_m_u2081_1363_, lean_object* v_m_u2082_1364_, lean_object* v_h__1_1365_, lean_object* v_h__2_1366_, lean_object* v_h__3_1367_, lean_object* v_h__4_1368_){
_start:
{
if (lean_obj_tag(v_m_u2081_1363_) == 0)
{
lean_dec(v_h__4_1368_);
lean_dec(v_h__3_1367_);
if (lean_obj_tag(v_m_u2082_1364_) == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec(v_h__2_1366_);
v___x_1369_ = lean_box(0);
v___x_1370_ = lean_apply_1(v_h__1_1365_, v___x_1369_);
return v___x_1370_;
}
else
{
lean_object* v_p_1371_; lean_object* v_m_1372_; lean_object* v___x_1373_; 
lean_dec(v_h__1_1365_);
v_p_1371_ = lean_ctor_get(v_m_u2082_1364_, 0);
lean_inc_ref(v_p_1371_);
v_m_1372_ = lean_ctor_get(v_m_u2082_1364_, 1);
lean_inc(v_m_1372_);
lean_dec_ref_known(v_m_u2082_1364_, 2);
v___x_1373_ = lean_apply_2(v_h__2_1366_, v_p_1371_, v_m_1372_);
return v___x_1373_;
}
}
else
{
lean_dec(v_h__2_1366_);
lean_dec(v_h__1_1365_);
if (lean_obj_tag(v_m_u2082_1364_) == 0)
{
lean_object* v_p_1374_; lean_object* v_m_1375_; lean_object* v___x_1376_; 
lean_dec(v_h__4_1368_);
v_p_1374_ = lean_ctor_get(v_m_u2081_1363_, 0);
lean_inc_ref(v_p_1374_);
v_m_1375_ = lean_ctor_get(v_m_u2081_1363_, 1);
lean_inc(v_m_1375_);
lean_dec_ref_known(v_m_u2081_1363_, 2);
v___x_1376_ = lean_apply_2(v_h__3_1367_, v_p_1374_, v_m_1375_);
return v___x_1376_;
}
else
{
lean_object* v_p_1377_; lean_object* v_m_1378_; lean_object* v_p_1379_; lean_object* v_m_1380_; lean_object* v___x_1381_; 
lean_dec(v_h__3_1367_);
v_p_1377_ = lean_ctor_get(v_m_u2081_1363_, 0);
lean_inc_ref(v_p_1377_);
v_m_1378_ = lean_ctor_get(v_m_u2081_1363_, 1);
lean_inc(v_m_1378_);
lean_dec_ref_known(v_m_u2081_1363_, 2);
v_p_1379_ = lean_ctor_get(v_m_u2082_1364_, 0);
lean_inc_ref(v_p_1379_);
v_m_1380_ = lean_ctor_get(v_m_u2082_1364_, 1);
lean_inc(v_m_1380_);
lean_dec_ref_known(v_m_u2082_1364_, 2);
v___x_1381_ = lean_apply_4(v_h__4_1368_, v_p_1377_, v_m_1378_, v_p_1379_, v_m_1380_);
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter(lean_object* v_motive_1382_, lean_object* v_m_u2081_1383_, lean_object* v_m_u2082_1384_, lean_object* v_h__1_1385_, lean_object* v_h__2_1386_, lean_object* v_h__3_1387_, lean_object* v_h__4_1388_){
_start:
{
if (lean_obj_tag(v_m_u2081_1383_) == 0)
{
lean_dec(v_h__4_1388_);
lean_dec(v_h__3_1387_);
if (lean_obj_tag(v_m_u2082_1384_) == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec(v_h__2_1386_);
v___x_1389_ = lean_box(0);
v___x_1390_ = lean_apply_1(v_h__1_1385_, v___x_1389_);
return v___x_1390_;
}
else
{
lean_object* v_p_1391_; lean_object* v_m_1392_; lean_object* v___x_1393_; 
lean_dec(v_h__1_1385_);
v_p_1391_ = lean_ctor_get(v_m_u2082_1384_, 0);
lean_inc_ref(v_p_1391_);
v_m_1392_ = lean_ctor_get(v_m_u2082_1384_, 1);
lean_inc(v_m_1392_);
lean_dec_ref_known(v_m_u2082_1384_, 2);
v___x_1393_ = lean_apply_2(v_h__2_1386_, v_p_1391_, v_m_1392_);
return v___x_1393_;
}
}
else
{
lean_dec(v_h__2_1386_);
lean_dec(v_h__1_1385_);
if (lean_obj_tag(v_m_u2082_1384_) == 0)
{
lean_object* v_p_1394_; lean_object* v_m_1395_; lean_object* v___x_1396_; 
lean_dec(v_h__4_1388_);
v_p_1394_ = lean_ctor_get(v_m_u2081_1383_, 0);
lean_inc_ref(v_p_1394_);
v_m_1395_ = lean_ctor_get(v_m_u2081_1383_, 1);
lean_inc(v_m_1395_);
lean_dec_ref_known(v_m_u2081_1383_, 2);
v___x_1396_ = lean_apply_2(v_h__3_1387_, v_p_1394_, v_m_1395_);
return v___x_1396_;
}
else
{
lean_object* v_p_1397_; lean_object* v_m_1398_; lean_object* v_p_1399_; lean_object* v_m_1400_; lean_object* v___x_1401_; 
lean_dec(v_h__3_1387_);
v_p_1397_ = lean_ctor_get(v_m_u2081_1383_, 0);
lean_inc_ref(v_p_1397_);
v_m_1398_ = lean_ctor_get(v_m_u2081_1383_, 1);
lean_inc(v_m_1398_);
lean_dec_ref_known(v_m_u2081_1383_, 2);
v_p_1399_ = lean_ctor_get(v_m_u2082_1384_, 0);
lean_inc_ref(v_p_1399_);
v_m_1400_ = lean_ctor_get(v_m_u2082_1384_, 1);
lean_inc(v_m_1400_);
lean_dec_ref_known(v_m_u2082_1384_, 2);
v___x_1401_ = lean_apply_4(v_h__4_1388_, v_p_1397_, v_m_1398_, v_p_1399_, v_m_1400_);
return v___x_1401_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexFuel(lean_object* v_fuel_1402_, lean_object* v_m_u2081_1403_, lean_object* v_m_u2082_1404_){
_start:
{
lean_object* v_zero_1405_; uint8_t v_isZero_1406_; 
v_zero_1405_ = lean_unsigned_to_nat(0u);
v_isZero_1406_ = lean_nat_dec_eq(v_fuel_1402_, v_zero_1405_);
if (v_isZero_1406_ == 1)
{
uint8_t v___x_1407_; 
v___x_1407_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1403_, v_m_u2082_1404_);
return v___x_1407_;
}
else
{
if (lean_obj_tag(v_m_u2081_1403_) == 0)
{
if (lean_obj_tag(v_m_u2082_1404_) == 0)
{
uint8_t v___x_1408_; 
v___x_1408_ = 1;
return v___x_1408_;
}
else
{
uint8_t v___x_1409_; 
v___x_1409_ = 2;
return v___x_1409_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1404_) == 0)
{
uint8_t v___x_1410_; 
v___x_1410_ = 0;
return v___x_1410_;
}
else
{
lean_object* v_p_1411_; lean_object* v_p_1412_; lean_object* v_m_1413_; lean_object* v_m_1414_; lean_object* v_x_1415_; lean_object* v_k_1416_; lean_object* v_x_1417_; lean_object* v_k_1418_; lean_object* v_one_1419_; lean_object* v_n_1420_; uint8_t v___x_1421_; 
v_p_1411_ = lean_ctor_get(v_m_u2081_1403_, 0);
v_p_1412_ = lean_ctor_get(v_m_u2082_1404_, 0);
v_m_1413_ = lean_ctor_get(v_m_u2081_1403_, 1);
v_m_1414_ = lean_ctor_get(v_m_u2082_1404_, 1);
v_x_1415_ = lean_ctor_get(v_p_1411_, 0);
v_k_1416_ = lean_ctor_get(v_p_1411_, 1);
v_x_1417_ = lean_ctor_get(v_p_1412_, 0);
v_k_1418_ = lean_ctor_get(v_p_1412_, 1);
v_one_1419_ = lean_unsigned_to_nat(1u);
v_n_1420_ = lean_nat_sub(v_fuel_1402_, v_one_1419_);
v___x_1421_ = lean_nat_dec_eq(v_x_1415_, v_x_1417_);
if (v___x_1421_ == 0)
{
uint8_t v___x_1422_; 
v___x_1422_ = l_Nat_blt(v_x_1415_, v_x_1417_);
if (v___x_1422_ == 0)
{
uint8_t v___x_1423_; 
v___x_1423_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1420_, v_m_u2081_1403_, v_m_1414_);
lean_dec(v_n_1420_);
if (v___x_1423_ == 1)
{
uint8_t v___x_1424_; 
v___x_1424_ = 2;
return v___x_1424_;
}
else
{
return v___x_1423_;
}
}
else
{
uint8_t v___x_1425_; 
v___x_1425_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1420_, v_m_1413_, v_m_u2082_1404_);
lean_dec(v_n_1420_);
if (v___x_1425_ == 1)
{
uint8_t v___x_1426_; 
v___x_1426_ = 0;
return v___x_1426_;
}
else
{
return v___x_1425_;
}
}
}
else
{
uint8_t v___x_1427_; 
v___x_1427_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1420_, v_m_1413_, v_m_1414_);
lean_dec(v_n_1420_);
if (v___x_1427_ == 1)
{
uint8_t v___x_1428_; 
v___x_1428_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1416_, v_k_1418_);
return v___x_1428_;
}
else
{
return v___x_1427_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexFuel___boxed(lean_object* v_fuel_1429_, lean_object* v_m_u2081_1430_, lean_object* v_m_u2082_1431_){
_start:
{
uint8_t v_res_1432_; lean_object* v_r_1433_; 
v_res_1432_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_fuel_1429_, v_m_u2081_1430_, v_m_u2082_1431_);
lean_dec(v_m_u2082_1431_);
lean_dec(v_m_u2081_1430_);
lean_dec(v_fuel_1429_);
v_r_1433_ = lean_box(v_res_1432_);
return v_r_1433_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlex(lean_object* v_m_u2081_1434_, lean_object* v_m_u2082_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1436_ = l_Lean_Grind_CommRing_Mon_length(v_m_u2081_1434_);
v___x_1437_ = l_Lean_Grind_CommRing_Mon_length(v_m_u2082_1435_);
v___x_1438_ = lean_nat_add(v___x_1436_, v___x_1437_);
lean_dec(v___x_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_unsigned_to_nat(1u);
v___x_1440_ = lean_nat_add(v___x_1438_, v___x_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v___x_1440_, v_m_u2081_1434_, v_m_u2082_1435_);
lean_dec(v___x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlex___boxed(lean_object* v_m_u2081_1442_, lean_object* v_m_u2082_1443_){
_start:
{
uint8_t v_res_1444_; lean_object* v_r_1445_; 
v_res_1444_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1442_, v_m_u2082_1443_);
lean_dec(v_m_u2082_1443_);
lean_dec(v_m_u2081_1442_);
v_r_1445_ = lean_box(v_res_1444_);
return v_r_1445_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object* v_m_u2081_1446_, lean_object* v_m_u2082_1447_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1448_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2081_1446_);
v___x_1449_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2082_1447_);
v___x_1450_ = lean_nat_dec_lt(v___x_1448_, v___x_1449_);
if (v___x_1450_ == 0)
{
uint8_t v___x_1451_; 
v___x_1451_ = lean_nat_dec_eq(v___x_1448_, v___x_1449_);
lean_dec(v___x_1449_);
lean_dec(v___x_1448_);
if (v___x_1451_ == 0)
{
uint8_t v___x_1452_; 
v___x_1452_ = 2;
return v___x_1452_;
}
else
{
uint8_t v___x_1453_; 
v___x_1453_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1446_, v_m_u2082_1447_);
return v___x_1453_;
}
}
else
{
uint8_t v___x_1454_; 
lean_dec(v___x_1449_);
lean_dec(v___x_1448_);
v___x_1454_ = 0;
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_grevlex___boxed(lean_object* v_m_u2081_1455_, lean_object* v_m_u2082_1456_){
_start:
{
uint8_t v_res_1457_; lean_object* v_r_1458_; 
v_res_1457_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_u2081_1455_, v_m_u2082_1456_);
lean_dec(v_m_u2082_1456_);
lean_dec(v_m_u2081_1455_);
v_r_1458_ = lean_box(v_res_1457_);
return v_r_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___impl(lean_object* v_x_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_obj_tag_nat(v_x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___impl___boxed(lean_object* v_x_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Grind_CommRing_Poly_ctorIdx___impl(v_x_1461_);
lean_dec_ref(v_x_1461_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___redArg(lean_object* v_t_1463_, lean_object* v_k_1464_){
_start:
{
if (lean_obj_tag(v_t_1463_) == 0)
{
lean_object* v_k_1465_; lean_object* v___x_1466_; 
v_k_1465_ = lean_ctor_get(v_t_1463_, 0);
lean_inc(v_k_1465_);
lean_dec_ref_known(v_t_1463_, 1);
v___x_1466_ = lean_apply_1(v_k_1464_, v_k_1465_);
return v___x_1466_;
}
else
{
lean_object* v_k_1467_; lean_object* v_v_1468_; lean_object* v_p_1469_; lean_object* v___x_1470_; 
v_k_1467_ = lean_ctor_get(v_t_1463_, 0);
lean_inc(v_k_1467_);
v_v_1468_ = lean_ctor_get(v_t_1463_, 1);
lean_inc(v_v_1468_);
v_p_1469_ = lean_ctor_get(v_t_1463_, 2);
lean_inc_ref(v_p_1469_);
lean_dec_ref_known(v_t_1463_, 3);
v___x_1470_ = lean_apply_3(v_k_1464_, v_k_1467_, v_v_1468_, v_p_1469_);
return v___x_1470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim(lean_object* v_motive_1471_, lean_object* v_ctorIdx_1472_, lean_object* v_t_1473_, lean_object* v_h_1474_, lean_object* v_k_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1473_, v_k_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___boxed(lean_object* v_motive_1477_, lean_object* v_ctorIdx_1478_, lean_object* v_t_1479_, lean_object* v_h_1480_, lean_object* v_k_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_Grind_CommRing_Poly_ctorElim(v_motive_1477_, v_ctorIdx_1478_, v_t_1479_, v_h_1480_, v_k_1481_);
lean_dec(v_ctorIdx_1478_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim___redArg(lean_object* v_t_1483_, lean_object* v_num_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1483_, v_num_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim(lean_object* v_motive_1486_, lean_object* v_t_1487_, lean_object* v_h_1488_, lean_object* v_num_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1487_, v_num_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim___redArg(lean_object* v_t_1491_, lean_object* v_add_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1491_, v_add_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim(lean_object* v_motive_1494_, lean_object* v_t_1495_, lean_object* v_h_1496_, lean_object* v_add_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1495_, v_add_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPoly_beq(lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
if (lean_obj_tag(v_x_1499_) == 0)
{
if (lean_obj_tag(v_x_1500_) == 0)
{
lean_object* v_k_1501_; lean_object* v_k_1502_; uint8_t v___x_1503_; 
v_k_1501_ = lean_ctor_get(v_x_1499_, 0);
v_k_1502_ = lean_ctor_get(v_x_1500_, 0);
v___x_1503_ = lean_int_dec_eq(v_k_1501_, v_k_1502_);
return v___x_1503_;
}
else
{
uint8_t v___x_1504_; 
v___x_1504_ = 0;
return v___x_1504_;
}
}
else
{
if (lean_obj_tag(v_x_1500_) == 1)
{
lean_object* v_k_1505_; lean_object* v_v_1506_; lean_object* v_p_1507_; lean_object* v_k_1508_; lean_object* v_v_1509_; lean_object* v_p_1510_; uint8_t v___x_1511_; 
v_k_1505_ = lean_ctor_get(v_x_1499_, 0);
v_v_1506_ = lean_ctor_get(v_x_1499_, 1);
v_p_1507_ = lean_ctor_get(v_x_1499_, 2);
v_k_1508_ = lean_ctor_get(v_x_1500_, 0);
v_v_1509_ = lean_ctor_get(v_x_1500_, 1);
v_p_1510_ = lean_ctor_get(v_x_1500_, 2);
v___x_1511_ = lean_int_dec_eq(v_k_1505_, v_k_1508_);
if (v___x_1511_ == 0)
{
return v___x_1511_;
}
else
{
uint8_t v___x_1512_; 
v___x_1512_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_v_1506_, v_v_1509_);
if (v___x_1512_ == 0)
{
return v___x_1512_;
}
else
{
v_x_1499_ = v_p_1507_;
v_x_1500_ = v_p_1510_;
goto _start;
}
}
}
else
{
uint8_t v___x_1514_; 
v___x_1514_ = 0;
return v___x_1514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPoly_beq___boxed(lean_object* v_x_1515_, lean_object* v_x_1516_){
_start:
{
uint8_t v_res_1517_; lean_object* v_r_1518_; 
v_res_1517_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_x_1515_, v_x_1516_);
lean_dec_ref(v_x_1516_);
lean_dec_ref(v_x_1515_);
v_r_1518_ = lean_box(v_res_1517_);
return v_r_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_1521_, lean_object* v_x_1522_, lean_object* v_h__1_1523_, lean_object* v_h__2_1524_, lean_object* v_h__3_1525_){
_start:
{
if (lean_obj_tag(v_x_1521_) == 0)
{
lean_dec(v_h__2_1524_);
if (lean_obj_tag(v_x_1522_) == 0)
{
lean_object* v_k_1526_; lean_object* v_k_1527_; lean_object* v___x_1528_; 
lean_dec(v_h__3_1525_);
v_k_1526_ = lean_ctor_get(v_x_1521_, 0);
lean_inc(v_k_1526_);
lean_dec_ref_known(v_x_1521_, 1);
v_k_1527_ = lean_ctor_get(v_x_1522_, 0);
lean_inc(v_k_1527_);
lean_dec_ref_known(v_x_1522_, 1);
v___x_1528_ = lean_apply_2(v_h__1_1523_, v_k_1526_, v_k_1527_);
return v___x_1528_;
}
else
{
lean_object* v___x_1529_; 
lean_dec(v_h__1_1523_);
v___x_1529_ = lean_apply_4(v_h__3_1525_, v_x_1521_, v_x_1522_, lean_box(0), lean_box(0));
return v___x_1529_;
}
}
else
{
lean_dec(v_h__1_1523_);
if (lean_obj_tag(v_x_1522_) == 1)
{
lean_object* v_k_1530_; lean_object* v_v_1531_; lean_object* v_p_1532_; lean_object* v_k_1533_; lean_object* v_v_1534_; lean_object* v_p_1535_; lean_object* v___x_1536_; 
lean_dec(v_h__3_1525_);
v_k_1530_ = lean_ctor_get(v_x_1521_, 0);
lean_inc(v_k_1530_);
v_v_1531_ = lean_ctor_get(v_x_1521_, 1);
lean_inc(v_v_1531_);
v_p_1532_ = lean_ctor_get(v_x_1521_, 2);
lean_inc_ref(v_p_1532_);
lean_dec_ref_known(v_x_1521_, 3);
v_k_1533_ = lean_ctor_get(v_x_1522_, 0);
lean_inc(v_k_1533_);
v_v_1534_ = lean_ctor_get(v_x_1522_, 1);
lean_inc(v_v_1534_);
v_p_1535_ = lean_ctor_get(v_x_1522_, 2);
lean_inc_ref(v_p_1535_);
lean_dec_ref_known(v_x_1522_, 3);
v___x_1536_ = lean_apply_6(v_h__2_1524_, v_k_1530_, v_v_1531_, v_p_1532_, v_k_1533_, v_v_1534_, v_p_1535_);
return v___x_1536_;
}
else
{
lean_object* v___x_1537_; 
lean_dec(v_h__2_1524_);
v___x_1537_ = lean_apply_4(v_h__3_1525_, v_x_1521_, v_x_1522_, lean_box(0), lean_box(0));
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_1538_, lean_object* v_x_1539_, lean_object* v_x_1540_, lean_object* v_h__1_1541_, lean_object* v_h__2_1542_, lean_object* v_h__3_1543_){
_start:
{
if (lean_obj_tag(v_x_1539_) == 0)
{
lean_dec(v_h__2_1542_);
if (lean_obj_tag(v_x_1540_) == 0)
{
lean_object* v_k_1544_; lean_object* v_k_1545_; lean_object* v___x_1546_; 
lean_dec(v_h__3_1543_);
v_k_1544_ = lean_ctor_get(v_x_1539_, 0);
lean_inc(v_k_1544_);
lean_dec_ref_known(v_x_1539_, 1);
v_k_1545_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_k_1545_);
lean_dec_ref_known(v_x_1540_, 1);
v___x_1546_ = lean_apply_2(v_h__1_1541_, v_k_1544_, v_k_1545_);
return v___x_1546_;
}
else
{
lean_object* v___x_1547_; 
lean_dec(v_h__1_1541_);
v___x_1547_ = lean_apply_4(v_h__3_1543_, v_x_1539_, v_x_1540_, lean_box(0), lean_box(0));
return v___x_1547_;
}
}
else
{
lean_dec(v_h__1_1541_);
if (lean_obj_tag(v_x_1540_) == 1)
{
lean_object* v_k_1548_; lean_object* v_v_1549_; lean_object* v_p_1550_; lean_object* v_k_1551_; lean_object* v_v_1552_; lean_object* v_p_1553_; lean_object* v___x_1554_; 
lean_dec(v_h__3_1543_);
v_k_1548_ = lean_ctor_get(v_x_1539_, 0);
lean_inc(v_k_1548_);
v_v_1549_ = lean_ctor_get(v_x_1539_, 1);
lean_inc(v_v_1549_);
v_p_1550_ = lean_ctor_get(v_x_1539_, 2);
lean_inc_ref(v_p_1550_);
lean_dec_ref_known(v_x_1539_, 3);
v_k_1551_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_k_1551_);
v_v_1552_ = lean_ctor_get(v_x_1540_, 1);
lean_inc(v_v_1552_);
v_p_1553_ = lean_ctor_get(v_x_1540_, 2);
lean_inc_ref(v_p_1553_);
lean_dec_ref_known(v_x_1540_, 3);
v___x_1554_ = lean_apply_6(v_h__2_1542_, v_k_1548_, v_v_1549_, v_p_1550_, v_k_1551_, v_v_1552_, v_p_1553_);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; 
lean_dec(v_h__2_1542_);
v___x_1555_ = lean_apply_4(v_h__3_1543_, v_x_1539_, v_x_1540_, lean_box(0), lean_box(0));
return v___x_1555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr(lean_object* v_x_1568_, lean_object* v_prec_1569_){
_start:
{
lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; 
if (lean_obj_tag(v_x_1568_) == 0)
{
lean_object* v_k_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1602_; 
v_k_1579_ = lean_ctor_get(v_x_1568_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_x_1568_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1581_ = v_x_1568_;
v_isShared_1582_ = v_isSharedCheck_1602_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_k_1579_);
lean_dec(v_x_1568_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1602_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___y_1584_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = lean_unsigned_to_nat(1024u);
v___x_1599_ = lean_nat_dec_le(v___x_1598_, v_prec_1569_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1584_ = v___x_1600_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1584_ = v___x_1601_;
goto v___jp_1583_;
}
v___jp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1585_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__2));
v___x_1586_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1587_ = lean_int_dec_lt(v_k_1579_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1588_ = l_Int_repr(v_k_1579_);
lean_dec(v_k_1579_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set_tag(v___x_1581_, 3);
lean_ctor_set(v___x_1581_, 0, v___x_1588_);
v___x_1590_ = v___x_1581_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
v___y_1571_ = v___x_1585_;
v___y_1572_ = v___y_1584_;
v___y_1573_ = v___x_1590_;
goto v___jp_1570_;
}
}
else
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1592_ = lean_unsigned_to_nat(1024u);
v___x_1593_ = l_Int_repr(v_k_1579_);
lean_dec(v_k_1579_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set_tag(v___x_1581_, 3);
lean_ctor_set(v___x_1581_, 0, v___x_1593_);
v___x_1595_ = v___x_1581_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Repr_addAppParen(v___x_1595_, v___x_1592_);
v___y_1571_ = v___x_1585_;
v___y_1572_ = v___y_1584_;
v___y_1573_ = v___x_1596_;
goto v___jp_1570_;
}
}
}
}
}
else
{
lean_object* v_k_1603_; lean_object* v_v_1604_; lean_object* v_p_1605_; lean_object* v___x_1606_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1624_; uint8_t v___x_1634_; 
v_k_1603_ = lean_ctor_get(v_x_1568_, 0);
lean_inc(v_k_1603_);
v_v_1604_ = lean_ctor_get(v_x_1568_, 1);
lean_inc(v_v_1604_);
v_p_1605_ = lean_ctor_get(v_x_1568_, 2);
lean_inc_ref(v_p_1605_);
lean_dec_ref_known(v_x_1568_, 3);
v___x_1606_ = lean_unsigned_to_nat(1024u);
v___x_1634_ = lean_nat_dec_le(v___x_1606_, v_prec_1569_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1624_ = v___x_1635_;
goto v___jp_1623_;
}
else
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1624_ = v___x_1636_;
goto v___jp_1623_;
}
v___jp_1607_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_inc(v___y_1610_);
v___x_1612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___y_1610_);
lean_ctor_set(v___x_1612_, 1, v___y_1611_);
lean_inc_n(v___y_1608_, 2);
v___x_1613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v___y_1608_);
v___x_1614_ = l_Lean_Grind_CommRing_instReprMon_repr(v_v_1604_, v___x_1606_);
v___x_1615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
lean_ctor_set(v___x_1616_, 1, v___y_1608_);
v___x_1617_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_p_1605_, v___x_1606_);
v___x_1618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
lean_inc(v___y_1609_);
v___x_1619_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___y_1609_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = 0;
v___x_1621_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set_uint8(v___x_1621_, sizeof(void*)*1, v___x_1620_);
v___x_1622_ = l_Repr_addAppParen(v___x_1621_, v_prec_1569_);
return v___x_1622_;
}
v___jp_1623_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1625_ = lean_box(1);
v___x_1626_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__5));
v___x_1627_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1628_ = lean_int_dec_lt(v_k_1603_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = l_Int_repr(v_k_1603_);
lean_dec(v_k_1603_);
v___x_1630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
v___y_1608_ = v___x_1625_;
v___y_1609_ = v___y_1624_;
v___y_1610_ = v___x_1626_;
v___y_1611_ = v___x_1630_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = l_Int_repr(v_k_1603_);
lean_dec(v_k_1603_);
v___x_1632_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
v___x_1633_ = l_Repr_addAppParen(v___x_1632_, v___x_1606_);
v___y_1608_ = v___x_1625_;
v___y_1609_ = v___y_1624_;
v___y_1610_ = v___x_1626_;
v___y_1611_ = v___x_1633_;
goto v___jp_1607_;
}
}
}
v___jp_1570_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_inc(v___y_1571_);
v___x_1574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___y_1571_);
lean_ctor_set(v___x_1574_, 1, v___y_1573_);
lean_inc(v___y_1572_);
v___x_1575_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___y_1572_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = 0;
v___x_1577_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*1, v___x_1576_);
v___x_1578_ = l_Repr_addAppParen(v___x_1577_, v_prec_1569_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___boxed(lean_object* v_x_1637_, lean_object* v_prec_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_x_1637_, v_prec_1638_);
lean_dec(v_prec_1638_);
return v_res_1639_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default(void){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_1644_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly(void){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
return v___x_1645_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePoly_hash(lean_object* v_x_1646_){
_start:
{
if (lean_obj_tag(v_x_1646_) == 0)
{
lean_object* v_k_1647_; uint64_t v___x_1648_; lean_object* v_intZero_1649_; uint8_t v_isNeg_1650_; 
v_k_1647_ = lean_ctor_get(v_x_1646_, 0);
v___x_1648_ = 0ULL;
v_intZero_1649_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1650_ = lean_int_dec_lt(v_k_1647_, v_intZero_1649_);
if (v_isNeg_1650_ == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; uint64_t v___x_1654_; uint64_t v___x_1655_; 
v_a_1651_ = lean_nat_abs(v_k_1647_);
v___x_1652_ = lean_unsigned_to_nat(2u);
v___x_1653_ = lean_nat_mul(v___x_1652_, v_a_1651_);
lean_dec(v_a_1651_);
v___x_1654_ = lean_uint64_of_nat(v___x_1653_);
lean_dec(v___x_1653_);
v___x_1655_ = lean_uint64_mix_hash(v___x_1648_, v___x_1654_);
return v___x_1655_;
}
else
{
lean_object* v_abs_1656_; lean_object* v_one_1657_; lean_object* v_a_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; uint64_t v___x_1662_; uint64_t v___x_1663_; 
v_abs_1656_ = lean_nat_abs(v_k_1647_);
v_one_1657_ = lean_unsigned_to_nat(1u);
v_a_1658_ = lean_nat_sub(v_abs_1656_, v_one_1657_);
lean_dec(v_abs_1656_);
v___x_1659_ = lean_unsigned_to_nat(2u);
v___x_1660_ = lean_nat_mul(v___x_1659_, v_a_1658_);
lean_dec(v_a_1658_);
v___x_1661_ = lean_nat_add(v___x_1660_, v_one_1657_);
lean_dec(v___x_1660_);
v___x_1662_ = lean_uint64_of_nat(v___x_1661_);
lean_dec(v___x_1661_);
v___x_1663_ = lean_uint64_mix_hash(v___x_1648_, v___x_1662_);
return v___x_1663_;
}
}
else
{
lean_object* v_k_1664_; lean_object* v_v_1665_; lean_object* v_p_1666_; uint64_t v___x_1667_; uint64_t v___y_1669_; lean_object* v_intZero_1675_; uint8_t v_isNeg_1676_; 
v_k_1664_ = lean_ctor_get(v_x_1646_, 0);
v_v_1665_ = lean_ctor_get(v_x_1646_, 1);
v_p_1666_ = lean_ctor_get(v_x_1646_, 2);
v___x_1667_ = 1ULL;
v_intZero_1675_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1676_ = lean_int_dec_lt(v_k_1664_, v_intZero_1675_);
if (v_isNeg_1676_ == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; uint64_t v___x_1680_; 
v_a_1677_ = lean_nat_abs(v_k_1664_);
v___x_1678_ = lean_unsigned_to_nat(2u);
v___x_1679_ = lean_nat_mul(v___x_1678_, v_a_1677_);
lean_dec(v_a_1677_);
v___x_1680_ = lean_uint64_of_nat(v___x_1679_);
lean_dec(v___x_1679_);
v___y_1669_ = v___x_1680_;
goto v___jp_1668_;
}
else
{
lean_object* v_abs_1681_; lean_object* v_one_1682_; lean_object* v_a_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; uint64_t v___x_1687_; 
v_abs_1681_ = lean_nat_abs(v_k_1664_);
v_one_1682_ = lean_unsigned_to_nat(1u);
v_a_1683_ = lean_nat_sub(v_abs_1681_, v_one_1682_);
lean_dec(v_abs_1681_);
v___x_1684_ = lean_unsigned_to_nat(2u);
v___x_1685_ = lean_nat_mul(v___x_1684_, v_a_1683_);
lean_dec(v_a_1683_);
v___x_1686_ = lean_nat_add(v___x_1685_, v_one_1682_);
lean_dec(v___x_1685_);
v___x_1687_ = lean_uint64_of_nat(v___x_1686_);
lean_dec(v___x_1686_);
v___y_1669_ = v___x_1687_;
goto v___jp_1668_;
}
v___jp_1668_:
{
uint64_t v___x_1670_; uint64_t v___x_1671_; uint64_t v___x_1672_; uint64_t v___x_1673_; uint64_t v___x_1674_; 
v___x_1670_ = lean_uint64_mix_hash(v___x_1667_, v___y_1669_);
v___x_1671_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_v_1665_);
v___x_1672_ = lean_uint64_mix_hash(v___x_1670_, v___x_1671_);
v___x_1673_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_p_1666_);
v___x_1674_ = lean_uint64_mix_hash(v___x_1672_, v___x_1673_);
return v___x_1674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePoly_hash___boxed(lean_object* v_x_1688_){
_start:
{
uint64_t v_res_1689_; lean_object* v_r_1690_; 
v_res_1689_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_x_1688_);
lean_dec_ref(v_x_1688_);
v_r_1690_ = lean_box_uint64(v_res_1689_);
return v_r_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg(lean_object* v_inst_1693_, lean_object* v_ctx_1694_, lean_object* v_p_1695_){
_start:
{
lean_object* v_toSemiring_1696_; lean_object* v_intCast_1697_; lean_object* v_toAdd_1698_; lean_object* v___x_1699_; 
v_toSemiring_1696_ = lean_ctor_get(v_inst_1693_, 0);
v_intCast_1697_ = lean_ctor_get(v_inst_1693_, 3);
v_toAdd_1698_ = lean_ctor_get(v_toSemiring_1696_, 0);
lean_inc(v_toAdd_1698_);
lean_inc_ref(v_inst_1693_);
v___x_1699_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1693_);
if (lean_obj_tag(v_p_1695_) == 0)
{
lean_object* v_k_1700_; lean_object* v___x_1701_; 
lean_inc(v_intCast_1697_);
lean_dec_ref(v___x_1699_);
lean_dec(v_toAdd_1698_);
lean_dec_ref(v_inst_1693_);
v_k_1700_ = lean_ctor_get(v_p_1695_, 0);
lean_inc(v_k_1700_);
lean_dec_ref_known(v_p_1695_, 1);
v___x_1701_ = lean_apply_1(v_intCast_1697_, v_k_1700_);
return v___x_1701_;
}
else
{
lean_object* v_zsmul_1702_; lean_object* v_k_1703_; lean_object* v_v_1704_; lean_object* v_p_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_zsmul_1702_ = lean_ctor_get(v___x_1699_, 2);
lean_inc(v_zsmul_1702_);
lean_dec_ref(v___x_1699_);
v_k_1703_ = lean_ctor_get(v_p_1695_, 0);
lean_inc(v_k_1703_);
v_v_1704_ = lean_ctor_get(v_p_1695_, 1);
lean_inc(v_v_1704_);
v_p_1705_ = lean_ctor_get(v_p_1695_, 2);
lean_inc_ref(v_p_1705_);
lean_dec_ref_known(v_p_1695_, 3);
lean_inc_ref(v_toSemiring_1696_);
v___x_1706_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_toSemiring_1696_, v_ctx_1694_, v_v_1704_);
v___x_1707_ = lean_apply_2(v_zsmul_1702_, v_k_1703_, v___x_1706_);
v___x_1708_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1693_, v_ctx_1694_, v_p_1705_);
v___x_1709_ = lean_apply_2(v_toAdd_1698_, v___x_1707_, v___x_1708_);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg___boxed(lean_object* v_inst_1710_, lean_object* v_ctx_1711_, lean_object* v_p_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1710_, v_ctx_1711_, v_p_1712_);
lean_dec_ref(v_ctx_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote(lean_object* v_00_u03b1_1714_, lean_object* v_inst_1715_, lean_object* v_ctx_1716_, lean_object* v_p_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1715_, v_ctx_1716_, v_p_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___boxed(lean_object* v_00_u03b1_1719_, lean_object* v_inst_1720_, lean_object* v_ctx_1721_, lean_object* v_p_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_Grind_CommRing_Poly_denote(v_00_u03b1_1719_, v_inst_1720_, v_ctx_1721_, v_p_1722_);
lean_dec_ref(v_ctx_1721_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg(lean_object* v_inst_1724_, lean_object* v_ctx_1725_, lean_object* v_k_1726_, lean_object* v_m_1727_){
_start:
{
lean_object* v_toSemiring_1728_; lean_object* v___x_1729_; lean_object* v_zsmul_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_toSemiring_1728_ = lean_ctor_get(v_inst_1724_, 0);
lean_inc_ref(v_toSemiring_1728_);
v___x_1729_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1724_);
v_zsmul_1730_ = lean_ctor_get(v___x_1729_, 2);
lean_inc(v_zsmul_1730_);
lean_dec_ref(v___x_1729_);
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1733_ = lean_int_dec_eq(v_k_1726_, v___x_1732_);
if (v___x_1733_ == 0)
{
if (lean_obj_tag(v_m_1727_) == 0)
{
lean_object* v_ofNat_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v_ofNat_1734_ = lean_ctor_get(v_toSemiring_1728_, 3);
lean_inc(v_ofNat_1734_);
lean_dec_ref(v_toSemiring_1728_);
v___x_1735_ = lean_apply_1(v_ofNat_1734_, v___x_1731_);
v___x_1736_ = lean_apply_2(v_zsmul_1730_, v_k_1726_, v___x_1735_);
return v___x_1736_;
}
else
{
lean_object* v_p_1737_; lean_object* v_m_1738_; lean_object* v_ofNat_1739_; lean_object* v_npow_1740_; lean_object* v_x_1741_; lean_object* v_k_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v_p_1737_ = lean_ctor_get(v_m_1727_, 0);
lean_inc_ref(v_p_1737_);
v_m_1738_ = lean_ctor_get(v_m_1727_, 1);
lean_inc(v_m_1738_);
lean_dec_ref_known(v_m_1727_, 2);
v_ofNat_1739_ = lean_ctor_get(v_toSemiring_1728_, 3);
v_npow_1740_ = lean_ctor_get(v_toSemiring_1728_, 5);
v_x_1741_ = lean_ctor_get(v_p_1737_, 0);
lean_inc(v_x_1741_);
v_k_1742_ = lean_ctor_get(v_p_1737_, 1);
lean_inc(v_k_1742_);
lean_dec_ref(v_p_1737_);
v___x_1743_ = lean_unsigned_to_nat(0u);
v___x_1744_ = lean_nat_dec_eq(v_k_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_nat_dec_eq(v_k_1742_, v___x_1731_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1746_ = l_Lean_RArray_getImpl___redArg(v_ctx_1725_, v_x_1741_);
lean_dec(v_x_1741_);
lean_inc(v_npow_1740_);
v___x_1747_ = lean_apply_2(v_npow_1740_, v___x_1746_, v_k_1742_);
v___x_1748_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1728_, v_ctx_1725_, v_m_1738_, v___x_1747_);
v___x_1749_ = lean_apply_2(v_zsmul_1730_, v_k_1726_, v___x_1748_);
return v___x_1749_;
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec(v_k_1742_);
v___x_1750_ = l_Lean_RArray_getImpl___redArg(v_ctx_1725_, v_x_1741_);
lean_dec(v_x_1741_);
v___x_1751_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1728_, v_ctx_1725_, v_m_1738_, v___x_1750_);
v___x_1752_ = lean_apply_2(v_zsmul_1730_, v_k_1726_, v___x_1751_);
return v___x_1752_;
}
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec(v_k_1742_);
lean_dec(v_x_1741_);
lean_inc(v_ofNat_1739_);
v___x_1753_ = lean_apply_1(v_ofNat_1739_, v___x_1731_);
v___x_1754_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1728_, v_ctx_1725_, v_m_1738_, v___x_1753_);
v___x_1755_ = lean_apply_2(v_zsmul_1730_, v_k_1726_, v___x_1754_);
return v___x_1755_;
}
}
}
else
{
lean_dec(v_zsmul_1730_);
lean_dec(v_k_1726_);
if (lean_obj_tag(v_m_1727_) == 0)
{
lean_object* v_ofNat_1756_; lean_object* v___x_1757_; 
v_ofNat_1756_ = lean_ctor_get(v_toSemiring_1728_, 3);
lean_inc(v_ofNat_1756_);
lean_dec_ref(v_toSemiring_1728_);
v___x_1757_ = lean_apply_1(v_ofNat_1756_, v___x_1731_);
return v___x_1757_;
}
else
{
lean_object* v_p_1758_; lean_object* v_m_1759_; lean_object* v_ofNat_1760_; lean_object* v_npow_1761_; lean_object* v_x_1762_; lean_object* v_k_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v_p_1758_ = lean_ctor_get(v_m_1727_, 0);
lean_inc_ref(v_p_1758_);
v_m_1759_ = lean_ctor_get(v_m_1727_, 1);
lean_inc(v_m_1759_);
lean_dec_ref_known(v_m_1727_, 2);
v_ofNat_1760_ = lean_ctor_get(v_toSemiring_1728_, 3);
v_npow_1761_ = lean_ctor_get(v_toSemiring_1728_, 5);
v_x_1762_ = lean_ctor_get(v_p_1758_, 0);
lean_inc(v_x_1762_);
v_k_1763_ = lean_ctor_get(v_p_1758_, 1);
lean_inc(v_k_1763_);
lean_dec_ref(v_p_1758_);
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = lean_nat_dec_eq(v_k_1763_, v___x_1764_);
if (v___x_1765_ == 0)
{
uint8_t v___x_1766_; 
v___x_1766_ = lean_nat_dec_eq(v_k_1763_, v___x_1731_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = l_Lean_RArray_getImpl___redArg(v_ctx_1725_, v_x_1762_);
lean_dec(v_x_1762_);
lean_inc(v_npow_1761_);
v___x_1768_ = lean_apply_2(v_npow_1761_, v___x_1767_, v_k_1763_);
v___x_1769_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1728_, v_ctx_1725_, v_m_1759_, v___x_1768_);
return v___x_1769_;
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec(v_k_1763_);
v___x_1770_ = l_Lean_RArray_getImpl___redArg(v_ctx_1725_, v_x_1762_);
lean_dec(v_x_1762_);
v___x_1771_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1728_, v_ctx_1725_, v_m_1759_, v___x_1770_);
return v___x_1771_;
}
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_dec(v_k_1763_);
lean_dec(v_x_1762_);
lean_inc(v_ofNat_1760_);
v___x_1772_ = lean_apply_1(v_ofNat_1760_, v___x_1731_);
v___x_1773_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1728_, v_ctx_1725_, v_m_1759_, v___x_1772_);
return v___x_1773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg___boxed(lean_object* v_inst_1774_, lean_object* v_ctx_1775_, lean_object* v_k_1776_, lean_object* v_m_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Grind_CommRing_denoteTerm___redArg(v_inst_1774_, v_ctx_1775_, v_k_1776_, v_m_1777_);
lean_dec_ref(v_ctx_1775_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm(lean_object* v_00_u03b1_1779_, lean_object* v_inst_1780_, lean_object* v_ctx_1781_, lean_object* v_k_1782_, lean_object* v_m_1783_){
_start:
{
lean_object* v_toSemiring_1784_; lean_object* v___x_1785_; lean_object* v_zsmul_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_toSemiring_1784_ = lean_ctor_get(v_inst_1780_, 0);
lean_inc_ref(v_toSemiring_1784_);
v___x_1785_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1780_);
v_zsmul_1786_ = lean_ctor_get(v___x_1785_, 2);
lean_inc(v_zsmul_1786_);
lean_dec_ref(v___x_1785_);
v___x_1787_ = lean_unsigned_to_nat(1u);
v___x_1788_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1789_ = lean_int_dec_eq(v_k_1782_, v___x_1788_);
if (v___x_1789_ == 0)
{
if (lean_obj_tag(v_m_1783_) == 0)
{
lean_object* v_ofNat_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v_ofNat_1790_ = lean_ctor_get(v_toSemiring_1784_, 3);
lean_inc(v_ofNat_1790_);
lean_dec_ref(v_toSemiring_1784_);
v___x_1791_ = lean_apply_1(v_ofNat_1790_, v___x_1787_);
v___x_1792_ = lean_apply_2(v_zsmul_1786_, v_k_1782_, v___x_1791_);
return v___x_1792_;
}
else
{
lean_object* v_p_1793_; lean_object* v_m_1794_; lean_object* v_ofNat_1795_; lean_object* v_npow_1796_; lean_object* v_x_1797_; lean_object* v_k_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v_p_1793_ = lean_ctor_get(v_m_1783_, 0);
lean_inc_ref(v_p_1793_);
v_m_1794_ = lean_ctor_get(v_m_1783_, 1);
lean_inc(v_m_1794_);
lean_dec_ref_known(v_m_1783_, 2);
v_ofNat_1795_ = lean_ctor_get(v_toSemiring_1784_, 3);
v_npow_1796_ = lean_ctor_get(v_toSemiring_1784_, 5);
v_x_1797_ = lean_ctor_get(v_p_1793_, 0);
lean_inc(v_x_1797_);
v_k_1798_ = lean_ctor_get(v_p_1793_, 1);
lean_inc(v_k_1798_);
lean_dec_ref(v_p_1793_);
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1800_ = lean_nat_dec_eq(v_k_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_nat_dec_eq(v_k_1798_, v___x_1787_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1802_ = l_Lean_RArray_getImpl___redArg(v_ctx_1781_, v_x_1797_);
lean_dec(v_x_1797_);
lean_inc(v_npow_1796_);
v___x_1803_ = lean_apply_2(v_npow_1796_, v___x_1802_, v_k_1798_);
v___x_1804_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1784_, v_ctx_1781_, v_m_1794_, v___x_1803_);
v___x_1805_ = lean_apply_2(v_zsmul_1786_, v_k_1782_, v___x_1804_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v_k_1798_);
v___x_1806_ = l_Lean_RArray_getImpl___redArg(v_ctx_1781_, v_x_1797_);
lean_dec(v_x_1797_);
v___x_1807_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1784_, v_ctx_1781_, v_m_1794_, v___x_1806_);
v___x_1808_ = lean_apply_2(v_zsmul_1786_, v_k_1782_, v___x_1807_);
return v___x_1808_;
}
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec(v_k_1798_);
lean_dec(v_x_1797_);
lean_inc(v_ofNat_1795_);
v___x_1809_ = lean_apply_1(v_ofNat_1795_, v___x_1787_);
v___x_1810_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1784_, v_ctx_1781_, v_m_1794_, v___x_1809_);
v___x_1811_ = lean_apply_2(v_zsmul_1786_, v_k_1782_, v___x_1810_);
return v___x_1811_;
}
}
}
else
{
lean_dec(v_zsmul_1786_);
lean_dec(v_k_1782_);
if (lean_obj_tag(v_m_1783_) == 0)
{
lean_object* v_ofNat_1812_; lean_object* v___x_1813_; 
v_ofNat_1812_ = lean_ctor_get(v_toSemiring_1784_, 3);
lean_inc(v_ofNat_1812_);
lean_dec_ref(v_toSemiring_1784_);
v___x_1813_ = lean_apply_1(v_ofNat_1812_, v___x_1787_);
return v___x_1813_;
}
else
{
lean_object* v_p_1814_; lean_object* v_m_1815_; lean_object* v_ofNat_1816_; lean_object* v_npow_1817_; lean_object* v_x_1818_; lean_object* v_k_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v_p_1814_ = lean_ctor_get(v_m_1783_, 0);
lean_inc_ref(v_p_1814_);
v_m_1815_ = lean_ctor_get(v_m_1783_, 1);
lean_inc(v_m_1815_);
lean_dec_ref_known(v_m_1783_, 2);
v_ofNat_1816_ = lean_ctor_get(v_toSemiring_1784_, 3);
v_npow_1817_ = lean_ctor_get(v_toSemiring_1784_, 5);
v_x_1818_ = lean_ctor_get(v_p_1814_, 0);
lean_inc(v_x_1818_);
v_k_1819_ = lean_ctor_get(v_p_1814_, 1);
lean_inc(v_k_1819_);
lean_dec_ref(v_p_1814_);
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = lean_nat_dec_eq(v_k_1819_, v___x_1820_);
if (v___x_1821_ == 0)
{
uint8_t v___x_1822_; 
v___x_1822_ = lean_nat_dec_eq(v_k_1819_, v___x_1787_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = l_Lean_RArray_getImpl___redArg(v_ctx_1781_, v_x_1818_);
lean_dec(v_x_1818_);
lean_inc(v_npow_1817_);
v___x_1824_ = lean_apply_2(v_npow_1817_, v___x_1823_, v_k_1819_);
v___x_1825_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1784_, v_ctx_1781_, v_m_1815_, v___x_1824_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec(v_k_1819_);
v___x_1826_ = l_Lean_RArray_getImpl___redArg(v_ctx_1781_, v_x_1818_);
lean_dec(v_x_1818_);
v___x_1827_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1784_, v_ctx_1781_, v_m_1815_, v___x_1826_);
return v___x_1827_;
}
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec(v_k_1819_);
lean_dec(v_x_1818_);
lean_inc(v_ofNat_1816_);
v___x_1828_ = lean_apply_1(v_ofNat_1816_, v___x_1787_);
v___x_1829_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1784_, v_ctx_1781_, v_m_1815_, v___x_1828_);
return v___x_1829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___boxed(lean_object* v_00_u03b1_1830_, lean_object* v_inst_1831_, lean_object* v_ctx_1832_, lean_object* v_k_1833_, lean_object* v_m_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Grind_CommRing_denoteTerm(v_00_u03b1_1830_, v_inst_1831_, v_ctx_1832_, v_k_1833_, v_m_1834_);
lean_dec_ref(v_ctx_1832_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(lean_object* v_inst_1836_, lean_object* v_ctx_1837_, lean_object* v_p_1838_, lean_object* v_acc_1839_){
_start:
{
if (lean_obj_tag(v_p_1838_) == 0)
{
lean_object* v_toSemiring_1840_; lean_object* v_intCast_1841_; lean_object* v_toAdd_1842_; lean_object* v_k_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v_toSemiring_1840_ = lean_ctor_get(v_inst_1836_, 0);
lean_inc_ref(v_toSemiring_1840_);
v_intCast_1841_ = lean_ctor_get(v_inst_1836_, 3);
lean_inc(v_intCast_1841_);
lean_dec_ref(v_inst_1836_);
v_toAdd_1842_ = lean_ctor_get(v_toSemiring_1840_, 0);
lean_inc(v_toAdd_1842_);
lean_dec_ref(v_toSemiring_1840_);
v_k_1843_ = lean_ctor_get(v_p_1838_, 0);
lean_inc(v_k_1843_);
lean_dec_ref_known(v_p_1838_, 1);
v___x_1844_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1845_ = lean_int_dec_eq(v_k_1843_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_apply_1(v_intCast_1841_, v_k_1843_);
v___x_1847_ = lean_apply_2(v_toAdd_1842_, v_acc_1839_, v___x_1846_);
return v___x_1847_;
}
else
{
lean_dec(v_k_1843_);
lean_dec(v_toAdd_1842_);
lean_dec(v_intCast_1841_);
return v_acc_1839_;
}
}
else
{
lean_object* v_toSemiring_1848_; lean_object* v_toAdd_1849_; lean_object* v_ofNat_1850_; lean_object* v_npow_1851_; lean_object* v_k_1852_; lean_object* v_v_1853_; lean_object* v_p_1854_; lean_object* v___y_1856_; lean_object* v___x_1859_; lean_object* v_zsmul_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v_toSemiring_1848_ = lean_ctor_get(v_inst_1836_, 0);
v_toAdd_1849_ = lean_ctor_get(v_toSemiring_1848_, 0);
v_ofNat_1850_ = lean_ctor_get(v_toSemiring_1848_, 3);
v_npow_1851_ = lean_ctor_get(v_toSemiring_1848_, 5);
v_k_1852_ = lean_ctor_get(v_p_1838_, 0);
lean_inc(v_k_1852_);
v_v_1853_ = lean_ctor_get(v_p_1838_, 1);
lean_inc(v_v_1853_);
v_p_1854_ = lean_ctor_get(v_p_1838_, 2);
lean_inc_ref(v_p_1854_);
lean_dec_ref_known(v_p_1838_, 3);
lean_inc_ref(v_inst_1836_);
v___x_1859_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1836_);
v_zsmul_1860_ = lean_ctor_get(v___x_1859_, 2);
lean_inc(v_zsmul_1860_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = lean_unsigned_to_nat(1u);
v___x_1862_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1863_ = lean_int_dec_eq(v_k_1852_, v___x_1862_);
if (v___x_1863_ == 0)
{
if (lean_obj_tag(v_v_1853_) == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_inc(v_ofNat_1850_);
v___x_1864_ = lean_apply_1(v_ofNat_1850_, v___x_1861_);
v___x_1865_ = lean_apply_2(v_zsmul_1860_, v_k_1852_, v___x_1864_);
v___y_1856_ = v___x_1865_;
goto v___jp_1855_;
}
else
{
lean_object* v_p_1866_; lean_object* v_m_1867_; lean_object* v_x_1868_; lean_object* v_k_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v_p_1866_ = lean_ctor_get(v_v_1853_, 0);
lean_inc_ref(v_p_1866_);
v_m_1867_ = lean_ctor_get(v_v_1853_, 1);
lean_inc(v_m_1867_);
lean_dec_ref_known(v_v_1853_, 2);
v_x_1868_ = lean_ctor_get(v_p_1866_, 0);
lean_inc(v_x_1868_);
v_k_1869_ = lean_ctor_get(v_p_1866_, 1);
lean_inc(v_k_1869_);
lean_dec_ref(v_p_1866_);
v___x_1870_ = lean_unsigned_to_nat(0u);
v___x_1871_ = lean_nat_dec_eq(v_k_1869_, v___x_1870_);
if (v___x_1871_ == 0)
{
uint8_t v___x_1872_; 
v___x_1872_ = lean_nat_dec_eq(v_k_1869_, v___x_1861_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1873_ = l_Lean_RArray_getImpl___redArg(v_ctx_1837_, v_x_1868_);
lean_dec(v_x_1868_);
lean_inc(v_npow_1851_);
v___x_1874_ = lean_apply_2(v_npow_1851_, v___x_1873_, v_k_1869_);
lean_inc_ref(v_toSemiring_1848_);
v___x_1875_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1848_, v_ctx_1837_, v_m_1867_, v___x_1874_);
v___x_1876_ = lean_apply_2(v_zsmul_1860_, v_k_1852_, v___x_1875_);
v___y_1856_ = v___x_1876_;
goto v___jp_1855_;
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_dec(v_k_1869_);
v___x_1877_ = l_Lean_RArray_getImpl___redArg(v_ctx_1837_, v_x_1868_);
lean_dec(v_x_1868_);
lean_inc_ref(v_toSemiring_1848_);
v___x_1878_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1848_, v_ctx_1837_, v_m_1867_, v___x_1877_);
v___x_1879_ = lean_apply_2(v_zsmul_1860_, v_k_1852_, v___x_1878_);
v___y_1856_ = v___x_1879_;
goto v___jp_1855_;
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec(v_k_1869_);
lean_dec(v_x_1868_);
lean_inc(v_ofNat_1850_);
v___x_1880_ = lean_apply_1(v_ofNat_1850_, v___x_1861_);
lean_inc_ref(v_toSemiring_1848_);
v___x_1881_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1848_, v_ctx_1837_, v_m_1867_, v___x_1880_);
v___x_1882_ = lean_apply_2(v_zsmul_1860_, v_k_1852_, v___x_1881_);
v___y_1856_ = v___x_1882_;
goto v___jp_1855_;
}
}
}
else
{
lean_dec(v_zsmul_1860_);
lean_dec(v_k_1852_);
if (lean_obj_tag(v_v_1853_) == 0)
{
lean_object* v___x_1883_; 
lean_inc(v_ofNat_1850_);
v___x_1883_ = lean_apply_1(v_ofNat_1850_, v___x_1861_);
v___y_1856_ = v___x_1883_;
goto v___jp_1855_;
}
else
{
lean_object* v_p_1884_; lean_object* v_m_1885_; lean_object* v_x_1886_; lean_object* v_k_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; 
v_p_1884_ = lean_ctor_get(v_v_1853_, 0);
lean_inc_ref(v_p_1884_);
v_m_1885_ = lean_ctor_get(v_v_1853_, 1);
lean_inc(v_m_1885_);
lean_dec_ref_known(v_v_1853_, 2);
v_x_1886_ = lean_ctor_get(v_p_1884_, 0);
lean_inc(v_x_1886_);
v_k_1887_ = lean_ctor_get(v_p_1884_, 1);
lean_inc(v_k_1887_);
lean_dec_ref(v_p_1884_);
v___x_1888_ = lean_unsigned_to_nat(0u);
v___x_1889_ = lean_nat_dec_eq(v_k_1887_, v___x_1888_);
if (v___x_1889_ == 0)
{
uint8_t v___x_1890_; 
v___x_1890_ = lean_nat_dec_eq(v_k_1887_, v___x_1861_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = l_Lean_RArray_getImpl___redArg(v_ctx_1837_, v_x_1886_);
lean_dec(v_x_1886_);
lean_inc(v_npow_1851_);
v___x_1892_ = lean_apply_2(v_npow_1851_, v___x_1891_, v_k_1887_);
lean_inc_ref(v_toSemiring_1848_);
v___x_1893_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1848_, v_ctx_1837_, v_m_1885_, v___x_1892_);
v___y_1856_ = v___x_1893_;
goto v___jp_1855_;
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec(v_k_1887_);
v___x_1894_ = l_Lean_RArray_getImpl___redArg(v_ctx_1837_, v_x_1886_);
lean_dec(v_x_1886_);
lean_inc_ref(v_toSemiring_1848_);
v___x_1895_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1848_, v_ctx_1837_, v_m_1885_, v___x_1894_);
v___y_1856_ = v___x_1895_;
goto v___jp_1855_;
}
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec(v_k_1887_);
lean_dec(v_x_1886_);
lean_inc(v_ofNat_1850_);
v___x_1896_ = lean_apply_1(v_ofNat_1850_, v___x_1861_);
lean_inc_ref(v_toSemiring_1848_);
v___x_1897_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1848_, v_ctx_1837_, v_m_1885_, v___x_1896_);
v___y_1856_ = v___x_1897_;
goto v___jp_1855_;
}
}
}
v___jp_1855_:
{
lean_object* v___x_1857_; 
lean_inc(v_toAdd_1849_);
v___x_1857_ = lean_apply_2(v_toAdd_1849_, v_acc_1839_, v___y_1856_);
v_p_1838_ = v_p_1854_;
v_acc_1839_ = v___x_1857_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg___boxed(lean_object* v_inst_1898_, lean_object* v_ctx_1899_, lean_object* v_p_1900_, lean_object* v_acc_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1898_, v_ctx_1899_, v_p_1900_, v_acc_1901_);
lean_dec_ref(v_ctx_1899_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go(lean_object* v_00_u03b1_1903_, lean_object* v_inst_1904_, lean_object* v_ctx_1905_, lean_object* v_p_1906_, lean_object* v_acc_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1904_, v_ctx_1905_, v_p_1906_, v_acc_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___boxed(lean_object* v_00_u03b1_1909_, lean_object* v_inst_1910_, lean_object* v_ctx_1911_, lean_object* v_p_1912_, lean_object* v_acc_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_Grind_CommRing_Poly_denote_x27_go(v_00_u03b1_1909_, v_inst_1910_, v_ctx_1911_, v_p_1912_, v_acc_1913_);
lean_dec_ref(v_ctx_1911_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg(lean_object* v_inst_1915_, lean_object* v_ctx_1916_, lean_object* v_p_1917_){
_start:
{
if (lean_obj_tag(v_p_1917_) == 0)
{
lean_object* v_intCast_1918_; lean_object* v_k_1919_; lean_object* v___x_1920_; 
v_intCast_1918_ = lean_ctor_get(v_inst_1915_, 3);
lean_inc(v_intCast_1918_);
lean_dec_ref(v_inst_1915_);
v_k_1919_ = lean_ctor_get(v_p_1917_, 0);
lean_inc(v_k_1919_);
lean_dec_ref_known(v_p_1917_, 1);
v___x_1920_ = lean_apply_1(v_intCast_1918_, v_k_1919_);
return v___x_1920_;
}
else
{
lean_object* v_toSemiring_1921_; lean_object* v_k_1922_; lean_object* v_v_1923_; lean_object* v_p_1924_; lean_object* v___x_1925_; lean_object* v_zsmul_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v_toSemiring_1921_ = lean_ctor_get(v_inst_1915_, 0);
v_k_1922_ = lean_ctor_get(v_p_1917_, 0);
lean_inc(v_k_1922_);
v_v_1923_ = lean_ctor_get(v_p_1917_, 1);
lean_inc(v_v_1923_);
v_p_1924_ = lean_ctor_get(v_p_1917_, 2);
lean_inc_ref(v_p_1924_);
lean_dec_ref_known(v_p_1917_, 3);
lean_inc_ref(v_inst_1915_);
v___x_1925_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1915_);
v_zsmul_1926_ = lean_ctor_get(v___x_1925_, 2);
lean_inc(v_zsmul_1926_);
lean_dec_ref(v___x_1925_);
v___x_1927_ = lean_unsigned_to_nat(1u);
v___x_1928_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1929_ = lean_int_dec_eq(v_k_1922_, v___x_1928_);
if (v___x_1929_ == 0)
{
if (lean_obj_tag(v_v_1923_) == 0)
{
lean_object* v_ofNat_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_ofNat_1930_ = lean_ctor_get(v_toSemiring_1921_, 3);
lean_inc(v_ofNat_1930_);
v___x_1931_ = lean_apply_1(v_ofNat_1930_, v___x_1927_);
v___x_1932_ = lean_apply_2(v_zsmul_1926_, v_k_1922_, v___x_1931_);
v___x_1933_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1915_, v_ctx_1916_, v_p_1924_, v___x_1932_);
return v___x_1933_;
}
else
{
lean_object* v_p_1934_; lean_object* v_m_1935_; lean_object* v_ofNat_1936_; lean_object* v_npow_1937_; lean_object* v_x_1938_; lean_object* v_k_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v_p_1934_ = lean_ctor_get(v_v_1923_, 0);
lean_inc_ref(v_p_1934_);
v_m_1935_ = lean_ctor_get(v_v_1923_, 1);
lean_inc(v_m_1935_);
lean_dec_ref_known(v_v_1923_, 2);
v_ofNat_1936_ = lean_ctor_get(v_toSemiring_1921_, 3);
v_npow_1937_ = lean_ctor_get(v_toSemiring_1921_, 5);
v_x_1938_ = lean_ctor_get(v_p_1934_, 0);
lean_inc(v_x_1938_);
v_k_1939_ = lean_ctor_get(v_p_1934_, 1);
lean_inc(v_k_1939_);
lean_dec_ref(v_p_1934_);
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1941_ = lean_nat_dec_eq(v_k_1939_, v___x_1940_);
if (v___x_1941_ == 0)
{
uint8_t v___x_1942_; 
v___x_1942_ = lean_nat_dec_eq(v_k_1939_, v___x_1927_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1943_ = l_Lean_RArray_getImpl___redArg(v_ctx_1916_, v_x_1938_);
lean_dec(v_x_1938_);
lean_inc(v_npow_1937_);
v___x_1944_ = lean_apply_2(v_npow_1937_, v___x_1943_, v_k_1939_);
lean_inc_ref(v_toSemiring_1921_);
v___x_1945_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1921_, v_ctx_1916_, v_m_1935_, v___x_1944_);
v___x_1946_ = lean_apply_2(v_zsmul_1926_, v_k_1922_, v___x_1945_);
v___x_1947_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1915_, v_ctx_1916_, v_p_1924_, v___x_1946_);
return v___x_1947_;
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_dec(v_k_1939_);
v___x_1948_ = l_Lean_RArray_getImpl___redArg(v_ctx_1916_, v_x_1938_);
lean_dec(v_x_1938_);
lean_inc_ref(v_toSemiring_1921_);
v___x_1949_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1921_, v_ctx_1916_, v_m_1935_, v___x_1948_);
v___x_1950_ = lean_apply_2(v_zsmul_1926_, v_k_1922_, v___x_1949_);
v___x_1951_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1915_, v_ctx_1916_, v_p_1924_, v___x_1950_);
return v___x_1951_;
}
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec(v_k_1939_);
lean_dec(v_x_1938_);
lean_inc(v_ofNat_1936_);
v___x_1952_ = lean_apply_1(v_ofNat_1936_, v___x_1927_);
lean_inc_ref(v_toSemiring_1921_);
v___x_1953_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1921_, v_ctx_1916_, v_m_1935_, v___x_1952_);
v___x_1954_ = lean_apply_2(v_zsmul_1926_, v_k_1922_, v___x_1953_);
v___x_1955_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1915_, v_ctx_1916_, v_p_1924_, v___x_1954_);
return v___x_1955_;
}
}
}
else
{
lean_dec(v_zsmul_1926_);
lean_dec(v_k_1922_);
if (lean_obj_tag(v_v_1923_) == 0)
{
lean_object* v_ofNat_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v_ofNat_1956_ = lean_ctor_get(v_toSemiring_1921_, 3);
lean_inc(v_ofNat_1956_);
v___x_1957_ = lean_apply_1(v_ofNat_1956_, v___x_1927_);
v___x_1958_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1915_, v_ctx_1916_, v_p_1924_, v___x_1957_);
return v___x_1958_;
}
else
{
lean_object* v_p_1959_; lean_object* v_m_1960_; lean_object* v_ofNat_1961_; lean_object* v_npow_1962_; lean_object* v_x_1963_; lean_object* v_k_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v_p_1959_ = lean_ctor_get(v_v_1923_, 0);
lean_inc_ref(v_p_1959_);
v_m_1960_ = lean_ctor_get(v_v_1923_, 1);
lean_inc(v_m_1960_);
lean_dec_ref_known(v_v_1923_, 2);
v_ofNat_1961_ = lean_ctor_get(v_toSemiring_1921_, 3);
v_npow_1962_ = lean_ctor_get(v_toSemiring_1921_, 5);
v_x_1963_ = lean_ctor_get(v_p_1959_, 0);
lean_inc(v_x_1963_);
v_k_1964_ = lean_ctor_get(v_p_1959_, 1);
lean_inc(v_k_1964_);
lean_dec_ref(v_p_1959_);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = lean_nat_dec_eq(v_k_1964_, v___x_1965_);
if (v___x_1966_ == 0)
{
uint8_t v___x_1967_; 
v___x_1967_ = lean_nat_dec_eq(v_k_1964_, v___x_1927_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1968_ = l_Lean_RArray_getImpl___redArg(v_ctx_1916_, v_x_1963_);
lean_dec(v_x_1963_);
lean_inc(v_npow_1962_);
v___x_1969_ = lean_apply_2(v_npow_1962_, v___x_1968_, v_k_1964_);
lean_inc_ref(v_toSemiring_1921_);
v___x_1970_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1921_, v_ctx_1916_, v_m_1960_, v___x_1969_);
v___x_1971_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1915_, v_ctx_1916_, v_p_1924_, v___x_1970_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_dec(v_k_1964_);
v___x_1972_ = l_Lean_RArray_getImpl___redArg(v_ctx_1916_, v_x_1963_);
lean_dec(v_x_1963_);
lean_inc_ref(v_toSemiring_1921_);
v___x_1973_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1921_, v_ctx_1916_, v_m_1960_, v___x_1972_);
v___x_1974_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1915_, v_ctx_1916_, v_p_1924_, v___x_1973_);
return v___x_1974_;
}
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_dec(v_k_1964_);
lean_dec(v_x_1963_);
lean_inc(v_ofNat_1961_);
v___x_1975_ = lean_apply_1(v_ofNat_1961_, v___x_1927_);
lean_inc_ref(v_toSemiring_1921_);
v___x_1976_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1921_, v_ctx_1916_, v_m_1960_, v___x_1975_);
v___x_1977_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1915_, v_ctx_1916_, v_p_1924_, v___x_1976_);
return v___x_1977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg___boxed(lean_object* v_inst_1978_, lean_object* v_ctx_1979_, lean_object* v_p_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Grind_CommRing_Poly_denote_x27___redArg(v_inst_1978_, v_ctx_1979_, v_p_1980_);
lean_dec_ref(v_ctx_1979_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27(lean_object* v_00_u03b1_1982_, lean_object* v_inst_1983_, lean_object* v_ctx_1984_, lean_object* v_p_1985_){
_start:
{
if (lean_obj_tag(v_p_1985_) == 0)
{
lean_object* v_intCast_1986_; lean_object* v_k_1987_; lean_object* v___x_1988_; 
v_intCast_1986_ = lean_ctor_get(v_inst_1983_, 3);
lean_inc(v_intCast_1986_);
lean_dec_ref(v_inst_1983_);
v_k_1987_ = lean_ctor_get(v_p_1985_, 0);
lean_inc(v_k_1987_);
lean_dec_ref_known(v_p_1985_, 1);
v___x_1988_ = lean_apply_1(v_intCast_1986_, v_k_1987_);
return v___x_1988_;
}
else
{
lean_object* v_toSemiring_1989_; lean_object* v_k_1990_; lean_object* v_v_1991_; lean_object* v_p_1992_; lean_object* v___x_1993_; lean_object* v_zsmul_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v_toSemiring_1989_ = lean_ctor_get(v_inst_1983_, 0);
v_k_1990_ = lean_ctor_get(v_p_1985_, 0);
lean_inc(v_k_1990_);
v_v_1991_ = lean_ctor_get(v_p_1985_, 1);
lean_inc(v_v_1991_);
v_p_1992_ = lean_ctor_get(v_p_1985_, 2);
lean_inc_ref(v_p_1992_);
lean_dec_ref_known(v_p_1985_, 3);
lean_inc_ref(v_inst_1983_);
v___x_1993_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1983_);
v_zsmul_1994_ = lean_ctor_get(v___x_1993_, 2);
lean_inc(v_zsmul_1994_);
lean_dec_ref(v___x_1993_);
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1997_ = lean_int_dec_eq(v_k_1990_, v___x_1996_);
if (v___x_1997_ == 0)
{
if (lean_obj_tag(v_v_1991_) == 0)
{
lean_object* v_ofNat_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v_ofNat_1998_ = lean_ctor_get(v_toSemiring_1989_, 3);
lean_inc(v_ofNat_1998_);
v___x_1999_ = lean_apply_1(v_ofNat_1998_, v___x_1995_);
v___x_2000_ = lean_apply_2(v_zsmul_1994_, v_k_1990_, v___x_1999_);
v___x_2001_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1983_, v_ctx_1984_, v_p_1992_, v___x_2000_);
return v___x_2001_;
}
else
{
lean_object* v_p_2002_; lean_object* v_m_2003_; lean_object* v_ofNat_2004_; lean_object* v_npow_2005_; lean_object* v_x_2006_; lean_object* v_k_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v_p_2002_ = lean_ctor_get(v_v_1991_, 0);
lean_inc_ref(v_p_2002_);
v_m_2003_ = lean_ctor_get(v_v_1991_, 1);
lean_inc(v_m_2003_);
lean_dec_ref_known(v_v_1991_, 2);
v_ofNat_2004_ = lean_ctor_get(v_toSemiring_1989_, 3);
v_npow_2005_ = lean_ctor_get(v_toSemiring_1989_, 5);
v_x_2006_ = lean_ctor_get(v_p_2002_, 0);
lean_inc(v_x_2006_);
v_k_2007_ = lean_ctor_get(v_p_2002_, 1);
lean_inc(v_k_2007_);
lean_dec_ref(v_p_2002_);
v___x_2008_ = lean_unsigned_to_nat(0u);
v___x_2009_ = lean_nat_dec_eq(v_k_2007_, v___x_2008_);
if (v___x_2009_ == 0)
{
uint8_t v___x_2010_; 
v___x_2010_ = lean_nat_dec_eq(v_k_2007_, v___x_1995_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2011_ = l_Lean_RArray_getImpl___redArg(v_ctx_1984_, v_x_2006_);
lean_dec(v_x_2006_);
lean_inc(v_npow_2005_);
v___x_2012_ = lean_apply_2(v_npow_2005_, v___x_2011_, v_k_2007_);
lean_inc_ref(v_toSemiring_1989_);
v___x_2013_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1989_, v_ctx_1984_, v_m_2003_, v___x_2012_);
v___x_2014_ = lean_apply_2(v_zsmul_1994_, v_k_1990_, v___x_2013_);
v___x_2015_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1983_, v_ctx_1984_, v_p_1992_, v___x_2014_);
return v___x_2015_;
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec(v_k_2007_);
v___x_2016_ = l_Lean_RArray_getImpl___redArg(v_ctx_1984_, v_x_2006_);
lean_dec(v_x_2006_);
lean_inc_ref(v_toSemiring_1989_);
v___x_2017_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1989_, v_ctx_1984_, v_m_2003_, v___x_2016_);
v___x_2018_ = lean_apply_2(v_zsmul_1994_, v_k_1990_, v___x_2017_);
v___x_2019_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1983_, v_ctx_1984_, v_p_1992_, v___x_2018_);
return v___x_2019_;
}
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec(v_k_2007_);
lean_dec(v_x_2006_);
lean_inc(v_ofNat_2004_);
v___x_2020_ = lean_apply_1(v_ofNat_2004_, v___x_1995_);
lean_inc_ref(v_toSemiring_1989_);
v___x_2021_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1989_, v_ctx_1984_, v_m_2003_, v___x_2020_);
v___x_2022_ = lean_apply_2(v_zsmul_1994_, v_k_1990_, v___x_2021_);
v___x_2023_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1983_, v_ctx_1984_, v_p_1992_, v___x_2022_);
return v___x_2023_;
}
}
}
else
{
lean_dec(v_zsmul_1994_);
lean_dec(v_k_1990_);
if (lean_obj_tag(v_v_1991_) == 0)
{
lean_object* v_ofNat_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v_ofNat_2024_ = lean_ctor_get(v_toSemiring_1989_, 3);
lean_inc(v_ofNat_2024_);
v___x_2025_ = lean_apply_1(v_ofNat_2024_, v___x_1995_);
v___x_2026_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1983_, v_ctx_1984_, v_p_1992_, v___x_2025_);
return v___x_2026_;
}
else
{
lean_object* v_p_2027_; lean_object* v_m_2028_; lean_object* v_ofNat_2029_; lean_object* v_npow_2030_; lean_object* v_x_2031_; lean_object* v_k_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v_p_2027_ = lean_ctor_get(v_v_1991_, 0);
lean_inc_ref(v_p_2027_);
v_m_2028_ = lean_ctor_get(v_v_1991_, 1);
lean_inc(v_m_2028_);
lean_dec_ref_known(v_v_1991_, 2);
v_ofNat_2029_ = lean_ctor_get(v_toSemiring_1989_, 3);
v_npow_2030_ = lean_ctor_get(v_toSemiring_1989_, 5);
v_x_2031_ = lean_ctor_get(v_p_2027_, 0);
lean_inc(v_x_2031_);
v_k_2032_ = lean_ctor_get(v_p_2027_, 1);
lean_inc(v_k_2032_);
lean_dec_ref(v_p_2027_);
v___x_2033_ = lean_unsigned_to_nat(0u);
v___x_2034_ = lean_nat_dec_eq(v_k_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_nat_dec_eq(v_k_2032_, v___x_1995_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2036_ = l_Lean_RArray_getImpl___redArg(v_ctx_1984_, v_x_2031_);
lean_dec(v_x_2031_);
lean_inc(v_npow_2030_);
v___x_2037_ = lean_apply_2(v_npow_2030_, v___x_2036_, v_k_2032_);
lean_inc_ref(v_toSemiring_1989_);
v___x_2038_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1989_, v_ctx_1984_, v_m_2028_, v___x_2037_);
v___x_2039_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1983_, v_ctx_1984_, v_p_1992_, v___x_2038_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
lean_dec(v_k_2032_);
v___x_2040_ = l_Lean_RArray_getImpl___redArg(v_ctx_1984_, v_x_2031_);
lean_dec(v_x_2031_);
lean_inc_ref(v_toSemiring_1989_);
v___x_2041_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1989_, v_ctx_1984_, v_m_2028_, v___x_2040_);
v___x_2042_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1983_, v_ctx_1984_, v_p_1992_, v___x_2041_);
return v___x_2042_;
}
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec(v_k_2032_);
lean_dec(v_x_2031_);
lean_inc(v_ofNat_2029_);
v___x_2043_ = lean_apply_1(v_ofNat_2029_, v___x_1995_);
lean_inc_ref(v_toSemiring_1989_);
v___x_2044_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1989_, v_ctx_1984_, v_m_2028_, v___x_2043_);
v___x_2045_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1983_, v_ctx_1984_, v_p_1992_, v___x_2044_);
return v___x_2045_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___boxed(lean_object* v_00_u03b1_2046_, lean_object* v_inst_2047_, lean_object* v_ctx_2048_, lean_object* v_p_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_Grind_CommRing_Poly_denote_x27(v_00_u03b1_2046_, v_inst_2047_, v_ctx_2048_, v_p_2049_);
lean_dec_ref(v_ctx_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object* v_m_2051_){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2053_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2054_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2052_);
lean_ctor_set(v___x_2054_, 1, v_m_2051_);
lean_ctor_set(v___x_2054_, 2, v___x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object* v_x_2055_){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = l_Lean_Grind_CommRing_Mon_ofVar(v_x_2055_);
v___x_2057_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_isSorted(lean_object* v_x_2058_){
_start:
{
if (lean_obj_tag(v_x_2058_) == 0)
{
uint8_t v___x_2059_; 
v___x_2059_ = 1;
return v___x_2059_;
}
else
{
lean_object* v_p_2060_; 
v_p_2060_ = lean_ctor_get(v_x_2058_, 2);
if (lean_obj_tag(v_p_2060_) == 0)
{
uint8_t v___x_2061_; 
v___x_2061_ = 1;
return v___x_2061_;
}
else
{
lean_object* v_v_2062_; lean_object* v_v_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v_v_2062_ = lean_ctor_get(v_x_2058_, 1);
v_v_2063_ = lean_ctor_get(v_p_2060_, 1);
v___x_2064_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2062_, v_v_2063_);
v___x_2065_ = lean_box(v___x_2064_);
v___x_2066_ = lean_obj_tag_nat(v___x_2065_);
lean_dec(v___x_2065_);
v___x_2067_ = lean_unsigned_to_nat(2u);
v___x_2068_ = lean_nat_dec_eq(v___x_2066_, v___x_2067_);
if (v___x_2068_ == 0)
{
return v___x_2068_;
}
else
{
v_x_2058_ = v_p_2060_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isSorted___boxed(lean_object* v_x_2070_){
_start:
{
uint8_t v_res_2071_; lean_object* v_r_2072_; 
v_res_2071_ = l_Lean_Grind_CommRing_Poly_isSorted(v_x_2070_);
lean_dec_ref(v_x_2070_);
v_r_2072_ = lean_box(v_res_2071_);
return v_r_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go(lean_object* v_k_2073_, lean_object* v_a_2074_){
_start:
{
if (lean_obj_tag(v_a_2074_) == 0)
{
lean_object* v_k_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2083_; 
v_k_2075_ = lean_ctor_get(v_a_2074_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_a_2074_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2077_ = v_a_2074_;
v_isShared_2078_ = v_isSharedCheck_2083_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_k_2075_);
lean_dec(v_a_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2083_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = lean_int_add(v_k_2075_, v_k_2073_);
lean_dec(v_k_2075_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2079_);
v___x_2081_ = v___x_2077_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
lean_object* v_k_2084_; lean_object* v_v_2085_; lean_object* v_p_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2094_; 
v_k_2084_ = lean_ctor_get(v_a_2074_, 0);
v_v_2085_ = lean_ctor_get(v_a_2074_, 1);
v_p_2086_ = lean_ctor_get(v_a_2074_, 2);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_a_2074_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2088_ = v_a_2074_;
v_isShared_2089_ = v_isSharedCheck_2094_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_p_2086_);
lean_inc(v_v_2085_);
lean_inc(v_k_2084_);
lean_dec(v_a_2074_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2094_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2073_, v_p_2086_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 2, v___x_2090_);
v___x_2092_ = v___x_2088_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go___boxed(lean_object* v_k_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2095_, v_a_2096_);
lean_dec(v_k_2095_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object* v_p_2098_, lean_object* v_k_2099_){
_start:
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2101_ = lean_int_dec_eq(v_k_2099_, v___x_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2099_, v_p_2098_);
return v___x_2102_;
}
else
{
return v_p_2098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst___boxed(lean_object* v_p_2103_, lean_object* v_k_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2103_, v_k_2104_);
lean_dec(v_k_2104_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object* v_p_2106_, lean_object* v_h__1_2107_, lean_object* v_h__2_2108_){
_start:
{
if (lean_obj_tag(v_p_2106_) == 0)
{
lean_object* v_k_2109_; lean_object* v___x_2110_; 
lean_dec(v_h__2_2108_);
v_k_2109_ = lean_ctor_get(v_p_2106_, 0);
lean_inc(v_k_2109_);
lean_dec_ref_known(v_p_2106_, 1);
v___x_2110_ = lean_apply_1(v_h__1_2107_, v_k_2109_);
return v___x_2110_;
}
else
{
lean_object* v_k_2111_; lean_object* v_v_2112_; lean_object* v_p_2113_; lean_object* v___x_2114_; 
lean_dec(v_h__1_2107_);
v_k_2111_ = lean_ctor_get(v_p_2106_, 0);
lean_inc(v_k_2111_);
v_v_2112_ = lean_ctor_get(v_p_2106_, 1);
lean_inc(v_v_2112_);
v_p_2113_ = lean_ctor_get(v_p_2106_, 2);
lean_inc_ref(v_p_2113_);
lean_dec_ref_known(v_p_2106_, 3);
v___x_2114_ = lean_apply_3(v_h__2_2108_, v_k_2111_, v_v_2112_, v_p_2113_);
return v___x_2114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object* v_motive_2115_, lean_object* v_p_2116_, lean_object* v_h__1_2117_, lean_object* v_h__2_2118_){
_start:
{
if (lean_obj_tag(v_p_2116_) == 0)
{
lean_object* v_k_2119_; lean_object* v___x_2120_; 
lean_dec(v_h__2_2118_);
v_k_2119_ = lean_ctor_get(v_p_2116_, 0);
lean_inc(v_k_2119_);
lean_dec_ref_known(v_p_2116_, 1);
v___x_2120_ = lean_apply_1(v_h__1_2117_, v_k_2119_);
return v___x_2120_;
}
else
{
lean_object* v_k_2121_; lean_object* v_v_2122_; lean_object* v_p_2123_; lean_object* v___x_2124_; 
lean_dec(v_h__1_2117_);
v_k_2121_ = lean_ctor_get(v_p_2116_, 0);
lean_inc(v_k_2121_);
v_v_2122_ = lean_ctor_get(v_p_2116_, 1);
lean_inc(v_v_2122_);
v_p_2123_ = lean_ctor_get(v_p_2116_, 2);
lean_inc_ref(v_p_2123_);
lean_dec_ref_known(v_p_2116_, 3);
v___x_2124_ = lean_apply_3(v_h__2_2118_, v_k_2121_, v_v_2122_, v_p_2123_);
return v___x_2124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert_go(lean_object* v_k_2125_, lean_object* v_m_2126_, lean_object* v_a_2127_){
_start:
{
if (lean_obj_tag(v_a_2127_) == 0)
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2128_, 0, v_k_2125_);
lean_ctor_set(v___x_2128_, 1, v_m_2126_);
lean_ctor_set(v___x_2128_, 2, v_a_2127_);
return v___x_2128_;
}
else
{
lean_object* v_k_2129_; lean_object* v_v_2130_; lean_object* v_p_2131_; uint8_t v___x_2132_; 
v_k_2129_ = lean_ctor_get(v_a_2127_, 0);
v_v_2130_ = lean_ctor_get(v_a_2127_, 1);
v_p_2131_ = lean_ctor_get(v_a_2127_, 2);
v___x_2132_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2126_, v_v_2130_);
switch(v___x_2132_)
{
case 0:
{
lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2140_; 
lean_inc_ref(v_p_2131_);
lean_inc(v_v_2130_);
lean_inc(v_k_2129_);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_a_2127_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; lean_object* v_unused_2142_; lean_object* v_unused_2143_; 
v_unused_2141_ = lean_ctor_get(v_a_2127_, 2);
lean_dec(v_unused_2141_);
v_unused_2142_ = lean_ctor_get(v_a_2127_, 1);
lean_dec(v_unused_2142_);
v_unused_2143_ = lean_ctor_get(v_a_2127_, 0);
lean_dec(v_unused_2143_);
v___x_2134_ = v_a_2127_;
v_isShared_2135_ = v_isSharedCheck_2140_;
goto v_resetjp_2133_;
}
else
{
lean_dec(v_a_2127_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2140_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2136_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2125_, v_m_2126_, v_p_2131_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 2, v___x_2136_);
v___x_2138_ = v___x_2134_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_k_2129_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_v_2130_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
case 1:
{
lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2153_; 
lean_inc_ref(v_p_2131_);
lean_inc(v_k_2129_);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_a_2127_);
if (v_isSharedCheck_2153_ == 0)
{
lean_object* v_unused_2154_; lean_object* v_unused_2155_; lean_object* v_unused_2156_; 
v_unused_2154_ = lean_ctor_get(v_a_2127_, 2);
lean_dec(v_unused_2154_);
v_unused_2155_ = lean_ctor_get(v_a_2127_, 1);
lean_dec(v_unused_2155_);
v_unused_2156_ = lean_ctor_get(v_a_2127_, 0);
lean_dec(v_unused_2156_);
v___x_2145_ = v_a_2127_;
v_isShared_2146_ = v_isSharedCheck_2153_;
goto v_resetjp_2144_;
}
else
{
lean_dec(v_a_2127_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2153_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v_k_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
v_k_2147_ = lean_int_add(v_k_2125_, v_k_2129_);
lean_dec(v_k_2129_);
lean_dec(v_k_2125_);
v___x_2148_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2149_ = lean_int_dec_eq(v_k_2147_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2151_; 
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 1, v_m_2126_);
lean_ctor_set(v___x_2145_, 0, v_k_2147_);
v___x_2151_ = v___x_2145_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_k_2147_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_m_2126_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_p_2131_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
else
{
lean_dec(v_k_2147_);
lean_del_object(v___x_2145_);
lean_dec(v_m_2126_);
return v_p_2131_;
}
}
}
default: 
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2157_, 0, v_k_2125_);
lean_ctor_set(v___x_2157_, 1, v_m_2126_);
lean_ctor_set(v___x_2157_, 2, v_a_2127_);
return v___x_2157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert(lean_object* v_k_2158_, lean_object* v_m_2159_, lean_object* v_p_2160_){
_start:
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2162_ = lean_int_dec_eq(v_k_2158_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = lean_box(0);
v___x_2164_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2159_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2158_, v_m_2159_, v_p_2160_);
return v___x_2165_;
}
else
{
lean_object* v___x_2166_; 
lean_dec(v_m_2159_);
v___x_2166_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2160_, v_k_2158_);
lean_dec(v_k_2158_);
return v___x_2166_;
}
}
else
{
lean_dec(v_m_2159_);
lean_dec(v_k_2158_);
return v_p_2160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_concat(lean_object* v_p_u2081_2167_, lean_object* v_p_u2082_2168_){
_start:
{
if (lean_obj_tag(v_p_u2081_2167_) == 0)
{
lean_object* v_k_2169_; lean_object* v___x_2170_; 
v_k_2169_ = lean_ctor_get(v_p_u2081_2167_, 0);
lean_inc(v_k_2169_);
lean_dec_ref_known(v_p_u2081_2167_, 1);
v___x_2170_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2168_, v_k_2169_);
lean_dec(v_k_2169_);
return v___x_2170_;
}
else
{
lean_object* v_k_2171_; lean_object* v_v_2172_; lean_object* v_p_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2181_; 
v_k_2171_ = lean_ctor_get(v_p_u2081_2167_, 0);
v_v_2172_ = lean_ctor_get(v_p_u2081_2167_, 1);
v_p_2173_ = lean_ctor_get(v_p_u2081_2167_, 2);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_p_u2081_2167_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2175_ = v_p_u2081_2167_;
v_isShared_2176_ = v_isSharedCheck_2181_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_p_2173_);
lean_inc(v_v_2172_);
lean_inc(v_k_2171_);
lean_dec(v_p_u2081_2167_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2181_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2177_ = l_Lean_Grind_CommRing_Poly_concat(v_p_2173_, v_p_u2082_2168_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 2, v___x_2177_);
v___x_2179_ = v___x_2175_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_k_2171_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_v_2172_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go(lean_object* v_k_2182_, lean_object* v_a_2183_){
_start:
{
if (lean_obj_tag(v_a_2183_) == 0)
{
lean_object* v_k_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2192_; 
v_k_2184_ = lean_ctor_get(v_a_2183_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_a_2183_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2186_ = v_a_2183_;
v_isShared_2187_ = v_isSharedCheck_2192_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_k_2184_);
lean_dec(v_a_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2192_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2188_ = lean_int_mul(v_k_2182_, v_k_2184_);
lean_dec(v_k_2184_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2188_);
v___x_2190_ = v___x_2186_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
else
{
lean_object* v_k_2193_; lean_object* v_v_2194_; lean_object* v_p_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2204_; 
v_k_2193_ = lean_ctor_get(v_a_2183_, 0);
v_v_2194_ = lean_ctor_get(v_a_2183_, 1);
v_p_2195_ = lean_ctor_get(v_a_2183_, 2);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_a_2183_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2197_ = v_a_2183_;
v_isShared_2198_ = v_isSharedCheck_2204_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_p_2195_);
lean_inc(v_v_2194_);
lean_inc(v_k_2193_);
lean_dec(v_a_2183_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2204_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2202_; 
v___x_2199_ = lean_int_mul(v_k_2182_, v_k_2193_);
lean_dec(v_k_2193_);
v___x_2200_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2182_, v_p_2195_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 2, v___x_2200_);
lean_ctor_set(v___x_2197_, 0, v___x_2199_);
v___x_2202_ = v___x_2197_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_v_2194_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go___boxed(lean_object* v_k_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2205_, v_a_2206_);
lean_dec(v_k_2205_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object* v_k_2208_, lean_object* v_p_2209_){
_start:
{
lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___x_2210_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2211_ = lean_int_dec_eq(v_k_2208_, v___x_2210_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; uint8_t v___x_2213_; 
v___x_2212_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2213_ = lean_int_dec_eq(v_k_2208_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2208_, v_p_2209_);
return v___x_2214_;
}
else
{
return v_p_2209_;
}
}
else
{
lean_object* v___x_2215_; 
lean_dec_ref(v_p_2209_);
v___x_2215_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst___boxed(lean_object* v_k_2216_, lean_object* v_p_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2216_, v_p_2217_);
lean_dec(v_k_2216_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go(lean_object* v_k_2219_, lean_object* v_m_2220_, lean_object* v_a_2221_){
_start:
{
if (lean_obj_tag(v_a_2221_) == 0)
{
lean_object* v_k_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v_k_2222_ = lean_ctor_get(v_a_2221_, 0);
lean_inc(v_k_2222_);
lean_dec_ref_known(v_a_2221_, 1);
v___x_2223_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2224_ = lean_int_dec_eq(v_k_2222_, v___x_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = lean_int_mul(v_k_2219_, v_k_2222_);
lean_dec(v_k_2222_);
v___x_2226_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2225_);
lean_ctor_set(v___x_2227_, 1, v_m_2220_);
lean_ctor_set(v___x_2227_, 2, v___x_2226_);
return v___x_2227_;
}
else
{
lean_object* v___x_2228_; 
lean_dec(v_k_2222_);
lean_dec(v_m_2220_);
v___x_2228_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2228_;
}
}
else
{
lean_object* v_k_2229_; lean_object* v_v_2230_; lean_object* v_p_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2241_; 
v_k_2229_ = lean_ctor_get(v_a_2221_, 0);
v_v_2230_ = lean_ctor_get(v_a_2221_, 1);
v_p_2231_ = lean_ctor_get(v_a_2221_, 2);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_a_2221_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2233_ = v_a_2221_;
v_isShared_2234_ = v_isSharedCheck_2241_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_p_2231_);
lean_inc(v_v_2230_);
lean_inc(v_k_2229_);
lean_dec(v_a_2221_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2241_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2235_ = lean_int_mul(v_k_2219_, v_k_2229_);
lean_dec(v_k_2229_);
lean_inc(v_m_2220_);
v___x_2236_ = l_Lean_Grind_CommRing_Mon_mul(v_m_2220_, v_v_2230_);
v___x_2237_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2219_, v_m_2220_, v_p_2231_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 2, v___x_2237_);
lean_ctor_set(v___x_2233_, 1, v___x_2236_);
lean_ctor_set(v___x_2233_, 0, v___x_2235_);
v___x_2239_ = v___x_2233_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go___boxed(lean_object* v_k_2242_, lean_object* v_m_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2242_, v_m_2243_, v_a_2244_);
lean_dec(v_k_2242_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object* v_k_2246_, lean_object* v_m_2247_, lean_object* v_p_2248_){
_start:
{
lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2250_ = lean_int_dec_eq(v_k_2246_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = lean_box(0);
v___x_2252_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2247_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2246_, v_m_2247_, v_p_2248_);
return v___x_2253_;
}
else
{
lean_object* v___x_2254_; 
lean_dec(v_m_2247_);
v___x_2254_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2246_, v_p_2248_);
return v___x_2254_;
}
}
else
{
lean_object* v___x_2255_; 
lean_dec_ref(v_p_2248_);
lean_dec(v_m_2247_);
v___x_2255_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon___boxed(lean_object* v_k_2256_, lean_object* v_m_2257_, lean_object* v_p_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2256_, v_m_2257_, v_p_2258_);
lean_dec(v_k_2256_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go(lean_object* v_k_2260_, lean_object* v_m_2261_, lean_object* v_p_2262_, lean_object* v_acc_2263_){
_start:
{
if (lean_obj_tag(v_p_2262_) == 0)
{
lean_object* v_k_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_k_2264_ = lean_ctor_get(v_p_2262_, 0);
lean_inc(v_k_2264_);
lean_dec_ref_known(v_p_2262_, 1);
v___x_2265_ = lean_int_mul(v_k_2260_, v_k_2264_);
lean_dec(v_k_2264_);
v___x_2266_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2265_, v_m_2261_, v_acc_2263_);
return v___x_2266_;
}
else
{
lean_object* v_k_2267_; lean_object* v_v_2268_; lean_object* v_p_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_k_2267_ = lean_ctor_get(v_p_2262_, 0);
lean_inc(v_k_2267_);
v_v_2268_ = lean_ctor_get(v_p_2262_, 1);
lean_inc(v_v_2268_);
v_p_2269_ = lean_ctor_get(v_p_2262_, 2);
lean_inc_ref(v_p_2269_);
lean_dec_ref_known(v_p_2262_, 3);
v___x_2270_ = lean_int_mul(v_k_2260_, v_k_2267_);
lean_dec(v_k_2267_);
lean_inc(v_m_2261_);
v___x_2271_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_2261_, v_v_2268_);
v___x_2272_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2270_, v___x_2271_, v_acc_2263_);
v_p_2262_ = v_p_2269_;
v_acc_2263_ = v___x_2272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go___boxed(lean_object* v_k_2274_, lean_object* v_m_2275_, lean_object* v_p_2276_, lean_object* v_acc_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2274_, v_m_2275_, v_p_2276_, v_acc_2277_);
lean_dec(v_k_2274_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc(lean_object* v_k_2279_, lean_object* v_m_2280_, lean_object* v_p_2281_){
_start:
{
lean_object* v___x_2282_; uint8_t v___x_2283_; 
v___x_2282_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2283_ = lean_int_dec_eq(v_k_2279_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = lean_box(0);
v___x_2285_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2280_, v___x_2284_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2287_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2279_, v_m_2280_, v_p_2281_, v___x_2286_);
return v___x_2287_;
}
else
{
lean_object* v___x_2288_; 
lean_dec(v_m_2280_);
v___x_2288_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2279_, v_p_2281_);
return v___x_2288_;
}
}
else
{
lean_object* v___x_2289_; 
lean_dec_ref(v_p_2281_);
lean_dec(v_m_2280_);
v___x_2289_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc___boxed(lean_object* v_k_2290_, lean_object* v_m_2291_, lean_object* v_p_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2290_, v_m_2291_, v_p_2292_);
lean_dec(v_k_2290_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length(lean_object* v_x_2294_){
_start:
{
if (lean_obj_tag(v_x_2294_) == 0)
{
lean_object* v___x_2295_; 
v___x_2295_ = lean_unsigned_to_nat(0u);
return v___x_2295_;
}
else
{
lean_object* v_p_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v_p_2296_ = lean_ctor_get(v_x_2294_, 2);
v___x_2297_ = lean_unsigned_to_nat(1u);
v___x_2298_ = l_Lean_Grind_CommRing_Poly_length(v_p_2296_);
v___x_2299_ = lean_nat_add(v___x_2297_, v___x_2298_);
lean_dec(v___x_2298_);
return v___x_2299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length___boxed(lean_object* v_x_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Grind_CommRing_Poly_length(v_x_2300_);
lean_dec_ref(v_x_2300_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_go(lean_object* v_fuel_2302_, lean_object* v_p_u2081_2303_, lean_object* v_p_u2082_2304_){
_start:
{
lean_object* v_zero_2305_; uint8_t v_isZero_2306_; 
v_zero_2305_ = lean_unsigned_to_nat(0u);
v_isZero_2306_ = lean_nat_dec_eq(v_fuel_2302_, v_zero_2305_);
if (v_isZero_2306_ == 1)
{
lean_object* v___x_2307_; 
lean_dec(v_fuel_2302_);
v___x_2307_ = l_Lean_Grind_CommRing_Poly_concat(v_p_u2081_2303_, v_p_u2082_2304_);
return v___x_2307_;
}
else
{
if (lean_obj_tag(v_p_u2081_2303_) == 0)
{
lean_dec(v_fuel_2302_);
if (lean_obj_tag(v_p_u2082_2304_) == 0)
{
lean_object* v_k_2308_; lean_object* v_k_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2317_; 
v_k_2308_ = lean_ctor_get(v_p_u2081_2303_, 0);
lean_inc(v_k_2308_);
lean_dec_ref_known(v_p_u2081_2303_, 1);
v_k_2309_ = lean_ctor_get(v_p_u2082_2304_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_p_u2082_2304_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2311_ = v_p_u2082_2304_;
v_isShared_2312_ = v_isSharedCheck_2317_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_k_2309_);
lean_dec(v_p_u2082_2304_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2317_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2313_ = lean_int_add(v_k_2308_, v_k_2309_);
lean_dec(v_k_2309_);
lean_dec(v_k_2308_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v___x_2313_);
v___x_2315_ = v___x_2311_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
else
{
lean_object* v_k_2318_; lean_object* v___x_2319_; 
v_k_2318_ = lean_ctor_get(v_p_u2081_2303_, 0);
lean_inc(v_k_2318_);
lean_dec_ref_known(v_p_u2081_2303_, 1);
v___x_2319_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2304_, v_k_2318_);
lean_dec(v_k_2318_);
return v___x_2319_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_2304_) == 0)
{
lean_object* v_k_2320_; lean_object* v___x_2321_; 
lean_dec(v_fuel_2302_);
v_k_2320_ = lean_ctor_get(v_p_u2082_2304_, 0);
lean_inc(v_k_2320_);
lean_dec_ref_known(v_p_u2082_2304_, 1);
v___x_2321_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2081_2303_, v_k_2320_);
lean_dec(v_k_2320_);
return v___x_2321_;
}
else
{
lean_object* v_k_2322_; lean_object* v_v_2323_; lean_object* v_p_2324_; lean_object* v_k_2325_; lean_object* v_v_2326_; lean_object* v_p_2327_; lean_object* v_one_2328_; lean_object* v_n_2329_; uint8_t v___x_2330_; 
v_k_2322_ = lean_ctor_get(v_p_u2081_2303_, 0);
v_v_2323_ = lean_ctor_get(v_p_u2081_2303_, 1);
v_p_2324_ = lean_ctor_get(v_p_u2081_2303_, 2);
v_k_2325_ = lean_ctor_get(v_p_u2082_2304_, 0);
v_v_2326_ = lean_ctor_get(v_p_u2082_2304_, 1);
v_p_2327_ = lean_ctor_get(v_p_u2082_2304_, 2);
v_one_2328_ = lean_unsigned_to_nat(1u);
v_n_2329_ = lean_nat_sub(v_fuel_2302_, v_one_2328_);
lean_dec(v_fuel_2302_);
v___x_2330_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2323_, v_v_2326_);
switch(v___x_2330_)
{
case 0:
{
lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2338_; 
lean_inc_ref(v_p_2327_);
lean_inc(v_v_2326_);
lean_inc(v_k_2325_);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_p_u2082_2304_);
if (v_isSharedCheck_2338_ == 0)
{
lean_object* v_unused_2339_; lean_object* v_unused_2340_; lean_object* v_unused_2341_; 
v_unused_2339_ = lean_ctor_get(v_p_u2082_2304_, 2);
lean_dec(v_unused_2339_);
v_unused_2340_ = lean_ctor_get(v_p_u2082_2304_, 1);
lean_dec(v_unused_2340_);
v_unused_2341_ = lean_ctor_get(v_p_u2082_2304_, 0);
lean_dec(v_unused_2341_);
v___x_2332_ = v_p_u2082_2304_;
v_isShared_2333_ = v_isSharedCheck_2338_;
goto v_resetjp_2331_;
}
else
{
lean_dec(v_p_u2082_2304_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2338_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2334_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2329_, v_p_u2081_2303_, v_p_2327_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 2, v___x_2334_);
v___x_2336_ = v___x_2332_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_k_2325_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_v_2326_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
case 1:
{
lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2353_; 
lean_inc_ref(v_p_2327_);
lean_inc(v_k_2325_);
lean_inc_ref(v_p_2324_);
lean_inc(v_v_2323_);
lean_inc(v_k_2322_);
lean_dec_ref_known(v_p_u2081_2303_, 3);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_p_u2082_2304_);
if (v_isSharedCheck_2353_ == 0)
{
lean_object* v_unused_2354_; lean_object* v_unused_2355_; lean_object* v_unused_2356_; 
v_unused_2354_ = lean_ctor_get(v_p_u2082_2304_, 2);
lean_dec(v_unused_2354_);
v_unused_2355_ = lean_ctor_get(v_p_u2082_2304_, 1);
lean_dec(v_unused_2355_);
v_unused_2356_ = lean_ctor_get(v_p_u2082_2304_, 0);
lean_dec(v_unused_2356_);
v___x_2343_ = v_p_u2082_2304_;
v_isShared_2344_ = v_isSharedCheck_2353_;
goto v_resetjp_2342_;
}
else
{
lean_dec(v_p_u2082_2304_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2353_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_k_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v_k_2345_ = lean_int_add(v_k_2322_, v_k_2325_);
lean_dec(v_k_2325_);
lean_dec(v_k_2322_);
v___x_2346_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2347_ = lean_int_dec_eq(v_k_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2348_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2329_, v_p_2324_, v_p_2327_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 2, v___x_2348_);
lean_ctor_set(v___x_2343_, 1, v_v_2323_);
lean_ctor_set(v___x_2343_, 0, v_k_2345_);
v___x_2350_ = v___x_2343_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_k_2345_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_v_2323_);
lean_ctor_set(v_reuseFailAlloc_2351_, 2, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
else
{
lean_dec(v_k_2345_);
lean_del_object(v___x_2343_);
lean_dec(v_v_2323_);
v_fuel_2302_ = v_n_2329_;
v_p_u2081_2303_ = v_p_2324_;
v_p_u2082_2304_ = v_p_2327_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2364_; 
lean_inc_ref(v_p_2324_);
lean_inc(v_v_2323_);
lean_inc(v_k_2322_);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_p_u2081_2303_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; lean_object* v_unused_2366_; lean_object* v_unused_2367_; 
v_unused_2365_ = lean_ctor_get(v_p_u2081_2303_, 2);
lean_dec(v_unused_2365_);
v_unused_2366_ = lean_ctor_get(v_p_u2081_2303_, 1);
lean_dec(v_unused_2366_);
v_unused_2367_ = lean_ctor_get(v_p_u2081_2303_, 0);
lean_dec(v_unused_2367_);
v___x_2358_ = v_p_u2081_2303_;
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
else
{
lean_dec(v_p_u2081_2303_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2360_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2329_, v_p_2324_, v_p_u2082_2304_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 2, v___x_2360_);
v___x_2362_ = v___x_2358_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_k_2322_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v_v_2323_);
lean_ctor_set(v_reuseFailAlloc_2363_, 2, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object* v_p_u2081_2368_, lean_object* v_p_u2082_2369_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2370_ = l_Lean_Grind_CommRing_Poly_length(v_p_u2081_2368_);
v___x_2371_ = l_Lean_Grind_CommRing_Poly_length(v_p_u2082_2369_);
v___x_2372_ = lean_nat_add(v___x_2370_, v___x_2371_);
lean_dec(v___x_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_unsigned_to_nat(1u);
v___x_2374_ = lean_nat_add(v___x_2372_, v___x_2373_);
lean_dec(v___x_2372_);
v___x_2375_ = l_Lean_Grind_CommRing_Poly_combine_go(v___x_2374_, v_p_u2081_2368_, v_p_u2082_2369_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object* v_p_u2081_2376_, lean_object* v_p_u2082_2377_, lean_object* v_h__1_2378_, lean_object* v_h__2_2379_, lean_object* v_h__3_2380_, lean_object* v_h__4_2381_){
_start:
{
if (lean_obj_tag(v_p_u2081_2376_) == 0)
{
lean_dec(v_h__4_2381_);
lean_dec(v_h__3_2380_);
if (lean_obj_tag(v_p_u2082_2377_) == 0)
{
lean_object* v_k_2382_; lean_object* v_k_2383_; lean_object* v___x_2384_; 
lean_dec(v_h__2_2379_);
v_k_2382_ = lean_ctor_get(v_p_u2081_2376_, 0);
lean_inc(v_k_2382_);
lean_dec_ref_known(v_p_u2081_2376_, 1);
v_k_2383_ = lean_ctor_get(v_p_u2082_2377_, 0);
lean_inc(v_k_2383_);
lean_dec_ref_known(v_p_u2082_2377_, 1);
v___x_2384_ = lean_apply_2(v_h__1_2378_, v_k_2382_, v_k_2383_);
return v___x_2384_;
}
else
{
lean_object* v_k_2385_; lean_object* v_k_2386_; lean_object* v_v_2387_; lean_object* v_p_2388_; lean_object* v___x_2389_; 
lean_dec(v_h__1_2378_);
v_k_2385_ = lean_ctor_get(v_p_u2081_2376_, 0);
lean_inc(v_k_2385_);
lean_dec_ref_known(v_p_u2081_2376_, 1);
v_k_2386_ = lean_ctor_get(v_p_u2082_2377_, 0);
lean_inc(v_k_2386_);
v_v_2387_ = lean_ctor_get(v_p_u2082_2377_, 1);
lean_inc(v_v_2387_);
v_p_2388_ = lean_ctor_get(v_p_u2082_2377_, 2);
lean_inc_ref(v_p_2388_);
lean_dec_ref_known(v_p_u2082_2377_, 3);
v___x_2389_ = lean_apply_4(v_h__2_2379_, v_k_2385_, v_k_2386_, v_v_2387_, v_p_2388_);
return v___x_2389_;
}
}
else
{
lean_dec(v_h__2_2379_);
lean_dec(v_h__1_2378_);
if (lean_obj_tag(v_p_u2082_2377_) == 0)
{
lean_object* v_k_2390_; lean_object* v_v_2391_; lean_object* v_p_2392_; lean_object* v_k_2393_; lean_object* v___x_2394_; 
lean_dec(v_h__4_2381_);
v_k_2390_ = lean_ctor_get(v_p_u2081_2376_, 0);
lean_inc(v_k_2390_);
v_v_2391_ = lean_ctor_get(v_p_u2081_2376_, 1);
lean_inc(v_v_2391_);
v_p_2392_ = lean_ctor_get(v_p_u2081_2376_, 2);
lean_inc_ref(v_p_2392_);
lean_dec_ref_known(v_p_u2081_2376_, 3);
v_k_2393_ = lean_ctor_get(v_p_u2082_2377_, 0);
lean_inc(v_k_2393_);
lean_dec_ref_known(v_p_u2082_2377_, 1);
v___x_2394_ = lean_apply_4(v_h__3_2380_, v_k_2390_, v_v_2391_, v_p_2392_, v_k_2393_);
return v___x_2394_;
}
else
{
lean_object* v_k_2395_; lean_object* v_v_2396_; lean_object* v_p_2397_; lean_object* v_k_2398_; lean_object* v_v_2399_; lean_object* v_p_2400_; lean_object* v___x_2401_; 
lean_dec(v_h__3_2380_);
v_k_2395_ = lean_ctor_get(v_p_u2081_2376_, 0);
lean_inc(v_k_2395_);
v_v_2396_ = lean_ctor_get(v_p_u2081_2376_, 1);
lean_inc(v_v_2396_);
v_p_2397_ = lean_ctor_get(v_p_u2081_2376_, 2);
lean_inc_ref(v_p_2397_);
lean_dec_ref_known(v_p_u2081_2376_, 3);
v_k_2398_ = lean_ctor_get(v_p_u2082_2377_, 0);
lean_inc(v_k_2398_);
v_v_2399_ = lean_ctor_get(v_p_u2082_2377_, 1);
lean_inc(v_v_2399_);
v_p_2400_ = lean_ctor_get(v_p_u2082_2377_, 2);
lean_inc_ref(v_p_2400_);
lean_dec_ref_known(v_p_u2082_2377_, 3);
v___x_2401_ = lean_apply_6(v_h__4_2381_, v_k_2395_, v_v_2396_, v_p_2397_, v_k_2398_, v_v_2399_, v_p_2400_);
return v___x_2401_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object* v_motive_2402_, lean_object* v_p_u2081_2403_, lean_object* v_p_u2082_2404_, lean_object* v_h__1_2405_, lean_object* v_h__2_2406_, lean_object* v_h__3_2407_, lean_object* v_h__4_2408_){
_start:
{
if (lean_obj_tag(v_p_u2081_2403_) == 0)
{
lean_dec(v_h__4_2408_);
lean_dec(v_h__3_2407_);
if (lean_obj_tag(v_p_u2082_2404_) == 0)
{
lean_object* v_k_2409_; lean_object* v_k_2410_; lean_object* v___x_2411_; 
lean_dec(v_h__2_2406_);
v_k_2409_ = lean_ctor_get(v_p_u2081_2403_, 0);
lean_inc(v_k_2409_);
lean_dec_ref_known(v_p_u2081_2403_, 1);
v_k_2410_ = lean_ctor_get(v_p_u2082_2404_, 0);
lean_inc(v_k_2410_);
lean_dec_ref_known(v_p_u2082_2404_, 1);
v___x_2411_ = lean_apply_2(v_h__1_2405_, v_k_2409_, v_k_2410_);
return v___x_2411_;
}
else
{
lean_object* v_k_2412_; lean_object* v_k_2413_; lean_object* v_v_2414_; lean_object* v_p_2415_; lean_object* v___x_2416_; 
lean_dec(v_h__1_2405_);
v_k_2412_ = lean_ctor_get(v_p_u2081_2403_, 0);
lean_inc(v_k_2412_);
lean_dec_ref_known(v_p_u2081_2403_, 1);
v_k_2413_ = lean_ctor_get(v_p_u2082_2404_, 0);
lean_inc(v_k_2413_);
v_v_2414_ = lean_ctor_get(v_p_u2082_2404_, 1);
lean_inc(v_v_2414_);
v_p_2415_ = lean_ctor_get(v_p_u2082_2404_, 2);
lean_inc_ref(v_p_2415_);
lean_dec_ref_known(v_p_u2082_2404_, 3);
v___x_2416_ = lean_apply_4(v_h__2_2406_, v_k_2412_, v_k_2413_, v_v_2414_, v_p_2415_);
return v___x_2416_;
}
}
else
{
lean_dec(v_h__2_2406_);
lean_dec(v_h__1_2405_);
if (lean_obj_tag(v_p_u2082_2404_) == 0)
{
lean_object* v_k_2417_; lean_object* v_v_2418_; lean_object* v_p_2419_; lean_object* v_k_2420_; lean_object* v___x_2421_; 
lean_dec(v_h__4_2408_);
v_k_2417_ = lean_ctor_get(v_p_u2081_2403_, 0);
lean_inc(v_k_2417_);
v_v_2418_ = lean_ctor_get(v_p_u2081_2403_, 1);
lean_inc(v_v_2418_);
v_p_2419_ = lean_ctor_get(v_p_u2081_2403_, 2);
lean_inc_ref(v_p_2419_);
lean_dec_ref_known(v_p_u2081_2403_, 3);
v_k_2420_ = lean_ctor_get(v_p_u2082_2404_, 0);
lean_inc(v_k_2420_);
lean_dec_ref_known(v_p_u2082_2404_, 1);
v___x_2421_ = lean_apply_4(v_h__3_2407_, v_k_2417_, v_v_2418_, v_p_2419_, v_k_2420_);
return v___x_2421_;
}
else
{
lean_object* v_k_2422_; lean_object* v_v_2423_; lean_object* v_p_2424_; lean_object* v_k_2425_; lean_object* v_v_2426_; lean_object* v_p_2427_; lean_object* v___x_2428_; 
lean_dec(v_h__3_2407_);
v_k_2422_ = lean_ctor_get(v_p_u2081_2403_, 0);
lean_inc(v_k_2422_);
v_v_2423_ = lean_ctor_get(v_p_u2081_2403_, 1);
lean_inc(v_v_2423_);
v_p_2424_ = lean_ctor_get(v_p_u2081_2403_, 2);
lean_inc_ref(v_p_2424_);
lean_dec_ref_known(v_p_u2081_2403_, 3);
v_k_2425_ = lean_ctor_get(v_p_u2082_2404_, 0);
lean_inc(v_k_2425_);
v_v_2426_ = lean_ctor_get(v_p_u2082_2404_, 1);
lean_inc(v_v_2426_);
v_p_2427_ = lean_ctor_get(v_p_u2082_2404_, 2);
lean_inc_ref(v_p_2427_);
lean_dec_ref_known(v_p_u2082_2404_, 3);
v___x_2428_ = lean_apply_6(v_h__4_2408_, v_k_2422_, v_v_2423_, v_p_2424_, v_k_2425_, v_v_2426_, v_p_2427_);
return v___x_2428_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t v_x_2429_, lean_object* v_h__1_2430_, lean_object* v_h__2_2431_, lean_object* v_h__3_2432_){
_start:
{
switch(v_x_2429_)
{
case 0:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_dec(v_h__2_2431_);
lean_dec(v_h__1_2430_);
v___x_2433_ = lean_box(0);
v___x_2434_ = lean_apply_1(v_h__3_2432_, v___x_2433_);
return v___x_2434_;
}
case 1:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec(v_h__3_2432_);
lean_dec(v_h__2_2431_);
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_apply_1(v_h__1_2430_, v___x_2435_);
return v___x_2436_;
}
default: 
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
lean_dec(v_h__3_2432_);
lean_dec(v_h__1_2430_);
v___x_2437_ = lean_box(0);
v___x_2438_ = lean_apply_1(v_h__2_2431_, v___x_2437_);
return v___x_2438_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object* v_x_2439_, lean_object* v_h__1_2440_, lean_object* v_h__2_2441_, lean_object* v_h__3_2442_){
_start:
{
uint8_t v_x_33__boxed_2443_; lean_object* v_res_2444_; 
v_x_33__boxed_2443_ = lean_unbox(v_x_2439_);
v_res_2444_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(v_x_33__boxed_2443_, v_h__1_2440_, v_h__2_2441_, v_h__3_2442_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object* v_motive_2445_, uint8_t v_x_2446_, lean_object* v_h__1_2447_, lean_object* v_h__2_2448_, lean_object* v_h__3_2449_){
_start:
{
switch(v_x_2446_)
{
case 0:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
lean_dec(v_h__2_2448_);
lean_dec(v_h__1_2447_);
v___x_2450_ = lean_box(0);
v___x_2451_ = lean_apply_1(v_h__3_2449_, v___x_2450_);
return v___x_2451_;
}
case 1:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
lean_dec(v_h__3_2449_);
lean_dec(v_h__2_2448_);
v___x_2452_ = lean_box(0);
v___x_2453_ = lean_apply_1(v_h__1_2447_, v___x_2452_);
return v___x_2453_;
}
default: 
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
lean_dec(v_h__3_2449_);
lean_dec(v_h__1_2447_);
v___x_2454_ = lean_box(0);
v___x_2455_ = lean_apply_1(v_h__2_2448_, v___x_2454_);
return v___x_2455_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object* v_motive_2456_, lean_object* v_x_2457_, lean_object* v_h__1_2458_, lean_object* v_h__2_2459_, lean_object* v_h__3_2460_){
_start:
{
uint8_t v_x_48__boxed_2461_; lean_object* v_res_2462_; 
v_x_48__boxed_2461_ = lean_unbox(v_x_2457_);
v_res_2462_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(v_motive_2456_, v_x_48__boxed_2461_, v_h__1_2458_, v_h__2_2459_, v_h__3_2460_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul_go(lean_object* v_p_u2082_2463_, lean_object* v_p_u2081_2464_, lean_object* v_acc_2465_){
_start:
{
if (lean_obj_tag(v_p_u2081_2464_) == 0)
{
lean_object* v_k_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v_k_2466_ = lean_ctor_get(v_p_u2081_2464_, 0);
lean_inc(v_k_2466_);
lean_dec_ref_known(v_p_u2081_2464_, 1);
v___x_2467_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2466_, v_p_u2082_2463_);
lean_dec(v_k_2466_);
v___x_2468_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2465_, v___x_2467_);
return v___x_2468_;
}
else
{
lean_object* v_k_2469_; lean_object* v_v_2470_; lean_object* v_p_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v_k_2469_ = lean_ctor_get(v_p_u2081_2464_, 0);
lean_inc(v_k_2469_);
v_v_2470_ = lean_ctor_get(v_p_u2081_2464_, 1);
lean_inc(v_v_2470_);
v_p_2471_ = lean_ctor_get(v_p_u2081_2464_, 2);
lean_inc_ref(v_p_2471_);
lean_dec_ref_known(v_p_u2081_2464_, 3);
lean_inc_ref(v_p_u2082_2463_);
v___x_2472_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2469_, v_v_2470_, v_p_u2082_2463_);
lean_dec(v_k_2469_);
v___x_2473_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2465_, v___x_2472_);
v_p_u2081_2464_ = v_p_2471_;
v_acc_2465_ = v___x_2473_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul(lean_object* v_p_u2081_2475_, lean_object* v_p_u2082_2476_){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2478_ = l_Lean_Grind_CommRing_Poly_mul_go(v_p_u2082_2476_, v_p_u2081_2475_, v___x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc_go(lean_object* v_p_u2082_2479_, lean_object* v_p_u2081_2480_, lean_object* v_acc_2481_){
_start:
{
if (lean_obj_tag(v_p_u2081_2480_) == 0)
{
lean_object* v_k_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_k_2482_ = lean_ctor_get(v_p_u2081_2480_, 0);
lean_inc(v_k_2482_);
lean_dec_ref_known(v_p_u2081_2480_, 1);
v___x_2483_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2482_, v_p_u2082_2479_);
lean_dec(v_k_2482_);
v___x_2484_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2481_, v___x_2483_);
return v___x_2484_;
}
else
{
lean_object* v_k_2485_; lean_object* v_v_2486_; lean_object* v_p_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v_k_2485_ = lean_ctor_get(v_p_u2081_2480_, 0);
lean_inc(v_k_2485_);
v_v_2486_ = lean_ctor_get(v_p_u2081_2480_, 1);
lean_inc(v_v_2486_);
v_p_2487_ = lean_ctor_get(v_p_u2081_2480_, 2);
lean_inc_ref(v_p_2487_);
lean_dec_ref_known(v_p_u2081_2480_, 3);
lean_inc_ref(v_p_u2082_2479_);
v___x_2488_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2485_, v_v_2486_, v_p_u2082_2479_);
lean_dec(v_k_2485_);
v___x_2489_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2481_, v___x_2488_);
v_p_u2081_2480_ = v_p_2487_;
v_acc_2481_ = v___x_2489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object* v_p_u2081_2491_, lean_object* v_p_u2082_2492_){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2494_ = l_Lean_Grind_CommRing_Poly_mul__nc_go(v_p_u2082_2492_, v_p_u2081_2491_, v___x_2493_);
return v___x_2494_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_pow___closed__0(void){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow(lean_object* v_p_2497_, lean_object* v_k_2498_){
_start:
{
lean_object* v_zero_2499_; uint8_t v_isZero_2500_; 
v_zero_2499_ = lean_unsigned_to_nat(0u);
v_isZero_2500_ = lean_nat_dec_eq(v_k_2498_, v_zero_2499_);
if (v_isZero_2500_ == 1)
{
lean_object* v___x_2501_; 
lean_dec_ref(v_p_2497_);
v___x_2501_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2501_;
}
else
{
lean_object* v_one_2502_; lean_object* v_n_2503_; uint8_t v___x_2504_; 
v_one_2502_ = lean_unsigned_to_nat(1u);
v_n_2503_ = lean_nat_sub(v_k_2498_, v_one_2502_);
v___x_2504_ = lean_nat_dec_eq(v_n_2503_, v_zero_2499_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_inc_ref(v_p_2497_);
v___x_2505_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2497_, v_n_2503_);
lean_dec(v_n_2503_);
v___x_2506_ = l_Lean_Grind_CommRing_Poly_mul(v_p_2497_, v___x_2505_);
return v___x_2506_;
}
else
{
lean_dec(v_n_2503_);
return v_p_2497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow___boxed(lean_object* v_p_2507_, lean_object* v_k_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2507_, v_k_2508_);
lean_dec(v_k_2508_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc(lean_object* v_p_2510_, lean_object* v_k_2511_){
_start:
{
lean_object* v_zero_2512_; uint8_t v_isZero_2513_; 
v_zero_2512_ = lean_unsigned_to_nat(0u);
v_isZero_2513_ = lean_nat_dec_eq(v_k_2511_, v_zero_2512_);
if (v_isZero_2513_ == 1)
{
lean_object* v___x_2514_; 
lean_dec_ref(v_p_2510_);
v___x_2514_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2514_;
}
else
{
lean_object* v_one_2515_; lean_object* v_n_2516_; uint8_t v___x_2517_; 
v_one_2515_ = lean_unsigned_to_nat(1u);
v_n_2516_ = lean_nat_sub(v_k_2511_, v_one_2515_);
v___x_2517_ = lean_nat_dec_eq(v_n_2516_, v_zero_2512_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_inc_ref(v_p_2510_);
v___x_2518_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2510_, v_n_2516_);
lean_dec(v_n_2516_);
v___x_2519_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2518_, v_p_2510_);
return v___x_2519_;
}
else
{
lean_dec(v_n_2516_);
return v_p_2510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc___boxed(lean_object* v_p_2520_, lean_object* v_k_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2520_, v_k_2521_);
lean_dec(v_k_2521_);
return v_res_2522_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2524_ = lean_int_neg(v___x_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object* v_x_2525_){
_start:
{
switch(lean_obj_tag(v_x_2525_))
{
case 0:
{
lean_object* v_k_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_k_2526_ = lean_ctor_get(v_x_2525_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_x_2525_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v_x_2525_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_k_2526_);
lean_dec(v_x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_k_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
case 1:
{
lean_object* v_k_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2542_; 
v_k_2534_ = lean_ctor_get(v_x_2525_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_x_2525_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2536_ = v_x_2525_;
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_k_2534_);
lean_dec(v_x_2525_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2538_ = lean_nat_to_int(v_k_2534_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set_tag(v___x_2536_, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2538_);
v___x_2540_ = v___x_2536_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
case 2:
{
lean_object* v_k_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
v_k_2543_ = lean_ctor_get(v_x_2525_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_x_2525_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v_x_2525_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_k_2543_);
lean_dec(v_x_2525_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
lean_ctor_set_tag(v___x_2545_, 0);
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_k_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
case 3:
{
lean_object* v_i_2551_; lean_object* v___x_2552_; 
v_i_2551_ = lean_ctor_get(v_x_2525_, 0);
lean_inc(v_i_2551_);
lean_dec_ref_known(v_x_2525_, 1);
v___x_2552_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2551_);
return v___x_2552_;
}
case 4:
{
lean_object* v_a_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v_a_2553_ = lean_ctor_get(v_x_2525_, 0);
lean_inc_ref(v_a_2553_);
lean_dec_ref_known(v_x_2525_, 1);
v___x_2554_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2555_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2553_);
v___x_2556_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2554_, v___x_2555_);
return v___x_2556_;
}
case 5:
{
lean_object* v_a_2557_; lean_object* v_b_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v_a_2557_ = lean_ctor_get(v_x_2525_, 0);
lean_inc_ref(v_a_2557_);
v_b_2558_ = lean_ctor_get(v_x_2525_, 1);
lean_inc_ref(v_b_2558_);
lean_dec_ref_known(v_x_2525_, 2);
v___x_2559_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2557_);
v___x_2560_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2558_);
v___x_2561_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2559_, v___x_2560_);
return v___x_2561_;
}
case 6:
{
lean_object* v_a_2562_; lean_object* v_b_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v_a_2562_ = lean_ctor_get(v_x_2525_, 0);
lean_inc_ref(v_a_2562_);
v_b_2563_ = lean_ctor_get(v_x_2525_, 1);
lean_inc_ref(v_b_2563_);
lean_dec_ref_known(v_x_2525_, 2);
v___x_2564_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2562_);
v___x_2565_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2566_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2563_);
v___x_2567_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2565_, v___x_2566_);
v___x_2568_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2564_, v___x_2567_);
return v___x_2568_;
}
case 7:
{
lean_object* v_a_2569_; lean_object* v_b_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v_a_2569_ = lean_ctor_get(v_x_2525_, 0);
lean_inc_ref(v_a_2569_);
v_b_2570_ = lean_ctor_get(v_x_2525_, 1);
lean_inc_ref(v_b_2570_);
lean_dec_ref_known(v_x_2525_, 2);
v___x_2571_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2569_);
v___x_2572_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2570_);
v___x_2573_ = l_Lean_Grind_CommRing_Poly_mul(v___x_2571_, v___x_2572_);
return v___x_2573_;
}
default: 
{
lean_object* v_a_2574_; lean_object* v_k_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2607_; 
v_a_2574_ = lean_ctor_get(v_x_2525_, 0);
v_k_2575_ = lean_ctor_get(v_x_2525_, 1);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_x_2525_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2577_ = v_x_2525_;
v_isShared_2578_ = v_isSharedCheck_2607_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_k_2575_);
lean_inc(v_a_2574_);
lean_dec(v_x_2525_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2607_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v_n_2580_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2583_ = lean_unsigned_to_nat(0u);
v___x_2584_ = lean_nat_dec_eq(v_k_2575_, v___x_2583_);
if (v___x_2584_ == 0)
{
switch(lean_obj_tag(v_a_2574_))
{
case 0:
{
lean_object* v_k_2585_; 
lean_del_object(v___x_2577_);
v_k_2585_ = lean_ctor_get(v_a_2574_, 0);
lean_inc(v_k_2585_);
lean_dec_ref_known(v_a_2574_, 1);
v_n_2580_ = v_k_2585_;
goto v___jp_2579_;
}
case 2:
{
lean_object* v_k_2586_; 
lean_del_object(v___x_2577_);
v_k_2586_ = lean_ctor_get(v_a_2574_, 0);
lean_inc(v_k_2586_);
lean_dec_ref_known(v_a_2574_, 1);
v_n_2580_ = v_k_2586_;
goto v___jp_2579_;
}
case 1:
{
lean_object* v_k_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2596_; 
lean_del_object(v___x_2577_);
v_k_2587_ = lean_ctor_get(v_a_2574_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_a_2574_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2589_ = v_a_2574_;
v_isShared_2590_ = v_isSharedCheck_2596_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_k_2587_);
lean_dec(v_a_2574_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2596_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2591_ = lean_nat_to_int(v_k_2587_);
v___x_2592_ = l_Int_pow(v___x_2591_, v_k_2575_);
lean_dec(v_k_2575_);
lean_dec(v___x_2591_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set_tag(v___x_2589_, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2592_);
v___x_2594_ = v___x_2589_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
case 3:
{
lean_object* v_i_2597_; lean_object* v___x_2599_; 
v_i_2597_ = lean_ctor_get(v_a_2574_, 0);
lean_inc(v_i_2597_);
lean_dec_ref_known(v_a_2574_, 1);
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 0);
lean_ctor_set(v___x_2577_, 0, v_i_2597_);
v___x_2599_ = v___x_2577_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_i_2597_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_k_2575_);
v___x_2599_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = lean_box(0);
v___x_2601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2599_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2601_);
return v___x_2602_;
}
}
default: 
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
lean_del_object(v___x_2577_);
v___x_2604_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2574_);
v___x_2605_ = l_Lean_Grind_CommRing_Poly_pow(v___x_2604_, v_k_2575_);
lean_dec(v_k_2575_);
return v___x_2605_;
}
}
}
else
{
lean_object* v___x_2606_; 
lean_del_object(v___x_2577_);
lean_dec(v_k_2575_);
lean_dec_ref(v_a_2574_);
v___x_2606_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2606_;
}
v___jp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = l_Int_pow(v_n_2580_, v_k_2575_);
lean_dec(v_k_2575_);
lean_dec(v_n_2580_);
v___x_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
return v___x_2582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf(lean_object* v_m_2608_, lean_object* v_x_2609_){
_start:
{
if (lean_obj_tag(v_m_2608_) == 0)
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_unsigned_to_nat(0u);
return v___x_2610_;
}
else
{
lean_object* v_p_2611_; lean_object* v_m_2612_; lean_object* v_x_2613_; lean_object* v_k_2614_; uint8_t v___x_2615_; 
v_p_2611_ = lean_ctor_get(v_m_2608_, 0);
v_m_2612_ = lean_ctor_get(v_m_2608_, 1);
v_x_2613_ = lean_ctor_get(v_p_2611_, 0);
v_k_2614_ = lean_ctor_get(v_p_2611_, 1);
v___x_2615_ = lean_nat_dec_eq(v_x_2613_, v_x_2609_);
if (v___x_2615_ == 0)
{
v_m_2608_ = v_m_2612_;
goto _start;
}
else
{
lean_inc(v_k_2614_);
return v_k_2614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf___boxed(lean_object* v_m_2617_, lean_object* v_x_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_2617_, v_x_2618_);
lean_dec(v_x_2618_);
lean_dec(v_m_2617_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar(lean_object* v_m_2620_, lean_object* v_x_2621_){
_start:
{
if (lean_obj_tag(v_m_2620_) == 0)
{
return v_m_2620_;
}
else
{
lean_object* v_p_2622_; lean_object* v_m_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2633_; 
v_p_2622_ = lean_ctor_get(v_m_2620_, 0);
v_m_2623_ = lean_ctor_get(v_m_2620_, 1);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_m_2620_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2625_ = v_m_2620_;
v_isShared_2626_ = v_isSharedCheck_2633_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_m_2623_);
lean_inc(v_p_2622_);
lean_dec(v_m_2620_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2633_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v_x_2627_; uint8_t v___x_2628_; 
v_x_2627_ = lean_ctor_get(v_p_2622_, 0);
v___x_2628_ = lean_nat_dec_eq(v_x_2627_, v_x_2621_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2629_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2623_, v_x_2621_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 1, v___x_2629_);
v___x_2631_ = v___x_2625_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_p_2622_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v___x_2629_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
else
{
lean_del_object(v___x_2625_);
lean_dec_ref(v_p_2622_);
return v_m_2623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar___boxed(lean_object* v_m_2634_, lean_object* v_x_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2634_, v_x_2635_);
lean_dec(v_x_2635_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27(lean_object* v_c_2637_, lean_object* v_x_2638_, lean_object* v_p_2639_, lean_object* v_acc_2640_){
_start:
{
if (lean_obj_tag(v_p_2639_) == 0)
{
lean_object* v_k_2641_; lean_object* v___x_2642_; 
v_k_2641_ = lean_ctor_get(v_p_2639_, 0);
lean_inc(v_k_2641_);
lean_dec_ref_known(v_p_2639_, 1);
v___x_2642_ = l_Lean_Grind_CommRing_Poly_addConst(v_acc_2640_, v_k_2641_);
lean_dec(v_k_2641_);
return v___x_2642_;
}
else
{
lean_object* v_k_2643_; lean_object* v_v_2644_; lean_object* v_p_2645_; lean_object* v_n_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v_k_2643_ = lean_ctor_get(v_p_2639_, 0);
lean_inc(v_k_2643_);
v_v_2644_ = lean_ctor_get(v_p_2639_, 1);
lean_inc(v_v_2644_);
v_p_2645_ = lean_ctor_get(v_p_2639_, 2);
lean_inc_ref(v_p_2645_);
lean_dec_ref_known(v_p_2639_, 3);
v_n_2649_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_2644_, v_x_2638_);
v___x_2650_ = lean_unsigned_to_nat(0u);
v___x_2651_ = lean_nat_dec_lt(v___x_2650_, v_n_2649_);
if (v___x_2651_ == 0)
{
lean_dec(v_n_2649_);
goto v___jp_2646_;
}
else
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2652_ = l_Int_pow(v_c_2637_, v_n_2649_);
lean_dec(v_n_2649_);
v___x_2653_ = lean_int_emod(v_k_2643_, v___x_2652_);
v___x_2654_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2655_ = lean_int_dec_eq(v___x_2653_, v___x_2654_);
lean_dec(v___x_2653_);
if (v___x_2655_ == 0)
{
lean_dec(v___x_2652_);
goto v___jp_2646_;
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2656_ = lean_int_ediv(v_k_2643_, v___x_2652_);
lean_dec(v___x_2652_);
lean_dec(v_k_2643_);
v___x_2657_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_v_2644_, v_x_2638_);
v___x_2658_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2656_, v___x_2657_, v_acc_2640_);
v_p_2639_ = v_p_2645_;
v_acc_2640_ = v___x_2658_;
goto _start;
}
}
v___jp_2646_:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_Grind_CommRing_Poly_insert(v_k_2643_, v_v_2644_, v_acc_2640_);
v_p_2639_ = v_p_2645_;
v_acc_2640_ = v___x_2647_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27___boxed(lean_object* v_c_2660_, lean_object* v_x_2661_, lean_object* v_p_2662_, lean_object* v_acc_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2660_, v_x_2661_, v_p_2662_, v_acc_2663_);
lean_dec(v_x_2661_);
lean_dec(v_c_2660_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar(lean_object* v_c_2665_, lean_object* v_x_2666_, lean_object* v_p_2667_){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2669_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2665_, v_x_2666_, v_p_2667_, v___x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar___boxed(lean_object* v_c_2670_, lean_object* v_x_2671_, lean_object* v_p_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_Grind_CommRing_Poly_cancelVar(v_c_2670_, v_x_2671_, v_p_2672_);
lean_dec(v_x_2671_);
lean_dec(v_c_2670_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(lean_object* v_p_2674_, lean_object* v_acc_2675_){
_start:
{
lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = lean_unsigned_to_nat(1u);
v___x_2677_ = lean_nat_dec_eq(v_acc_2675_, v___x_2676_);
if (v___x_2677_ == 0)
{
if (lean_obj_tag(v_p_2674_) == 0)
{
lean_object* v_k_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v_k_2678_ = lean_ctor_get(v_p_2674_, 0);
v___x_2679_ = lean_nat_abs(v_k_2678_);
v___x_2680_ = lean_nat_gcd(v_acc_2675_, v___x_2679_);
lean_dec(v___x_2679_);
lean_dec(v_acc_2675_);
return v___x_2680_;
}
else
{
lean_object* v_k_2681_; lean_object* v_p_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v_k_2681_ = lean_ctor_get(v_p_2674_, 0);
v_p_2682_ = lean_ctor_get(v_p_2674_, 2);
v___x_2683_ = lean_nat_abs(v_k_2681_);
v___x_2684_ = lean_nat_gcd(v_acc_2675_, v___x_2683_);
lean_dec(v___x_2683_);
lean_dec(v_acc_2675_);
v_p_2674_ = v_p_2682_;
v_acc_2675_ = v___x_2684_;
goto _start;
}
}
else
{
return v_acc_2675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs_go___boxed(lean_object* v_p_2686_, lean_object* v_acc_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_2686_, v_acc_2687_);
lean_dec_ref(v_p_2686_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs(lean_object* v_x_2689_){
_start:
{
if (lean_obj_tag(v_x_2689_) == 0)
{
lean_object* v_k_2690_; lean_object* v___x_2691_; 
v_k_2690_ = lean_ctor_get(v_x_2689_, 0);
v___x_2691_ = lean_nat_abs(v_k_2690_);
return v___x_2691_;
}
else
{
lean_object* v_k_2692_; lean_object* v_p_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v_k_2692_ = lean_ctor_get(v_x_2689_, 0);
v_p_2693_ = lean_ctor_get(v_x_2689_, 2);
v___x_2694_ = lean_nat_abs(v_k_2692_);
v___x_2695_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_2693_, v___x_2694_);
return v___x_2695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs___boxed(lean_object* v_x_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs(v_x_2696_);
lean_dec_ref(v_x_2696_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst(lean_object* v_p_2698_, lean_object* v_a_2699_){
_start:
{
if (lean_obj_tag(v_p_2698_) == 0)
{
lean_object* v_k_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2708_; 
v_k_2700_ = lean_ctor_get(v_p_2698_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_p_2698_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2702_ = v_p_2698_;
v_isShared_2703_ = v_isSharedCheck_2708_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_k_2700_);
lean_dec(v_p_2698_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2708_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2704_ = lean_int_ediv(v_k_2700_, v_a_2699_);
lean_dec(v_k_2700_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v___x_2704_);
v___x_2706_ = v___x_2702_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
else
{
lean_object* v_k_2709_; lean_object* v_v_2710_; lean_object* v_p_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2720_; 
v_k_2709_ = lean_ctor_get(v_p_2698_, 0);
v_v_2710_ = lean_ctor_get(v_p_2698_, 1);
v_p_2711_ = lean_ctor_get(v_p_2698_, 2);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_p_2698_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2713_ = v_p_2698_;
v_isShared_2714_ = v_isSharedCheck_2720_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_p_2711_);
lean_inc(v_v_2710_);
lean_inc(v_k_2709_);
lean_dec(v_p_2698_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2720_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2715_ = lean_int_ediv(v_k_2709_, v_a_2699_);
lean_dec(v_k_2709_);
v___x_2716_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_2711_, v_a_2699_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 2, v___x_2716_);
lean_ctor_set(v___x_2713_, 0, v___x_2715_);
v___x_2718_ = v___x_2713_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2715_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v_v_2710_);
lean_ctor_set(v_reuseFailAlloc_2719_, 2, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst___boxed(lean_object* v_p_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_2721_, v_a_2722_);
lean_dec(v_a_2722_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(lean_object* v_x_2724_, lean_object* v_p_2725_, lean_object* v_max_2726_){
_start:
{
if (lean_obj_tag(v_p_2725_) == 0)
{
return v_max_2726_;
}
else
{
lean_object* v_v_2727_; lean_object* v_p_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v_v_2727_ = lean_ctor_get(v_p_2725_, 1);
v_p_2728_ = lean_ctor_get(v_p_2725_, 2);
v___x_2729_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_2727_, v_x_2724_);
v___x_2730_ = lean_nat_dec_le(v_max_2726_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_dec(v___x_2729_);
v_p_2725_ = v_p_2728_;
goto _start;
}
else
{
lean_dec(v_max_2726_);
v_p_2725_ = v_p_2728_;
v_max_2726_ = v___x_2729_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf_go___boxed(lean_object* v_x_2733_, lean_object* v_p_2734_, lean_object* v_max_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_2733_, v_p_2734_, v_max_2735_);
lean_dec_ref(v_p_2734_);
lean_dec(v_x_2733_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf(lean_object* v_p_2737_, lean_object* v_x_2738_){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = lean_unsigned_to_nat(0u);
v___x_2740_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_2738_, v_p_2737_, v___x_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf___boxed(lean_object* v_p_2741_, lean_object* v_x_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_2741_, v_x_2742_);
lean_dec(v_x_2742_);
lean_dec_ref(v_p_2741_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(lean_object* v_x_2744_, lean_object* v_h__1_2745_, lean_object* v_h__2_2746_, lean_object* v_h__3_2747_, lean_object* v_h__4_2748_, lean_object* v_h__5_2749_, lean_object* v_h__6_2750_, lean_object* v_h__7_2751_, lean_object* v_h__8_2752_, lean_object* v_h__9_2753_){
_start:
{
switch(lean_obj_tag(v_x_2744_))
{
case 0:
{
lean_object* v_k_2754_; lean_object* v___x_2755_; 
lean_dec(v_h__9_2753_);
lean_dec(v_h__8_2752_);
lean_dec(v_h__7_2751_);
lean_dec(v_h__6_2750_);
lean_dec(v_h__5_2749_);
lean_dec(v_h__4_2748_);
lean_dec(v_h__3_2747_);
lean_dec(v_h__2_2746_);
v_k_2754_ = lean_ctor_get(v_x_2744_, 0);
lean_inc(v_k_2754_);
lean_dec_ref_known(v_x_2744_, 1);
v___x_2755_ = lean_apply_1(v_h__1_2745_, v_k_2754_);
return v___x_2755_;
}
case 1:
{
lean_object* v_k_2756_; lean_object* v___x_2757_; 
lean_dec(v_h__9_2753_);
lean_dec(v_h__8_2752_);
lean_dec(v_h__7_2751_);
lean_dec(v_h__6_2750_);
lean_dec(v_h__5_2749_);
lean_dec(v_h__4_2748_);
lean_dec(v_h__2_2746_);
lean_dec(v_h__1_2745_);
v_k_2756_ = lean_ctor_get(v_x_2744_, 0);
lean_inc(v_k_2756_);
lean_dec_ref_known(v_x_2744_, 1);
v___x_2757_ = lean_apply_1(v_h__3_2747_, v_k_2756_);
return v___x_2757_;
}
case 2:
{
lean_object* v_k_2758_; lean_object* v___x_2759_; 
lean_dec(v_h__9_2753_);
lean_dec(v_h__8_2752_);
lean_dec(v_h__7_2751_);
lean_dec(v_h__6_2750_);
lean_dec(v_h__5_2749_);
lean_dec(v_h__4_2748_);
lean_dec(v_h__3_2747_);
lean_dec(v_h__1_2745_);
v_k_2758_ = lean_ctor_get(v_x_2744_, 0);
lean_inc(v_k_2758_);
lean_dec_ref_known(v_x_2744_, 1);
v___x_2759_ = lean_apply_1(v_h__2_2746_, v_k_2758_);
return v___x_2759_;
}
case 3:
{
lean_object* v_i_2760_; lean_object* v___x_2761_; 
lean_dec(v_h__9_2753_);
lean_dec(v_h__8_2752_);
lean_dec(v_h__7_2751_);
lean_dec(v_h__6_2750_);
lean_dec(v_h__5_2749_);
lean_dec(v_h__3_2747_);
lean_dec(v_h__2_2746_);
lean_dec(v_h__1_2745_);
v_i_2760_ = lean_ctor_get(v_x_2744_, 0);
lean_inc(v_i_2760_);
lean_dec_ref_known(v_x_2744_, 1);
v___x_2761_ = lean_apply_1(v_h__4_2748_, v_i_2760_);
return v___x_2761_;
}
case 4:
{
lean_object* v_a_2762_; lean_object* v___x_2763_; 
lean_dec(v_h__9_2753_);
lean_dec(v_h__8_2752_);
lean_dec(v_h__6_2750_);
lean_dec(v_h__5_2749_);
lean_dec(v_h__4_2748_);
lean_dec(v_h__3_2747_);
lean_dec(v_h__2_2746_);
lean_dec(v_h__1_2745_);
v_a_2762_ = lean_ctor_get(v_x_2744_, 0);
lean_inc_ref(v_a_2762_);
lean_dec_ref_known(v_x_2744_, 1);
v___x_2763_ = lean_apply_1(v_h__7_2751_, v_a_2762_);
return v___x_2763_;
}
case 5:
{
lean_object* v_a_2764_; lean_object* v_b_2765_; lean_object* v___x_2766_; 
lean_dec(v_h__9_2753_);
lean_dec(v_h__8_2752_);
lean_dec(v_h__7_2751_);
lean_dec(v_h__6_2750_);
lean_dec(v_h__4_2748_);
lean_dec(v_h__3_2747_);
lean_dec(v_h__2_2746_);
lean_dec(v_h__1_2745_);
v_a_2764_ = lean_ctor_get(v_x_2744_, 0);
lean_inc_ref(v_a_2764_);
v_b_2765_ = lean_ctor_get(v_x_2744_, 1);
lean_inc_ref(v_b_2765_);
lean_dec_ref_known(v_x_2744_, 2);
v___x_2766_ = lean_apply_2(v_h__5_2749_, v_a_2764_, v_b_2765_);
return v___x_2766_;
}
case 6:
{
lean_object* v_a_2767_; lean_object* v_b_2768_; lean_object* v___x_2769_; 
lean_dec(v_h__9_2753_);
lean_dec(v_h__7_2751_);
lean_dec(v_h__6_2750_);
lean_dec(v_h__5_2749_);
lean_dec(v_h__4_2748_);
lean_dec(v_h__3_2747_);
lean_dec(v_h__2_2746_);
lean_dec(v_h__1_2745_);
v_a_2767_ = lean_ctor_get(v_x_2744_, 0);
lean_inc_ref(v_a_2767_);
v_b_2768_ = lean_ctor_get(v_x_2744_, 1);
lean_inc_ref(v_b_2768_);
lean_dec_ref_known(v_x_2744_, 2);
v___x_2769_ = lean_apply_2(v_h__8_2752_, v_a_2767_, v_b_2768_);
return v___x_2769_;
}
case 7:
{
lean_object* v_a_2770_; lean_object* v_b_2771_; lean_object* v___x_2772_; 
lean_dec(v_h__9_2753_);
lean_dec(v_h__8_2752_);
lean_dec(v_h__7_2751_);
lean_dec(v_h__5_2749_);
lean_dec(v_h__4_2748_);
lean_dec(v_h__3_2747_);
lean_dec(v_h__2_2746_);
lean_dec(v_h__1_2745_);
v_a_2770_ = lean_ctor_get(v_x_2744_, 0);
lean_inc_ref(v_a_2770_);
v_b_2771_ = lean_ctor_get(v_x_2744_, 1);
lean_inc_ref(v_b_2771_);
lean_dec_ref_known(v_x_2744_, 2);
v___x_2772_ = lean_apply_2(v_h__6_2750_, v_a_2770_, v_b_2771_);
return v___x_2772_;
}
default: 
{
lean_object* v_a_2773_; lean_object* v_k_2774_; lean_object* v___x_2775_; 
lean_dec(v_h__8_2752_);
lean_dec(v_h__7_2751_);
lean_dec(v_h__6_2750_);
lean_dec(v_h__5_2749_);
lean_dec(v_h__4_2748_);
lean_dec(v_h__3_2747_);
lean_dec(v_h__2_2746_);
lean_dec(v_h__1_2745_);
v_a_2773_ = lean_ctor_get(v_x_2744_, 0);
lean_inc_ref(v_a_2773_);
v_k_2774_ = lean_ctor_get(v_x_2744_, 1);
lean_inc(v_k_2774_);
lean_dec_ref_known(v_x_2744_, 2);
v___x_2775_ = lean_apply_2(v_h__9_2753_, v_a_2773_, v_k_2774_);
return v___x_2775_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter(lean_object* v_motive_2776_, lean_object* v_x_2777_, lean_object* v_h__1_2778_, lean_object* v_h__2_2779_, lean_object* v_h__3_2780_, lean_object* v_h__4_2781_, lean_object* v_h__5_2782_, lean_object* v_h__6_2783_, lean_object* v_h__7_2784_, lean_object* v_h__8_2785_, lean_object* v_h__9_2786_){
_start:
{
switch(lean_obj_tag(v_x_2777_))
{
case 0:
{
lean_object* v_k_2787_; lean_object* v___x_2788_; 
lean_dec(v_h__9_2786_);
lean_dec(v_h__8_2785_);
lean_dec(v_h__7_2784_);
lean_dec(v_h__6_2783_);
lean_dec(v_h__5_2782_);
lean_dec(v_h__4_2781_);
lean_dec(v_h__3_2780_);
lean_dec(v_h__2_2779_);
v_k_2787_ = lean_ctor_get(v_x_2777_, 0);
lean_inc(v_k_2787_);
lean_dec_ref_known(v_x_2777_, 1);
v___x_2788_ = lean_apply_1(v_h__1_2778_, v_k_2787_);
return v___x_2788_;
}
case 1:
{
lean_object* v_k_2789_; lean_object* v___x_2790_; 
lean_dec(v_h__9_2786_);
lean_dec(v_h__8_2785_);
lean_dec(v_h__7_2784_);
lean_dec(v_h__6_2783_);
lean_dec(v_h__5_2782_);
lean_dec(v_h__4_2781_);
lean_dec(v_h__2_2779_);
lean_dec(v_h__1_2778_);
v_k_2789_ = lean_ctor_get(v_x_2777_, 0);
lean_inc(v_k_2789_);
lean_dec_ref_known(v_x_2777_, 1);
v___x_2790_ = lean_apply_1(v_h__3_2780_, v_k_2789_);
return v___x_2790_;
}
case 2:
{
lean_object* v_k_2791_; lean_object* v___x_2792_; 
lean_dec(v_h__9_2786_);
lean_dec(v_h__8_2785_);
lean_dec(v_h__7_2784_);
lean_dec(v_h__6_2783_);
lean_dec(v_h__5_2782_);
lean_dec(v_h__4_2781_);
lean_dec(v_h__3_2780_);
lean_dec(v_h__1_2778_);
v_k_2791_ = lean_ctor_get(v_x_2777_, 0);
lean_inc(v_k_2791_);
lean_dec_ref_known(v_x_2777_, 1);
v___x_2792_ = lean_apply_1(v_h__2_2779_, v_k_2791_);
return v___x_2792_;
}
case 3:
{
lean_object* v_i_2793_; lean_object* v___x_2794_; 
lean_dec(v_h__9_2786_);
lean_dec(v_h__8_2785_);
lean_dec(v_h__7_2784_);
lean_dec(v_h__6_2783_);
lean_dec(v_h__5_2782_);
lean_dec(v_h__3_2780_);
lean_dec(v_h__2_2779_);
lean_dec(v_h__1_2778_);
v_i_2793_ = lean_ctor_get(v_x_2777_, 0);
lean_inc(v_i_2793_);
lean_dec_ref_known(v_x_2777_, 1);
v___x_2794_ = lean_apply_1(v_h__4_2781_, v_i_2793_);
return v___x_2794_;
}
case 4:
{
lean_object* v_a_2795_; lean_object* v___x_2796_; 
lean_dec(v_h__9_2786_);
lean_dec(v_h__8_2785_);
lean_dec(v_h__6_2783_);
lean_dec(v_h__5_2782_);
lean_dec(v_h__4_2781_);
lean_dec(v_h__3_2780_);
lean_dec(v_h__2_2779_);
lean_dec(v_h__1_2778_);
v_a_2795_ = lean_ctor_get(v_x_2777_, 0);
lean_inc_ref(v_a_2795_);
lean_dec_ref_known(v_x_2777_, 1);
v___x_2796_ = lean_apply_1(v_h__7_2784_, v_a_2795_);
return v___x_2796_;
}
case 5:
{
lean_object* v_a_2797_; lean_object* v_b_2798_; lean_object* v___x_2799_; 
lean_dec(v_h__9_2786_);
lean_dec(v_h__8_2785_);
lean_dec(v_h__7_2784_);
lean_dec(v_h__6_2783_);
lean_dec(v_h__4_2781_);
lean_dec(v_h__3_2780_);
lean_dec(v_h__2_2779_);
lean_dec(v_h__1_2778_);
v_a_2797_ = lean_ctor_get(v_x_2777_, 0);
lean_inc_ref(v_a_2797_);
v_b_2798_ = lean_ctor_get(v_x_2777_, 1);
lean_inc_ref(v_b_2798_);
lean_dec_ref_known(v_x_2777_, 2);
v___x_2799_ = lean_apply_2(v_h__5_2782_, v_a_2797_, v_b_2798_);
return v___x_2799_;
}
case 6:
{
lean_object* v_a_2800_; lean_object* v_b_2801_; lean_object* v___x_2802_; 
lean_dec(v_h__9_2786_);
lean_dec(v_h__7_2784_);
lean_dec(v_h__6_2783_);
lean_dec(v_h__5_2782_);
lean_dec(v_h__4_2781_);
lean_dec(v_h__3_2780_);
lean_dec(v_h__2_2779_);
lean_dec(v_h__1_2778_);
v_a_2800_ = lean_ctor_get(v_x_2777_, 0);
lean_inc_ref(v_a_2800_);
v_b_2801_ = lean_ctor_get(v_x_2777_, 1);
lean_inc_ref(v_b_2801_);
lean_dec_ref_known(v_x_2777_, 2);
v___x_2802_ = lean_apply_2(v_h__8_2785_, v_a_2800_, v_b_2801_);
return v___x_2802_;
}
case 7:
{
lean_object* v_a_2803_; lean_object* v_b_2804_; lean_object* v___x_2805_; 
lean_dec(v_h__9_2786_);
lean_dec(v_h__8_2785_);
lean_dec(v_h__7_2784_);
lean_dec(v_h__5_2782_);
lean_dec(v_h__4_2781_);
lean_dec(v_h__3_2780_);
lean_dec(v_h__2_2779_);
lean_dec(v_h__1_2778_);
v_a_2803_ = lean_ctor_get(v_x_2777_, 0);
lean_inc_ref(v_a_2803_);
v_b_2804_ = lean_ctor_get(v_x_2777_, 1);
lean_inc_ref(v_b_2804_);
lean_dec_ref_known(v_x_2777_, 2);
v___x_2805_ = lean_apply_2(v_h__6_2783_, v_a_2803_, v_b_2804_);
return v___x_2805_;
}
default: 
{
lean_object* v_a_2806_; lean_object* v_k_2807_; lean_object* v___x_2808_; 
lean_dec(v_h__8_2785_);
lean_dec(v_h__7_2784_);
lean_dec(v_h__6_2783_);
lean_dec(v_h__5_2782_);
lean_dec(v_h__4_2781_);
lean_dec(v_h__3_2780_);
lean_dec(v_h__2_2779_);
lean_dec(v_h__1_2778_);
v_a_2806_ = lean_ctor_get(v_x_2777_, 0);
lean_inc_ref(v_a_2806_);
v_k_2807_ = lean_ctor_get(v_x_2777_, 1);
lean_inc(v_k_2807_);
lean_dec_ref_known(v_x_2777_, 2);
v___x_2808_ = lean_apply_2(v_h__9_2786_, v_a_2806_, v_k_2807_);
return v___x_2808_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter___redArg(lean_object* v_a_2809_, lean_object* v_h__1_2810_, lean_object* v_h__2_2811_, lean_object* v_h__3_2812_, lean_object* v_h__4_2813_, lean_object* v_h__5_2814_){
_start:
{
switch(lean_obj_tag(v_a_2809_))
{
case 0:
{
lean_object* v_k_2815_; lean_object* v___x_2816_; 
lean_dec(v_h__5_2814_);
lean_dec(v_h__4_2813_);
lean_dec(v_h__3_2812_);
lean_dec(v_h__2_2811_);
v_k_2815_ = lean_ctor_get(v_a_2809_, 0);
lean_inc(v_k_2815_);
lean_dec_ref_known(v_a_2809_, 1);
v___x_2816_ = lean_apply_1(v_h__1_2810_, v_k_2815_);
return v___x_2816_;
}
case 2:
{
lean_object* v_k_2817_; lean_object* v___x_2818_; 
lean_dec(v_h__5_2814_);
lean_dec(v_h__4_2813_);
lean_dec(v_h__3_2812_);
lean_dec(v_h__1_2810_);
v_k_2817_ = lean_ctor_get(v_a_2809_, 0);
lean_inc(v_k_2817_);
lean_dec_ref_known(v_a_2809_, 1);
v___x_2818_ = lean_apply_1(v_h__2_2811_, v_k_2817_);
return v___x_2818_;
}
case 1:
{
lean_object* v_k_2819_; lean_object* v___x_2820_; 
lean_dec(v_h__5_2814_);
lean_dec(v_h__4_2813_);
lean_dec(v_h__2_2811_);
lean_dec(v_h__1_2810_);
v_k_2819_ = lean_ctor_get(v_a_2809_, 0);
lean_inc(v_k_2819_);
lean_dec_ref_known(v_a_2809_, 1);
v___x_2820_ = lean_apply_1(v_h__3_2812_, v_k_2819_);
return v___x_2820_;
}
case 3:
{
lean_object* v_i_2821_; lean_object* v___x_2822_; 
lean_dec(v_h__5_2814_);
lean_dec(v_h__3_2812_);
lean_dec(v_h__2_2811_);
lean_dec(v_h__1_2810_);
v_i_2821_ = lean_ctor_get(v_a_2809_, 0);
lean_inc(v_i_2821_);
lean_dec_ref_known(v_a_2809_, 1);
v___x_2822_ = lean_apply_1(v_h__4_2813_, v_i_2821_);
return v___x_2822_;
}
default: 
{
lean_object* v___x_2823_; 
lean_dec(v_h__4_2813_);
lean_dec(v_h__3_2812_);
lean_dec(v_h__2_2811_);
lean_dec(v_h__1_2810_);
v___x_2823_ = lean_apply_5(v_h__5_2814_, v_a_2809_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2823_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter(lean_object* v_motive_2824_, lean_object* v_a_2825_, lean_object* v_h__1_2826_, lean_object* v_h__2_2827_, lean_object* v_h__3_2828_, lean_object* v_h__4_2829_, lean_object* v_h__5_2830_){
_start:
{
switch(lean_obj_tag(v_a_2825_))
{
case 0:
{
lean_object* v_k_2831_; lean_object* v___x_2832_; 
lean_dec(v_h__5_2830_);
lean_dec(v_h__4_2829_);
lean_dec(v_h__3_2828_);
lean_dec(v_h__2_2827_);
v_k_2831_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_k_2831_);
lean_dec_ref_known(v_a_2825_, 1);
v___x_2832_ = lean_apply_1(v_h__1_2826_, v_k_2831_);
return v___x_2832_;
}
case 2:
{
lean_object* v_k_2833_; lean_object* v___x_2834_; 
lean_dec(v_h__5_2830_);
lean_dec(v_h__4_2829_);
lean_dec(v_h__3_2828_);
lean_dec(v_h__1_2826_);
v_k_2833_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_k_2833_);
lean_dec_ref_known(v_a_2825_, 1);
v___x_2834_ = lean_apply_1(v_h__2_2827_, v_k_2833_);
return v___x_2834_;
}
case 1:
{
lean_object* v_k_2835_; lean_object* v___x_2836_; 
lean_dec(v_h__5_2830_);
lean_dec(v_h__4_2829_);
lean_dec(v_h__2_2827_);
lean_dec(v_h__1_2826_);
v_k_2835_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_k_2835_);
lean_dec_ref_known(v_a_2825_, 1);
v___x_2836_ = lean_apply_1(v_h__3_2828_, v_k_2835_);
return v___x_2836_;
}
case 3:
{
lean_object* v_i_2837_; lean_object* v___x_2838_; 
lean_dec(v_h__5_2830_);
lean_dec(v_h__3_2828_);
lean_dec(v_h__2_2827_);
lean_dec(v_h__1_2826_);
v_i_2837_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_i_2837_);
lean_dec_ref_known(v_a_2825_, 1);
v___x_2838_ = lean_apply_1(v_h__4_2829_, v_i_2837_);
return v___x_2838_;
}
default: 
{
lean_object* v___x_2839_; 
lean_dec(v_h__4_2829_);
lean_dec(v_h__3_2828_);
lean_dec(v_h__2_2827_);
lean_dec(v_h__1_2826_);
v___x_2839_ = lean_apply_5(v_h__5_2830_, v_a_2825_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly__nc(lean_object* v_x_2840_){
_start:
{
switch(lean_obj_tag(v_x_2840_))
{
case 0:
{
lean_object* v_k_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
v_k_2841_ = lean_ctor_get(v_x_2840_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_x_2840_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v_x_2840_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_k_2841_);
lean_dec(v_x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_k_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
case 1:
{
lean_object* v_k_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2857_; 
v_k_2849_ = lean_ctor_get(v_x_2840_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_x_2840_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2851_ = v_x_2840_;
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_k_2849_);
lean_dec(v_x_2840_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; lean_object* v___x_2855_; 
v___x_2853_ = lean_nat_to_int(v_k_2849_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set_tag(v___x_2851_, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2853_);
v___x_2855_ = v___x_2851_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2853_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
case 2:
{
lean_object* v_k_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
v_k_2858_ = lean_ctor_get(v_x_2840_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_x_2840_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v_x_2840_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_k_2858_);
lean_dec(v_x_2840_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
lean_ctor_set_tag(v___x_2860_, 0);
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_k_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
case 3:
{
lean_object* v_i_2866_; lean_object* v___x_2867_; 
v_i_2866_ = lean_ctor_get(v_x_2840_, 0);
lean_inc(v_i_2866_);
lean_dec_ref_known(v_x_2840_, 1);
v___x_2867_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2866_);
return v___x_2867_;
}
case 4:
{
lean_object* v_a_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_a_2868_ = lean_ctor_get(v_x_2840_, 0);
lean_inc_ref(v_a_2868_);
lean_dec_ref_known(v_x_2840_, 1);
v___x_2869_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2870_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2868_);
v___x_2871_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2869_, v___x_2870_);
return v___x_2871_;
}
case 5:
{
lean_object* v_a_2872_; lean_object* v_b_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v_a_2872_ = lean_ctor_get(v_x_2840_, 0);
lean_inc_ref(v_a_2872_);
v_b_2873_ = lean_ctor_get(v_x_2840_, 1);
lean_inc_ref(v_b_2873_);
lean_dec_ref_known(v_x_2840_, 2);
v___x_2874_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2872_);
v___x_2875_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2873_);
v___x_2876_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2874_, v___x_2875_);
return v___x_2876_;
}
case 6:
{
lean_object* v_a_2877_; lean_object* v_b_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v_a_2877_ = lean_ctor_get(v_x_2840_, 0);
lean_inc_ref(v_a_2877_);
v_b_2878_ = lean_ctor_get(v_x_2840_, 1);
lean_inc_ref(v_b_2878_);
lean_dec_ref_known(v_x_2840_, 2);
v___x_2879_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2877_);
v___x_2880_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2881_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2878_);
v___x_2882_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2880_, v___x_2881_);
v___x_2883_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2879_, v___x_2882_);
return v___x_2883_;
}
case 7:
{
lean_object* v_a_2884_; lean_object* v_b_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v_a_2884_ = lean_ctor_get(v_x_2840_, 0);
lean_inc_ref(v_a_2884_);
v_b_2885_ = lean_ctor_get(v_x_2840_, 1);
lean_inc_ref(v_b_2885_);
lean_dec_ref_known(v_x_2840_, 2);
v___x_2886_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2884_);
v___x_2887_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2885_);
v___x_2888_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2886_, v___x_2887_);
return v___x_2888_;
}
default: 
{
lean_object* v_a_2889_; lean_object* v_k_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2922_; 
v_a_2889_ = lean_ctor_get(v_x_2840_, 0);
v_k_2890_ = lean_ctor_get(v_x_2840_, 1);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_x_2840_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2892_ = v_x_2840_;
v_isShared_2893_ = v_isSharedCheck_2922_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_k_2890_);
lean_inc(v_a_2889_);
lean_dec(v_x_2840_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2922_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v_n_2895_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v___x_2898_ = lean_unsigned_to_nat(0u);
v___x_2899_ = lean_nat_dec_eq(v_k_2890_, v___x_2898_);
if (v___x_2899_ == 0)
{
switch(lean_obj_tag(v_a_2889_))
{
case 0:
{
lean_object* v_k_2900_; 
lean_del_object(v___x_2892_);
v_k_2900_ = lean_ctor_get(v_a_2889_, 0);
lean_inc(v_k_2900_);
lean_dec_ref_known(v_a_2889_, 1);
v_n_2895_ = v_k_2900_;
goto v___jp_2894_;
}
case 2:
{
lean_object* v_k_2901_; 
lean_del_object(v___x_2892_);
v_k_2901_ = lean_ctor_get(v_a_2889_, 0);
lean_inc(v_k_2901_);
lean_dec_ref_known(v_a_2889_, 1);
v_n_2895_ = v_k_2901_;
goto v___jp_2894_;
}
case 1:
{
lean_object* v_k_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2911_; 
lean_del_object(v___x_2892_);
v_k_2902_ = lean_ctor_get(v_a_2889_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_a_2889_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2904_ = v_a_2889_;
v_isShared_2905_ = v_isSharedCheck_2911_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_k_2902_);
lean_dec(v_a_2889_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2911_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2906_ = lean_nat_to_int(v_k_2902_);
v___x_2907_ = l_Int_pow(v___x_2906_, v_k_2890_);
lean_dec(v_k_2890_);
lean_dec(v___x_2906_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set_tag(v___x_2904_, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2907_);
v___x_2909_ = v___x_2904_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
case 3:
{
lean_object* v_i_2912_; lean_object* v___x_2914_; 
v_i_2912_ = lean_ctor_get(v_a_2889_, 0);
lean_inc(v_i_2912_);
lean_dec_ref_known(v_a_2889_, 1);
if (v_isShared_2893_ == 0)
{
lean_ctor_set_tag(v___x_2892_, 0);
lean_ctor_set(v___x_2892_, 0, v_i_2912_);
v___x_2914_ = v___x_2892_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_i_2912_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_k_2890_);
v___x_2914_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2915_ = lean_box(0);
v___x_2916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2914_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
v___x_2917_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2916_);
return v___x_2917_;
}
}
default: 
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
lean_del_object(v___x_2892_);
v___x_2919_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2889_);
v___x_2920_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_2919_, v_k_2890_);
lean_dec(v_k_2890_);
return v___x_2920_;
}
}
}
else
{
lean_object* v___x_2921_; 
lean_del_object(v___x_2892_);
lean_dec(v_k_2890_);
lean_dec_ref(v_a_2889_);
v___x_2921_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2921_;
}
v___jp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = l_Int_pow(v_n_2895_, v_k_2890_);
lean_dec(v_k_2890_);
lean_dec(v_n_2895_);
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
return v___x_2897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_normEq0(lean_object* v_p_2923_, lean_object* v_c_2924_){
_start:
{
if (lean_obj_tag(v_p_2923_) == 0)
{
lean_object* v_k_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
v_k_2925_ = lean_ctor_get(v_p_2923_, 0);
v___x_2926_ = lean_nat_to_int(v_c_2924_);
v___x_2927_ = lean_int_emod(v_k_2925_, v___x_2926_);
lean_dec(v___x_2926_);
v___x_2928_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2929_ = lean_int_dec_eq(v___x_2927_, v___x_2928_);
lean_dec(v___x_2927_);
if (v___x_2929_ == 0)
{
return v_p_2923_;
}
else
{
lean_object* v___x_2930_; 
lean_dec_ref_known(v_p_2923_, 1);
v___x_2930_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2930_;
}
}
else
{
lean_object* v_k_2931_; lean_object* v_v_2932_; lean_object* v_p_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2946_; 
v_k_2931_ = lean_ctor_get(v_p_2923_, 0);
v_v_2932_ = lean_ctor_get(v_p_2923_, 1);
v_p_2933_ = lean_ctor_get(v_p_2923_, 2);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_p_2923_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2935_ = v_p_2923_;
v_isShared_2936_ = v_isSharedCheck_2946_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_p_2933_);
lean_inc(v_v_2932_);
lean_inc(v_k_2931_);
lean_dec(v_p_2923_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2946_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
lean_inc(v_c_2924_);
v___x_2937_ = lean_nat_to_int(v_c_2924_);
v___x_2938_ = lean_int_emod(v_k_2931_, v___x_2937_);
lean_dec(v___x_2937_);
v___x_2939_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2940_ = lean_int_dec_eq(v___x_2938_, v___x_2939_);
lean_dec(v___x_2938_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; lean_object* v___x_2943_; 
v___x_2941_ = l_Lean_Grind_CommRing_Poly_normEq0(v_p_2933_, v_c_2924_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 2, v___x_2941_);
v___x_2943_ = v___x_2935_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_k_2931_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_v_2932_);
lean_ctor_set(v_reuseFailAlloc_2944_, 2, v___x_2941_);
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
lean_del_object(v___x_2935_);
lean_dec(v_v_2932_);
lean_dec(v_k_2931_);
v_p_2923_ = v_p_2933_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object* v_p_2947_, lean_object* v_k_2948_, lean_object* v_c_2949_){
_start:
{
if (lean_obj_tag(v_p_2947_) == 0)
{
lean_object* v_k_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2960_; 
v_k_2950_ = lean_ctor_get(v_p_2947_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_p_2947_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2952_ = v_p_2947_;
v_isShared_2953_ = v_isSharedCheck_2960_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_k_2950_);
lean_dec(v_p_2947_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2960_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2954_ = lean_int_add(v_k_2950_, v_k_2948_);
lean_dec(v_k_2950_);
v___x_2955_ = lean_nat_to_int(v_c_2949_);
v___x_2956_ = lean_int_emod(v___x_2954_, v___x_2955_);
lean_dec(v___x_2955_);
lean_dec(v___x_2954_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 0, v___x_2956_);
v___x_2958_ = v___x_2952_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2956_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
else
{
lean_object* v_k_2961_; lean_object* v_v_2962_; lean_object* v_p_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2971_; 
v_k_2961_ = lean_ctor_get(v_p_2947_, 0);
v_v_2962_ = lean_ctor_get(v_p_2947_, 1);
v_p_2963_ = lean_ctor_get(v_p_2947_, 2);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_p_2947_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2965_ = v_p_2947_;
v_isShared_2966_ = v_isSharedCheck_2971_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_p_2963_);
lean_inc(v_v_2962_);
lean_inc(v_k_2961_);
lean_dec(v_p_2947_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2971_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2967_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2963_, v_k_2948_, v_c_2949_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 2, v___x_2967_);
v___x_2969_ = v___x_2965_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_k_2961_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_v_2962_);
lean_ctor_set(v_reuseFailAlloc_2970_, 2, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC___boxed(lean_object* v_p_2972_, lean_object* v_k_2973_, lean_object* v_c_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2972_, v_k_2973_, v_c_2974_);
lean_dec(v_k_2973_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC_go(lean_object* v_m_2976_, lean_object* v_c_2977_, lean_object* v_k_2978_, lean_object* v_a_2979_){
_start:
{
if (lean_obj_tag(v_a_2979_) == 0)
{
lean_object* v___x_2980_; 
lean_dec(v_c_2977_);
v___x_2980_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2980_, 0, v_k_2978_);
lean_ctor_set(v___x_2980_, 1, v_m_2976_);
lean_ctor_set(v___x_2980_, 2, v_a_2979_);
return v___x_2980_;
}
else
{
lean_object* v_k_2981_; lean_object* v_v_2982_; lean_object* v_p_2983_; uint8_t v___x_2984_; 
v_k_2981_ = lean_ctor_get(v_a_2979_, 0);
v_v_2982_ = lean_ctor_get(v_a_2979_, 1);
v_p_2983_ = lean_ctor_get(v_a_2979_, 2);
v___x_2984_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2976_, v_v_2982_);
switch(v___x_2984_)
{
case 0:
{
lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2992_; 
lean_inc_ref(v_p_2983_);
lean_inc(v_v_2982_);
lean_inc(v_k_2981_);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_a_2979_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; lean_object* v_unused_2994_; lean_object* v_unused_2995_; 
v_unused_2993_ = lean_ctor_get(v_a_2979_, 2);
lean_dec(v_unused_2993_);
v_unused_2994_ = lean_ctor_get(v_a_2979_, 1);
lean_dec(v_unused_2994_);
v_unused_2995_ = lean_ctor_get(v_a_2979_, 0);
lean_dec(v_unused_2995_);
v___x_2986_ = v_a_2979_;
v_isShared_2987_ = v_isSharedCheck_2992_;
goto v_resetjp_2985_;
}
else
{
lean_dec(v_a_2979_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2992_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2988_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_2976_, v_c_2977_, v_k_2978_, v_p_2983_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 2, v___x_2988_);
v___x_2990_ = v___x_2986_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_k_2981_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_v_2982_);
lean_ctor_set(v_reuseFailAlloc_2991_, 2, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
case 1:
{
lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3007_; 
lean_inc_ref(v_p_2983_);
lean_inc(v_k_2981_);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_a_2979_);
if (v_isSharedCheck_3007_ == 0)
{
lean_object* v_unused_3008_; lean_object* v_unused_3009_; lean_object* v_unused_3010_; 
v_unused_3008_ = lean_ctor_get(v_a_2979_, 2);
lean_dec(v_unused_3008_);
v_unused_3009_ = lean_ctor_get(v_a_2979_, 1);
lean_dec(v_unused_3009_);
v_unused_3010_ = lean_ctor_get(v_a_2979_, 0);
lean_dec(v_unused_3010_);
v___x_2997_ = v_a_2979_;
v_isShared_2998_ = v_isSharedCheck_3007_;
goto v_resetjp_2996_;
}
else
{
lean_dec(v_a_2979_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3007_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v_k_x27_x27_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_2999_ = lean_int_add(v_k_2978_, v_k_2981_);
lean_dec(v_k_2981_);
lean_dec(v_k_2978_);
v___x_3000_ = lean_nat_to_int(v_c_2977_);
v_k_x27_x27_3001_ = lean_int_emod(v___x_2999_, v___x_3000_);
lean_dec(v___x_3000_);
lean_dec(v___x_2999_);
v___x_3002_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3003_ = lean_int_dec_eq(v_k_x27_x27_3001_, v___x_3002_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3005_; 
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 1, v_m_2976_);
lean_ctor_set(v___x_2997_, 0, v_k_x27_x27_3001_);
v___x_3005_ = v___x_2997_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_k_x27_x27_3001_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_m_2976_);
lean_ctor_set(v_reuseFailAlloc_3006_, 2, v_p_2983_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
else
{
lean_dec(v_k_x27_x27_3001_);
lean_del_object(v___x_2997_);
lean_dec(v_m_2976_);
return v_p_2983_;
}
}
}
default: 
{
lean_object* v___x_3011_; 
lean_dec(v_c_2977_);
v___x_3011_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3011_, 0, v_k_2978_);
lean_ctor_set(v___x_3011_, 1, v_m_2976_);
lean_ctor_set(v___x_3011_, 2, v_a_2979_);
return v___x_3011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC(lean_object* v_k_3012_, lean_object* v_m_3013_, lean_object* v_p_3014_, lean_object* v_c_3015_){
_start:
{
lean_object* v___x_3016_; lean_object* v_k_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
lean_inc(v_c_3015_);
v___x_3016_ = lean_nat_to_int(v_c_3015_);
v_k_3017_ = lean_int_emod(v_k_3012_, v___x_3016_);
lean_dec(v___x_3016_);
v___x_3018_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3019_ = lean_int_dec_eq(v_k_3017_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_3013_, v_c_3015_, v_k_3017_, v_p_3014_);
return v___x_3020_;
}
else
{
lean_dec(v_k_3017_);
lean_dec(v_c_3015_);
lean_dec(v_m_3013_);
return v_p_3014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC___boxed(lean_object* v_k_3021_, lean_object* v_m_3022_, lean_object* v_p_3023_, lean_object* v_c_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_Grind_CommRing_Poly_insertC(v_k_3021_, v_m_3022_, v_p_3023_, v_c_3024_);
lean_dec(v_k_3021_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go(lean_object* v_k_3026_, lean_object* v_c_3027_, lean_object* v_a_3028_){
_start:
{
if (lean_obj_tag(v_a_3028_) == 0)
{
lean_object* v_k_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3039_; 
v_k_3029_ = lean_ctor_get(v_a_3028_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_a_3028_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3031_ = v_a_3028_;
v_isShared_3032_ = v_isSharedCheck_3039_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_k_3029_);
lean_dec(v_a_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3039_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___x_3033_ = lean_int_mul(v_k_3026_, v_k_3029_);
lean_dec(v_k_3029_);
v___x_3034_ = lean_nat_to_int(v_c_3027_);
v___x_3035_ = lean_int_emod(v___x_3033_, v___x_3034_);
lean_dec(v___x_3034_);
lean_dec(v___x_3033_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3035_);
v___x_3037_ = v___x_3031_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
else
{
lean_object* v_k_3040_; lean_object* v_v_3041_; lean_object* v_p_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3056_; 
v_k_3040_ = lean_ctor_get(v_a_3028_, 0);
v_v_3041_ = lean_ctor_get(v_a_3028_, 1);
v_p_3042_ = lean_ctor_get(v_a_3028_, 2);
v_isSharedCheck_3056_ = !lean_is_exclusive(v_a_3028_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3044_ = v_a_3028_;
v_isShared_3045_ = v_isSharedCheck_3056_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_p_3042_);
lean_inc(v_v_3041_);
lean_inc(v_k_3040_);
lean_dec(v_a_3028_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3056_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v_k_3048_; lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3046_ = lean_int_mul(v_k_3026_, v_k_3040_);
lean_dec(v_k_3040_);
lean_inc(v_c_3027_);
v___x_3047_ = lean_nat_to_int(v_c_3027_);
v_k_3048_ = lean_int_emod(v___x_3046_, v___x_3047_);
lean_dec(v___x_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3050_ = lean_int_dec_eq(v_k_3048_, v___x_3049_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; lean_object* v___x_3053_; 
v___x_3051_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_3026_, v_c_3027_, v_p_3042_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 2, v___x_3051_);
lean_ctor_set(v___x_3044_, 0, v_k_3048_);
v___x_3053_ = v___x_3044_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_k_3048_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_v_3041_);
lean_ctor_set(v_reuseFailAlloc_3054_, 2, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
else
{
lean_dec(v_k_3048_);
lean_del_object(v___x_3044_);
lean_dec(v_v_3041_);
v_a_3028_ = v_p_3042_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go___boxed(lean_object* v_k_3057_, lean_object* v_c_3058_, lean_object* v_a_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_3057_, v_c_3058_, v_a_3059_);
lean_dec(v_k_3057_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object* v_k_3061_, lean_object* v_p_3062_, lean_object* v_c_3063_){
_start:
{
lean_object* v___x_3064_; lean_object* v_k_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
lean_inc(v_c_3063_);
v___x_3064_ = lean_nat_to_int(v_c_3063_);
v_k_3065_ = lean_int_emod(v_k_3061_, v___x_3064_);
lean_dec(v___x_3064_);
v___x_3066_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3067_ = lean_int_dec_eq(v_k_3065_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3068_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_3069_ = lean_int_dec_eq(v_k_3065_, v___x_3068_);
lean_dec(v_k_3065_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_3061_, v_c_3063_, v_p_3062_);
return v___x_3070_;
}
else
{
lean_dec(v_c_3063_);
return v_p_3062_;
}
}
else
{
lean_object* v___x_3071_; 
lean_dec(v_k_3065_);
lean_dec(v_c_3063_);
lean_dec_ref(v_p_3062_);
v___x_3071_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC___boxed(lean_object* v_k_3072_, lean_object* v_p_3073_, lean_object* v_c_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3072_, v_p_3073_, v_c_3074_);
lean_dec(v_k_3072_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go(lean_object* v_k_3076_, lean_object* v_m_3077_, lean_object* v_c_3078_, lean_object* v_a_3079_){
_start:
{
if (lean_obj_tag(v_a_3079_) == 0)
{
lean_object* v_k_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v_k_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v_k_3080_ = lean_ctor_get(v_a_3079_, 0);
lean_inc(v_k_3080_);
lean_dec_ref_known(v_a_3079_, 1);
v___x_3081_ = lean_int_mul(v_k_3076_, v_k_3080_);
lean_dec(v_k_3080_);
v___x_3082_ = lean_nat_to_int(v_c_3078_);
v_k_3083_ = lean_int_emod(v___x_3081_, v___x_3082_);
lean_dec(v___x_3082_);
lean_dec(v___x_3081_);
v___x_3084_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3085_ = lean_int_dec_eq(v_k_3083_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3087_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3087_, 0, v_k_3083_);
lean_ctor_set(v___x_3087_, 1, v_m_3077_);
lean_ctor_set(v___x_3087_, 2, v___x_3086_);
return v___x_3087_;
}
else
{
lean_object* v___x_3088_; 
lean_dec(v_k_3083_);
lean_dec(v_m_3077_);
v___x_3088_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3088_;
}
}
else
{
lean_object* v_k_3089_; lean_object* v_v_3090_; lean_object* v_p_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3106_; 
v_k_3089_ = lean_ctor_get(v_a_3079_, 0);
v_v_3090_ = lean_ctor_get(v_a_3079_, 1);
v_p_3091_ = lean_ctor_get(v_a_3079_, 2);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_a_3079_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3093_ = v_a_3079_;
v_isShared_3094_ = v_isSharedCheck_3106_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_p_3091_);
lean_inc(v_v_3090_);
lean_inc(v_k_3089_);
lean_dec(v_a_3079_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3106_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v_k_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3095_ = lean_int_mul(v_k_3076_, v_k_3089_);
lean_dec(v_k_3089_);
lean_inc(v_c_3078_);
v___x_3096_ = lean_nat_to_int(v_c_3078_);
v_k_3097_ = lean_int_emod(v___x_3095_, v___x_3096_);
lean_dec(v___x_3096_);
lean_dec(v___x_3095_);
v___x_3098_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3099_ = lean_int_dec_eq(v_k_3097_, v___x_3098_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3103_; 
lean_inc(v_m_3077_);
v___x_3100_ = l_Lean_Grind_CommRing_Mon_mul(v_m_3077_, v_v_3090_);
v___x_3101_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3076_, v_m_3077_, v_c_3078_, v_p_3091_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 2, v___x_3101_);
lean_ctor_set(v___x_3093_, 1, v___x_3100_);
lean_ctor_set(v___x_3093_, 0, v_k_3097_);
v___x_3103_ = v___x_3093_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_k_3097_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
else
{
lean_dec(v_k_3097_);
lean_del_object(v___x_3093_);
lean_dec(v_v_3090_);
v_a_3079_ = v_p_3091_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go___boxed(lean_object* v_k_3107_, lean_object* v_m_3108_, lean_object* v_c_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3107_, v_m_3108_, v_c_3109_, v_a_3110_);
lean_dec(v_k_3107_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object* v_k_3112_, lean_object* v_m_3113_, lean_object* v_p_3114_, lean_object* v_c_3115_){
_start:
{
lean_object* v___x_3116_; lean_object* v_k_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; 
lean_inc(v_c_3115_);
v___x_3116_ = lean_nat_to_int(v_c_3115_);
v_k_3117_ = lean_int_emod(v_k_3112_, v___x_3116_);
lean_dec(v___x_3116_);
v___x_3118_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3119_ = lean_int_dec_eq(v_k_3117_, v___x_3118_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3120_ = lean_box(0);
v___x_3121_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_3113_, v___x_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; 
lean_dec(v_k_3117_);
v___x_3122_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_3112_, v_m_3113_, v_c_3115_, v_p_3114_);
return v___x_3122_;
}
else
{
lean_object* v___x_3123_; 
lean_dec(v_m_3113_);
v___x_3123_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3117_, v_p_3114_, v_c_3115_);
lean_dec(v_k_3117_);
return v___x_3123_;
}
}
else
{
lean_object* v___x_3124_; 
lean_dec(v_k_3117_);
lean_dec(v_c_3115_);
lean_dec_ref(v_p_3114_);
lean_dec(v_m_3113_);
v___x_3124_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC___boxed(lean_object* v_k_3125_, lean_object* v_m_3126_, lean_object* v_p_3127_, lean_object* v_c_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_3125_, v_m_3126_, v_p_3127_, v_c_3128_);
lean_dec(v_k_3125_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(lean_object* v_k_3130_, lean_object* v_m_3131_, lean_object* v_c_3132_, lean_object* v_p_3133_, lean_object* v_acc_3134_){
_start:
{
if (lean_obj_tag(v_p_3133_) == 0)
{
lean_object* v_k_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v_k_3135_ = lean_ctor_get(v_p_3133_, 0);
lean_inc(v_k_3135_);
lean_dec_ref_known(v_p_3133_, 1);
v___x_3136_ = lean_int_mul(v_k_3130_, v_k_3135_);
lean_dec(v_k_3135_);
v___x_3137_ = lean_nat_to_int(v_c_3132_);
v___x_3138_ = lean_int_emod(v___x_3136_, v___x_3137_);
lean_dec(v___x_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = l_Lean_Grind_CommRing_Poly_insert(v___x_3138_, v_m_3131_, v_acc_3134_);
return v___x_3139_;
}
else
{
lean_object* v_k_3140_; lean_object* v_v_3141_; lean_object* v_p_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v_k_3140_ = lean_ctor_get(v_p_3133_, 0);
lean_inc(v_k_3140_);
v_v_3141_ = lean_ctor_get(v_p_3133_, 1);
lean_inc(v_v_3141_);
v_p_3142_ = lean_ctor_get(v_p_3133_, 2);
lean_inc_ref(v_p_3142_);
lean_dec_ref_known(v_p_3133_, 3);
v___x_3143_ = lean_int_mul(v_k_3130_, v_k_3140_);
lean_dec(v_k_3140_);
lean_inc(v_c_3132_);
v___x_3144_ = lean_nat_to_int(v_c_3132_);
v___x_3145_ = lean_int_emod(v___x_3143_, v___x_3144_);
lean_dec(v___x_3144_);
lean_dec(v___x_3143_);
lean_inc(v_m_3131_);
v___x_3146_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_3131_, v_v_3141_);
v___x_3147_ = l_Lean_Grind_CommRing_Poly_insert(v___x_3145_, v___x_3146_, v_acc_3134_);
v_p_3133_ = v_p_3142_;
v_acc_3134_ = v___x_3147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go___boxed(lean_object* v_k_3149_, lean_object* v_m_3150_, lean_object* v_c_3151_, lean_object* v_p_3152_, lean_object* v_acc_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_3149_, v_m_3150_, v_c_3151_, v_p_3152_, v_acc_3153_);
lean_dec(v_k_3149_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc(lean_object* v_k_3155_, lean_object* v_m_3156_, lean_object* v_p_3157_, lean_object* v_c_3158_){
_start:
{
lean_object* v___x_3159_; lean_object* v_k_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
lean_inc(v_c_3158_);
v___x_3159_ = lean_nat_to_int(v_c_3158_);
v_k_3160_ = lean_int_emod(v_k_3155_, v___x_3159_);
lean_dec(v___x_3159_);
v___x_3161_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3162_ = lean_int_dec_eq(v_k_3160_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; uint8_t v___x_3164_; 
v___x_3163_ = lean_box(0);
v___x_3164_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_3156_, v___x_3163_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_dec(v_k_3160_);
v___x_3165_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3166_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_3155_, v_m_3156_, v_c_3158_, v_p_3157_, v___x_3165_);
return v___x_3166_;
}
else
{
lean_object* v___x_3167_; 
lean_dec(v_m_3156_);
v___x_3167_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3160_, v_p_3157_, v_c_3158_);
lean_dec(v_k_3160_);
return v___x_3167_;
}
}
else
{
lean_object* v___x_3168_; 
lean_dec(v_k_3160_);
lean_dec(v_c_3158_);
lean_dec_ref(v_p_3157_);
lean_dec(v_m_3156_);
v___x_3168_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc___boxed(lean_object* v_k_3169_, lean_object* v_m_3170_, lean_object* v_p_3171_, lean_object* v_c_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3169_, v_m_3170_, v_p_3171_, v_c_3172_);
lean_dec(v_k_3169_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineC(lean_object* v_p_u2081_3174_, lean_object* v_p_u2082_3175_, lean_object* v_c_3176_){
_start:
{
if (lean_obj_tag(v_p_u2081_3174_) == 0)
{
if (lean_obj_tag(v_p_u2082_3175_) == 0)
{
lean_object* v_k_3177_; lean_object* v_k_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3188_; 
v_k_3177_ = lean_ctor_get(v_p_u2081_3174_, 0);
lean_inc(v_k_3177_);
lean_dec_ref_known(v_p_u2081_3174_, 1);
v_k_3178_ = lean_ctor_get(v_p_u2082_3175_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v_p_u2082_3175_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3180_ = v_p_u2082_3175_;
v_isShared_3181_ = v_isSharedCheck_3188_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_k_3178_);
lean_dec(v_p_u2082_3175_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3188_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3186_; 
v___x_3182_ = lean_int_add(v_k_3177_, v_k_3178_);
lean_dec(v_k_3178_);
lean_dec(v_k_3177_);
v___x_3183_ = lean_nat_to_int(v_c_3176_);
v___x_3184_ = lean_int_emod(v___x_3182_, v___x_3183_);
lean_dec(v___x_3183_);
lean_dec(v___x_3182_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3184_);
v___x_3186_ = v___x_3180_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3184_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
else
{
lean_object* v_k_3189_; lean_object* v___x_3190_; 
v_k_3189_ = lean_ctor_get(v_p_u2081_3174_, 0);
lean_inc(v_k_3189_);
lean_dec_ref_known(v_p_u2081_3174_, 1);
v___x_3190_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2082_3175_, v_k_3189_, v_c_3176_);
lean_dec(v_k_3189_);
return v___x_3190_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_3175_) == 0)
{
lean_object* v_k_3191_; lean_object* v___x_3192_; 
v_k_3191_ = lean_ctor_get(v_p_u2082_3175_, 0);
lean_inc(v_k_3191_);
lean_dec_ref_known(v_p_u2082_3175_, 1);
v___x_3192_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2081_3174_, v_k_3191_, v_c_3176_);
lean_dec(v_k_3191_);
return v___x_3192_;
}
else
{
lean_object* v_k_3193_; lean_object* v_v_3194_; lean_object* v_p_3195_; lean_object* v_k_3196_; lean_object* v_v_3197_; lean_object* v_p_3198_; uint8_t v___x_3199_; 
v_k_3193_ = lean_ctor_get(v_p_u2081_3174_, 0);
v_v_3194_ = lean_ctor_get(v_p_u2081_3174_, 1);
v_p_3195_ = lean_ctor_get(v_p_u2081_3174_, 2);
v_k_3196_ = lean_ctor_get(v_p_u2082_3175_, 0);
v_v_3197_ = lean_ctor_get(v_p_u2082_3175_, 1);
v_p_3198_ = lean_ctor_get(v_p_u2082_3175_, 2);
v___x_3199_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_3194_, v_v_3197_);
switch(v___x_3199_)
{
case 0:
{
lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3207_; 
lean_inc_ref(v_p_3198_);
lean_inc(v_v_3197_);
lean_inc(v_k_3196_);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_p_u2082_3175_);
if (v_isSharedCheck_3207_ == 0)
{
lean_object* v_unused_3208_; lean_object* v_unused_3209_; lean_object* v_unused_3210_; 
v_unused_3208_ = lean_ctor_get(v_p_u2082_3175_, 2);
lean_dec(v_unused_3208_);
v_unused_3209_ = lean_ctor_get(v_p_u2082_3175_, 1);
lean_dec(v_unused_3209_);
v_unused_3210_ = lean_ctor_get(v_p_u2082_3175_, 0);
lean_dec(v_unused_3210_);
v___x_3201_ = v_p_u2082_3175_;
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
else
{
lean_dec(v_p_u2082_3175_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3203_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_u2081_3174_, v_p_3198_, v_c_3176_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 2, v___x_3203_);
v___x_3205_ = v___x_3201_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_k_3196_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_v_3197_);
lean_ctor_set(v_reuseFailAlloc_3206_, 2, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
case 1:
{
lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3224_; 
lean_inc_ref(v_p_3198_);
lean_inc(v_k_3196_);
lean_inc_ref(v_p_3195_);
lean_inc(v_v_3194_);
lean_inc(v_k_3193_);
lean_dec_ref_known(v_p_u2081_3174_, 3);
v_isSharedCheck_3224_ = !lean_is_exclusive(v_p_u2082_3175_);
if (v_isSharedCheck_3224_ == 0)
{
lean_object* v_unused_3225_; lean_object* v_unused_3226_; lean_object* v_unused_3227_; 
v_unused_3225_ = lean_ctor_get(v_p_u2082_3175_, 2);
lean_dec(v_unused_3225_);
v_unused_3226_ = lean_ctor_get(v_p_u2082_3175_, 1);
lean_dec(v_unused_3226_);
v_unused_3227_ = lean_ctor_get(v_p_u2082_3175_, 0);
lean_dec(v_unused_3227_);
v___x_3212_ = v_p_u2082_3175_;
v_isShared_3213_ = v_isSharedCheck_3224_;
goto v_resetjp_3211_;
}
else
{
lean_dec(v_p_u2082_3175_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3224_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v_k_3216_; lean_object* v___x_3217_; uint8_t v___x_3218_; 
v___x_3214_ = lean_int_add(v_k_3193_, v_k_3196_);
lean_dec(v_k_3196_);
lean_dec(v_k_3193_);
lean_inc(v_c_3176_);
v___x_3215_ = lean_nat_to_int(v_c_3176_);
v_k_3216_ = lean_int_emod(v___x_3214_, v___x_3215_);
lean_dec(v___x_3215_);
lean_dec(v___x_3214_);
v___x_3217_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3218_ = lean_int_dec_eq(v_k_3216_, v___x_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3221_; 
v___x_3219_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3195_, v_p_3198_, v_c_3176_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 2, v___x_3219_);
lean_ctor_set(v___x_3212_, 1, v_v_3194_);
lean_ctor_set(v___x_3212_, 0, v_k_3216_);
v___x_3221_ = v___x_3212_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_k_3216_);
lean_ctor_set(v_reuseFailAlloc_3222_, 1, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3222_, 2, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
else
{
lean_dec(v_k_3216_);
lean_del_object(v___x_3212_);
lean_dec(v_v_3194_);
v_p_u2081_3174_ = v_p_3195_;
v_p_u2082_3175_ = v_p_3198_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3235_; 
lean_inc_ref(v_p_3195_);
lean_inc(v_v_3194_);
lean_inc(v_k_3193_);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_p_u2081_3174_);
if (v_isSharedCheck_3235_ == 0)
{
lean_object* v_unused_3236_; lean_object* v_unused_3237_; lean_object* v_unused_3238_; 
v_unused_3236_ = lean_ctor_get(v_p_u2081_3174_, 2);
lean_dec(v_unused_3236_);
v_unused_3237_ = lean_ctor_get(v_p_u2081_3174_, 1);
lean_dec(v_unused_3237_);
v_unused_3238_ = lean_ctor_get(v_p_u2081_3174_, 0);
lean_dec(v_unused_3238_);
v___x_3229_ = v_p_u2081_3174_;
v_isShared_3230_ = v_isSharedCheck_3235_;
goto v_resetjp_3228_;
}
else
{
lean_dec(v_p_u2081_3174_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3235_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3231_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3195_, v_p_u2082_3175_, v_c_3176_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 2, v___x_3231_);
v___x_3233_ = v___x_3229_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3234_, 2, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC_go(lean_object* v_p_u2082_3239_, lean_object* v_c_3240_, lean_object* v_p_u2081_3241_, lean_object* v_acc_3242_){
_start:
{
if (lean_obj_tag(v_p_u2081_3241_) == 0)
{
lean_object* v_k_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v_k_3243_ = lean_ctor_get(v_p_u2081_3241_, 0);
lean_inc(v_k_3243_);
lean_dec_ref_known(v_p_u2081_3241_, 1);
lean_inc(v_c_3240_);
v___x_3244_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3243_, v_p_u2082_3239_, v_c_3240_);
lean_dec(v_k_3243_);
v___x_3245_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3242_, v___x_3244_, v_c_3240_);
return v___x_3245_;
}
else
{
lean_object* v_k_3246_; lean_object* v_v_3247_; lean_object* v_p_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v_k_3246_ = lean_ctor_get(v_p_u2081_3241_, 0);
lean_inc(v_k_3246_);
v_v_3247_ = lean_ctor_get(v_p_u2081_3241_, 1);
lean_inc(v_v_3247_);
v_p_3248_ = lean_ctor_get(v_p_u2081_3241_, 2);
lean_inc_ref(v_p_3248_);
lean_dec_ref_known(v_p_u2081_3241_, 3);
lean_inc_n(v_c_3240_, 2);
lean_inc_ref(v_p_u2082_3239_);
v___x_3249_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_3246_, v_v_3247_, v_p_u2082_3239_, v_c_3240_);
lean_dec(v_k_3246_);
v___x_3250_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3242_, v___x_3249_, v_c_3240_);
v_p_u2081_3241_ = v_p_3248_;
v_acc_3242_ = v___x_3250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC(lean_object* v_p_u2081_3252_, lean_object* v_p_u2082_3253_, lean_object* v_c_3254_){
_start:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3256_ = l_Lean_Grind_CommRing_Poly_mulC_go(v_p_u2082_3253_, v_c_3254_, v_p_u2081_3252_, v___x_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc_go(lean_object* v_p_u2082_3257_, lean_object* v_c_3258_, lean_object* v_p_u2081_3259_, lean_object* v_acc_3260_){
_start:
{
if (lean_obj_tag(v_p_u2081_3259_) == 0)
{
lean_object* v_k_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v_k_3261_ = lean_ctor_get(v_p_u2081_3259_, 0);
lean_inc(v_k_3261_);
lean_dec_ref_known(v_p_u2081_3259_, 1);
lean_inc(v_c_3258_);
v___x_3262_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3261_, v_p_u2082_3257_, v_c_3258_);
lean_dec(v_k_3261_);
v___x_3263_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3260_, v___x_3262_, v_c_3258_);
return v___x_3263_;
}
else
{
lean_object* v_k_3264_; lean_object* v_v_3265_; lean_object* v_p_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_k_3264_ = lean_ctor_get(v_p_u2081_3259_, 0);
lean_inc(v_k_3264_);
v_v_3265_ = lean_ctor_get(v_p_u2081_3259_, 1);
lean_inc(v_v_3265_);
v_p_3266_ = lean_ctor_get(v_p_u2081_3259_, 2);
lean_inc_ref(v_p_3266_);
lean_dec_ref_known(v_p_u2081_3259_, 3);
lean_inc_n(v_c_3258_, 2);
lean_inc_ref(v_p_u2082_3257_);
v___x_3267_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3264_, v_v_3265_, v_p_u2082_3257_, v_c_3258_);
lean_dec(v_k_3264_);
v___x_3268_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3260_, v___x_3267_, v_c_3258_);
v_p_u2081_3259_ = v_p_3266_;
v_acc_3260_ = v___x_3268_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc(lean_object* v_p_u2081_3270_, lean_object* v_p_u2082_3271_, lean_object* v_c_3272_){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3274_ = l_Lean_Grind_CommRing_Poly_mulC__nc_go(v_p_u2082_3271_, v_c_3272_, v_p_u2081_3270_, v___x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC(lean_object* v_p_3275_, lean_object* v_k_3276_, lean_object* v_c_3277_){
_start:
{
lean_object* v_zero_3278_; uint8_t v_isZero_3279_; 
v_zero_3278_ = lean_unsigned_to_nat(0u);
v_isZero_3279_ = lean_nat_dec_eq(v_k_3276_, v_zero_3278_);
if (v_isZero_3279_ == 1)
{
lean_object* v___x_3280_; 
lean_dec(v_c_3277_);
lean_dec_ref(v_p_3275_);
v___x_3280_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3280_;
}
else
{
lean_object* v_one_3281_; lean_object* v_n_3282_; uint8_t v___x_3283_; 
v_one_3281_ = lean_unsigned_to_nat(1u);
v_n_3282_ = lean_nat_sub(v_k_3276_, v_one_3281_);
v___x_3283_ = lean_nat_dec_eq(v_n_3282_, v_zero_3278_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_inc(v_c_3277_);
lean_inc_ref(v_p_3275_);
v___x_3284_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3275_, v_n_3282_, v_c_3277_);
lean_dec(v_n_3282_);
v___x_3285_ = l_Lean_Grind_CommRing_Poly_mulC(v_p_3275_, v___x_3284_, v_c_3277_);
return v___x_3285_;
}
else
{
lean_dec(v_n_3282_);
lean_dec(v_c_3277_);
return v_p_3275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC___boxed(lean_object* v_p_3286_, lean_object* v_k_3287_, lean_object* v_c_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3286_, v_k_3287_, v_c_3288_);
lean_dec(v_k_3287_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc(lean_object* v_p_3290_, lean_object* v_k_3291_, lean_object* v_c_3292_){
_start:
{
lean_object* v_zero_3293_; uint8_t v_isZero_3294_; 
v_zero_3293_ = lean_unsigned_to_nat(0u);
v_isZero_3294_ = lean_nat_dec_eq(v_k_3291_, v_zero_3293_);
if (v_isZero_3294_ == 1)
{
lean_object* v___x_3295_; 
lean_dec(v_c_3292_);
lean_dec_ref(v_p_3290_);
v___x_3295_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3295_;
}
else
{
lean_object* v_one_3296_; lean_object* v_n_3297_; uint8_t v___x_3298_; 
v_one_3296_ = lean_unsigned_to_nat(1u);
v_n_3297_ = lean_nat_sub(v_k_3291_, v_one_3296_);
v___x_3298_ = lean_nat_dec_eq(v_n_3297_, v_zero_3293_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_inc(v_c_3292_);
lean_inc_ref(v_p_3290_);
v___x_3299_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3290_, v_n_3297_, v_c_3292_);
lean_dec(v_n_3297_);
v___x_3300_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3299_, v_p_3290_, v_c_3292_);
return v___x_3300_;
}
else
{
lean_dec(v_n_3297_);
lean_dec(v_c_3292_);
return v_p_3290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc___boxed(lean_object* v_p_3301_, lean_object* v_k_3302_, lean_object* v_c_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3301_, v_k_3302_, v_c_3303_);
lean_dec(v_k_3302_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC_go(lean_object* v_c_3305_, lean_object* v_a_3306_){
_start:
{
lean_object* v_k_3308_; 
switch(lean_obj_tag(v_a_3306_))
{
case 1:
{
lean_object* v_k_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3322_; 
v_k_3312_ = lean_ctor_get(v_a_3306_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v_a_3306_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3314_ = v_a_3306_;
v_isShared_3315_ = v_isSharedCheck_3322_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_k_3312_);
lean_dec(v_a_3306_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3322_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3316_ = lean_nat_to_int(v_k_3312_);
v___x_3317_ = lean_nat_to_int(v_c_3305_);
v___x_3318_ = lean_int_emod(v___x_3316_, v___x_3317_);
lean_dec(v___x_3317_);
lean_dec(v___x_3316_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 0);
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
lean_object* v_i_3323_; lean_object* v___x_3324_; 
lean_dec(v_c_3305_);
v_i_3323_ = lean_ctor_get(v_a_3306_, 0);
lean_inc(v_i_3323_);
lean_dec_ref_known(v_a_3306_, 1);
v___x_3324_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3323_);
return v___x_3324_;
}
case 4:
{
lean_object* v_a_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v_a_3325_ = lean_ctor_get(v_a_3306_, 0);
lean_inc_ref(v_a_3325_);
lean_dec_ref_known(v_a_3306_, 1);
v___x_3326_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3305_);
v___x_3327_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3305_, v_a_3325_);
v___x_3328_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3326_, v___x_3327_, v_c_3305_);
return v___x_3328_;
}
case 5:
{
lean_object* v_a_3329_; lean_object* v_b_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_a_3329_ = lean_ctor_get(v_a_3306_, 0);
lean_inc_ref(v_a_3329_);
v_b_3330_ = lean_ctor_get(v_a_3306_, 1);
lean_inc_ref(v_b_3330_);
lean_dec_ref_known(v_a_3306_, 2);
lean_inc_n(v_c_3305_, 2);
v___x_3331_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3305_, v_a_3329_);
v___x_3332_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3305_, v_b_3330_);
v___x_3333_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3331_, v___x_3332_, v_c_3305_);
return v___x_3333_;
}
case 6:
{
lean_object* v_a_3334_; lean_object* v_b_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v_a_3334_ = lean_ctor_get(v_a_3306_, 0);
lean_inc_ref(v_a_3334_);
v_b_3335_ = lean_ctor_get(v_a_3306_, 1);
lean_inc_ref(v_b_3335_);
lean_dec_ref_known(v_a_3306_, 2);
lean_inc_n(v_c_3305_, 3);
v___x_3336_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3305_, v_a_3334_);
v___x_3337_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_3338_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3305_, v_b_3335_);
v___x_3339_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3337_, v___x_3338_, v_c_3305_);
v___x_3340_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3336_, v___x_3339_, v_c_3305_);
return v___x_3340_;
}
case 7:
{
lean_object* v_a_3341_; lean_object* v_b_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v_a_3341_ = lean_ctor_get(v_a_3306_, 0);
lean_inc_ref(v_a_3341_);
v_b_3342_ = lean_ctor_get(v_a_3306_, 1);
lean_inc_ref(v_b_3342_);
lean_dec_ref_known(v_a_3306_, 2);
lean_inc_n(v_c_3305_, 2);
v___x_3343_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3305_, v_a_3341_);
v___x_3344_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3305_, v_b_3342_);
v___x_3345_ = l_Lean_Grind_CommRing_Poly_mulC(v___x_3343_, v___x_3344_, v_c_3305_);
return v___x_3345_;
}
case 8:
{
lean_object* v_a_3346_; lean_object* v_k_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3374_; 
v_a_3346_ = lean_ctor_get(v_a_3306_, 0);
v_k_3347_ = lean_ctor_get(v_a_3306_, 1);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_a_3306_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3349_ = v_a_3306_;
v_isShared_3350_ = v_isSharedCheck_3374_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_k_3347_);
lean_inc(v_a_3346_);
lean_dec(v_a_3306_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3374_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; uint8_t v___x_3352_; 
v___x_3351_ = lean_unsigned_to_nat(0u);
v___x_3352_ = lean_nat_dec_eq(v_k_3347_, v___x_3351_);
if (v___x_3352_ == 0)
{
switch(lean_obj_tag(v_a_3346_))
{
case 0:
{
lean_object* v_k_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3363_; 
lean_del_object(v___x_3349_);
v_k_3353_ = lean_ctor_get(v_a_3346_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v_a_3346_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3355_ = v_a_3346_;
v_isShared_3356_ = v_isSharedCheck_3363_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_k_3353_);
lean_dec(v_a_3346_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3363_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3361_; 
v___x_3357_ = l_Int_pow(v_k_3353_, v_k_3347_);
lean_dec(v_k_3347_);
lean_dec(v_k_3353_);
v___x_3358_ = lean_nat_to_int(v_c_3305_);
v___x_3359_ = lean_int_emod(v___x_3357_, v___x_3358_);
lean_dec(v___x_3358_);
lean_dec(v___x_3357_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3359_);
v___x_3361_ = v___x_3355_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3359_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
case 3:
{
lean_object* v_i_3364_; lean_object* v___x_3366_; 
lean_dec(v_c_3305_);
v_i_3364_ = lean_ctor_get(v_a_3346_, 0);
lean_inc(v_i_3364_);
lean_dec_ref_known(v_a_3346_, 1);
if (v_isShared_3350_ == 0)
{
lean_ctor_set_tag(v___x_3349_, 0);
lean_ctor_set(v___x_3349_, 0, v_i_3364_);
v___x_3366_ = v___x_3349_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_i_3364_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_k_3347_);
v___x_3366_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3367_ = lean_box(0);
v___x_3368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3366_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3368_);
return v___x_3369_;
}
}
default: 
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
lean_del_object(v___x_3349_);
lean_inc(v_c_3305_);
v___x_3371_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3305_, v_a_3346_);
v___x_3372_ = l_Lean_Grind_CommRing_Poly_powC(v___x_3371_, v_k_3347_, v_c_3305_);
lean_dec(v_k_3347_);
return v___x_3372_;
}
}
}
else
{
lean_object* v___x_3373_; 
lean_del_object(v___x_3349_);
lean_dec(v_k_3347_);
lean_dec_ref(v_a_3346_);
lean_dec(v_c_3305_);
v___x_3373_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3373_;
}
}
}
default: 
{
lean_object* v_k_3375_; 
v_k_3375_ = lean_ctor_get(v_a_3306_, 0);
lean_inc(v_k_3375_);
lean_dec_ref(v_a_3306_);
v_k_3308_ = v_k_3375_;
goto v___jp_3307_;
}
}
v___jp_3307_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3309_ = lean_nat_to_int(v_c_3305_);
v___x_3310_ = lean_int_emod(v_k_3308_, v___x_3309_);
lean_dec(v___x_3309_);
lean_dec(v_k_3308_);
v___x_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
return v___x_3311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC(lean_object* v_e_3376_, lean_object* v_c_3377_){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3377_, v_e_3376_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(lean_object* v_c_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v_k_3382_; 
switch(lean_obj_tag(v_a_3380_))
{
case 1:
{
lean_object* v_k_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3396_; 
v_k_3386_ = lean_ctor_get(v_a_3380_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_a_3380_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3388_ = v_a_3380_;
v_isShared_3389_ = v_isSharedCheck_3396_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_k_3386_);
lean_dec(v_a_3380_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3396_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3390_ = lean_nat_to_int(v_k_3386_);
v___x_3391_ = lean_nat_to_int(v_c_3379_);
v___x_3392_ = lean_int_emod(v___x_3390_, v___x_3391_);
lean_dec(v___x_3391_);
lean_dec(v___x_3390_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set_tag(v___x_3388_, 0);
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
lean_object* v_i_3397_; lean_object* v___x_3398_; 
lean_dec(v_c_3379_);
v_i_3397_ = lean_ctor_get(v_a_3380_, 0);
lean_inc(v_i_3397_);
lean_dec_ref_known(v_a_3380_, 1);
v___x_3398_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3397_);
return v___x_3398_;
}
case 4:
{
lean_object* v_a_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_a_3399_ = lean_ctor_get(v_a_3380_, 0);
lean_inc_ref(v_a_3399_);
lean_dec_ref_known(v_a_3380_, 1);
v___x_3400_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3379_);
v___x_3401_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3379_, v_a_3399_);
v___x_3402_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3400_, v___x_3401_, v_c_3379_);
return v___x_3402_;
}
case 5:
{
lean_object* v_a_3403_; lean_object* v_b_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v_a_3403_ = lean_ctor_get(v_a_3380_, 0);
lean_inc_ref(v_a_3403_);
v_b_3404_ = lean_ctor_get(v_a_3380_, 1);
lean_inc_ref(v_b_3404_);
lean_dec_ref_known(v_a_3380_, 2);
lean_inc_n(v_c_3379_, 2);
v___x_3405_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3379_, v_a_3403_);
v___x_3406_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3379_, v_b_3404_);
v___x_3407_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3405_, v___x_3406_, v_c_3379_);
return v___x_3407_;
}
case 6:
{
lean_object* v_a_3408_; lean_object* v_b_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v_a_3408_ = lean_ctor_get(v_a_3380_, 0);
lean_inc_ref(v_a_3408_);
v_b_3409_ = lean_ctor_get(v_a_3380_, 1);
lean_inc_ref(v_b_3409_);
lean_dec_ref_known(v_a_3380_, 2);
lean_inc_n(v_c_3379_, 3);
v___x_3410_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3379_, v_a_3408_);
v___x_3411_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_3412_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3379_, v_b_3409_);
v___x_3413_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3411_, v___x_3412_, v_c_3379_);
v___x_3414_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3410_, v___x_3413_, v_c_3379_);
return v___x_3414_;
}
case 7:
{
lean_object* v_a_3415_; lean_object* v_b_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v_a_3415_ = lean_ctor_get(v_a_3380_, 0);
lean_inc_ref(v_a_3415_);
v_b_3416_ = lean_ctor_get(v_a_3380_, 1);
lean_inc_ref(v_b_3416_);
lean_dec_ref_known(v_a_3380_, 2);
lean_inc_n(v_c_3379_, 2);
v___x_3417_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3379_, v_a_3415_);
v___x_3418_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3379_, v_b_3416_);
v___x_3419_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3417_, v___x_3418_, v_c_3379_);
return v___x_3419_;
}
case 8:
{
lean_object* v_a_3420_; lean_object* v_k_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3448_; 
v_a_3420_ = lean_ctor_get(v_a_3380_, 0);
v_k_3421_ = lean_ctor_get(v_a_3380_, 1);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_a_3380_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3423_ = v_a_3380_;
v_isShared_3424_ = v_isSharedCheck_3448_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_k_3421_);
lean_inc(v_a_3420_);
lean_dec(v_a_3380_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3448_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; uint8_t v___x_3426_; 
v___x_3425_ = lean_unsigned_to_nat(0u);
v___x_3426_ = lean_nat_dec_eq(v_k_3421_, v___x_3425_);
if (v___x_3426_ == 0)
{
switch(lean_obj_tag(v_a_3420_))
{
case 0:
{
lean_object* v_k_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3437_; 
lean_del_object(v___x_3423_);
v_k_3427_ = lean_ctor_get(v_a_3420_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v_a_3420_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3429_ = v_a_3420_;
v_isShared_3430_ = v_isSharedCheck_3437_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_k_3427_);
lean_dec(v_a_3420_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3437_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3435_; 
v___x_3431_ = l_Int_pow(v_k_3427_, v_k_3421_);
lean_dec(v_k_3421_);
lean_dec(v_k_3427_);
v___x_3432_ = lean_nat_to_int(v_c_3379_);
v___x_3433_ = lean_int_emod(v___x_3431_, v___x_3432_);
lean_dec(v___x_3432_);
lean_dec(v___x_3431_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3433_);
v___x_3435_ = v___x_3429_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
case 3:
{
lean_object* v_i_3438_; lean_object* v___x_3440_; 
lean_dec(v_c_3379_);
v_i_3438_ = lean_ctor_get(v_a_3420_, 0);
lean_inc(v_i_3438_);
lean_dec_ref_known(v_a_3420_, 1);
if (v_isShared_3424_ == 0)
{
lean_ctor_set_tag(v___x_3423_, 0);
lean_ctor_set(v___x_3423_, 0, v_i_3438_);
v___x_3440_ = v___x_3423_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_i_3438_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_k_3421_);
v___x_3440_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3441_ = lean_box(0);
v___x_3442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3440_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
v___x_3443_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3442_);
return v___x_3443_;
}
}
default: 
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
lean_del_object(v___x_3423_);
lean_inc(v_c_3379_);
v___x_3445_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3379_, v_a_3420_);
v___x_3446_ = l_Lean_Grind_CommRing_Poly_powC__nc(v___x_3445_, v_k_3421_, v_c_3379_);
lean_dec(v_k_3421_);
return v___x_3446_;
}
}
}
else
{
lean_object* v___x_3447_; 
lean_del_object(v___x_3423_);
lean_dec(v_k_3421_);
lean_dec_ref(v_a_3420_);
lean_dec(v_c_3379_);
v___x_3447_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3447_;
}
}
}
default: 
{
lean_object* v_k_3449_; 
v_k_3449_ = lean_ctor_get(v_a_3380_, 0);
lean_inc(v_k_3449_);
lean_dec_ref(v_a_3380_);
v_k_3382_ = v_k_3449_;
goto v___jp_3381_;
}
}
v___jp_3381_:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = lean_nat_to_int(v_c_3379_);
v___x_3384_ = lean_int_emod(v_k_3382_, v___x_3383_);
lean_dec(v___x_3383_);
lean_dec(v_k_3382_);
v___x_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
return v___x_3385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc(lean_object* v_e_3450_, lean_object* v_c_3451_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3451_, v_e_3450_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(lean_object* v_x_3453_, lean_object* v_h__1_3454_, lean_object* v_h__2_3455_, lean_object* v_h__3_3456_, lean_object* v_h__4_3457_, lean_object* v_h__5_3458_, lean_object* v_h__6_3459_, lean_object* v_h__7_3460_, lean_object* v_h__8_3461_, lean_object* v_h__9_3462_){
_start:
{
switch(lean_obj_tag(v_x_3453_))
{
case 0:
{
lean_object* v_k_3463_; lean_object* v___x_3464_; 
lean_dec(v_h__9_3462_);
lean_dec(v_h__8_3461_);
lean_dec(v_h__7_3460_);
lean_dec(v_h__6_3459_);
lean_dec(v_h__5_3458_);
lean_dec(v_h__4_3457_);
lean_dec(v_h__3_3456_);
lean_dec(v_h__2_3455_);
v_k_3463_ = lean_ctor_get(v_x_3453_, 0);
lean_inc(v_k_3463_);
lean_dec_ref_known(v_x_3453_, 1);
v___x_3464_ = lean_apply_1(v_h__1_3454_, v_k_3463_);
return v___x_3464_;
}
case 1:
{
lean_object* v_k_3465_; lean_object* v___x_3466_; 
lean_dec(v_h__9_3462_);
lean_dec(v_h__8_3461_);
lean_dec(v_h__7_3460_);
lean_dec(v_h__6_3459_);
lean_dec(v_h__5_3458_);
lean_dec(v_h__4_3457_);
lean_dec(v_h__3_3456_);
lean_dec(v_h__1_3454_);
v_k_3465_ = lean_ctor_get(v_x_3453_, 0);
lean_inc(v_k_3465_);
lean_dec_ref_known(v_x_3453_, 1);
v___x_3466_ = lean_apply_1(v_h__2_3455_, v_k_3465_);
return v___x_3466_;
}
case 2:
{
lean_object* v_k_3467_; lean_object* v___x_3468_; 
lean_dec(v_h__9_3462_);
lean_dec(v_h__8_3461_);
lean_dec(v_h__7_3460_);
lean_dec(v_h__6_3459_);
lean_dec(v_h__5_3458_);
lean_dec(v_h__4_3457_);
lean_dec(v_h__2_3455_);
lean_dec(v_h__1_3454_);
v_k_3467_ = lean_ctor_get(v_x_3453_, 0);
lean_inc(v_k_3467_);
lean_dec_ref_known(v_x_3453_, 1);
v___x_3468_ = lean_apply_1(v_h__3_3456_, v_k_3467_);
return v___x_3468_;
}
case 3:
{
lean_object* v_i_3469_; lean_object* v___x_3470_; 
lean_dec(v_h__9_3462_);
lean_dec(v_h__8_3461_);
lean_dec(v_h__7_3460_);
lean_dec(v_h__6_3459_);
lean_dec(v_h__5_3458_);
lean_dec(v_h__3_3456_);
lean_dec(v_h__2_3455_);
lean_dec(v_h__1_3454_);
v_i_3469_ = lean_ctor_get(v_x_3453_, 0);
lean_inc(v_i_3469_);
lean_dec_ref_known(v_x_3453_, 1);
v___x_3470_ = lean_apply_1(v_h__4_3457_, v_i_3469_);
return v___x_3470_;
}
case 4:
{
lean_object* v_a_3471_; lean_object* v___x_3472_; 
lean_dec(v_h__9_3462_);
lean_dec(v_h__8_3461_);
lean_dec(v_h__6_3459_);
lean_dec(v_h__5_3458_);
lean_dec(v_h__4_3457_);
lean_dec(v_h__3_3456_);
lean_dec(v_h__2_3455_);
lean_dec(v_h__1_3454_);
v_a_3471_ = lean_ctor_get(v_x_3453_, 0);
lean_inc_ref(v_a_3471_);
lean_dec_ref_known(v_x_3453_, 1);
v___x_3472_ = lean_apply_1(v_h__7_3460_, v_a_3471_);
return v___x_3472_;
}
case 5:
{
lean_object* v_a_3473_; lean_object* v_b_3474_; lean_object* v___x_3475_; 
lean_dec(v_h__9_3462_);
lean_dec(v_h__8_3461_);
lean_dec(v_h__7_3460_);
lean_dec(v_h__6_3459_);
lean_dec(v_h__4_3457_);
lean_dec(v_h__3_3456_);
lean_dec(v_h__2_3455_);
lean_dec(v_h__1_3454_);
v_a_3473_ = lean_ctor_get(v_x_3453_, 0);
lean_inc_ref(v_a_3473_);
v_b_3474_ = lean_ctor_get(v_x_3453_, 1);
lean_inc_ref(v_b_3474_);
lean_dec_ref_known(v_x_3453_, 2);
v___x_3475_ = lean_apply_2(v_h__5_3458_, v_a_3473_, v_b_3474_);
return v___x_3475_;
}
case 6:
{
lean_object* v_a_3476_; lean_object* v_b_3477_; lean_object* v___x_3478_; 
lean_dec(v_h__9_3462_);
lean_dec(v_h__7_3460_);
lean_dec(v_h__6_3459_);
lean_dec(v_h__5_3458_);
lean_dec(v_h__4_3457_);
lean_dec(v_h__3_3456_);
lean_dec(v_h__2_3455_);
lean_dec(v_h__1_3454_);
v_a_3476_ = lean_ctor_get(v_x_3453_, 0);
lean_inc_ref(v_a_3476_);
v_b_3477_ = lean_ctor_get(v_x_3453_, 1);
lean_inc_ref(v_b_3477_);
lean_dec_ref_known(v_x_3453_, 2);
v___x_3478_ = lean_apply_2(v_h__8_3461_, v_a_3476_, v_b_3477_);
return v___x_3478_;
}
case 7:
{
lean_object* v_a_3479_; lean_object* v_b_3480_; lean_object* v___x_3481_; 
lean_dec(v_h__9_3462_);
lean_dec(v_h__8_3461_);
lean_dec(v_h__7_3460_);
lean_dec(v_h__5_3458_);
lean_dec(v_h__4_3457_);
lean_dec(v_h__3_3456_);
lean_dec(v_h__2_3455_);
lean_dec(v_h__1_3454_);
v_a_3479_ = lean_ctor_get(v_x_3453_, 0);
lean_inc_ref(v_a_3479_);
v_b_3480_ = lean_ctor_get(v_x_3453_, 1);
lean_inc_ref(v_b_3480_);
lean_dec_ref_known(v_x_3453_, 2);
v___x_3481_ = lean_apply_2(v_h__6_3459_, v_a_3479_, v_b_3480_);
return v___x_3481_;
}
default: 
{
lean_object* v_a_3482_; lean_object* v_k_3483_; lean_object* v___x_3484_; 
lean_dec(v_h__8_3461_);
lean_dec(v_h__7_3460_);
lean_dec(v_h__6_3459_);
lean_dec(v_h__5_3458_);
lean_dec(v_h__4_3457_);
lean_dec(v_h__3_3456_);
lean_dec(v_h__2_3455_);
lean_dec(v_h__1_3454_);
v_a_3482_ = lean_ctor_get(v_x_3453_, 0);
lean_inc_ref(v_a_3482_);
v_k_3483_ = lean_ctor_get(v_x_3453_, 1);
lean_inc(v_k_3483_);
lean_dec_ref_known(v_x_3453_, 2);
v___x_3484_ = lean_apply_2(v_h__9_3462_, v_a_3482_, v_k_3483_);
return v___x_3484_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter(lean_object* v_motive_3485_, lean_object* v_x_3486_, lean_object* v_h__1_3487_, lean_object* v_h__2_3488_, lean_object* v_h__3_3489_, lean_object* v_h__4_3490_, lean_object* v_h__5_3491_, lean_object* v_h__6_3492_, lean_object* v_h__7_3493_, lean_object* v_h__8_3494_, lean_object* v_h__9_3495_){
_start:
{
switch(lean_obj_tag(v_x_3486_))
{
case 0:
{
lean_object* v_k_3496_; lean_object* v___x_3497_; 
lean_dec(v_h__9_3495_);
lean_dec(v_h__8_3494_);
lean_dec(v_h__7_3493_);
lean_dec(v_h__6_3492_);
lean_dec(v_h__5_3491_);
lean_dec(v_h__4_3490_);
lean_dec(v_h__3_3489_);
lean_dec(v_h__2_3488_);
v_k_3496_ = lean_ctor_get(v_x_3486_, 0);
lean_inc(v_k_3496_);
lean_dec_ref_known(v_x_3486_, 1);
v___x_3497_ = lean_apply_1(v_h__1_3487_, v_k_3496_);
return v___x_3497_;
}
case 1:
{
lean_object* v_k_3498_; lean_object* v___x_3499_; 
lean_dec(v_h__9_3495_);
lean_dec(v_h__8_3494_);
lean_dec(v_h__7_3493_);
lean_dec(v_h__6_3492_);
lean_dec(v_h__5_3491_);
lean_dec(v_h__4_3490_);
lean_dec(v_h__3_3489_);
lean_dec(v_h__1_3487_);
v_k_3498_ = lean_ctor_get(v_x_3486_, 0);
lean_inc(v_k_3498_);
lean_dec_ref_known(v_x_3486_, 1);
v___x_3499_ = lean_apply_1(v_h__2_3488_, v_k_3498_);
return v___x_3499_;
}
case 2:
{
lean_object* v_k_3500_; lean_object* v___x_3501_; 
lean_dec(v_h__9_3495_);
lean_dec(v_h__8_3494_);
lean_dec(v_h__7_3493_);
lean_dec(v_h__6_3492_);
lean_dec(v_h__5_3491_);
lean_dec(v_h__4_3490_);
lean_dec(v_h__2_3488_);
lean_dec(v_h__1_3487_);
v_k_3500_ = lean_ctor_get(v_x_3486_, 0);
lean_inc(v_k_3500_);
lean_dec_ref_known(v_x_3486_, 1);
v___x_3501_ = lean_apply_1(v_h__3_3489_, v_k_3500_);
return v___x_3501_;
}
case 3:
{
lean_object* v_i_3502_; lean_object* v___x_3503_; 
lean_dec(v_h__9_3495_);
lean_dec(v_h__8_3494_);
lean_dec(v_h__7_3493_);
lean_dec(v_h__6_3492_);
lean_dec(v_h__5_3491_);
lean_dec(v_h__3_3489_);
lean_dec(v_h__2_3488_);
lean_dec(v_h__1_3487_);
v_i_3502_ = lean_ctor_get(v_x_3486_, 0);
lean_inc(v_i_3502_);
lean_dec_ref_known(v_x_3486_, 1);
v___x_3503_ = lean_apply_1(v_h__4_3490_, v_i_3502_);
return v___x_3503_;
}
case 4:
{
lean_object* v_a_3504_; lean_object* v___x_3505_; 
lean_dec(v_h__9_3495_);
lean_dec(v_h__8_3494_);
lean_dec(v_h__6_3492_);
lean_dec(v_h__5_3491_);
lean_dec(v_h__4_3490_);
lean_dec(v_h__3_3489_);
lean_dec(v_h__2_3488_);
lean_dec(v_h__1_3487_);
v_a_3504_ = lean_ctor_get(v_x_3486_, 0);
lean_inc_ref(v_a_3504_);
lean_dec_ref_known(v_x_3486_, 1);
v___x_3505_ = lean_apply_1(v_h__7_3493_, v_a_3504_);
return v___x_3505_;
}
case 5:
{
lean_object* v_a_3506_; lean_object* v_b_3507_; lean_object* v___x_3508_; 
lean_dec(v_h__9_3495_);
lean_dec(v_h__8_3494_);
lean_dec(v_h__7_3493_);
lean_dec(v_h__6_3492_);
lean_dec(v_h__4_3490_);
lean_dec(v_h__3_3489_);
lean_dec(v_h__2_3488_);
lean_dec(v_h__1_3487_);
v_a_3506_ = lean_ctor_get(v_x_3486_, 0);
lean_inc_ref(v_a_3506_);
v_b_3507_ = lean_ctor_get(v_x_3486_, 1);
lean_inc_ref(v_b_3507_);
lean_dec_ref_known(v_x_3486_, 2);
v___x_3508_ = lean_apply_2(v_h__5_3491_, v_a_3506_, v_b_3507_);
return v___x_3508_;
}
case 6:
{
lean_object* v_a_3509_; lean_object* v_b_3510_; lean_object* v___x_3511_; 
lean_dec(v_h__9_3495_);
lean_dec(v_h__7_3493_);
lean_dec(v_h__6_3492_);
lean_dec(v_h__5_3491_);
lean_dec(v_h__4_3490_);
lean_dec(v_h__3_3489_);
lean_dec(v_h__2_3488_);
lean_dec(v_h__1_3487_);
v_a_3509_ = lean_ctor_get(v_x_3486_, 0);
lean_inc_ref(v_a_3509_);
v_b_3510_ = lean_ctor_get(v_x_3486_, 1);
lean_inc_ref(v_b_3510_);
lean_dec_ref_known(v_x_3486_, 2);
v___x_3511_ = lean_apply_2(v_h__8_3494_, v_a_3509_, v_b_3510_);
return v___x_3511_;
}
case 7:
{
lean_object* v_a_3512_; lean_object* v_b_3513_; lean_object* v___x_3514_; 
lean_dec(v_h__9_3495_);
lean_dec(v_h__8_3494_);
lean_dec(v_h__7_3493_);
lean_dec(v_h__5_3491_);
lean_dec(v_h__4_3490_);
lean_dec(v_h__3_3489_);
lean_dec(v_h__2_3488_);
lean_dec(v_h__1_3487_);
v_a_3512_ = lean_ctor_get(v_x_3486_, 0);
lean_inc_ref(v_a_3512_);
v_b_3513_ = lean_ctor_get(v_x_3486_, 1);
lean_inc_ref(v_b_3513_);
lean_dec_ref_known(v_x_3486_, 2);
v___x_3514_ = lean_apply_2(v_h__6_3492_, v_a_3512_, v_b_3513_);
return v___x_3514_;
}
default: 
{
lean_object* v_a_3515_; lean_object* v_k_3516_; lean_object* v___x_3517_; 
lean_dec(v_h__8_3494_);
lean_dec(v_h__7_3493_);
lean_dec(v_h__6_3492_);
lean_dec(v_h__5_3491_);
lean_dec(v_h__4_3490_);
lean_dec(v_h__3_3489_);
lean_dec(v_h__2_3488_);
lean_dec(v_h__1_3487_);
v_a_3515_ = lean_ctor_get(v_x_3486_, 0);
lean_inc_ref(v_a_3515_);
v_k_3516_ = lean_ctor_get(v_x_3486_, 1);
lean_inc(v_k_3516_);
lean_dec_ref_known(v_x_3486_, 2);
v___x_3517_ = lean_apply_2(v_h__9_3495_, v_a_3515_, v_k_3516_);
return v___x_3517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter___redArg(lean_object* v_a_3518_, lean_object* v_h__1_3519_, lean_object* v_h__2_3520_, lean_object* v_h__3_3521_){
_start:
{
switch(lean_obj_tag(v_a_3518_))
{
case 0:
{
lean_object* v_k_3522_; lean_object* v___x_3523_; 
lean_dec(v_h__3_3521_);
lean_dec(v_h__2_3520_);
v_k_3522_ = lean_ctor_get(v_a_3518_, 0);
lean_inc(v_k_3522_);
lean_dec_ref_known(v_a_3518_, 1);
v___x_3523_ = lean_apply_1(v_h__1_3519_, v_k_3522_);
return v___x_3523_;
}
case 3:
{
lean_object* v_i_3524_; lean_object* v___x_3525_; 
lean_dec(v_h__3_3521_);
lean_dec(v_h__1_3519_);
v_i_3524_ = lean_ctor_get(v_a_3518_, 0);
lean_inc(v_i_3524_);
lean_dec_ref_known(v_a_3518_, 1);
v___x_3525_ = lean_apply_1(v_h__2_3520_, v_i_3524_);
return v___x_3525_;
}
default: 
{
lean_object* v___x_3526_; 
lean_dec(v_h__2_3520_);
lean_dec(v_h__1_3519_);
v___x_3526_ = lean_apply_3(v_h__3_3521_, v_a_3518_, lean_box(0), lean_box(0));
return v___x_3526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter(lean_object* v_motive_3527_, lean_object* v_a_3528_, lean_object* v_h__1_3529_, lean_object* v_h__2_3530_, lean_object* v_h__3_3531_){
_start:
{
switch(lean_obj_tag(v_a_3528_))
{
case 0:
{
lean_object* v_k_3532_; lean_object* v___x_3533_; 
lean_dec(v_h__3_3531_);
lean_dec(v_h__2_3530_);
v_k_3532_ = lean_ctor_get(v_a_3528_, 0);
lean_inc(v_k_3532_);
lean_dec_ref_known(v_a_3528_, 1);
v___x_3533_ = lean_apply_1(v_h__1_3529_, v_k_3532_);
return v___x_3533_;
}
case 3:
{
lean_object* v_i_3534_; lean_object* v___x_3535_; 
lean_dec(v_h__3_3531_);
lean_dec(v_h__1_3529_);
v_i_3534_ = lean_ctor_get(v_a_3528_, 0);
lean_inc(v_i_3534_);
lean_dec_ref_known(v_a_3528_, 1);
v___x_3535_ = lean_apply_1(v_h__2_3530_, v_i_3534_);
return v___x_3535_;
}
default: 
{
lean_object* v___x_3536_; 
lean_dec(v_h__2_3530_);
lean_dec(v_h__1_3529_);
v___x_3536_ = lean_apply_3(v_h__3_3531_, v_a_3528_, lean_box(0), lean_box(0));
return v___x_3536_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter___redArg(lean_object* v_x_3537_, lean_object* v_h__1_3538_){
_start:
{
lean_object* v_x_3539_; lean_object* v_k_3540_; lean_object* v___x_3541_; 
v_x_3539_ = lean_ctor_get(v_x_3537_, 0);
lean_inc(v_x_3539_);
v_k_3540_ = lean_ctor_get(v_x_3537_, 1);
lean_inc(v_k_3540_);
lean_dec_ref(v_x_3537_);
v___x_3541_ = lean_apply_2(v_h__1_3538_, v_x_3539_, v_k_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__3_splitter(lean_object* v_motive_3542_, lean_object* v_x_3543_, lean_object* v_h__1_3544_){
_start:
{
lean_object* v_x_3545_; lean_object* v_k_3546_; lean_object* v___x_3547_; 
v_x_3545_ = lean_ctor_get(v_x_3543_, 0);
lean_inc(v_x_3545_);
v_k_3546_ = lean_ctor_get(v_x_3543_, 1);
lean_inc(v_k_3546_);
lean_dec_ref(v_x_3543_);
v___x_3547_ = lean_apply_2(v_h__1_3544_, v_x_3545_, v_k_3546_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(lean_object* v_k_3548_, lean_object* v_h__1_3549_, lean_object* v_h__2_3550_, lean_object* v_h__3_3551_){
_start:
{
lean_object* v___x_3552_; uint8_t v___x_3553_; 
v___x_3552_ = lean_unsigned_to_nat(0u);
v___x_3553_ = lean_nat_dec_eq(v_k_3548_, v___x_3552_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; uint8_t v___x_3555_; 
lean_dec(v_h__1_3549_);
v___x_3554_ = lean_unsigned_to_nat(1u);
v___x_3555_ = lean_nat_dec_eq(v_k_3548_, v___x_3554_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; 
lean_dec(v_h__2_3550_);
v___x_3556_ = lean_apply_3(v_h__3_3551_, v_k_3548_, lean_box(0), lean_box(0));
return v___x_3556_;
}
else
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_dec(v_h__3_3551_);
lean_dec(v_k_3548_);
v___x_3557_ = lean_box(0);
v___x_3558_ = lean_apply_1(v_h__2_3550_, v___x_3557_);
return v___x_3558_;
}
}
else
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
lean_dec(v_h__3_3551_);
lean_dec(v_h__2_3550_);
lean_dec(v_k_3548_);
v___x_3559_ = lean_box(0);
v___x_3560_ = lean_apply_1(v_h__1_3549_, v___x_3559_);
return v___x_3560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(lean_object* v_motive_3561_, lean_object* v_k_3562_, lean_object* v_h__1_3563_, lean_object* v_h__2_3564_, lean_object* v_h__3_3565_){
_start:
{
lean_object* v___x_3566_; uint8_t v___x_3567_; 
v___x_3566_ = lean_unsigned_to_nat(0u);
v___x_3567_ = lean_nat_dec_eq(v_k_3562_, v___x_3566_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; uint8_t v___x_3569_; 
lean_dec(v_h__1_3563_);
v___x_3568_ = lean_unsigned_to_nat(1u);
v___x_3569_ = lean_nat_dec_eq(v_k_3562_, v___x_3568_);
if (v___x_3569_ == 0)
{
lean_object* v___x_3570_; 
lean_dec(v_h__2_3564_);
v___x_3570_ = lean_apply_3(v_h__3_3565_, v_k_3562_, lean_box(0), lean_box(0));
return v___x_3570_;
}
else
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
lean_dec(v_h__3_3565_);
lean_dec(v_k_3562_);
v___x_3571_ = lean_box(0);
v___x_3572_ = lean_apply_1(v_h__2_3564_, v___x_3571_);
return v___x_3572_;
}
}
else
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
lean_dec(v_h__3_3565_);
lean_dec(v_h__2_3564_);
lean_dec(v_k_3562_);
v___x_3573_ = lean_box(0);
v___x_3574_ = lean_apply_1(v_h__1_3563_, v___x_3573_);
return v___x_3574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(lean_object* v_m_u2081_3575_, lean_object* v_h__1_3576_, lean_object* v_h__2_3577_, lean_object* v_h__3_3578_){
_start:
{
if (lean_obj_tag(v_m_u2081_3575_) == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
lean_dec(v_h__3_3578_);
lean_dec(v_h__2_3577_);
v___x_3579_ = lean_box(0);
v___x_3580_ = lean_apply_1(v_h__1_3576_, v___x_3579_);
return v___x_3580_;
}
else
{
lean_object* v_m_3581_; 
lean_dec(v_h__1_3576_);
v_m_3581_ = lean_ctor_get(v_m_u2081_3575_, 1);
if (lean_obj_tag(v_m_3581_) == 0)
{
lean_object* v_p_3582_; lean_object* v___x_3583_; 
lean_dec(v_h__3_3578_);
v_p_3582_ = lean_ctor_get(v_m_u2081_3575_, 0);
lean_inc_ref(v_p_3582_);
lean_dec_ref_known(v_m_u2081_3575_, 2);
v___x_3583_ = lean_apply_1(v_h__2_3577_, v_p_3582_);
return v___x_3583_;
}
else
{
lean_object* v_p_3584_; lean_object* v___x_3585_; 
lean_inc(v_m_3581_);
lean_dec(v_h__2_3577_);
v_p_3584_ = lean_ctor_get(v_m_u2081_3575_, 0);
lean_inc_ref(v_p_3584_);
lean_dec_ref_known(v_m_u2081_3575_, 2);
v___x_3585_ = lean_apply_3(v_h__3_3578_, v_p_3584_, v_m_3581_, lean_box(0));
return v___x_3585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(lean_object* v_motive_3586_, lean_object* v_m_u2081_3587_, lean_object* v_h__1_3588_, lean_object* v_h__2_3589_, lean_object* v_h__3_3590_){
_start:
{
if (lean_obj_tag(v_m_u2081_3587_) == 0)
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
lean_dec(v_h__3_3590_);
lean_dec(v_h__2_3589_);
v___x_3591_ = lean_box(0);
v___x_3592_ = lean_apply_1(v_h__1_3588_, v___x_3591_);
return v___x_3592_;
}
else
{
lean_object* v_m_3593_; 
lean_dec(v_h__1_3588_);
v_m_3593_ = lean_ctor_get(v_m_u2081_3587_, 1);
if (lean_obj_tag(v_m_3593_) == 0)
{
lean_object* v_p_3594_; lean_object* v___x_3595_; 
lean_dec(v_h__3_3590_);
v_p_3594_ = lean_ctor_get(v_m_u2081_3587_, 0);
lean_inc_ref(v_p_3594_);
lean_dec_ref_known(v_m_u2081_3587_, 2);
v___x_3595_ = lean_apply_1(v_h__2_3589_, v_p_3594_);
return v___x_3595_;
}
else
{
lean_object* v_p_3596_; lean_object* v___x_3597_; 
lean_inc(v_m_3593_);
lean_dec(v_h__2_3589_);
v_p_3596_ = lean_ctor_get(v_m_u2081_3587_, 0);
lean_inc_ref(v_p_3596_);
lean_dec_ref_known(v_m_u2081_3587_, 2);
v___x_3597_ = lean_apply_3(v_h__3_3590_, v_p_3596_, v_m_3593_, lean_box(0));
return v___x_3597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(lean_object* v_p_3598_, lean_object* v_h__1_3599_, lean_object* v_h__2_3600_, lean_object* v_h__3_3601_){
_start:
{
if (lean_obj_tag(v_p_3598_) == 0)
{
lean_object* v_k_3602_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
lean_dec(v_h__3_3601_);
v_k_3602_ = lean_ctor_get(v_p_3598_, 0);
lean_inc(v_k_3602_);
lean_dec_ref_known(v_p_3598_, 1);
v___x_3603_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3604_ = lean_int_dec_eq(v_k_3602_, v___x_3603_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; 
lean_dec(v_h__1_3599_);
v___x_3605_ = lean_apply_2(v_h__2_3600_, v_k_3602_, lean_box(0));
return v___x_3605_;
}
else
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
lean_dec(v_k_3602_);
lean_dec(v_h__2_3600_);
v___x_3606_ = lean_box(0);
v___x_3607_ = lean_apply_1(v_h__1_3599_, v___x_3606_);
return v___x_3607_;
}
}
else
{
lean_object* v_k_3608_; lean_object* v_v_3609_; lean_object* v_p_3610_; lean_object* v___x_3611_; 
lean_dec(v_h__2_3600_);
lean_dec(v_h__1_3599_);
v_k_3608_ = lean_ctor_get(v_p_3598_, 0);
lean_inc(v_k_3608_);
v_v_3609_ = lean_ctor_get(v_p_3598_, 1);
lean_inc(v_v_3609_);
v_p_3610_ = lean_ctor_get(v_p_3598_, 2);
lean_inc_ref(v_p_3610_);
lean_dec_ref_known(v_p_3598_, 3);
v___x_3611_ = lean_apply_3(v_h__3_3601_, v_k_3608_, v_v_3609_, v_p_3610_);
return v___x_3611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(lean_object* v_motive_3612_, lean_object* v_p_3613_, lean_object* v_h__1_3614_, lean_object* v_h__2_3615_, lean_object* v_h__3_3616_){
_start:
{
if (lean_obj_tag(v_p_3613_) == 0)
{
lean_object* v_k_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; 
lean_dec(v_h__3_3616_);
v_k_3617_ = lean_ctor_get(v_p_3613_, 0);
lean_inc(v_k_3617_);
lean_dec_ref_known(v_p_3613_, 1);
v___x_3618_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3619_ = lean_int_dec_eq(v_k_3617_, v___x_3618_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3620_; 
lean_dec(v_h__1_3614_);
v___x_3620_ = lean_apply_2(v_h__2_3615_, v_k_3617_, lean_box(0));
return v___x_3620_;
}
else
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
lean_dec(v_k_3617_);
lean_dec(v_h__2_3615_);
v___x_3621_ = lean_box(0);
v___x_3622_ = lean_apply_1(v_h__1_3614_, v___x_3621_);
return v___x_3622_;
}
}
else
{
lean_object* v_k_3623_; lean_object* v_v_3624_; lean_object* v_p_3625_; lean_object* v___x_3626_; 
lean_dec(v_h__2_3615_);
lean_dec(v_h__1_3614_);
v_k_3623_ = lean_ctor_get(v_p_3613_, 0);
lean_inc(v_k_3623_);
v_v_3624_ = lean_ctor_get(v_p_3613_, 1);
lean_inc(v_v_3624_);
v_p_3625_ = lean_ctor_get(v_p_3613_, 2);
lean_inc_ref(v_p_3625_);
lean_dec_ref_known(v_p_3613_, 3);
v___x_3626_ = lean_apply_3(v_h__3_3616_, v_k_3623_, v_v_3624_, v_p_3625_);
return v___x_3626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object* v_k_3627_, lean_object* v_h__1_3628_, lean_object* v_h__2_3629_, lean_object* v_h__3_3630_){
_start:
{
lean_object* v_zero_3631_; uint8_t v_isZero_3632_; 
v_zero_3631_ = lean_unsigned_to_nat(0u);
v_isZero_3632_ = lean_nat_dec_eq(v_k_3627_, v_zero_3631_);
if (v_isZero_3632_ == 1)
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
lean_dec(v_h__3_3630_);
lean_dec(v_h__2_3629_);
v___x_3633_ = lean_box(0);
v___x_3634_ = lean_apply_1(v_h__1_3628_, v___x_3633_);
return v___x_3634_;
}
else
{
lean_object* v_one_3635_; lean_object* v_n_3636_; uint8_t v___x_3637_; 
lean_dec(v_h__1_3628_);
v_one_3635_ = lean_unsigned_to_nat(1u);
v_n_3636_ = lean_nat_sub(v_k_3627_, v_one_3635_);
v___x_3637_ = lean_nat_dec_eq(v_n_3636_, v_zero_3631_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; 
lean_dec(v_h__2_3629_);
v___x_3638_ = lean_apply_2(v_h__3_3630_, v_n_3636_, lean_box(0));
return v___x_3638_;
}
else
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
lean_dec(v_n_3636_);
lean_dec(v_h__3_3630_);
v___x_3639_ = lean_box(0);
v___x_3640_ = lean_apply_1(v_h__2_3629_, v___x_3639_);
return v___x_3640_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object* v_k_3641_, lean_object* v_h__1_3642_, lean_object* v_h__2_3643_, lean_object* v_h__3_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(v_k_3641_, v_h__1_3642_, v_h__2_3643_, v_h__3_3644_);
lean_dec(v_k_3641_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object* v_motive_3646_, lean_object* v_k_3647_, lean_object* v_h__1_3648_, lean_object* v_h__2_3649_, lean_object* v_h__3_3650_){
_start:
{
lean_object* v_zero_3651_; uint8_t v_isZero_3652_; 
v_zero_3651_ = lean_unsigned_to_nat(0u);
v_isZero_3652_ = lean_nat_dec_eq(v_k_3647_, v_zero_3651_);
if (v_isZero_3652_ == 1)
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
lean_dec(v_h__3_3650_);
lean_dec(v_h__2_3649_);
v___x_3653_ = lean_box(0);
v___x_3654_ = lean_apply_1(v_h__1_3648_, v___x_3653_);
return v___x_3654_;
}
else
{
lean_object* v_one_3655_; lean_object* v_n_3656_; uint8_t v___x_3657_; 
lean_dec(v_h__1_3648_);
v_one_3655_ = lean_unsigned_to_nat(1u);
v_n_3656_ = lean_nat_sub(v_k_3647_, v_one_3655_);
v___x_3657_ = lean_nat_dec_eq(v_n_3656_, v_zero_3651_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; 
lean_dec(v_h__2_3649_);
v___x_3658_ = lean_apply_2(v_h__3_3650_, v_n_3656_, lean_box(0));
return v___x_3658_;
}
else
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
lean_dec(v_n_3656_);
lean_dec(v_h__3_3650_);
v___x_3659_ = lean_box(0);
v___x_3660_ = lean_apply_1(v_h__2_3649_, v___x_3659_);
return v___x_3660_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object* v_motive_3661_, lean_object* v_k_3662_, lean_object* v_h__1_3663_, lean_object* v_h__2_3664_, lean_object* v_h__3_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(v_motive_3661_, v_k_3662_, v_h__1_3663_, v_h__2_3664_, v_h__3_3665_);
lean_dec(v_k_3662_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_toExpr(lean_object* v_pw_3667_){
_start:
{
lean_object* v_x_3668_; lean_object* v_k_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3680_; 
v_x_3668_ = lean_ctor_get(v_pw_3667_, 0);
v_k_3669_ = lean_ctor_get(v_pw_3667_, 1);
v_isSharedCheck_3680_ = !lean_is_exclusive(v_pw_3667_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3671_ = v_pw_3667_;
v_isShared_3672_ = v_isSharedCheck_3680_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_k_3669_);
lean_inc(v_x_3668_);
lean_dec(v_pw_3667_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3680_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3673_; uint8_t v___x_3674_; 
v___x_3673_ = lean_unsigned_to_nat(1u);
v___x_3674_ = lean_nat_dec_eq(v_k_3669_, v___x_3673_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3675_; lean_object* v___x_3677_; 
v___x_3675_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3675_, 0, v_x_3668_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set_tag(v___x_3671_, 8);
lean_ctor_set(v___x_3671_, 0, v___x_3675_);
v___x_3677_ = v___x_3671_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v_k_3669_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
else
{
lean_object* v___x_3679_; 
lean_del_object(v___x_3671_);
lean_dec(v_k_3669_);
v___x_3679_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3679_, 0, v_x_3668_);
return v___x_3679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_toExpr_go(lean_object* v_m_3681_, lean_object* v_acc_3682_){
_start:
{
if (lean_obj_tag(v_m_3681_) == 0)
{
return v_acc_3682_;
}
else
{
lean_object* v_p_3683_; lean_object* v_m_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3693_; 
v_p_3683_ = lean_ctor_get(v_m_3681_, 0);
v_m_3684_ = lean_ctor_get(v_m_3681_, 1);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_m_3681_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3686_ = v_m_3681_;
v_isShared_3687_ = v_isSharedCheck_3693_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_m_3684_);
lean_inc(v_p_3683_);
lean_dec(v_m_3681_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3693_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3688_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_3683_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set_tag(v___x_3686_, 7);
lean_ctor_set(v___x_3686_, 1, v___x_3688_);
lean_ctor_set(v___x_3686_, 0, v_acc_3682_);
v___x_3690_ = v___x_3686_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_acc_3682_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
v_m_3681_ = v_m_3684_;
v_acc_3682_ = v___x_3690_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_toExpr(lean_object* v_m_3696_){
_start:
{
if (lean_obj_tag(v_m_3696_) == 0)
{
lean_object* v___x_3697_; 
v___x_3697_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__0, &l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0);
return v___x_3697_;
}
else
{
lean_object* v_p_3698_; lean_object* v_m_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v_p_3698_ = lean_ctor_get(v_m_3696_, 0);
lean_inc_ref(v_p_3698_);
v_m_3699_ = lean_ctor_get(v_m_3696_, 1);
lean_inc(v_m_3699_);
lean_dec_ref_known(v_m_3696_, 2);
v___x_3700_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_3698_);
v___x_3701_ = l_Lean_Grind_CommRing_Mon_toExpr_go(v_m_3699_, v___x_3700_);
return v___x_3701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr_goTerm(lean_object* v_k_3702_, lean_object* v_m_3703_){
_start:
{
lean_object* v___x_3704_; uint8_t v___x_3705_; 
v___x_3704_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_3705_ = lean_int_dec_eq(v_k_3702_, v___x_3704_);
if (v___x_3705_ == 0)
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3706_, 0, v_k_3702_);
v___x_3707_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_3703_);
v___x_3708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3706_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
return v___x_3708_;
}
else
{
lean_object* v___x_3709_; 
lean_dec(v_k_3702_);
v___x_3709_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_3703_);
return v___x_3709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr_go(lean_object* v_p_3710_, lean_object* v_acc_3711_){
_start:
{
if (lean_obj_tag(v_p_3710_) == 0)
{
lean_object* v_k_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3722_; 
v_k_3712_ = lean_ctor_get(v_p_3710_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v_p_3710_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3714_ = v_p_3710_;
v_isShared_3715_ = v_isSharedCheck_3722_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_k_3712_);
lean_dec(v_p_3710_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3722_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3716_; uint8_t v___x_3717_; 
v___x_3716_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3717_ = lean_int_dec_eq(v_k_3712_, v___x_3716_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3719_; 
if (v_isShared_3715_ == 0)
{
v___x_3719_ = v___x_3714_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_k_3712_);
v___x_3719_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3720_, 0, v_acc_3711_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
return v___x_3720_;
}
}
else
{
lean_del_object(v___x_3714_);
lean_dec(v_k_3712_);
return v_acc_3711_;
}
}
}
else
{
lean_object* v_k_3723_; lean_object* v_v_3724_; lean_object* v_p_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v_k_3723_ = lean_ctor_get(v_p_3710_, 0);
lean_inc(v_k_3723_);
v_v_3724_ = lean_ctor_get(v_p_3710_, 1);
lean_inc(v_v_3724_);
v_p_3725_ = lean_ctor_get(v_p_3710_, 2);
lean_inc_ref(v_p_3725_);
lean_dec_ref_known(v_p_3710_, 3);
v___x_3726_ = l_Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_3723_, v_v_3724_);
v___x_3727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3727_, 0, v_acc_3711_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v_p_3710_ = v_p_3725_;
v_acc_3711_ = v___x_3727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr(lean_object* v_p_3729_){
_start:
{
if (lean_obj_tag(v_p_3729_) == 0)
{
lean_object* v_k_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
v_k_3730_ = lean_ctor_get(v_p_3729_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v_p_3729_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v_p_3729_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_k_3730_);
lean_dec(v_p_3729_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_k_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
else
{
lean_object* v_k_3738_; lean_object* v_v_3739_; lean_object* v_p_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_k_3738_ = lean_ctor_get(v_p_3729_, 0);
lean_inc(v_k_3738_);
v_v_3739_ = lean_ctor_get(v_p_3729_, 1);
lean_inc(v_v_3739_);
v_p_3740_ = lean_ctor_get(v_p_3729_, 2);
lean_inc_ref(v_p_3740_);
lean_dec_ref_known(v_p_3729_, 3);
v___x_3741_ = l_Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_3738_, v_v_3739_);
v___x_3742_ = l_Lean_Grind_CommRing_Poly_toExpr_go(v_p_3740_, v___x_3741_);
return v___x_3742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteList___redArg(lean_object* v_inst_3743_, lean_object* v_ctx_3744_, lean_object* v_x_3745_){
_start:
{
if (lean_obj_tag(v_x_3745_) == 0)
{
lean_object* v_toSemiring_3746_; lean_object* v_ofNat_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v_toSemiring_3746_ = lean_ctor_get(v_inst_3743_, 0);
lean_inc_ref(v_toSemiring_3746_);
lean_dec_ref(v_inst_3743_);
v_ofNat_3747_ = lean_ctor_get(v_toSemiring_3746_, 3);
lean_inc(v_ofNat_3747_);
lean_dec_ref(v_toSemiring_3746_);
v___x_3748_ = lean_unsigned_to_nat(0u);
v___x_3749_ = lean_apply_1(v_ofNat_3747_, v___x_3748_);
return v___x_3749_;
}
else
{
lean_object* v_toSemiring_3750_; lean_object* v_toAdd_3751_; lean_object* v_head_3752_; lean_object* v_tail_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v_toSemiring_3750_ = lean_ctor_get(v_inst_3743_, 0);
v_toAdd_3751_ = lean_ctor_get(v_toSemiring_3750_, 0);
lean_inc(v_toAdd_3751_);
v_head_3752_ = lean_ctor_get(v_x_3745_, 0);
lean_inc(v_head_3752_);
v_tail_3753_ = lean_ctor_get(v_x_3745_, 1);
lean_inc(v_tail_3753_);
lean_dec_ref_known(v_x_3745_, 2);
lean_inc_ref(v_inst_3743_);
v___x_3754_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_3743_, v_ctx_3744_, v_head_3752_);
v___x_3755_ = l_Lean_Grind_CommRing_Poly_denoteList___redArg(v_inst_3743_, v_ctx_3744_, v_tail_3753_);
v___x_3756_ = lean_apply_2(v_toAdd_3751_, v___x_3754_, v___x_3755_);
return v___x_3756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteList___redArg___boxed(lean_object* v_inst_3757_, lean_object* v_ctx_3758_, lean_object* v_x_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l_Lean_Grind_CommRing_Poly_denoteList___redArg(v_inst_3757_, v_ctx_3758_, v_x_3759_);
lean_dec_ref(v_ctx_3758_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteList(lean_object* v_00_u03b1_3761_, lean_object* v_inst_3762_, lean_object* v_ctx_3763_, lean_object* v_x_3764_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l_Lean_Grind_CommRing_Poly_denoteList___redArg(v_inst_3762_, v_ctx_3763_, v_x_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteList___boxed(lean_object* v_00_u03b1_3766_, lean_object* v_inst_3767_, lean_object* v_ctx_3768_, lean_object* v_x_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l_Lean_Grind_CommRing_Poly_denoteList(v_00_u03b1_3766_, v_inst_3767_, v_ctx_3768_, v_x_3769_);
lean_dec_ref(v_ctx_3768_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denoteList_match__1_splitter___redArg(lean_object* v_x_3771_, lean_object* v_h__1_3772_, lean_object* v_h__2_3773_){
_start:
{
if (lean_obj_tag(v_x_3771_) == 0)
{
lean_object* v___x_3774_; lean_object* v___x_3775_; 
lean_dec(v_h__2_3773_);
v___x_3774_ = lean_box(0);
v___x_3775_ = lean_apply_1(v_h__1_3772_, v___x_3774_);
return v___x_3775_;
}
else
{
lean_object* v_head_3776_; lean_object* v_tail_3777_; lean_object* v___x_3778_; 
lean_dec(v_h__1_3772_);
v_head_3776_ = lean_ctor_get(v_x_3771_, 0);
lean_inc(v_head_3776_);
v_tail_3777_ = lean_ctor_get(v_x_3771_, 1);
lean_inc(v_tail_3777_);
lean_dec_ref_known(v_x_3771_, 2);
v___x_3778_ = lean_apply_2(v_h__2_3773_, v_head_3776_, v_tail_3777_);
return v___x_3778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denoteList_match__1_splitter(lean_object* v_motive_3779_, lean_object* v_x_3780_, lean_object* v_h__1_3781_, lean_object* v_h__2_3782_){
_start:
{
if (lean_obj_tag(v_x_3780_) == 0)
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
lean_dec(v_h__2_3782_);
v___x_3783_ = lean_box(0);
v___x_3784_ = lean_apply_1(v_h__1_3781_, v___x_3783_);
return v___x_3784_;
}
else
{
lean_object* v_head_3785_; lean_object* v_tail_3786_; lean_object* v___x_3787_; 
lean_dec(v_h__1_3781_);
v_head_3785_ = lean_ctor_get(v_x_3780_, 0);
lean_inc(v_head_3785_);
v_tail_3786_ = lean_ctor_get(v_x_3780_, 1);
lean_inc(v_tail_3786_);
lean_dec_ref_known(v_x_3780_, 2);
v___x_3787_ = lean_apply_2(v_h__2_3782_, v_head_3785_, v_tail_3786_);
return v___x_3787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(lean_object* v_inst_3788_, lean_object* v_ctx_3789_, lean_object* v_m_3790_, lean_object* v_acc_3791_){
_start:
{
if (lean_obj_tag(v_m_3790_) == 0)
{
lean_dec_ref(v_inst_3788_);
return v_acc_3791_;
}
else
{
lean_object* v_toSemiring_3792_; lean_object* v_toMul_3793_; lean_object* v_ofNat_3794_; lean_object* v_npow_3795_; lean_object* v_p_3796_; lean_object* v_m_3797_; lean_object* v___y_3799_; lean_object* v_x_3802_; lean_object* v_k_3803_; lean_object* v___x_3804_; uint8_t v___x_3805_; 
v_toSemiring_3792_ = lean_ctor_get(v_inst_3788_, 0);
v_toMul_3793_ = lean_ctor_get(v_toSemiring_3792_, 1);
v_ofNat_3794_ = lean_ctor_get(v_toSemiring_3792_, 3);
v_npow_3795_ = lean_ctor_get(v_toSemiring_3792_, 5);
v_p_3796_ = lean_ctor_get(v_m_3790_, 0);
lean_inc_ref(v_p_3796_);
v_m_3797_ = lean_ctor_get(v_m_3790_, 1);
lean_inc(v_m_3797_);
lean_dec_ref_known(v_m_3790_, 2);
v_x_3802_ = lean_ctor_get(v_p_3796_, 0);
lean_inc(v_x_3802_);
v_k_3803_ = lean_ctor_get(v_p_3796_, 1);
lean_inc(v_k_3803_);
lean_dec_ref(v_p_3796_);
v___x_3804_ = lean_unsigned_to_nat(0u);
v___x_3805_ = lean_nat_dec_eq(v_k_3803_, v___x_3804_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; uint8_t v___x_3807_; 
v___x_3806_ = lean_unsigned_to_nat(1u);
v___x_3807_ = lean_nat_dec_eq(v_k_3803_, v___x_3806_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = l_Lean_RArray_getImpl___redArg(v_ctx_3789_, v_x_3802_);
lean_dec(v_x_3802_);
lean_inc(v_npow_3795_);
v___x_3809_ = lean_apply_2(v_npow_3795_, v___x_3808_, v_k_3803_);
v___y_3799_ = v___x_3809_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3810_; 
lean_dec(v_k_3803_);
v___x_3810_ = l_Lean_RArray_getImpl___redArg(v_ctx_3789_, v_x_3802_);
lean_dec(v_x_3802_);
v___y_3799_ = v___x_3810_;
goto v___jp_3798_;
}
}
else
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
lean_dec(v_k_3803_);
lean_dec(v_x_3802_);
v___x_3811_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3794_);
v___x_3812_ = lean_apply_1(v_ofNat_3794_, v___x_3811_);
v___y_3799_ = v___x_3812_;
goto v___jp_3798_;
}
v___jp_3798_:
{
lean_object* v___x_3800_; 
lean_inc(v_toMul_3793_);
v___x_3800_ = lean_apply_2(v_toMul_3793_, v_acc_3791_, v___y_3799_);
v_m_3790_ = v_m_3797_;
v_acc_3791_ = v___x_3800_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg___boxed(lean_object* v_inst_3813_, lean_object* v_ctx_3814_, lean_object* v_m_3815_, lean_object* v_acc_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3813_, v_ctx_3814_, v_m_3815_, v_acc_3816_);
lean_dec_ref(v_ctx_3814_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(lean_object* v_00_u03b1_3818_, lean_object* v_inst_3819_, lean_object* v_ctx_3820_, lean_object* v_m_3821_, lean_object* v_acc_3822_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3819_, v_ctx_3820_, v_m_3821_, v_acc_3822_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___boxed(lean_object* v_00_u03b1_3824_, lean_object* v_inst_3825_, lean_object* v_ctx_3826_, lean_object* v_m_3827_, lean_object* v_acc_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(v_00_u03b1_3824_, v_inst_3825_, v_ctx_3826_, v_m_3827_, v_acc_3828_);
lean_dec_ref(v_ctx_3826_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(lean_object* v_inst_3830_, lean_object* v_ctx_3831_, lean_object* v_m_3832_){
_start:
{
if (lean_obj_tag(v_m_3832_) == 0)
{
lean_object* v_toSemiring_3833_; lean_object* v_ofNat_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v_toSemiring_3833_ = lean_ctor_get(v_inst_3830_, 0);
lean_inc_ref(v_toSemiring_3833_);
lean_dec_ref(v_inst_3830_);
v_ofNat_3834_ = lean_ctor_get(v_toSemiring_3833_, 3);
lean_inc(v_ofNat_3834_);
lean_dec_ref(v_toSemiring_3833_);
v___x_3835_ = lean_unsigned_to_nat(1u);
v___x_3836_ = lean_apply_1(v_ofNat_3834_, v___x_3835_);
return v___x_3836_;
}
else
{
lean_object* v_toSemiring_3837_; lean_object* v_p_3838_; lean_object* v_m_3839_; lean_object* v_ofNat_3840_; lean_object* v_npow_3841_; lean_object* v_x_3842_; lean_object* v_k_3843_; lean_object* v___x_3844_; uint8_t v___x_3845_; 
v_toSemiring_3837_ = lean_ctor_get(v_inst_3830_, 0);
v_p_3838_ = lean_ctor_get(v_m_3832_, 0);
lean_inc_ref(v_p_3838_);
v_m_3839_ = lean_ctor_get(v_m_3832_, 1);
lean_inc(v_m_3839_);
lean_dec_ref_known(v_m_3832_, 2);
v_ofNat_3840_ = lean_ctor_get(v_toSemiring_3837_, 3);
v_npow_3841_ = lean_ctor_get(v_toSemiring_3837_, 5);
v_x_3842_ = lean_ctor_get(v_p_3838_, 0);
lean_inc(v_x_3842_);
v_k_3843_ = lean_ctor_get(v_p_3838_, 1);
lean_inc(v_k_3843_);
lean_dec_ref(v_p_3838_);
v___x_3844_ = lean_unsigned_to_nat(0u);
v___x_3845_ = lean_nat_dec_eq(v_k_3843_, v___x_3844_);
if (v___x_3845_ == 0)
{
lean_object* v___x_3846_; uint8_t v___x_3847_; 
v___x_3846_ = lean_unsigned_to_nat(1u);
v___x_3847_ = lean_nat_dec_eq(v_k_3843_, v___x_3846_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3848_ = l_Lean_RArray_getImpl___redArg(v_ctx_3831_, v_x_3842_);
lean_dec(v_x_3842_);
lean_inc(v_npow_3841_);
v___x_3849_ = lean_apply_2(v_npow_3841_, v___x_3848_, v_k_3843_);
v___x_3850_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3830_, v_ctx_3831_, v_m_3839_, v___x_3849_);
return v___x_3850_;
}
else
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
lean_dec(v_k_3843_);
v___x_3851_ = l_Lean_RArray_getImpl___redArg(v_ctx_3831_, v_x_3842_);
lean_dec(v_x_3842_);
v___x_3852_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3830_, v_ctx_3831_, v_m_3839_, v___x_3851_);
return v___x_3852_;
}
}
else
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
lean_dec(v_k_3843_);
lean_dec(v_x_3842_);
v___x_3853_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3840_);
v___x_3854_ = lean_apply_1(v_ofNat_3840_, v___x_3853_);
v___x_3855_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3830_, v_ctx_3831_, v_m_3839_, v___x_3854_);
return v___x_3855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3856_, lean_object* v_ctx_3857_, lean_object* v_m_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3856_, v_ctx_3857_, v_m_3858_);
lean_dec_ref(v_ctx_3857_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule(lean_object* v_00_u03b1_3860_, lean_object* v_inst_3861_, lean_object* v_ctx_3862_, lean_object* v_m_3863_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3861_, v_ctx_3862_, v_m_3863_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3865_, lean_object* v_inst_3866_, lean_object* v_ctx_3867_, lean_object* v_m_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule(v_00_u03b1_3865_, v_inst_3866_, v_ctx_3867_, v_m_3868_);
lean_dec_ref(v_ctx_3867_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(lean_object* v_inst_3870_, lean_object* v_ctx_3871_, lean_object* v_p_3872_){
_start:
{
lean_object* v___x_3873_; 
lean_inc_ref(v_inst_3870_);
v___x_3873_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_3870_);
if (lean_obj_tag(v_p_3872_) == 0)
{
lean_object* v_toSemiring_3874_; lean_object* v_zsmul_3875_; lean_object* v_ofNat_3876_; lean_object* v_k_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v_toSemiring_3874_ = lean_ctor_get(v_inst_3870_, 0);
lean_inc_ref(v_toSemiring_3874_);
lean_dec_ref(v_inst_3870_);
v_zsmul_3875_ = lean_ctor_get(v___x_3873_, 2);
lean_inc(v_zsmul_3875_);
lean_dec_ref(v___x_3873_);
v_ofNat_3876_ = lean_ctor_get(v_toSemiring_3874_, 3);
lean_inc(v_ofNat_3876_);
lean_dec_ref(v_toSemiring_3874_);
v_k_3877_ = lean_ctor_get(v_p_3872_, 0);
lean_inc(v_k_3877_);
lean_dec_ref_known(v_p_3872_, 1);
v___x_3878_ = lean_unsigned_to_nat(1u);
v___x_3879_ = lean_apply_1(v_ofNat_3876_, v___x_3878_);
v___x_3880_ = lean_apply_2(v_zsmul_3875_, v_k_3877_, v___x_3879_);
return v___x_3880_;
}
else
{
lean_object* v_toSemiring_3881_; lean_object* v_zsmul_3882_; lean_object* v_toAdd_3883_; lean_object* v_k_3884_; lean_object* v_v_3885_; lean_object* v_p_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v_toSemiring_3881_ = lean_ctor_get(v_inst_3870_, 0);
v_zsmul_3882_ = lean_ctor_get(v___x_3873_, 2);
lean_inc(v_zsmul_3882_);
lean_dec_ref(v___x_3873_);
v_toAdd_3883_ = lean_ctor_get(v_toSemiring_3881_, 0);
lean_inc(v_toAdd_3883_);
v_k_3884_ = lean_ctor_get(v_p_3872_, 0);
lean_inc(v_k_3884_);
v_v_3885_ = lean_ctor_get(v_p_3872_, 1);
lean_inc(v_v_3885_);
v_p_3886_ = lean_ctor_get(v_p_3872_, 2);
lean_inc_ref(v_p_3886_);
lean_dec_ref_known(v_p_3872_, 3);
lean_inc_ref(v_inst_3870_);
v___x_3887_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3870_, v_ctx_3871_, v_v_3885_);
v___x_3888_ = lean_apply_2(v_zsmul_3882_, v_k_3884_, v___x_3887_);
v___x_3889_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3870_, v_ctx_3871_, v_p_3886_);
v___x_3890_ = lean_apply_2(v_toAdd_3883_, v___x_3888_, v___x_3889_);
return v___x_3890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3891_, lean_object* v_ctx_3892_, lean_object* v_p_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3891_, v_ctx_3892_, v_p_3893_);
lean_dec_ref(v_ctx_3892_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule(lean_object* v_00_u03b1_3895_, lean_object* v_inst_3896_, lean_object* v_ctx_3897_, lean_object* v_p_3898_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3896_, v_ctx_3897_, v_p_3898_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3900_, lean_object* v_inst_3901_, lean_object* v_ctx_3902_, lean_object* v_p_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule(v_00_u03b1_3900_, v_inst_3901_, v_ctx_3902_, v_p_3903_);
lean_dec_ref(v_ctx_3902_);
return v_res_3904_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__gcd__cert(lean_object* v_a_3905_, lean_object* v_b_3906_, lean_object* v_p_u2081_3907_, lean_object* v_p_u2082_3908_, lean_object* v_p_3909_){
_start:
{
if (lean_obj_tag(v_p_u2081_3907_) == 0)
{
if (lean_obj_tag(v_p_u2082_3908_) == 0)
{
if (lean_obj_tag(v_p_3909_) == 0)
{
lean_object* v_k_3910_; lean_object* v_k_3911_; lean_object* v_k_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; uint8_t v___x_3916_; 
v_k_3910_ = lean_ctor_get(v_p_u2081_3907_, 0);
v_k_3911_ = lean_ctor_get(v_p_u2082_3908_, 0);
v_k_3912_ = lean_ctor_get(v_p_3909_, 0);
v___x_3913_ = lean_int_mul(v_a_3905_, v_k_3910_);
v___x_3914_ = lean_int_mul(v_b_3906_, v_k_3911_);
v___x_3915_ = lean_int_add(v___x_3913_, v___x_3914_);
lean_dec(v___x_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_int_dec_eq(v_k_3912_, v___x_3915_);
lean_dec(v___x_3915_);
return v___x_3916_;
}
else
{
uint8_t v___x_3917_; 
v___x_3917_ = 0;
return v___x_3917_;
}
}
else
{
uint8_t v___x_3918_; 
v___x_3918_ = 0;
return v___x_3918_;
}
}
else
{
uint8_t v___x_3919_; 
v___x_3919_ = 0;
return v___x_3919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__gcd__cert___boxed(lean_object* v_a_3920_, lean_object* v_b_3921_, lean_object* v_p_u2081_3922_, lean_object* v_p_u2082_3923_, lean_object* v_p_3924_){
_start:
{
uint8_t v_res_3925_; lean_object* v_r_3926_; 
v_res_3925_ = l_Lean_Grind_CommRing_eq__gcd__cert(v_a_3920_, v_b_3921_, v_p_u2081_3922_, v_p_u2082_3923_, v_p_3924_);
lean_dec_ref(v_p_3924_);
lean_dec_ref(v_p_u2082_3923_);
lean_dec_ref(v_p_u2081_3922_);
lean_dec(v_b_3921_);
lean_dec(v_a_3920_);
v_r_3926_ = lean_box(v_res_3925_);
return v_r_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(lean_object* v_p_3927_, lean_object* v_h__1_3928_, lean_object* v_h__2_3929_){
_start:
{
if (lean_obj_tag(v_p_3927_) == 0)
{
lean_object* v_k_3930_; lean_object* v___x_3931_; 
lean_dec(v_h__1_3928_);
v_k_3930_ = lean_ctor_get(v_p_3927_, 0);
lean_inc(v_k_3930_);
lean_dec_ref_known(v_p_3927_, 1);
v___x_3931_ = lean_apply_1(v_h__2_3929_, v_k_3930_);
return v___x_3931_;
}
else
{
lean_object* v_k_3932_; lean_object* v_v_3933_; lean_object* v_p_3934_; lean_object* v___x_3935_; 
lean_dec(v_h__2_3929_);
v_k_3932_ = lean_ctor_get(v_p_3927_, 0);
lean_inc(v_k_3932_);
v_v_3933_ = lean_ctor_get(v_p_3927_, 1);
lean_inc(v_v_3933_);
v_p_3934_ = lean_ctor_get(v_p_3927_, 2);
lean_inc_ref(v_p_3934_);
lean_dec_ref_known(v_p_3927_, 3);
v___x_3935_ = lean_apply_3(v_h__1_3928_, v_k_3932_, v_v_3933_, v_p_3934_);
return v___x_3935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter(lean_object* v_motive_3936_, lean_object* v_p_3937_, lean_object* v_h__1_3938_, lean_object* v_h__2_3939_){
_start:
{
if (lean_obj_tag(v_p_3937_) == 0)
{
lean_object* v_k_3940_; lean_object* v___x_3941_; 
lean_dec(v_h__1_3938_);
v_k_3940_ = lean_ctor_get(v_p_3937_, 0);
lean_inc(v_k_3940_);
lean_dec_ref_known(v_p_3937_, 1);
v___x_3941_ = lean_apply_1(v_h__2_3939_, v_k_3940_);
return v___x_3941_;
}
else
{
lean_object* v_k_3942_; lean_object* v_v_3943_; lean_object* v_p_3944_; lean_object* v___x_3945_; 
lean_dec(v_h__2_3939_);
v_k_3942_ = lean_ctor_get(v_p_3937_, 0);
lean_inc(v_k_3942_);
v_v_3943_ = lean_ctor_get(v_p_3937_, 1);
lean_inc(v_v_3943_);
v_p_3944_ = lean_ctor_get(v_p_3937_, 2);
lean_inc_ref(v_p_3944_);
lean_dec_ref_known(v_p_3937_, 3);
v___x_3945_ = lean_apply_3(v_h__1_3938_, v_k_3942_, v_v_3943_, v_p_3944_);
return v___x_3945_;
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
lean_object* runtime_initialize_Init_Data_Int_Kernel(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Int_Kernel(builtin);
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
lean_object* initialize_Init_Data_Int_Kernel(uint8_t builtin);
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
res = initialize_Init_Data_Int_Kernel(builtin);
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
