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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go(lean_object* v_fuel_1090_, lean_object* v_m_u2081_1091_, lean_object* v_m_u2082_1092_){
_start:
{
lean_object* v_zero_1093_; uint8_t v_isZero_1094_; 
v_zero_1093_ = lean_unsigned_to_nat(0u);
v_isZero_1094_ = lean_nat_dec_eq(v_fuel_1090_, v_zero_1093_);
if (v_isZero_1094_ == 1)
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Grind_CommRing_Mon_concat(v_m_u2081_1091_, v_m_u2082_1092_);
lean_dec(v_m_u2082_1092_);
return v___x_1095_;
}
else
{
if (lean_obj_tag(v_m_u2082_1092_) == 0)
{
return v_m_u2081_1091_;
}
else
{
if (lean_obj_tag(v_m_u2081_1091_) == 0)
{
return v_m_u2082_1092_;
}
else
{
lean_object* v_p_1096_; lean_object* v_m_1097_; lean_object* v_p_1098_; lean_object* v_m_1099_; lean_object* v_one_1100_; lean_object* v_n_1101_; uint8_t v___x_1102_; 
v_p_1096_ = lean_ctor_get(v_m_u2082_1092_, 0);
lean_inc_ref(v_p_1096_);
v_m_1097_ = lean_ctor_get(v_m_u2082_1092_, 1);
v_p_1098_ = lean_ctor_get(v_m_u2081_1091_, 0);
v_m_1099_ = lean_ctor_get(v_m_u2081_1091_, 1);
v_one_1100_ = lean_unsigned_to_nat(1u);
v_n_1101_ = lean_nat_sub(v_fuel_1090_, v_one_1100_);
v___x_1102_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1098_, v_p_1096_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1133_; 
lean_inc(v_m_1097_);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_m_u2082_1092_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; lean_object* v_unused_1135_; 
v_unused_1134_ = lean_ctor_get(v_m_u2082_1092_, 1);
lean_dec(v_unused_1134_);
v_unused_1135_ = lean_ctor_get(v_m_u2082_1092_, 0);
lean_dec(v_unused_1135_);
v___x_1104_ = v_m_u2082_1092_;
v_isShared_1105_ = v_isSharedCheck_1133_;
goto v_resetjp_1103_;
}
else
{
lean_dec(v_m_u2082_1092_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1133_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
uint8_t v___x_1106_; 
v___x_1106_ = l_Lean_Grind_CommRing_Power_varLt(v_p_1096_, v_p_1098_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1126_; 
lean_inc(v_m_1099_);
lean_inc_ref(v_p_1098_);
lean_del_object(v___x_1104_);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_m_u2081_1091_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; lean_object* v_unused_1128_; 
v_unused_1127_ = lean_ctor_get(v_m_u2081_1091_, 1);
lean_dec(v_unused_1127_);
v_unused_1128_ = lean_ctor_get(v_m_u2081_1091_, 0);
lean_dec(v_unused_1128_);
v___x_1108_ = v_m_u2081_1091_;
v_isShared_1109_ = v_isSharedCheck_1126_;
goto v_resetjp_1107_;
}
else
{
lean_dec(v_m_u2081_1091_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1126_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_x_1110_; lean_object* v_k_1111_; lean_object* v_k_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1124_; 
v_x_1110_ = lean_ctor_get(v_p_1098_, 0);
lean_inc(v_x_1110_);
v_k_1111_ = lean_ctor_get(v_p_1098_, 1);
lean_inc(v_k_1111_);
lean_dec_ref(v_p_1098_);
v_k_1112_ = lean_ctor_get(v_p_1096_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_p_1096_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; 
v_unused_1125_ = lean_ctor_get(v_p_1096_, 0);
lean_dec(v_unused_1125_);
v___x_1114_ = v_p_1096_;
v_isShared_1115_ = v_isSharedCheck_1124_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_k_1112_);
lean_dec(v_p_1096_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1124_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1116_ = lean_nat_add(v_k_1111_, v_k_1112_);
lean_dec(v_k_1112_);
lean_dec(v_k_1111_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1116_);
lean_ctor_set(v___x_1114_, 0, v_x_1110_);
v___x_1118_ = v___x_1114_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_x_1110_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1119_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1101_, v_m_1099_, v_m_1097_);
lean_dec(v_n_1101_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 1, v___x_1119_);
lean_ctor_set(v___x_1108_, 0, v___x_1118_);
v___x_1121_ = v___x_1108_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1101_, v_m_u2081_1091_, v_m_1097_);
lean_dec(v_n_1101_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 1, v___x_1129_);
v___x_1131_ = v___x_1104_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_p_1096_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
lean_inc(v_m_1099_);
lean_inc_ref(v_p_1098_);
lean_dec_ref(v_p_1096_);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_m_u2081_1091_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; lean_object* v_unused_1145_; 
v_unused_1144_ = lean_ctor_get(v_m_u2081_1091_, 1);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_m_u2081_1091_, 0);
lean_dec(v_unused_1145_);
v___x_1137_ = v_m_u2081_1091_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_dec(v_m_u2081_1091_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = l_Lean_Grind_CommRing_Mon_mul_go(v_n_1101_, v_m_1099_, v_m_u2082_1092_);
lean_dec(v_n_1101_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_p_1098_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul_go___boxed(lean_object* v_fuel_1146_, lean_object* v_m_u2081_1147_, lean_object* v_m_u2082_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Grind_CommRing_Mon_mul_go(v_fuel_1146_, v_m_u2081_1147_, v_m_u2082_1148_);
lean_dec(v_fuel_1146_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul(lean_object* v_m_u2081_1150_, lean_object* v_m_u2082_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1152_ = l_Lean_Grind_CommRing_Mon_length(v_m_u2081_1150_);
v___x_1153_ = l_Lean_Grind_CommRing_Mon_length(v_m_u2082_1151_);
v___x_1154_ = lean_nat_add(v___x_1152_, v___x_1153_);
lean_dec(v___x_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_unsigned_to_nat(1u);
v___x_1156_ = lean_nat_add(v___x_1154_, v___x_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = l_Lean_Grind_CommRing_Mon_mul_go(v___x_1156_, v_m_u2081_1150_, v_m_u2082_1151_);
lean_dec(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object* v_fuel_1158_, lean_object* v_h__1_1159_, lean_object* v_h__2_1160_){
_start:
{
lean_object* v_zero_1161_; uint8_t v_isZero_1162_; 
v_zero_1161_ = lean_unsigned_to_nat(0u);
v_isZero_1162_ = lean_nat_dec_eq(v_fuel_1158_, v_zero_1161_);
if (v_isZero_1162_ == 1)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec(v_h__2_1160_);
v___x_1163_ = lean_box(0);
v___x_1164_ = lean_apply_1(v_h__1_1159_, v___x_1163_);
return v___x_1164_;
}
else
{
lean_object* v_one_1165_; lean_object* v_n_1166_; lean_object* v___x_1167_; 
lean_dec(v_h__1_1159_);
v_one_1165_ = lean_unsigned_to_nat(1u);
v_n_1166_ = lean_nat_sub(v_fuel_1158_, v_one_1165_);
v___x_1167_ = lean_apply_1(v_h__2_1160_, v_n_1166_);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object* v_fuel_1168_, lean_object* v_h__1_1169_, lean_object* v_h__2_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(v_fuel_1168_, v_h__1_1169_, v_h__2_1170_);
lean_dec(v_fuel_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object* v_motive_1172_, lean_object* v_fuel_1173_, lean_object* v_h__1_1174_, lean_object* v_h__2_1175_){
_start:
{
lean_object* v_zero_1176_; uint8_t v_isZero_1177_; 
v_zero_1176_ = lean_unsigned_to_nat(0u);
v_isZero_1177_ = lean_nat_dec_eq(v_fuel_1173_, v_zero_1176_);
if (v_isZero_1177_ == 1)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec(v_h__2_1175_);
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_apply_1(v_h__1_1174_, v___x_1178_);
return v___x_1179_;
}
else
{
lean_object* v_one_1180_; lean_object* v_n_1181_; lean_object* v___x_1182_; 
lean_dec(v_h__1_1174_);
v_one_1180_ = lean_unsigned_to_nat(1u);
v_n_1181_ = lean_nat_sub(v_fuel_1173_, v_one_1180_);
v___x_1182_ = lean_apply_1(v_h__2_1175_, v_n_1181_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object* v_motive_1183_, lean_object* v_fuel_1184_, lean_object* v_h__1_1185_, lean_object* v_h__2_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(v_motive_1183_, v_fuel_1184_, v_h__1_1185_, v_h__2_1186_);
lean_dec(v_fuel_1184_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter___redArg(lean_object* v_m_u2081_1188_, lean_object* v_m_u2082_1189_, lean_object* v_h__1_1190_, lean_object* v_h__2_1191_, lean_object* v_h__3_1192_){
_start:
{
if (lean_obj_tag(v_m_u2082_1189_) == 0)
{
lean_object* v___x_1193_; 
lean_dec(v_h__3_1192_);
lean_dec(v_h__2_1191_);
v___x_1193_ = lean_apply_1(v_h__1_1190_, v_m_u2081_1188_);
return v___x_1193_;
}
else
{
lean_dec(v_h__1_1190_);
if (lean_obj_tag(v_m_u2081_1188_) == 0)
{
lean_object* v___x_1194_; 
lean_dec(v_h__3_1192_);
v___x_1194_ = lean_apply_2(v_h__2_1191_, v_m_u2082_1189_, lean_box(0));
return v___x_1194_;
}
else
{
lean_object* v_p_1195_; lean_object* v_m_1196_; lean_object* v_p_1197_; lean_object* v_m_1198_; lean_object* v___x_1199_; 
lean_dec(v_h__2_1191_);
v_p_1195_ = lean_ctor_get(v_m_u2082_1189_, 0);
lean_inc_ref(v_p_1195_);
v_m_1196_ = lean_ctor_get(v_m_u2082_1189_, 1);
lean_inc(v_m_1196_);
lean_dec_ref_known(v_m_u2082_1189_, 2);
v_p_1197_ = lean_ctor_get(v_m_u2081_1188_, 0);
lean_inc_ref(v_p_1197_);
v_m_1198_ = lean_ctor_get(v_m_u2081_1188_, 1);
lean_inc(v_m_1198_);
lean_dec_ref_known(v_m_u2081_1188_, 2);
v___x_1199_ = lean_apply_4(v_h__3_1192_, v_p_1197_, v_m_1198_, v_p_1195_, v_m_1196_);
return v___x_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul_go_match__1_splitter(lean_object* v_motive_1200_, lean_object* v_m_u2081_1201_, lean_object* v_m_u2082_1202_, lean_object* v_h__1_1203_, lean_object* v_h__2_1204_, lean_object* v_h__3_1205_){
_start:
{
if (lean_obj_tag(v_m_u2082_1202_) == 0)
{
lean_object* v___x_1206_; 
lean_dec(v_h__3_1205_);
lean_dec(v_h__2_1204_);
v___x_1206_ = lean_apply_1(v_h__1_1203_, v_m_u2081_1201_);
return v___x_1206_;
}
else
{
lean_dec(v_h__1_1203_);
if (lean_obj_tag(v_m_u2081_1201_) == 0)
{
lean_object* v___x_1207_; 
lean_dec(v_h__3_1205_);
v___x_1207_ = lean_apply_2(v_h__2_1204_, v_m_u2082_1202_, lean_box(0));
return v___x_1207_;
}
else
{
lean_object* v_p_1208_; lean_object* v_m_1209_; lean_object* v_p_1210_; lean_object* v_m_1211_; lean_object* v___x_1212_; 
lean_dec(v_h__2_1204_);
v_p_1208_ = lean_ctor_get(v_m_u2082_1202_, 0);
lean_inc_ref(v_p_1208_);
v_m_1209_ = lean_ctor_get(v_m_u2082_1202_, 1);
lean_inc(v_m_1209_);
lean_dec_ref_known(v_m_u2082_1202_, 2);
v_p_1210_ = lean_ctor_get(v_m_u2081_1201_, 0);
lean_inc_ref(v_p_1210_);
v_m_1211_ = lean_ctor_get(v_m_u2081_1201_, 1);
lean_inc(v_m_1211_);
lean_dec_ref_known(v_m_u2081_1201_, 2);
v___x_1212_ = lean_apply_4(v_h__3_1205_, v_p_1210_, v_m_1211_, v_p_1208_, v_m_1209_);
return v___x_1212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_mul__nc(lean_object* v_m_u2081_1213_, lean_object* v_m_u2082_1214_){
_start:
{
if (lean_obj_tag(v_m_u2081_1213_) == 0)
{
return v_m_u2082_1214_;
}
else
{
lean_object* v_m_1215_; 
v_m_1215_ = lean_ctor_get(v_m_u2081_1213_, 1);
if (lean_obj_tag(v_m_1215_) == 0)
{
lean_object* v_p_1216_; lean_object* v___x_1217_; 
v_p_1216_ = lean_ctor_get(v_m_u2081_1213_, 0);
lean_inc_ref(v_p_1216_);
lean_dec_ref_known(v_m_u2081_1213_, 2);
v___x_1217_ = l_Lean_Grind_CommRing_Mon_mulPow__nc(v_p_1216_, v_m_u2082_1214_);
return v___x_1217_;
}
else
{
lean_object* v_p_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1226_; 
lean_inc(v_m_1215_);
v_p_1218_ = lean_ctor_get(v_m_u2081_1213_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_m_u2081_1213_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; 
v_unused_1227_ = lean_ctor_get(v_m_u2081_1213_, 1);
lean_dec(v_unused_1227_);
v___x_1220_ = v_m_u2081_1213_;
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_p_1218_);
lean_dec(v_m_u2081_1213_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_1215_, v_m_u2082_1214_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 1, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_p_1218_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object* v_x_1228_){
_start:
{
if (lean_obj_tag(v_x_1228_) == 0)
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_unsigned_to_nat(0u);
return v___x_1229_;
}
else
{
lean_object* v_p_1230_; lean_object* v_m_1231_; lean_object* v_k_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_p_1230_ = lean_ctor_get(v_x_1228_, 0);
v_m_1231_ = lean_ctor_get(v_x_1228_, 1);
v_k_1232_ = lean_ctor_get(v_p_1230_, 1);
v___x_1233_ = l_Lean_Grind_CommRing_Mon_degree(v_m_1231_);
v___x_1234_ = lean_nat_add(v_k_1232_, v___x_1233_);
lean_dec(v___x_1233_);
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degree___boxed(lean_object* v_x_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Grind_CommRing_Mon_degree(v_x_1235_);
lean_dec(v_x_1235_);
return v_res_1236_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Var_revlex(lean_object* v_x_1237_, lean_object* v_y_1238_){
_start:
{
uint8_t v___x_1239_; 
v___x_1239_ = l_Nat_blt(v_x_1237_, v_y_1238_);
if (v___x_1239_ == 0)
{
uint8_t v___x_1240_; 
v___x_1240_ = l_Nat_blt(v_y_1238_, v_x_1237_);
if (v___x_1240_ == 0)
{
uint8_t v___x_1241_; 
v___x_1241_ = 1;
return v___x_1241_;
}
else
{
uint8_t v___x_1242_; 
v___x_1242_ = 0;
return v___x_1242_;
}
}
else
{
uint8_t v___x_1243_; 
v___x_1243_ = 2;
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Var_revlex___boxed(lean_object* v_x_1244_, lean_object* v_y_1245_){
_start:
{
uint8_t v_res_1246_; lean_object* v_r_1247_; 
v_res_1246_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1244_, v_y_1245_);
lean_dec(v_y_1245_);
lean_dec(v_x_1244_);
v_r_1247_ = lean_box(v_res_1246_);
return v_r_1247_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_powerRevlex(lean_object* v_k_u2081_1248_, lean_object* v_k_u2082_1249_){
_start:
{
uint8_t v___x_1250_; 
v___x_1250_ = l_Nat_blt(v_k_u2081_1248_, v_k_u2082_1249_);
if (v___x_1250_ == 0)
{
uint8_t v___x_1251_; 
v___x_1251_ = l_Nat_blt(v_k_u2082_1249_, v_k_u2081_1248_);
if (v___x_1251_ == 0)
{
uint8_t v___x_1252_; 
v___x_1252_ = 1;
return v___x_1252_;
}
else
{
uint8_t v___x_1253_; 
v___x_1253_ = 0;
return v___x_1253_;
}
}
else
{
uint8_t v___x_1254_; 
v___x_1254_ = 2;
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_powerRevlex___boxed(lean_object* v_k_u2081_1255_, lean_object* v_k_u2082_1256_){
_start:
{
uint8_t v_res_1257_; lean_object* v_r_1258_; 
v_res_1257_ = l_Lean_Grind_CommRing_powerRevlex(v_k_u2081_1255_, v_k_u2082_1256_);
lean_dec(v_k_u2082_1256_);
lean_dec(v_k_u2081_1255_);
v_r_1258_ = lean_box(v_res_1257_);
return v_r_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(uint8_t v_c_1259_, lean_object* v_h__1_1260_, lean_object* v_h__2_1261_){
_start:
{
if (v_c_1259_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec(v_h__1_1260_);
v___x_1262_ = lean_box(0);
v___x_1263_ = lean_apply_1(v_h__2_1261_, v___x_1262_);
return v___x_1263_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec(v_h__2_1261_);
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_apply_1(v_h__1_1260_, v___x_1264_);
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg___boxed(lean_object* v_c_1266_, lean_object* v_h__1_1267_, lean_object* v_h__2_1268_){
_start:
{
uint8_t v_c_24__boxed_1269_; lean_object* v_res_1270_; 
v_c_24__boxed_1269_ = lean_unbox(v_c_1266_);
v_res_1270_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___redArg(v_c_24__boxed_1269_, v_h__1_1267_, v_h__2_1268_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(lean_object* v_motive_1271_, uint8_t v_c_1272_, lean_object* v_h__1_1273_, lean_object* v_h__2_1274_){
_start:
{
if (v_c_1272_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec(v_h__1_1273_);
v___x_1275_ = lean_box(0);
v___x_1276_ = lean_apply_1(v_h__2_1274_, v___x_1275_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec(v_h__2_1274_);
v___x_1277_ = lean_box(0);
v___x_1278_ = lean_apply_1(v_h__1_1273_, v___x_1277_);
return v___x_1278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter___boxed(lean_object* v_motive_1279_, lean_object* v_c_1280_, lean_object* v_h__1_1281_, lean_object* v_h__2_1282_){
_start:
{
uint8_t v_c_35__boxed_1283_; lean_object* v_res_1284_; 
v_c_35__boxed_1283_ = lean_unbox(v_c_1280_);
v_res_1284_ = l___private_Init_Grind_Ring_CommSolver_0__cond_match__1_splitter(v_motive_1279_, v_c_35__boxed_1283_, v_h__1_1281_, v_h__2_1282_);
return v_res_1284_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Power_revlex(lean_object* v_p_u2081_1285_, lean_object* v_p_u2082_1286_){
_start:
{
lean_object* v_x_1287_; lean_object* v_k_1288_; lean_object* v_x_1289_; lean_object* v_k_1290_; uint8_t v___x_1291_; 
v_x_1287_ = lean_ctor_get(v_p_u2081_1285_, 0);
v_k_1288_ = lean_ctor_get(v_p_u2081_1285_, 1);
v_x_1289_ = lean_ctor_get(v_p_u2082_1286_, 0);
v_k_1290_ = lean_ctor_get(v_p_u2082_1286_, 1);
v___x_1291_ = l_Lean_Grind_CommRing_Var_revlex(v_x_1287_, v_x_1289_);
if (v___x_1291_ == 1)
{
uint8_t v___x_1292_; 
v___x_1292_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1288_, v_k_1290_);
return v___x_1292_;
}
else
{
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_revlex___boxed(lean_object* v_p_u2081_1293_, lean_object* v_p_u2082_1294_){
_start:
{
uint8_t v_res_1295_; lean_object* v_r_1296_; 
v_res_1295_ = l_Lean_Grind_CommRing_Power_revlex(v_p_u2081_1293_, v_p_u2082_1294_);
lean_dec_ref(v_p_u2082_1294_);
lean_dec_ref(v_p_u2081_1293_);
v_r_1296_ = lean_box(v_res_1295_);
return v_r_1296_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexWF(lean_object* v_m_u2081_1297_, lean_object* v_m_u2082_1298_){
_start:
{
if (lean_obj_tag(v_m_u2081_1297_) == 0)
{
if (lean_obj_tag(v_m_u2082_1298_) == 0)
{
uint8_t v___x_1299_; 
v___x_1299_ = 1;
return v___x_1299_;
}
else
{
uint8_t v___x_1300_; 
v___x_1300_ = 2;
return v___x_1300_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1298_) == 0)
{
uint8_t v___x_1301_; 
v___x_1301_ = 0;
return v___x_1301_;
}
else
{
lean_object* v_p_1302_; lean_object* v_p_1303_; lean_object* v_m_1304_; lean_object* v_m_1305_; lean_object* v_x_1306_; lean_object* v_k_1307_; lean_object* v_x_1308_; lean_object* v_k_1309_; uint8_t v___x_1310_; 
v_p_1302_ = lean_ctor_get(v_m_u2081_1297_, 0);
v_p_1303_ = lean_ctor_get(v_m_u2082_1298_, 0);
v_m_1304_ = lean_ctor_get(v_m_u2081_1297_, 1);
v_m_1305_ = lean_ctor_get(v_m_u2082_1298_, 1);
v_x_1306_ = lean_ctor_get(v_p_1302_, 0);
v_k_1307_ = lean_ctor_get(v_p_1302_, 1);
v_x_1308_ = lean_ctor_get(v_p_1303_, 0);
v_k_1309_ = lean_ctor_get(v_p_1303_, 1);
v___x_1310_ = lean_nat_dec_eq(v_x_1306_, v_x_1308_);
if (v___x_1310_ == 0)
{
uint8_t v___x_1311_; 
v___x_1311_ = l_Nat_blt(v_x_1306_, v_x_1308_);
if (v___x_1311_ == 0)
{
uint8_t v___x_1312_; 
v___x_1312_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1297_, v_m_1305_);
if (v___x_1312_ == 1)
{
uint8_t v___x_1313_; 
v___x_1313_ = 2;
return v___x_1313_;
}
else
{
return v___x_1312_;
}
}
else
{
uint8_t v___x_1314_; 
v___x_1314_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1304_, v_m_u2082_1298_);
if (v___x_1314_ == 1)
{
uint8_t v___x_1315_; 
v___x_1315_ = 0;
return v___x_1315_;
}
else
{
return v___x_1314_;
}
}
}
else
{
uint8_t v___x_1316_; 
v___x_1316_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_1304_, v_m_1305_);
if (v___x_1316_ == 1)
{
uint8_t v___x_1317_; 
v___x_1317_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1307_, v_k_1309_);
return v___x_1317_;
}
else
{
return v___x_1316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexWF___boxed(lean_object* v_m_u2081_1318_, lean_object* v_m_u2082_1319_){
_start:
{
uint8_t v_res_1320_; lean_object* v_r_1321_; 
v_res_1320_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1318_, v_m_u2082_1319_);
lean_dec(v_m_u2082_1319_);
lean_dec(v_m_u2081_1318_);
v_r_1321_ = lean_box(v_res_1320_);
return v_r_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter___redArg(lean_object* v_m_u2081_1322_, lean_object* v_m_u2082_1323_, lean_object* v_h__1_1324_, lean_object* v_h__2_1325_, lean_object* v_h__3_1326_, lean_object* v_h__4_1327_){
_start:
{
if (lean_obj_tag(v_m_u2081_1322_) == 0)
{
lean_dec(v_h__4_1327_);
lean_dec(v_h__3_1326_);
if (lean_obj_tag(v_m_u2082_1323_) == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec(v_h__2_1325_);
v___x_1328_ = lean_box(0);
v___x_1329_ = lean_apply_1(v_h__1_1324_, v___x_1328_);
return v___x_1329_;
}
else
{
lean_object* v_p_1330_; lean_object* v_m_1331_; lean_object* v___x_1332_; 
lean_dec(v_h__1_1324_);
v_p_1330_ = lean_ctor_get(v_m_u2082_1323_, 0);
lean_inc_ref(v_p_1330_);
v_m_1331_ = lean_ctor_get(v_m_u2082_1323_, 1);
lean_inc(v_m_1331_);
lean_dec_ref_known(v_m_u2082_1323_, 2);
v___x_1332_ = lean_apply_2(v_h__2_1325_, v_p_1330_, v_m_1331_);
return v___x_1332_;
}
}
else
{
lean_dec(v_h__2_1325_);
lean_dec(v_h__1_1324_);
if (lean_obj_tag(v_m_u2082_1323_) == 0)
{
lean_object* v_p_1333_; lean_object* v_m_1334_; lean_object* v___x_1335_; 
lean_dec(v_h__4_1327_);
v_p_1333_ = lean_ctor_get(v_m_u2081_1322_, 0);
lean_inc_ref(v_p_1333_);
v_m_1334_ = lean_ctor_get(v_m_u2081_1322_, 1);
lean_inc(v_m_1334_);
lean_dec_ref_known(v_m_u2081_1322_, 2);
v___x_1335_ = lean_apply_2(v_h__3_1326_, v_p_1333_, v_m_1334_);
return v___x_1335_;
}
else
{
lean_object* v_p_1336_; lean_object* v_m_1337_; lean_object* v_p_1338_; lean_object* v_m_1339_; lean_object* v___x_1340_; 
lean_dec(v_h__3_1326_);
v_p_1336_ = lean_ctor_get(v_m_u2081_1322_, 0);
lean_inc_ref(v_p_1336_);
v_m_1337_ = lean_ctor_get(v_m_u2081_1322_, 1);
lean_inc(v_m_1337_);
lean_dec_ref_known(v_m_u2081_1322_, 2);
v_p_1338_ = lean_ctor_get(v_m_u2082_1323_, 0);
lean_inc_ref(v_p_1338_);
v_m_1339_ = lean_ctor_get(v_m_u2082_1323_, 1);
lean_inc(v_m_1339_);
lean_dec_ref_known(v_m_u2082_1323_, 2);
v___x_1340_ = lean_apply_4(v_h__4_1327_, v_p_1336_, v_m_1337_, v_p_1338_, v_m_1339_);
return v___x_1340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_revlexWF_match__1_splitter(lean_object* v_motive_1341_, lean_object* v_m_u2081_1342_, lean_object* v_m_u2082_1343_, lean_object* v_h__1_1344_, lean_object* v_h__2_1345_, lean_object* v_h__3_1346_, lean_object* v_h__4_1347_){
_start:
{
if (lean_obj_tag(v_m_u2081_1342_) == 0)
{
lean_dec(v_h__4_1347_);
lean_dec(v_h__3_1346_);
if (lean_obj_tag(v_m_u2082_1343_) == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec(v_h__2_1345_);
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_apply_1(v_h__1_1344_, v___x_1348_);
return v___x_1349_;
}
else
{
lean_object* v_p_1350_; lean_object* v_m_1351_; lean_object* v___x_1352_; 
lean_dec(v_h__1_1344_);
v_p_1350_ = lean_ctor_get(v_m_u2082_1343_, 0);
lean_inc_ref(v_p_1350_);
v_m_1351_ = lean_ctor_get(v_m_u2082_1343_, 1);
lean_inc(v_m_1351_);
lean_dec_ref_known(v_m_u2082_1343_, 2);
v___x_1352_ = lean_apply_2(v_h__2_1345_, v_p_1350_, v_m_1351_);
return v___x_1352_;
}
}
else
{
lean_dec(v_h__2_1345_);
lean_dec(v_h__1_1344_);
if (lean_obj_tag(v_m_u2082_1343_) == 0)
{
lean_object* v_p_1353_; lean_object* v_m_1354_; lean_object* v___x_1355_; 
lean_dec(v_h__4_1347_);
v_p_1353_ = lean_ctor_get(v_m_u2081_1342_, 0);
lean_inc_ref(v_p_1353_);
v_m_1354_ = lean_ctor_get(v_m_u2081_1342_, 1);
lean_inc(v_m_1354_);
lean_dec_ref_known(v_m_u2081_1342_, 2);
v___x_1355_ = lean_apply_2(v_h__3_1346_, v_p_1353_, v_m_1354_);
return v___x_1355_;
}
else
{
lean_object* v_p_1356_; lean_object* v_m_1357_; lean_object* v_p_1358_; lean_object* v_m_1359_; lean_object* v___x_1360_; 
lean_dec(v_h__3_1346_);
v_p_1356_ = lean_ctor_get(v_m_u2081_1342_, 0);
lean_inc_ref(v_p_1356_);
v_m_1357_ = lean_ctor_get(v_m_u2081_1342_, 1);
lean_inc(v_m_1357_);
lean_dec_ref_known(v_m_u2081_1342_, 2);
v_p_1358_ = lean_ctor_get(v_m_u2082_1343_, 0);
lean_inc_ref(v_p_1358_);
v_m_1359_ = lean_ctor_get(v_m_u2082_1343_, 1);
lean_inc(v_m_1359_);
lean_dec_ref_known(v_m_u2082_1343_, 2);
v___x_1360_ = lean_apply_4(v_h__4_1347_, v_p_1356_, v_m_1357_, v_p_1358_, v_m_1359_);
return v___x_1360_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlexFuel(lean_object* v_fuel_1361_, lean_object* v_m_u2081_1362_, lean_object* v_m_u2082_1363_){
_start:
{
lean_object* v_zero_1364_; uint8_t v_isZero_1365_; 
v_zero_1364_ = lean_unsigned_to_nat(0u);
v_isZero_1365_ = lean_nat_dec_eq(v_fuel_1361_, v_zero_1364_);
if (v_isZero_1365_ == 1)
{
uint8_t v___x_1366_; 
v___x_1366_ = l_Lean_Grind_CommRing_Mon_revlexWF(v_m_u2081_1362_, v_m_u2082_1363_);
return v___x_1366_;
}
else
{
if (lean_obj_tag(v_m_u2081_1362_) == 0)
{
if (lean_obj_tag(v_m_u2082_1363_) == 0)
{
uint8_t v___x_1367_; 
v___x_1367_ = 1;
return v___x_1367_;
}
else
{
uint8_t v___x_1368_; 
v___x_1368_ = 2;
return v___x_1368_;
}
}
else
{
if (lean_obj_tag(v_m_u2082_1363_) == 0)
{
uint8_t v___x_1369_; 
v___x_1369_ = 0;
return v___x_1369_;
}
else
{
lean_object* v_p_1370_; lean_object* v_p_1371_; lean_object* v_m_1372_; lean_object* v_m_1373_; lean_object* v_x_1374_; lean_object* v_k_1375_; lean_object* v_x_1376_; lean_object* v_k_1377_; lean_object* v_one_1378_; lean_object* v_n_1379_; uint8_t v___x_1380_; 
v_p_1370_ = lean_ctor_get(v_m_u2081_1362_, 0);
v_p_1371_ = lean_ctor_get(v_m_u2082_1363_, 0);
v_m_1372_ = lean_ctor_get(v_m_u2081_1362_, 1);
v_m_1373_ = lean_ctor_get(v_m_u2082_1363_, 1);
v_x_1374_ = lean_ctor_get(v_p_1370_, 0);
v_k_1375_ = lean_ctor_get(v_p_1370_, 1);
v_x_1376_ = lean_ctor_get(v_p_1371_, 0);
v_k_1377_ = lean_ctor_get(v_p_1371_, 1);
v_one_1378_ = lean_unsigned_to_nat(1u);
v_n_1379_ = lean_nat_sub(v_fuel_1361_, v_one_1378_);
v___x_1380_ = lean_nat_dec_eq(v_x_1374_, v_x_1376_);
if (v___x_1380_ == 0)
{
uint8_t v___x_1381_; 
v___x_1381_ = l_Nat_blt(v_x_1374_, v_x_1376_);
if (v___x_1381_ == 0)
{
uint8_t v___x_1382_; 
v___x_1382_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1379_, v_m_u2081_1362_, v_m_1373_);
lean_dec(v_n_1379_);
if (v___x_1382_ == 1)
{
uint8_t v___x_1383_; 
v___x_1383_ = 2;
return v___x_1383_;
}
else
{
return v___x_1382_;
}
}
else
{
uint8_t v___x_1384_; 
v___x_1384_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1379_, v_m_1372_, v_m_u2082_1363_);
lean_dec(v_n_1379_);
if (v___x_1384_ == 1)
{
uint8_t v___x_1385_; 
v___x_1385_ = 0;
return v___x_1385_;
}
else
{
return v___x_1384_;
}
}
}
else
{
uint8_t v___x_1386_; 
v___x_1386_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_n_1379_, v_m_1372_, v_m_1373_);
lean_dec(v_n_1379_);
if (v___x_1386_ == 1)
{
uint8_t v___x_1387_; 
v___x_1387_ = l_Lean_Grind_CommRing_powerRevlex(v_k_1375_, v_k_1377_);
return v___x_1387_;
}
else
{
return v___x_1386_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlexFuel___boxed(lean_object* v_fuel_1388_, lean_object* v_m_u2081_1389_, lean_object* v_m_u2082_1390_){
_start:
{
uint8_t v_res_1391_; lean_object* v_r_1392_; 
v_res_1391_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v_fuel_1388_, v_m_u2081_1389_, v_m_u2082_1390_);
lean_dec(v_m_u2082_1390_);
lean_dec(v_m_u2081_1389_);
lean_dec(v_fuel_1388_);
v_r_1392_ = lean_box(v_res_1391_);
return v_r_1392_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_revlex(lean_object* v_m_u2081_1393_, lean_object* v_m_u2082_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1395_ = l_Lean_Grind_CommRing_Mon_length(v_m_u2081_1393_);
v___x_1396_ = l_Lean_Grind_CommRing_Mon_length(v_m_u2082_1394_);
v___x_1397_ = lean_nat_add(v___x_1395_, v___x_1396_);
lean_dec(v___x_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_unsigned_to_nat(1u);
v___x_1399_ = lean_nat_add(v___x_1397_, v___x_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = l_Lean_Grind_CommRing_Mon_revlexFuel(v___x_1399_, v_m_u2081_1393_, v_m_u2082_1394_);
lean_dec(v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_revlex___boxed(lean_object* v_m_u2081_1401_, lean_object* v_m_u2082_1402_){
_start:
{
uint8_t v_res_1403_; lean_object* v_r_1404_; 
v_res_1403_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1401_, v_m_u2082_1402_);
lean_dec(v_m_u2082_1402_);
lean_dec(v_m_u2081_1401_);
v_r_1404_ = lean_box(v_res_1403_);
return v_r_1404_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object* v_m_u2081_1405_, lean_object* v_m_u2082_1406_){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1407_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2081_1405_);
v___x_1408_ = l_Lean_Grind_CommRing_Mon_degree(v_m_u2082_1406_);
v___x_1409_ = lean_nat_dec_lt(v___x_1407_, v___x_1408_);
if (v___x_1409_ == 0)
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_nat_dec_eq(v___x_1407_, v___x_1408_);
lean_dec(v___x_1408_);
lean_dec(v___x_1407_);
if (v___x_1410_ == 0)
{
uint8_t v___x_1411_; 
v___x_1411_ = 2;
return v___x_1411_;
}
else
{
uint8_t v___x_1412_; 
v___x_1412_ = l_Lean_Grind_CommRing_Mon_revlex(v_m_u2081_1405_, v_m_u2082_1406_);
return v___x_1412_;
}
}
else
{
uint8_t v___x_1413_; 
lean_dec(v___x_1408_);
lean_dec(v___x_1407_);
v___x_1413_ = 0;
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_grevlex___boxed(lean_object* v_m_u2081_1414_, lean_object* v_m_u2082_1415_){
_start:
{
uint8_t v_res_1416_; lean_object* v_r_1417_; 
v_res_1416_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_u2081_1414_, v_m_u2082_1415_);
lean_dec(v_m_u2082_1415_);
lean_dec(v_m_u2081_1414_);
v_r_1417_ = lean_box(v_res_1416_);
return v_r_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___impl(lean_object* v_x_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_obj_tag_nat(v_x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorIdx___impl___boxed(lean_object* v_x_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_Grind_CommRing_Poly_ctorIdx___impl(v_x_1420_);
lean_dec_ref(v_x_1420_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___redArg(lean_object* v_t_1422_, lean_object* v_k_1423_){
_start:
{
if (lean_obj_tag(v_t_1422_) == 0)
{
lean_object* v_k_1424_; lean_object* v___x_1425_; 
v_k_1424_ = lean_ctor_get(v_t_1422_, 0);
lean_inc(v_k_1424_);
lean_dec_ref_known(v_t_1422_, 1);
v___x_1425_ = lean_apply_1(v_k_1423_, v_k_1424_);
return v___x_1425_;
}
else
{
lean_object* v_k_1426_; lean_object* v_v_1427_; lean_object* v_p_1428_; lean_object* v___x_1429_; 
v_k_1426_ = lean_ctor_get(v_t_1422_, 0);
lean_inc(v_k_1426_);
v_v_1427_ = lean_ctor_get(v_t_1422_, 1);
lean_inc(v_v_1427_);
v_p_1428_ = lean_ctor_get(v_t_1422_, 2);
lean_inc_ref(v_p_1428_);
lean_dec_ref_known(v_t_1422_, 3);
v___x_1429_ = lean_apply_3(v_k_1423_, v_k_1426_, v_v_1427_, v_p_1428_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim(lean_object* v_motive_1430_, lean_object* v_ctorIdx_1431_, lean_object* v_t_1432_, lean_object* v_h_1433_, lean_object* v_k_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1432_, v_k_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ctorElim___boxed(lean_object* v_motive_1436_, lean_object* v_ctorIdx_1437_, lean_object* v_t_1438_, lean_object* v_h_1439_, lean_object* v_k_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_Grind_CommRing_Poly_ctorElim(v_motive_1436_, v_ctorIdx_1437_, v_t_1438_, v_h_1439_, v_k_1440_);
lean_dec(v_ctorIdx_1437_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim___redArg(lean_object* v_t_1442_, lean_object* v_num_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1442_, v_num_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_num_elim(lean_object* v_motive_1445_, lean_object* v_t_1446_, lean_object* v_h_1447_, lean_object* v_num_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1446_, v_num_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim___redArg(lean_object* v_t_1450_, lean_object* v_add_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1450_, v_add_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_add_elim(lean_object* v_motive_1453_, lean_object* v_t_1454_, lean_object* v_h_1455_, lean_object* v_add_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_Grind_CommRing_Poly_ctorElim___redArg(v_t_1454_, v_add_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_instBEqPoly_beq(lean_object* v_x_1458_, lean_object* v_x_1459_){
_start:
{
if (lean_obj_tag(v_x_1458_) == 0)
{
if (lean_obj_tag(v_x_1459_) == 0)
{
lean_object* v_k_1460_; lean_object* v_k_1461_; uint8_t v___x_1462_; 
v_k_1460_ = lean_ctor_get(v_x_1458_, 0);
v_k_1461_ = lean_ctor_get(v_x_1459_, 0);
v___x_1462_ = lean_int_dec_eq(v_k_1460_, v_k_1461_);
return v___x_1462_;
}
else
{
uint8_t v___x_1463_; 
v___x_1463_ = 0;
return v___x_1463_;
}
}
else
{
if (lean_obj_tag(v_x_1459_) == 1)
{
lean_object* v_k_1464_; lean_object* v_v_1465_; lean_object* v_p_1466_; lean_object* v_k_1467_; lean_object* v_v_1468_; lean_object* v_p_1469_; uint8_t v___x_1470_; 
v_k_1464_ = lean_ctor_get(v_x_1458_, 0);
v_v_1465_ = lean_ctor_get(v_x_1458_, 1);
v_p_1466_ = lean_ctor_get(v_x_1458_, 2);
v_k_1467_ = lean_ctor_get(v_x_1459_, 0);
v_v_1468_ = lean_ctor_get(v_x_1459_, 1);
v_p_1469_ = lean_ctor_get(v_x_1459_, 2);
v___x_1470_ = lean_int_dec_eq(v_k_1464_, v_k_1467_);
if (v___x_1470_ == 0)
{
return v___x_1470_;
}
else
{
uint8_t v___x_1471_; 
v___x_1471_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_v_1465_, v_v_1468_);
if (v___x_1471_ == 0)
{
return v___x_1471_;
}
else
{
v_x_1458_ = v_p_1466_;
v_x_1459_ = v_p_1469_;
goto _start;
}
}
}
else
{
uint8_t v___x_1473_; 
v___x_1473_ = 0;
return v___x_1473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instBEqPoly_beq___boxed(lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
uint8_t v_res_1476_; lean_object* v_r_1477_; 
v_res_1476_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v_x_1474_, v_x_1475_);
lean_dec_ref(v_x_1475_);
lean_dec_ref(v_x_1474_);
v_r_1477_ = lean_box(v_res_1476_);
return v_r_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter___redArg(lean_object* v_x_1480_, lean_object* v_x_1481_, lean_object* v_h__1_1482_, lean_object* v_h__2_1483_, lean_object* v_h__3_1484_){
_start:
{
if (lean_obj_tag(v_x_1480_) == 0)
{
lean_dec(v_h__2_1483_);
if (lean_obj_tag(v_x_1481_) == 0)
{
lean_object* v_k_1485_; lean_object* v_k_1486_; lean_object* v___x_1487_; 
lean_dec(v_h__3_1484_);
v_k_1485_ = lean_ctor_get(v_x_1480_, 0);
lean_inc(v_k_1485_);
lean_dec_ref_known(v_x_1480_, 1);
v_k_1486_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_k_1486_);
lean_dec_ref_known(v_x_1481_, 1);
v___x_1487_ = lean_apply_2(v_h__1_1482_, v_k_1485_, v_k_1486_);
return v___x_1487_;
}
else
{
lean_object* v___x_1488_; 
lean_dec(v_h__1_1482_);
v___x_1488_ = lean_apply_4(v_h__3_1484_, v_x_1480_, v_x_1481_, lean_box(0), lean_box(0));
return v___x_1488_;
}
}
else
{
lean_dec(v_h__1_1482_);
if (lean_obj_tag(v_x_1481_) == 1)
{
lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v_p_1491_; lean_object* v_k_1492_; lean_object* v_v_1493_; lean_object* v_p_1494_; lean_object* v___x_1495_; 
lean_dec(v_h__3_1484_);
v_k_1489_ = lean_ctor_get(v_x_1480_, 0);
lean_inc(v_k_1489_);
v_v_1490_ = lean_ctor_get(v_x_1480_, 1);
lean_inc(v_v_1490_);
v_p_1491_ = lean_ctor_get(v_x_1480_, 2);
lean_inc_ref(v_p_1491_);
lean_dec_ref_known(v_x_1480_, 3);
v_k_1492_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_k_1492_);
v_v_1493_ = lean_ctor_get(v_x_1481_, 1);
lean_inc(v_v_1493_);
v_p_1494_ = lean_ctor_get(v_x_1481_, 2);
lean_inc_ref(v_p_1494_);
lean_dec_ref_known(v_x_1481_, 3);
v___x_1495_ = lean_apply_6(v_h__2_1483_, v_k_1489_, v_v_1490_, v_p_1491_, v_k_1492_, v_v_1493_, v_p_1494_);
return v___x_1495_;
}
else
{
lean_object* v___x_1496_; 
lean_dec(v_h__2_1483_);
v___x_1496_ = lean_apply_4(v_h__3_1484_, v_x_1480_, v_x_1481_, lean_box(0), lean_box(0));
return v___x_1496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_instBEqPoly_beq_match__1_splitter(lean_object* v_motive_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_, lean_object* v_h__1_1500_, lean_object* v_h__2_1501_, lean_object* v_h__3_1502_){
_start:
{
if (lean_obj_tag(v_x_1498_) == 0)
{
lean_dec(v_h__2_1501_);
if (lean_obj_tag(v_x_1499_) == 0)
{
lean_object* v_k_1503_; lean_object* v_k_1504_; lean_object* v___x_1505_; 
lean_dec(v_h__3_1502_);
v_k_1503_ = lean_ctor_get(v_x_1498_, 0);
lean_inc(v_k_1503_);
lean_dec_ref_known(v_x_1498_, 1);
v_k_1504_ = lean_ctor_get(v_x_1499_, 0);
lean_inc(v_k_1504_);
lean_dec_ref_known(v_x_1499_, 1);
v___x_1505_ = lean_apply_2(v_h__1_1500_, v_k_1503_, v_k_1504_);
return v___x_1505_;
}
else
{
lean_object* v___x_1506_; 
lean_dec(v_h__1_1500_);
v___x_1506_ = lean_apply_4(v_h__3_1502_, v_x_1498_, v_x_1499_, lean_box(0), lean_box(0));
return v___x_1506_;
}
}
else
{
lean_dec(v_h__1_1500_);
if (lean_obj_tag(v_x_1499_) == 1)
{
lean_object* v_k_1507_; lean_object* v_v_1508_; lean_object* v_p_1509_; lean_object* v_k_1510_; lean_object* v_v_1511_; lean_object* v_p_1512_; lean_object* v___x_1513_; 
lean_dec(v_h__3_1502_);
v_k_1507_ = lean_ctor_get(v_x_1498_, 0);
lean_inc(v_k_1507_);
v_v_1508_ = lean_ctor_get(v_x_1498_, 1);
lean_inc(v_v_1508_);
v_p_1509_ = lean_ctor_get(v_x_1498_, 2);
lean_inc_ref(v_p_1509_);
lean_dec_ref_known(v_x_1498_, 3);
v_k_1510_ = lean_ctor_get(v_x_1499_, 0);
lean_inc(v_k_1510_);
v_v_1511_ = lean_ctor_get(v_x_1499_, 1);
lean_inc(v_v_1511_);
v_p_1512_ = lean_ctor_get(v_x_1499_, 2);
lean_inc_ref(v_p_1512_);
lean_dec_ref_known(v_x_1499_, 3);
v___x_1513_ = lean_apply_6(v_h__2_1501_, v_k_1507_, v_v_1508_, v_p_1509_, v_k_1510_, v_v_1511_, v_p_1512_);
return v___x_1513_;
}
else
{
lean_object* v___x_1514_; 
lean_dec(v_h__2_1501_);
v___x_1514_ = lean_apply_4(v_h__3_1502_, v_x_1498_, v_x_1499_, lean_box(0), lean_box(0));
return v___x_1514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr(lean_object* v_x_1527_, lean_object* v_prec_1528_){
_start:
{
lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; 
if (lean_obj_tag(v_x_1527_) == 0)
{
lean_object* v_k_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1561_; 
v_k_1538_ = lean_ctor_get(v_x_1527_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_x_1527_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1540_ = v_x_1527_;
v_isShared_1541_ = v_isSharedCheck_1561_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_k_1538_);
lean_dec(v_x_1527_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1561_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___y_1543_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = lean_unsigned_to_nat(1024u);
v___x_1558_ = lean_nat_dec_le(v___x_1557_, v_prec_1528_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1543_ = v___x_1559_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1543_ = v___x_1560_;
goto v___jp_1542_;
}
v___jp_1542_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1544_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__2));
v___x_1545_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1546_ = lean_int_dec_lt(v_k_1538_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1547_ = l_Int_repr(v_k_1538_);
lean_dec(v_k_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 3);
lean_ctor_set(v___x_1540_, 0, v___x_1547_);
v___x_1549_ = v___x_1540_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
v___y_1530_ = v___x_1544_;
v___y_1531_ = v___y_1543_;
v___y_1532_ = v___x_1549_;
goto v___jp_1529_;
}
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1551_ = lean_unsigned_to_nat(1024u);
v___x_1552_ = l_Int_repr(v_k_1538_);
lean_dec(v_k_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 3);
lean_ctor_set(v___x_1540_, 0, v___x_1552_);
v___x_1554_ = v___x_1540_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Repr_addAppParen(v___x_1554_, v___x_1551_);
v___y_1530_ = v___x_1544_;
v___y_1531_ = v___y_1543_;
v___y_1532_ = v___x_1555_;
goto v___jp_1529_;
}
}
}
}
}
else
{
lean_object* v_k_1562_; lean_object* v_v_1563_; lean_object* v_p_1564_; lean_object* v___x_1565_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1583_; uint8_t v___x_1593_; 
v_k_1562_ = lean_ctor_get(v_x_1527_, 0);
lean_inc(v_k_1562_);
v_v_1563_ = lean_ctor_get(v_x_1527_, 1);
lean_inc(v_v_1563_);
v_p_1564_ = lean_ctor_get(v_x_1527_, 2);
lean_inc_ref(v_p_1564_);
lean_dec_ref_known(v_x_1527_, 3);
v___x_1565_ = lean_unsigned_to_nat(1024u);
v___x_1593_ = lean_nat_dec_le(v___x_1565_, v_prec_1528_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__3, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__3_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__3);
v___y_1583_ = v___x_1594_;
goto v___jp_1582_;
}
else
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___y_1583_ = v___x_1595_;
goto v___jp_1582_;
}
v___jp_1566_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_inc(v___y_1567_);
v___x_1571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___y_1567_);
lean_ctor_set(v___x_1571_, 1, v___y_1570_);
lean_inc_n(v___y_1569_, 2);
v___x_1572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v___y_1569_);
v___x_1573_ = l_Lean_Grind_CommRing_instReprMon_repr(v_v_1563_, v___x_1565_);
v___x_1574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v___y_1569_);
v___x_1576_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_p_1564_, v___x_1565_);
v___x_1577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
lean_inc(v___y_1568_);
v___x_1578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___y_1568_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = 0;
v___x_1580_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*1, v___x_1579_);
v___x_1581_ = l_Repr_addAppParen(v___x_1580_, v_prec_1528_);
return v___x_1581_;
}
v___jp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1584_ = lean_box(1);
v___x_1585_ = ((lean_object*)(l_Lean_Grind_CommRing_instReprPoly_repr___closed__5));
v___x_1586_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1587_ = lean_int_dec_lt(v_k_1562_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = l_Int_repr(v_k_1562_);
lean_dec(v_k_1562_);
v___x_1589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
v___y_1567_ = v___x_1585_;
v___y_1568_ = v___y_1583_;
v___y_1569_ = v___x_1584_;
v___y_1570_ = v___x_1589_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = l_Int_repr(v_k_1562_);
lean_dec(v_k_1562_);
v___x_1591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
v___x_1592_ = l_Repr_addAppParen(v___x_1591_, v___x_1565_);
v___y_1567_ = v___x_1585_;
v___y_1568_ = v___y_1583_;
v___y_1569_ = v___x_1584_;
v___y_1570_ = v___x_1592_;
goto v___jp_1566_;
}
}
}
v___jp_1529_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_inc(v___y_1530_);
v___x_1533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___y_1530_);
lean_ctor_set(v___x_1533_, 1, v___y_1532_);
lean_inc(v___y_1531_);
v___x_1534_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___y_1531_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = 0;
v___x_1536_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*1, v___x_1535_);
v___x_1537_ = l_Repr_addAppParen(v___x_1536_, v_prec_1528_);
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instReprPoly_repr___boxed(lean_object* v_x_1596_, lean_object* v_prec_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Grind_CommRing_instReprPoly_repr(v_x_1596_, v_prec_1597_);
lean_dec(v_prec_1597_);
return v_res_1598_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly_default(void){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_1603_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_instInhabitedPoly(void){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
return v___x_1604_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_CommRing_instHashablePoly_hash(lean_object* v_x_1605_){
_start:
{
if (lean_obj_tag(v_x_1605_) == 0)
{
lean_object* v_k_1606_; uint64_t v___x_1607_; lean_object* v_intZero_1608_; uint8_t v_isNeg_1609_; 
v_k_1606_ = lean_ctor_get(v_x_1605_, 0);
v___x_1607_ = 0ULL;
v_intZero_1608_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1609_ = lean_int_dec_lt(v_k_1606_, v_intZero_1608_);
if (v_isNeg_1609_ == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint64_t v___x_1613_; uint64_t v___x_1614_; 
v_a_1610_ = lean_nat_abs(v_k_1606_);
v___x_1611_ = lean_unsigned_to_nat(2u);
v___x_1612_ = lean_nat_mul(v___x_1611_, v_a_1610_);
lean_dec(v_a_1610_);
v___x_1613_ = lean_uint64_of_nat(v___x_1612_);
lean_dec(v___x_1612_);
v___x_1614_ = lean_uint64_mix_hash(v___x_1607_, v___x_1613_);
return v___x_1614_;
}
else
{
lean_object* v_abs_1615_; lean_object* v_one_1616_; lean_object* v_a_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint64_t v___x_1621_; uint64_t v___x_1622_; 
v_abs_1615_ = lean_nat_abs(v_k_1606_);
v_one_1616_ = lean_unsigned_to_nat(1u);
v_a_1617_ = lean_nat_sub(v_abs_1615_, v_one_1616_);
lean_dec(v_abs_1615_);
v___x_1618_ = lean_unsigned_to_nat(2u);
v___x_1619_ = lean_nat_mul(v___x_1618_, v_a_1617_);
lean_dec(v_a_1617_);
v___x_1620_ = lean_nat_add(v___x_1619_, v_one_1616_);
lean_dec(v___x_1619_);
v___x_1621_ = lean_uint64_of_nat(v___x_1620_);
lean_dec(v___x_1620_);
v___x_1622_ = lean_uint64_mix_hash(v___x_1607_, v___x_1621_);
return v___x_1622_;
}
}
else
{
lean_object* v_k_1623_; lean_object* v_v_1624_; lean_object* v_p_1625_; uint64_t v___x_1626_; uint64_t v___y_1628_; lean_object* v_intZero_1634_; uint8_t v_isNeg_1635_; 
v_k_1623_ = lean_ctor_get(v_x_1605_, 0);
v_v_1624_ = lean_ctor_get(v_x_1605_, 1);
v_p_1625_ = lean_ctor_get(v_x_1605_, 2);
v___x_1626_ = 1ULL;
v_intZero_1634_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v_isNeg_1635_ = lean_int_dec_lt(v_k_1623_, v_intZero_1634_);
if (v_isNeg_1635_ == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint64_t v___x_1639_; 
v_a_1636_ = lean_nat_abs(v_k_1623_);
v___x_1637_ = lean_unsigned_to_nat(2u);
v___x_1638_ = lean_nat_mul(v___x_1637_, v_a_1636_);
lean_dec(v_a_1636_);
v___x_1639_ = lean_uint64_of_nat(v___x_1638_);
lean_dec(v___x_1638_);
v___y_1628_ = v___x_1639_;
goto v___jp_1627_;
}
else
{
lean_object* v_abs_1640_; lean_object* v_one_1641_; lean_object* v_a_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; uint64_t v___x_1646_; 
v_abs_1640_ = lean_nat_abs(v_k_1623_);
v_one_1641_ = lean_unsigned_to_nat(1u);
v_a_1642_ = lean_nat_sub(v_abs_1640_, v_one_1641_);
lean_dec(v_abs_1640_);
v___x_1643_ = lean_unsigned_to_nat(2u);
v___x_1644_ = lean_nat_mul(v___x_1643_, v_a_1642_);
lean_dec(v_a_1642_);
v___x_1645_ = lean_nat_add(v___x_1644_, v_one_1641_);
lean_dec(v___x_1644_);
v___x_1646_ = lean_uint64_of_nat(v___x_1645_);
lean_dec(v___x_1645_);
v___y_1628_ = v___x_1646_;
goto v___jp_1627_;
}
v___jp_1627_:
{
uint64_t v___x_1629_; uint64_t v___x_1630_; uint64_t v___x_1631_; uint64_t v___x_1632_; uint64_t v___x_1633_; 
v___x_1629_ = lean_uint64_mix_hash(v___x_1626_, v___y_1628_);
v___x_1630_ = l_Lean_Grind_CommRing_instHashableMon_hash(v_v_1624_);
v___x_1631_ = lean_uint64_mix_hash(v___x_1629_, v___x_1630_);
v___x_1632_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_p_1625_);
v___x_1633_ = lean_uint64_mix_hash(v___x_1631_, v___x_1632_);
return v___x_1633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_instHashablePoly_hash___boxed(lean_object* v_x_1647_){
_start:
{
uint64_t v_res_1648_; lean_object* v_r_1649_; 
v_res_1648_ = l_Lean_Grind_CommRing_instHashablePoly_hash(v_x_1647_);
lean_dec_ref(v_x_1647_);
v_r_1649_ = lean_box_uint64(v_res_1648_);
return v_r_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg(lean_object* v_inst_1652_, lean_object* v_ctx_1653_, lean_object* v_p_1654_){
_start:
{
lean_object* v_toSemiring_1655_; lean_object* v_intCast_1656_; lean_object* v_toAdd_1657_; lean_object* v___x_1658_; 
v_toSemiring_1655_ = lean_ctor_get(v_inst_1652_, 0);
v_intCast_1656_ = lean_ctor_get(v_inst_1652_, 3);
v_toAdd_1657_ = lean_ctor_get(v_toSemiring_1655_, 0);
lean_inc(v_toAdd_1657_);
lean_inc_ref(v_inst_1652_);
v___x_1658_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1652_);
if (lean_obj_tag(v_p_1654_) == 0)
{
lean_object* v_k_1659_; lean_object* v___x_1660_; 
lean_inc(v_intCast_1656_);
lean_dec_ref(v___x_1658_);
lean_dec(v_toAdd_1657_);
lean_dec_ref(v_inst_1652_);
v_k_1659_ = lean_ctor_get(v_p_1654_, 0);
lean_inc(v_k_1659_);
lean_dec_ref_known(v_p_1654_, 1);
v___x_1660_ = lean_apply_1(v_intCast_1656_, v_k_1659_);
return v___x_1660_;
}
else
{
lean_object* v_zsmul_1661_; lean_object* v_k_1662_; lean_object* v_v_1663_; lean_object* v_p_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_zsmul_1661_ = lean_ctor_get(v___x_1658_, 2);
lean_inc(v_zsmul_1661_);
lean_dec_ref(v___x_1658_);
v_k_1662_ = lean_ctor_get(v_p_1654_, 0);
lean_inc(v_k_1662_);
v_v_1663_ = lean_ctor_get(v_p_1654_, 1);
lean_inc(v_v_1663_);
v_p_1664_ = lean_ctor_get(v_p_1654_, 2);
lean_inc_ref(v_p_1664_);
lean_dec_ref_known(v_p_1654_, 3);
lean_inc_ref(v_toSemiring_1655_);
v___x_1665_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_toSemiring_1655_, v_ctx_1653_, v_v_1663_);
v___x_1666_ = lean_apply_2(v_zsmul_1661_, v_k_1662_, v___x_1665_);
v___x_1667_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1652_, v_ctx_1653_, v_p_1664_);
v___x_1668_ = lean_apply_2(v_toAdd_1657_, v___x_1666_, v___x_1667_);
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___redArg___boxed(lean_object* v_inst_1669_, lean_object* v_ctx_1670_, lean_object* v_p_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1669_, v_ctx_1670_, v_p_1671_);
lean_dec_ref(v_ctx_1670_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote(lean_object* v_00_u03b1_1673_, lean_object* v_inst_1674_, lean_object* v_ctx_1675_, lean_object* v_p_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_1674_, v_ctx_1675_, v_p_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote___boxed(lean_object* v_00_u03b1_1678_, lean_object* v_inst_1679_, lean_object* v_ctx_1680_, lean_object* v_p_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Grind_CommRing_Poly_denote(v_00_u03b1_1678_, v_inst_1679_, v_ctx_1680_, v_p_1681_);
lean_dec_ref(v_ctx_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg(lean_object* v_inst_1683_, lean_object* v_ctx_1684_, lean_object* v_k_1685_, lean_object* v_m_1686_){
_start:
{
lean_object* v_toSemiring_1687_; lean_object* v___x_1688_; lean_object* v_zsmul_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v_toSemiring_1687_ = lean_ctor_get(v_inst_1683_, 0);
lean_inc_ref(v_toSemiring_1687_);
v___x_1688_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1683_);
v_zsmul_1689_ = lean_ctor_get(v___x_1688_, 2);
lean_inc(v_zsmul_1689_);
lean_dec_ref(v___x_1688_);
v___x_1690_ = lean_unsigned_to_nat(1u);
v___x_1691_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1692_ = lean_int_dec_eq(v_k_1685_, v___x_1691_);
if (v___x_1692_ == 0)
{
if (lean_obj_tag(v_m_1686_) == 0)
{
lean_object* v_ofNat_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_ofNat_1693_ = lean_ctor_get(v_toSemiring_1687_, 3);
lean_inc(v_ofNat_1693_);
lean_dec_ref(v_toSemiring_1687_);
v___x_1694_ = lean_apply_1(v_ofNat_1693_, v___x_1690_);
v___x_1695_ = lean_apply_2(v_zsmul_1689_, v_k_1685_, v___x_1694_);
return v___x_1695_;
}
else
{
lean_object* v_p_1696_; lean_object* v_m_1697_; lean_object* v_ofNat_1698_; lean_object* v_npow_1699_; lean_object* v_x_1700_; lean_object* v_k_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v_p_1696_ = lean_ctor_get(v_m_1686_, 0);
lean_inc_ref(v_p_1696_);
v_m_1697_ = lean_ctor_get(v_m_1686_, 1);
lean_inc(v_m_1697_);
lean_dec_ref_known(v_m_1686_, 2);
v_ofNat_1698_ = lean_ctor_get(v_toSemiring_1687_, 3);
v_npow_1699_ = lean_ctor_get(v_toSemiring_1687_, 5);
v_x_1700_ = lean_ctor_get(v_p_1696_, 0);
lean_inc(v_x_1700_);
v_k_1701_ = lean_ctor_get(v_p_1696_, 1);
lean_inc(v_k_1701_);
lean_dec_ref(v_p_1696_);
v___x_1702_ = lean_unsigned_to_nat(0u);
v___x_1703_ = lean_nat_dec_eq(v_k_1701_, v___x_1702_);
if (v___x_1703_ == 0)
{
uint8_t v___x_1704_; 
v___x_1704_ = lean_nat_dec_eq(v_k_1701_, v___x_1690_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1705_ = l_Lean_RArray_getImpl___redArg(v_ctx_1684_, v_x_1700_);
lean_dec(v_x_1700_);
lean_inc(v_npow_1699_);
v___x_1706_ = lean_apply_2(v_npow_1699_, v___x_1705_, v_k_1701_);
v___x_1707_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1687_, v_ctx_1684_, v_m_1697_, v___x_1706_);
v___x_1708_ = lean_apply_2(v_zsmul_1689_, v_k_1685_, v___x_1707_);
return v___x_1708_;
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_dec(v_k_1701_);
v___x_1709_ = l_Lean_RArray_getImpl___redArg(v_ctx_1684_, v_x_1700_);
lean_dec(v_x_1700_);
v___x_1710_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1687_, v_ctx_1684_, v_m_1697_, v___x_1709_);
v___x_1711_ = lean_apply_2(v_zsmul_1689_, v_k_1685_, v___x_1710_);
return v___x_1711_;
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec(v_k_1701_);
lean_dec(v_x_1700_);
lean_inc(v_ofNat_1698_);
v___x_1712_ = lean_apply_1(v_ofNat_1698_, v___x_1690_);
v___x_1713_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1687_, v_ctx_1684_, v_m_1697_, v___x_1712_);
v___x_1714_ = lean_apply_2(v_zsmul_1689_, v_k_1685_, v___x_1713_);
return v___x_1714_;
}
}
}
else
{
lean_dec(v_zsmul_1689_);
lean_dec(v_k_1685_);
if (lean_obj_tag(v_m_1686_) == 0)
{
lean_object* v_ofNat_1715_; lean_object* v___x_1716_; 
v_ofNat_1715_ = lean_ctor_get(v_toSemiring_1687_, 3);
lean_inc(v_ofNat_1715_);
lean_dec_ref(v_toSemiring_1687_);
v___x_1716_ = lean_apply_1(v_ofNat_1715_, v___x_1690_);
return v___x_1716_;
}
else
{
lean_object* v_p_1717_; lean_object* v_m_1718_; lean_object* v_ofNat_1719_; lean_object* v_npow_1720_; lean_object* v_x_1721_; lean_object* v_k_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; 
v_p_1717_ = lean_ctor_get(v_m_1686_, 0);
lean_inc_ref(v_p_1717_);
v_m_1718_ = lean_ctor_get(v_m_1686_, 1);
lean_inc(v_m_1718_);
lean_dec_ref_known(v_m_1686_, 2);
v_ofNat_1719_ = lean_ctor_get(v_toSemiring_1687_, 3);
v_npow_1720_ = lean_ctor_get(v_toSemiring_1687_, 5);
v_x_1721_ = lean_ctor_get(v_p_1717_, 0);
lean_inc(v_x_1721_);
v_k_1722_ = lean_ctor_get(v_p_1717_, 1);
lean_inc(v_k_1722_);
lean_dec_ref(v_p_1717_);
v___x_1723_ = lean_unsigned_to_nat(0u);
v___x_1724_ = lean_nat_dec_eq(v_k_1722_, v___x_1723_);
if (v___x_1724_ == 0)
{
uint8_t v___x_1725_; 
v___x_1725_ = lean_nat_dec_eq(v_k_1722_, v___x_1690_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = l_Lean_RArray_getImpl___redArg(v_ctx_1684_, v_x_1721_);
lean_dec(v_x_1721_);
lean_inc(v_npow_1720_);
v___x_1727_ = lean_apply_2(v_npow_1720_, v___x_1726_, v_k_1722_);
v___x_1728_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1687_, v_ctx_1684_, v_m_1718_, v___x_1727_);
return v___x_1728_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v_k_1722_);
v___x_1729_ = l_Lean_RArray_getImpl___redArg(v_ctx_1684_, v_x_1721_);
lean_dec(v_x_1721_);
v___x_1730_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1687_, v_ctx_1684_, v_m_1718_, v___x_1729_);
return v___x_1730_;
}
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec(v_k_1722_);
lean_dec(v_x_1721_);
lean_inc(v_ofNat_1719_);
v___x_1731_ = lean_apply_1(v_ofNat_1719_, v___x_1690_);
v___x_1732_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1687_, v_ctx_1684_, v_m_1718_, v___x_1731_);
return v___x_1732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___redArg___boxed(lean_object* v_inst_1733_, lean_object* v_ctx_1734_, lean_object* v_k_1735_, lean_object* v_m_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_Grind_CommRing_denoteTerm___redArg(v_inst_1733_, v_ctx_1734_, v_k_1735_, v_m_1736_);
lean_dec_ref(v_ctx_1734_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm(lean_object* v_00_u03b1_1738_, lean_object* v_inst_1739_, lean_object* v_ctx_1740_, lean_object* v_k_1741_, lean_object* v_m_1742_){
_start:
{
lean_object* v_toSemiring_1743_; lean_object* v___x_1744_; lean_object* v_zsmul_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_toSemiring_1743_ = lean_ctor_get(v_inst_1739_, 0);
lean_inc_ref(v_toSemiring_1743_);
v___x_1744_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1739_);
v_zsmul_1745_ = lean_ctor_get(v___x_1744_, 2);
lean_inc(v_zsmul_1745_);
lean_dec_ref(v___x_1744_);
v___x_1746_ = lean_unsigned_to_nat(1u);
v___x_1747_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1748_ = lean_int_dec_eq(v_k_1741_, v___x_1747_);
if (v___x_1748_ == 0)
{
if (lean_obj_tag(v_m_1742_) == 0)
{
lean_object* v_ofNat_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_ofNat_1749_ = lean_ctor_get(v_toSemiring_1743_, 3);
lean_inc(v_ofNat_1749_);
lean_dec_ref(v_toSemiring_1743_);
v___x_1750_ = lean_apply_1(v_ofNat_1749_, v___x_1746_);
v___x_1751_ = lean_apply_2(v_zsmul_1745_, v_k_1741_, v___x_1750_);
return v___x_1751_;
}
else
{
lean_object* v_p_1752_; lean_object* v_m_1753_; lean_object* v_ofNat_1754_; lean_object* v_npow_1755_; lean_object* v_x_1756_; lean_object* v_k_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v_p_1752_ = lean_ctor_get(v_m_1742_, 0);
lean_inc_ref(v_p_1752_);
v_m_1753_ = lean_ctor_get(v_m_1742_, 1);
lean_inc(v_m_1753_);
lean_dec_ref_known(v_m_1742_, 2);
v_ofNat_1754_ = lean_ctor_get(v_toSemiring_1743_, 3);
v_npow_1755_ = lean_ctor_get(v_toSemiring_1743_, 5);
v_x_1756_ = lean_ctor_get(v_p_1752_, 0);
lean_inc(v_x_1756_);
v_k_1757_ = lean_ctor_get(v_p_1752_, 1);
lean_inc(v_k_1757_);
lean_dec_ref(v_p_1752_);
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = lean_nat_dec_eq(v_k_1757_, v___x_1758_);
if (v___x_1759_ == 0)
{
uint8_t v___x_1760_; 
v___x_1760_ = lean_nat_dec_eq(v_k_1757_, v___x_1746_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1761_ = l_Lean_RArray_getImpl___redArg(v_ctx_1740_, v_x_1756_);
lean_dec(v_x_1756_);
lean_inc(v_npow_1755_);
v___x_1762_ = lean_apply_2(v_npow_1755_, v___x_1761_, v_k_1757_);
v___x_1763_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1743_, v_ctx_1740_, v_m_1753_, v___x_1762_);
v___x_1764_ = lean_apply_2(v_zsmul_1745_, v_k_1741_, v___x_1763_);
return v___x_1764_;
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec(v_k_1757_);
v___x_1765_ = l_Lean_RArray_getImpl___redArg(v_ctx_1740_, v_x_1756_);
lean_dec(v_x_1756_);
v___x_1766_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1743_, v_ctx_1740_, v_m_1753_, v___x_1765_);
v___x_1767_ = lean_apply_2(v_zsmul_1745_, v_k_1741_, v___x_1766_);
return v___x_1767_;
}
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec(v_k_1757_);
lean_dec(v_x_1756_);
lean_inc(v_ofNat_1754_);
v___x_1768_ = lean_apply_1(v_ofNat_1754_, v___x_1746_);
v___x_1769_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1743_, v_ctx_1740_, v_m_1753_, v___x_1768_);
v___x_1770_ = lean_apply_2(v_zsmul_1745_, v_k_1741_, v___x_1769_);
return v___x_1770_;
}
}
}
else
{
lean_dec(v_zsmul_1745_);
lean_dec(v_k_1741_);
if (lean_obj_tag(v_m_1742_) == 0)
{
lean_object* v_ofNat_1771_; lean_object* v___x_1772_; 
v_ofNat_1771_ = lean_ctor_get(v_toSemiring_1743_, 3);
lean_inc(v_ofNat_1771_);
lean_dec_ref(v_toSemiring_1743_);
v___x_1772_ = lean_apply_1(v_ofNat_1771_, v___x_1746_);
return v___x_1772_;
}
else
{
lean_object* v_p_1773_; lean_object* v_m_1774_; lean_object* v_ofNat_1775_; lean_object* v_npow_1776_; lean_object* v_x_1777_; lean_object* v_k_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v_p_1773_ = lean_ctor_get(v_m_1742_, 0);
lean_inc_ref(v_p_1773_);
v_m_1774_ = lean_ctor_get(v_m_1742_, 1);
lean_inc(v_m_1774_);
lean_dec_ref_known(v_m_1742_, 2);
v_ofNat_1775_ = lean_ctor_get(v_toSemiring_1743_, 3);
v_npow_1776_ = lean_ctor_get(v_toSemiring_1743_, 5);
v_x_1777_ = lean_ctor_get(v_p_1773_, 0);
lean_inc(v_x_1777_);
v_k_1778_ = lean_ctor_get(v_p_1773_, 1);
lean_inc(v_k_1778_);
lean_dec_ref(v_p_1773_);
v___x_1779_ = lean_unsigned_to_nat(0u);
v___x_1780_ = lean_nat_dec_eq(v_k_1778_, v___x_1779_);
if (v___x_1780_ == 0)
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_nat_dec_eq(v_k_1778_, v___x_1746_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = l_Lean_RArray_getImpl___redArg(v_ctx_1740_, v_x_1777_);
lean_dec(v_x_1777_);
lean_inc(v_npow_1776_);
v___x_1783_ = lean_apply_2(v_npow_1776_, v___x_1782_, v_k_1778_);
v___x_1784_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1743_, v_ctx_1740_, v_m_1774_, v___x_1783_);
return v___x_1784_;
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_dec(v_k_1778_);
v___x_1785_ = l_Lean_RArray_getImpl___redArg(v_ctx_1740_, v_x_1777_);
lean_dec(v_x_1777_);
v___x_1786_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1743_, v_ctx_1740_, v_m_1774_, v___x_1785_);
return v___x_1786_;
}
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_dec(v_k_1778_);
lean_dec(v_x_1777_);
lean_inc(v_ofNat_1775_);
v___x_1787_ = lean_apply_1(v_ofNat_1775_, v___x_1746_);
v___x_1788_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1743_, v_ctx_1740_, v_m_1774_, v___x_1787_);
return v___x_1788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteTerm___boxed(lean_object* v_00_u03b1_1789_, lean_object* v_inst_1790_, lean_object* v_ctx_1791_, lean_object* v_k_1792_, lean_object* v_m_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_Grind_CommRing_denoteTerm(v_00_u03b1_1789_, v_inst_1790_, v_ctx_1791_, v_k_1792_, v_m_1793_);
lean_dec_ref(v_ctx_1791_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(lean_object* v_inst_1795_, lean_object* v_ctx_1796_, lean_object* v_p_1797_, lean_object* v_acc_1798_){
_start:
{
if (lean_obj_tag(v_p_1797_) == 0)
{
lean_object* v_toSemiring_1799_; lean_object* v_intCast_1800_; lean_object* v_toAdd_1801_; lean_object* v_k_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_toSemiring_1799_ = lean_ctor_get(v_inst_1795_, 0);
lean_inc_ref(v_toSemiring_1799_);
v_intCast_1800_ = lean_ctor_get(v_inst_1795_, 3);
lean_inc(v_intCast_1800_);
lean_dec_ref(v_inst_1795_);
v_toAdd_1801_ = lean_ctor_get(v_toSemiring_1799_, 0);
lean_inc(v_toAdd_1801_);
lean_dec_ref(v_toSemiring_1799_);
v_k_1802_ = lean_ctor_get(v_p_1797_, 0);
lean_inc(v_k_1802_);
lean_dec_ref_known(v_p_1797_, 1);
v___x_1803_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_1804_ = lean_int_dec_eq(v_k_1802_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = lean_apply_1(v_intCast_1800_, v_k_1802_);
v___x_1806_ = lean_apply_2(v_toAdd_1801_, v_acc_1798_, v___x_1805_);
return v___x_1806_;
}
else
{
lean_dec(v_k_1802_);
lean_dec(v_toAdd_1801_);
lean_dec(v_intCast_1800_);
return v_acc_1798_;
}
}
else
{
lean_object* v_toSemiring_1807_; lean_object* v_toAdd_1808_; lean_object* v_ofNat_1809_; lean_object* v_npow_1810_; lean_object* v_k_1811_; lean_object* v_v_1812_; lean_object* v_p_1813_; lean_object* v___y_1815_; lean_object* v___x_1818_; lean_object* v_zsmul_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v_toSemiring_1807_ = lean_ctor_get(v_inst_1795_, 0);
v_toAdd_1808_ = lean_ctor_get(v_toSemiring_1807_, 0);
v_ofNat_1809_ = lean_ctor_get(v_toSemiring_1807_, 3);
v_npow_1810_ = lean_ctor_get(v_toSemiring_1807_, 5);
v_k_1811_ = lean_ctor_get(v_p_1797_, 0);
lean_inc(v_k_1811_);
v_v_1812_ = lean_ctor_get(v_p_1797_, 1);
lean_inc(v_v_1812_);
v_p_1813_ = lean_ctor_get(v_p_1797_, 2);
lean_inc_ref(v_p_1813_);
lean_dec_ref_known(v_p_1797_, 3);
lean_inc_ref(v_inst_1795_);
v___x_1818_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1795_);
v_zsmul_1819_ = lean_ctor_get(v___x_1818_, 2);
lean_inc(v_zsmul_1819_);
lean_dec_ref(v___x_1818_);
v___x_1820_ = lean_unsigned_to_nat(1u);
v___x_1821_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1822_ = lean_int_dec_eq(v_k_1811_, v___x_1821_);
if (v___x_1822_ == 0)
{
if (lean_obj_tag(v_v_1812_) == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_inc(v_ofNat_1809_);
v___x_1823_ = lean_apply_1(v_ofNat_1809_, v___x_1820_);
v___x_1824_ = lean_apply_2(v_zsmul_1819_, v_k_1811_, v___x_1823_);
v___y_1815_ = v___x_1824_;
goto v___jp_1814_;
}
else
{
lean_object* v_p_1825_; lean_object* v_m_1826_; lean_object* v_x_1827_; lean_object* v_k_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v_p_1825_ = lean_ctor_get(v_v_1812_, 0);
lean_inc_ref(v_p_1825_);
v_m_1826_ = lean_ctor_get(v_v_1812_, 1);
lean_inc(v_m_1826_);
lean_dec_ref_known(v_v_1812_, 2);
v_x_1827_ = lean_ctor_get(v_p_1825_, 0);
lean_inc(v_x_1827_);
v_k_1828_ = lean_ctor_get(v_p_1825_, 1);
lean_inc(v_k_1828_);
lean_dec_ref(v_p_1825_);
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1830_ = lean_nat_dec_eq(v_k_1828_, v___x_1829_);
if (v___x_1830_ == 0)
{
uint8_t v___x_1831_; 
v___x_1831_ = lean_nat_dec_eq(v_k_1828_, v___x_1820_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1832_ = l_Lean_RArray_getImpl___redArg(v_ctx_1796_, v_x_1827_);
lean_dec(v_x_1827_);
lean_inc(v_npow_1810_);
v___x_1833_ = lean_apply_2(v_npow_1810_, v___x_1832_, v_k_1828_);
lean_inc_ref(v_toSemiring_1807_);
v___x_1834_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1807_, v_ctx_1796_, v_m_1826_, v___x_1833_);
v___x_1835_ = lean_apply_2(v_zsmul_1819_, v_k_1811_, v___x_1834_);
v___y_1815_ = v___x_1835_;
goto v___jp_1814_;
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec(v_k_1828_);
v___x_1836_ = l_Lean_RArray_getImpl___redArg(v_ctx_1796_, v_x_1827_);
lean_dec(v_x_1827_);
lean_inc_ref(v_toSemiring_1807_);
v___x_1837_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1807_, v_ctx_1796_, v_m_1826_, v___x_1836_);
v___x_1838_ = lean_apply_2(v_zsmul_1819_, v_k_1811_, v___x_1837_);
v___y_1815_ = v___x_1838_;
goto v___jp_1814_;
}
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec(v_k_1828_);
lean_dec(v_x_1827_);
lean_inc(v_ofNat_1809_);
v___x_1839_ = lean_apply_1(v_ofNat_1809_, v___x_1820_);
lean_inc_ref(v_toSemiring_1807_);
v___x_1840_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1807_, v_ctx_1796_, v_m_1826_, v___x_1839_);
v___x_1841_ = lean_apply_2(v_zsmul_1819_, v_k_1811_, v___x_1840_);
v___y_1815_ = v___x_1841_;
goto v___jp_1814_;
}
}
}
else
{
lean_dec(v_zsmul_1819_);
lean_dec(v_k_1811_);
if (lean_obj_tag(v_v_1812_) == 0)
{
lean_object* v___x_1842_; 
lean_inc(v_ofNat_1809_);
v___x_1842_ = lean_apply_1(v_ofNat_1809_, v___x_1820_);
v___y_1815_ = v___x_1842_;
goto v___jp_1814_;
}
else
{
lean_object* v_p_1843_; lean_object* v_m_1844_; lean_object* v_x_1845_; lean_object* v_k_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v_p_1843_ = lean_ctor_get(v_v_1812_, 0);
lean_inc_ref(v_p_1843_);
v_m_1844_ = lean_ctor_get(v_v_1812_, 1);
lean_inc(v_m_1844_);
lean_dec_ref_known(v_v_1812_, 2);
v_x_1845_ = lean_ctor_get(v_p_1843_, 0);
lean_inc(v_x_1845_);
v_k_1846_ = lean_ctor_get(v_p_1843_, 1);
lean_inc(v_k_1846_);
lean_dec_ref(v_p_1843_);
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = lean_nat_dec_eq(v_k_1846_, v___x_1847_);
if (v___x_1848_ == 0)
{
uint8_t v___x_1849_; 
v___x_1849_ = lean_nat_dec_eq(v_k_1846_, v___x_1820_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = l_Lean_RArray_getImpl___redArg(v_ctx_1796_, v_x_1845_);
lean_dec(v_x_1845_);
lean_inc(v_npow_1810_);
v___x_1851_ = lean_apply_2(v_npow_1810_, v___x_1850_, v_k_1846_);
lean_inc_ref(v_toSemiring_1807_);
v___x_1852_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1807_, v_ctx_1796_, v_m_1844_, v___x_1851_);
v___y_1815_ = v___x_1852_;
goto v___jp_1814_;
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_dec(v_k_1846_);
v___x_1853_ = l_Lean_RArray_getImpl___redArg(v_ctx_1796_, v_x_1845_);
lean_dec(v_x_1845_);
lean_inc_ref(v_toSemiring_1807_);
v___x_1854_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1807_, v_ctx_1796_, v_m_1844_, v___x_1853_);
v___y_1815_ = v___x_1854_;
goto v___jp_1814_;
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec(v_k_1846_);
lean_dec(v_x_1845_);
lean_inc(v_ofNat_1809_);
v___x_1855_ = lean_apply_1(v_ofNat_1809_, v___x_1820_);
lean_inc_ref(v_toSemiring_1807_);
v___x_1856_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1807_, v_ctx_1796_, v_m_1844_, v___x_1855_);
v___y_1815_ = v___x_1856_;
goto v___jp_1814_;
}
}
}
v___jp_1814_:
{
lean_object* v___x_1816_; 
lean_inc(v_toAdd_1808_);
v___x_1816_ = lean_apply_2(v_toAdd_1808_, v_acc_1798_, v___y_1815_);
v_p_1797_ = v_p_1813_;
v_acc_1798_ = v___x_1816_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg___boxed(lean_object* v_inst_1857_, lean_object* v_ctx_1858_, lean_object* v_p_1859_, lean_object* v_acc_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1857_, v_ctx_1858_, v_p_1859_, v_acc_1860_);
lean_dec_ref(v_ctx_1858_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go(lean_object* v_00_u03b1_1862_, lean_object* v_inst_1863_, lean_object* v_ctx_1864_, lean_object* v_p_1865_, lean_object* v_acc_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1863_, v_ctx_1864_, v_p_1865_, v_acc_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27_go___boxed(lean_object* v_00_u03b1_1868_, lean_object* v_inst_1869_, lean_object* v_ctx_1870_, lean_object* v_p_1871_, lean_object* v_acc_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Grind_CommRing_Poly_denote_x27_go(v_00_u03b1_1868_, v_inst_1869_, v_ctx_1870_, v_p_1871_, v_acc_1872_);
lean_dec_ref(v_ctx_1870_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg(lean_object* v_inst_1874_, lean_object* v_ctx_1875_, lean_object* v_p_1876_){
_start:
{
if (lean_obj_tag(v_p_1876_) == 0)
{
lean_object* v_intCast_1877_; lean_object* v_k_1878_; lean_object* v___x_1879_; 
v_intCast_1877_ = lean_ctor_get(v_inst_1874_, 3);
lean_inc(v_intCast_1877_);
lean_dec_ref(v_inst_1874_);
v_k_1878_ = lean_ctor_get(v_p_1876_, 0);
lean_inc(v_k_1878_);
lean_dec_ref_known(v_p_1876_, 1);
v___x_1879_ = lean_apply_1(v_intCast_1877_, v_k_1878_);
return v___x_1879_;
}
else
{
lean_object* v_toSemiring_1880_; lean_object* v_k_1881_; lean_object* v_v_1882_; lean_object* v_p_1883_; lean_object* v___x_1884_; lean_object* v_zsmul_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v_toSemiring_1880_ = lean_ctor_get(v_inst_1874_, 0);
v_k_1881_ = lean_ctor_get(v_p_1876_, 0);
lean_inc(v_k_1881_);
v_v_1882_ = lean_ctor_get(v_p_1876_, 1);
lean_inc(v_v_1882_);
v_p_1883_ = lean_ctor_get(v_p_1876_, 2);
lean_inc_ref(v_p_1883_);
lean_dec_ref_known(v_p_1876_, 3);
lean_inc_ref(v_inst_1874_);
v___x_1884_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1874_);
v_zsmul_1885_ = lean_ctor_get(v___x_1884_, 2);
lean_inc(v_zsmul_1885_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = lean_unsigned_to_nat(1u);
v___x_1887_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1888_ = lean_int_dec_eq(v_k_1881_, v___x_1887_);
if (v___x_1888_ == 0)
{
if (lean_obj_tag(v_v_1882_) == 0)
{
lean_object* v_ofNat_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_ofNat_1889_ = lean_ctor_get(v_toSemiring_1880_, 3);
lean_inc(v_ofNat_1889_);
v___x_1890_ = lean_apply_1(v_ofNat_1889_, v___x_1886_);
v___x_1891_ = lean_apply_2(v_zsmul_1885_, v_k_1881_, v___x_1890_);
v___x_1892_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1874_, v_ctx_1875_, v_p_1883_, v___x_1891_);
return v___x_1892_;
}
else
{
lean_object* v_p_1893_; lean_object* v_m_1894_; lean_object* v_ofNat_1895_; lean_object* v_npow_1896_; lean_object* v_x_1897_; lean_object* v_k_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; 
v_p_1893_ = lean_ctor_get(v_v_1882_, 0);
lean_inc_ref(v_p_1893_);
v_m_1894_ = lean_ctor_get(v_v_1882_, 1);
lean_inc(v_m_1894_);
lean_dec_ref_known(v_v_1882_, 2);
v_ofNat_1895_ = lean_ctor_get(v_toSemiring_1880_, 3);
v_npow_1896_ = lean_ctor_get(v_toSemiring_1880_, 5);
v_x_1897_ = lean_ctor_get(v_p_1893_, 0);
lean_inc(v_x_1897_);
v_k_1898_ = lean_ctor_get(v_p_1893_, 1);
lean_inc(v_k_1898_);
lean_dec_ref(v_p_1893_);
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = lean_nat_dec_eq(v_k_1898_, v___x_1899_);
if (v___x_1900_ == 0)
{
uint8_t v___x_1901_; 
v___x_1901_ = lean_nat_dec_eq(v_k_1898_, v___x_1886_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1902_ = l_Lean_RArray_getImpl___redArg(v_ctx_1875_, v_x_1897_);
lean_dec(v_x_1897_);
lean_inc(v_npow_1896_);
v___x_1903_ = lean_apply_2(v_npow_1896_, v___x_1902_, v_k_1898_);
lean_inc_ref(v_toSemiring_1880_);
v___x_1904_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1880_, v_ctx_1875_, v_m_1894_, v___x_1903_);
v___x_1905_ = lean_apply_2(v_zsmul_1885_, v_k_1881_, v___x_1904_);
v___x_1906_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1874_, v_ctx_1875_, v_p_1883_, v___x_1905_);
return v___x_1906_;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
lean_dec(v_k_1898_);
v___x_1907_ = l_Lean_RArray_getImpl___redArg(v_ctx_1875_, v_x_1897_);
lean_dec(v_x_1897_);
lean_inc_ref(v_toSemiring_1880_);
v___x_1908_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1880_, v_ctx_1875_, v_m_1894_, v___x_1907_);
v___x_1909_ = lean_apply_2(v_zsmul_1885_, v_k_1881_, v___x_1908_);
v___x_1910_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1874_, v_ctx_1875_, v_p_1883_, v___x_1909_);
return v___x_1910_;
}
}
else
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_dec(v_k_1898_);
lean_dec(v_x_1897_);
lean_inc(v_ofNat_1895_);
v___x_1911_ = lean_apply_1(v_ofNat_1895_, v___x_1886_);
lean_inc_ref(v_toSemiring_1880_);
v___x_1912_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1880_, v_ctx_1875_, v_m_1894_, v___x_1911_);
v___x_1913_ = lean_apply_2(v_zsmul_1885_, v_k_1881_, v___x_1912_);
v___x_1914_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1874_, v_ctx_1875_, v_p_1883_, v___x_1913_);
return v___x_1914_;
}
}
}
else
{
lean_dec(v_zsmul_1885_);
lean_dec(v_k_1881_);
if (lean_obj_tag(v_v_1882_) == 0)
{
lean_object* v_ofNat_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_ofNat_1915_ = lean_ctor_get(v_toSemiring_1880_, 3);
lean_inc(v_ofNat_1915_);
v___x_1916_ = lean_apply_1(v_ofNat_1915_, v___x_1886_);
v___x_1917_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1874_, v_ctx_1875_, v_p_1883_, v___x_1916_);
return v___x_1917_;
}
else
{
lean_object* v_p_1918_; lean_object* v_m_1919_; lean_object* v_ofNat_1920_; lean_object* v_npow_1921_; lean_object* v_x_1922_; lean_object* v_k_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v_p_1918_ = lean_ctor_get(v_v_1882_, 0);
lean_inc_ref(v_p_1918_);
v_m_1919_ = lean_ctor_get(v_v_1882_, 1);
lean_inc(v_m_1919_);
lean_dec_ref_known(v_v_1882_, 2);
v_ofNat_1920_ = lean_ctor_get(v_toSemiring_1880_, 3);
v_npow_1921_ = lean_ctor_get(v_toSemiring_1880_, 5);
v_x_1922_ = lean_ctor_get(v_p_1918_, 0);
lean_inc(v_x_1922_);
v_k_1923_ = lean_ctor_get(v_p_1918_, 1);
lean_inc(v_k_1923_);
lean_dec_ref(v_p_1918_);
v___x_1924_ = lean_unsigned_to_nat(0u);
v___x_1925_ = lean_nat_dec_eq(v_k_1923_, v___x_1924_);
if (v___x_1925_ == 0)
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_nat_dec_eq(v_k_1923_, v___x_1886_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1927_ = l_Lean_RArray_getImpl___redArg(v_ctx_1875_, v_x_1922_);
lean_dec(v_x_1922_);
lean_inc(v_npow_1921_);
v___x_1928_ = lean_apply_2(v_npow_1921_, v___x_1927_, v_k_1923_);
lean_inc_ref(v_toSemiring_1880_);
v___x_1929_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1880_, v_ctx_1875_, v_m_1919_, v___x_1928_);
v___x_1930_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1874_, v_ctx_1875_, v_p_1883_, v___x_1929_);
return v___x_1930_;
}
else
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
lean_dec(v_k_1923_);
v___x_1931_ = l_Lean_RArray_getImpl___redArg(v_ctx_1875_, v_x_1922_);
lean_dec(v_x_1922_);
lean_inc_ref(v_toSemiring_1880_);
v___x_1932_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1880_, v_ctx_1875_, v_m_1919_, v___x_1931_);
v___x_1933_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1874_, v_ctx_1875_, v_p_1883_, v___x_1932_);
return v___x_1933_;
}
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
lean_dec(v_k_1923_);
lean_dec(v_x_1922_);
lean_inc(v_ofNat_1920_);
v___x_1934_ = lean_apply_1(v_ofNat_1920_, v___x_1886_);
lean_inc_ref(v_toSemiring_1880_);
v___x_1935_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1880_, v_ctx_1875_, v_m_1919_, v___x_1934_);
v___x_1936_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1874_, v_ctx_1875_, v_p_1883_, v___x_1935_);
return v___x_1936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___redArg___boxed(lean_object* v_inst_1937_, lean_object* v_ctx_1938_, lean_object* v_p_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_Grind_CommRing_Poly_denote_x27___redArg(v_inst_1937_, v_ctx_1938_, v_p_1939_);
lean_dec_ref(v_ctx_1938_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27(lean_object* v_00_u03b1_1941_, lean_object* v_inst_1942_, lean_object* v_ctx_1943_, lean_object* v_p_1944_){
_start:
{
if (lean_obj_tag(v_p_1944_) == 0)
{
lean_object* v_intCast_1945_; lean_object* v_k_1946_; lean_object* v___x_1947_; 
v_intCast_1945_ = lean_ctor_get(v_inst_1942_, 3);
lean_inc(v_intCast_1945_);
lean_dec_ref(v_inst_1942_);
v_k_1946_ = lean_ctor_get(v_p_1944_, 0);
lean_inc(v_k_1946_);
lean_dec_ref_known(v_p_1944_, 1);
v___x_1947_ = lean_apply_1(v_intCast_1945_, v_k_1946_);
return v___x_1947_;
}
else
{
lean_object* v_toSemiring_1948_; lean_object* v_k_1949_; lean_object* v_v_1950_; lean_object* v_p_1951_; lean_object* v___x_1952_; lean_object* v_zsmul_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v_toSemiring_1948_ = lean_ctor_get(v_inst_1942_, 0);
v_k_1949_ = lean_ctor_get(v_p_1944_, 0);
lean_inc(v_k_1949_);
v_v_1950_ = lean_ctor_get(v_p_1944_, 1);
lean_inc(v_v_1950_);
v_p_1951_ = lean_ctor_get(v_p_1944_, 2);
lean_inc_ref(v_p_1951_);
lean_dec_ref_known(v_p_1944_, 3);
lean_inc_ref(v_inst_1942_);
v___x_1952_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_1942_);
v_zsmul_1953_ = lean_ctor_get(v___x_1952_, 2);
lean_inc(v_zsmul_1953_);
lean_dec_ref(v___x_1952_);
v___x_1954_ = lean_unsigned_to_nat(1u);
v___x_1955_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_1956_ = lean_int_dec_eq(v_k_1949_, v___x_1955_);
if (v___x_1956_ == 0)
{
if (lean_obj_tag(v_v_1950_) == 0)
{
lean_object* v_ofNat_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v_ofNat_1957_ = lean_ctor_get(v_toSemiring_1948_, 3);
lean_inc(v_ofNat_1957_);
v___x_1958_ = lean_apply_1(v_ofNat_1957_, v___x_1954_);
v___x_1959_ = lean_apply_2(v_zsmul_1953_, v_k_1949_, v___x_1958_);
v___x_1960_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1942_, v_ctx_1943_, v_p_1951_, v___x_1959_);
return v___x_1960_;
}
else
{
lean_object* v_p_1961_; lean_object* v_m_1962_; lean_object* v_ofNat_1963_; lean_object* v_npow_1964_; lean_object* v_x_1965_; lean_object* v_k_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_p_1961_ = lean_ctor_get(v_v_1950_, 0);
lean_inc_ref(v_p_1961_);
v_m_1962_ = lean_ctor_get(v_v_1950_, 1);
lean_inc(v_m_1962_);
lean_dec_ref_known(v_v_1950_, 2);
v_ofNat_1963_ = lean_ctor_get(v_toSemiring_1948_, 3);
v_npow_1964_ = lean_ctor_get(v_toSemiring_1948_, 5);
v_x_1965_ = lean_ctor_get(v_p_1961_, 0);
lean_inc(v_x_1965_);
v_k_1966_ = lean_ctor_get(v_p_1961_, 1);
lean_inc(v_k_1966_);
lean_dec_ref(v_p_1961_);
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = lean_nat_dec_eq(v_k_1966_, v___x_1967_);
if (v___x_1968_ == 0)
{
uint8_t v___x_1969_; 
v___x_1969_ = lean_nat_dec_eq(v_k_1966_, v___x_1954_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1970_ = l_Lean_RArray_getImpl___redArg(v_ctx_1943_, v_x_1965_);
lean_dec(v_x_1965_);
lean_inc(v_npow_1964_);
v___x_1971_ = lean_apply_2(v_npow_1964_, v___x_1970_, v_k_1966_);
lean_inc_ref(v_toSemiring_1948_);
v___x_1972_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1948_, v_ctx_1943_, v_m_1962_, v___x_1971_);
v___x_1973_ = lean_apply_2(v_zsmul_1953_, v_k_1949_, v___x_1972_);
v___x_1974_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1942_, v_ctx_1943_, v_p_1951_, v___x_1973_);
return v___x_1974_;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_dec(v_k_1966_);
v___x_1975_ = l_Lean_RArray_getImpl___redArg(v_ctx_1943_, v_x_1965_);
lean_dec(v_x_1965_);
lean_inc_ref(v_toSemiring_1948_);
v___x_1976_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1948_, v_ctx_1943_, v_m_1962_, v___x_1975_);
v___x_1977_ = lean_apply_2(v_zsmul_1953_, v_k_1949_, v___x_1976_);
v___x_1978_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1942_, v_ctx_1943_, v_p_1951_, v___x_1977_);
return v___x_1978_;
}
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
lean_dec(v_k_1966_);
lean_dec(v_x_1965_);
lean_inc(v_ofNat_1963_);
v___x_1979_ = lean_apply_1(v_ofNat_1963_, v___x_1954_);
lean_inc_ref(v_toSemiring_1948_);
v___x_1980_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1948_, v_ctx_1943_, v_m_1962_, v___x_1979_);
v___x_1981_ = lean_apply_2(v_zsmul_1953_, v_k_1949_, v___x_1980_);
v___x_1982_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1942_, v_ctx_1943_, v_p_1951_, v___x_1981_);
return v___x_1982_;
}
}
}
else
{
lean_dec(v_zsmul_1953_);
lean_dec(v_k_1949_);
if (lean_obj_tag(v_v_1950_) == 0)
{
lean_object* v_ofNat_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_ofNat_1983_ = lean_ctor_get(v_toSemiring_1948_, 3);
lean_inc(v_ofNat_1983_);
v___x_1984_ = lean_apply_1(v_ofNat_1983_, v___x_1954_);
v___x_1985_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1942_, v_ctx_1943_, v_p_1951_, v___x_1984_);
return v___x_1985_;
}
else
{
lean_object* v_p_1986_; lean_object* v_m_1987_; lean_object* v_ofNat_1988_; lean_object* v_npow_1989_; lean_object* v_x_1990_; lean_object* v_k_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v_p_1986_ = lean_ctor_get(v_v_1950_, 0);
lean_inc_ref(v_p_1986_);
v_m_1987_ = lean_ctor_get(v_v_1950_, 1);
lean_inc(v_m_1987_);
lean_dec_ref_known(v_v_1950_, 2);
v_ofNat_1988_ = lean_ctor_get(v_toSemiring_1948_, 3);
v_npow_1989_ = lean_ctor_get(v_toSemiring_1948_, 5);
v_x_1990_ = lean_ctor_get(v_p_1986_, 0);
lean_inc(v_x_1990_);
v_k_1991_ = lean_ctor_get(v_p_1986_, 1);
lean_inc(v_k_1991_);
lean_dec_ref(v_p_1986_);
v___x_1992_ = lean_unsigned_to_nat(0u);
v___x_1993_ = lean_nat_dec_eq(v_k_1991_, v___x_1992_);
if (v___x_1993_ == 0)
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_nat_dec_eq(v_k_1991_, v___x_1954_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1995_ = l_Lean_RArray_getImpl___redArg(v_ctx_1943_, v_x_1990_);
lean_dec(v_x_1990_);
lean_inc(v_npow_1989_);
v___x_1996_ = lean_apply_2(v_npow_1989_, v___x_1995_, v_k_1991_);
lean_inc_ref(v_toSemiring_1948_);
v___x_1997_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1948_, v_ctx_1943_, v_m_1987_, v___x_1996_);
v___x_1998_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1942_, v_ctx_1943_, v_p_1951_, v___x_1997_);
return v___x_1998_;
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec(v_k_1991_);
v___x_1999_ = l_Lean_RArray_getImpl___redArg(v_ctx_1943_, v_x_1990_);
lean_dec(v_x_1990_);
lean_inc_ref(v_toSemiring_1948_);
v___x_2000_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1948_, v_ctx_1943_, v_m_1987_, v___x_1999_);
v___x_2001_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1942_, v_ctx_1943_, v_p_1951_, v___x_2000_);
return v___x_2001_;
}
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
lean_dec(v_k_1991_);
lean_dec(v_x_1990_);
lean_inc(v_ofNat_1988_);
v___x_2002_ = lean_apply_1(v_ofNat_1988_, v___x_1954_);
lean_inc_ref(v_toSemiring_1948_);
v___x_2003_ = l_Lean_Grind_CommRing_Mon_denote_x27_go___redArg(v_toSemiring_1948_, v_ctx_1943_, v_m_1987_, v___x_2002_);
v___x_2004_ = l_Lean_Grind_CommRing_Poly_denote_x27_go___redArg(v_inst_1942_, v_ctx_1943_, v_p_1951_, v___x_2003_);
return v___x_2004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denote_x27___boxed(lean_object* v_00_u03b1_2005_, lean_object* v_inst_2006_, lean_object* v_ctx_2007_, lean_object* v_p_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_Grind_CommRing_Poly_denote_x27(v_00_u03b1_2005_, v_inst_2006_, v_ctx_2007_, v_p_2008_);
lean_dec_ref(v_ctx_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object* v_m_2010_){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2011_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2012_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v_m_2010_);
lean_ctor_set(v___x_2013_, 2, v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object* v_x_2014_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = l_Lean_Grind_CommRing_Mon_ofVar(v_x_2014_);
v___x_2016_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_isSorted(lean_object* v_x_2017_){
_start:
{
if (lean_obj_tag(v_x_2017_) == 0)
{
uint8_t v___x_2018_; 
v___x_2018_ = 1;
return v___x_2018_;
}
else
{
lean_object* v_p_2019_; 
v_p_2019_ = lean_ctor_get(v_x_2017_, 2);
if (lean_obj_tag(v_p_2019_) == 0)
{
uint8_t v___x_2020_; 
v___x_2020_ = 1;
return v___x_2020_;
}
else
{
lean_object* v_v_2021_; lean_object* v_v_2022_; uint8_t v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_v_2021_ = lean_ctor_get(v_x_2017_, 1);
v_v_2022_ = lean_ctor_get(v_p_2019_, 1);
v___x_2023_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2021_, v_v_2022_);
v___x_2024_ = lean_box(v___x_2023_);
v___x_2025_ = lean_obj_tag_nat(v___x_2024_);
lean_dec(v___x_2024_);
v___x_2026_ = lean_unsigned_to_nat(2u);
v___x_2027_ = lean_nat_dec_eq(v___x_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
return v___x_2027_;
}
else
{
v_x_2017_ = v_p_2019_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isSorted___boxed(lean_object* v_x_2029_){
_start:
{
uint8_t v_res_2030_; lean_object* v_r_2031_; 
v_res_2030_ = l_Lean_Grind_CommRing_Poly_isSorted(v_x_2029_);
lean_dec_ref(v_x_2029_);
v_r_2031_ = lean_box(v_res_2030_);
return v_r_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go(lean_object* v_k_2032_, lean_object* v_a_2033_){
_start:
{
if (lean_obj_tag(v_a_2033_) == 0)
{
lean_object* v_k_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2042_; 
v_k_2034_ = lean_ctor_get(v_a_2033_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_a_2033_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2036_ = v_a_2033_;
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_k_2034_);
lean_dec(v_a_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = lean_int_add(v_k_2034_, v_k_2032_);
lean_dec(v_k_2034_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2038_);
v___x_2040_ = v___x_2036_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
else
{
lean_object* v_k_2043_; lean_object* v_v_2044_; lean_object* v_p_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2053_; 
v_k_2043_ = lean_ctor_get(v_a_2033_, 0);
v_v_2044_ = lean_ctor_get(v_a_2033_, 1);
v_p_2045_ = lean_ctor_get(v_a_2033_, 2);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_a_2033_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2047_ = v_a_2033_;
v_isShared_2048_ = v_isSharedCheck_2053_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_p_2045_);
lean_inc(v_v_2044_);
lean_inc(v_k_2043_);
lean_dec(v_a_2033_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2053_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2049_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2032_, v_p_2045_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 2, v___x_2049_);
v___x_2051_ = v___x_2047_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_k_2043_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_v_2044_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst_go___boxed(lean_object* v_k_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2054_, v_a_2055_);
lean_dec(v_k_2054_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst(lean_object* v_p_2057_, lean_object* v_k_2058_){
_start:
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2060_ = lean_int_dec_eq(v_k_2058_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_Grind_CommRing_Poly_addConst_go(v_k_2058_, v_p_2057_);
return v___x_2061_;
}
else
{
return v_p_2057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConst___boxed(lean_object* v_p_2062_, lean_object* v_k_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2062_, v_k_2063_);
lean_dec(v_k_2063_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert_go(lean_object* v_k_2065_, lean_object* v_m_2066_, lean_object* v_a_2067_){
_start:
{
if (lean_obj_tag(v_a_2067_) == 0)
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2068_, 0, v_k_2065_);
lean_ctor_set(v___x_2068_, 1, v_m_2066_);
lean_ctor_set(v___x_2068_, 2, v_a_2067_);
return v___x_2068_;
}
else
{
lean_object* v_k_2069_; lean_object* v_v_2070_; lean_object* v_p_2071_; uint8_t v___x_2072_; 
v_k_2069_ = lean_ctor_get(v_a_2067_, 0);
v_v_2070_ = lean_ctor_get(v_a_2067_, 1);
v_p_2071_ = lean_ctor_get(v_a_2067_, 2);
v___x_2072_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2066_, v_v_2070_);
switch(v___x_2072_)
{
case 0:
{
lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2080_; 
lean_inc_ref(v_p_2071_);
lean_inc(v_v_2070_);
lean_inc(v_k_2069_);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_a_2067_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; lean_object* v_unused_2082_; lean_object* v_unused_2083_; 
v_unused_2081_ = lean_ctor_get(v_a_2067_, 2);
lean_dec(v_unused_2081_);
v_unused_2082_ = lean_ctor_get(v_a_2067_, 1);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v_a_2067_, 0);
lean_dec(v_unused_2083_);
v___x_2074_ = v_a_2067_;
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
else
{
lean_dec(v_a_2067_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2065_, v_m_2066_, v_p_2071_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 2, v___x_2076_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_k_2069_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_v_2070_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
case 1:
{
lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2093_; 
lean_inc_ref(v_p_2071_);
lean_inc(v_k_2069_);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_a_2067_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; lean_object* v_unused_2095_; lean_object* v_unused_2096_; 
v_unused_2094_ = lean_ctor_get(v_a_2067_, 2);
lean_dec(v_unused_2094_);
v_unused_2095_ = lean_ctor_get(v_a_2067_, 1);
lean_dec(v_unused_2095_);
v_unused_2096_ = lean_ctor_get(v_a_2067_, 0);
lean_dec(v_unused_2096_);
v___x_2085_ = v_a_2067_;
v_isShared_2086_ = v_isSharedCheck_2093_;
goto v_resetjp_2084_;
}
else
{
lean_dec(v_a_2067_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2093_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v_k_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_k_2087_ = lean_int_add(v_k_2065_, v_k_2069_);
lean_dec(v_k_2069_);
lean_dec(v_k_2065_);
v___x_2088_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2089_ = lean_int_dec_eq(v_k_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2091_; 
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 1, v_m_2066_);
lean_ctor_set(v___x_2085_, 0, v_k_2087_);
v___x_2091_ = v___x_2085_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_k_2087_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_m_2066_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_p_2071_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
else
{
lean_dec(v_k_2087_);
lean_del_object(v___x_2085_);
lean_dec(v_m_2066_);
return v_p_2071_;
}
}
}
default: 
{
lean_object* v___x_2097_; 
v___x_2097_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2097_, 0, v_k_2065_);
lean_ctor_set(v___x_2097_, 1, v_m_2066_);
lean_ctor_set(v___x_2097_, 2, v_a_2067_);
return v___x_2097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insert(lean_object* v_k_2098_, lean_object* v_m_2099_, lean_object* v_p_2100_){
_start:
{
lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2101_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2102_ = lean_int_dec_eq(v_k_2098_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = lean_box(0);
v___x_2104_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2099_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_Grind_CommRing_Poly_insert_go(v_k_2098_, v_m_2099_, v_p_2100_);
return v___x_2105_;
}
else
{
lean_object* v___x_2106_; 
lean_dec(v_m_2099_);
v___x_2106_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_2100_, v_k_2098_);
lean_dec(v_k_2098_);
return v___x_2106_;
}
}
else
{
lean_dec(v_m_2099_);
lean_dec(v_k_2098_);
return v_p_2100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_concat(lean_object* v_p_u2081_2107_, lean_object* v_p_u2082_2108_){
_start:
{
if (lean_obj_tag(v_p_u2081_2107_) == 0)
{
lean_object* v_k_2109_; lean_object* v___x_2110_; 
v_k_2109_ = lean_ctor_get(v_p_u2081_2107_, 0);
lean_inc(v_k_2109_);
lean_dec_ref_known(v_p_u2081_2107_, 1);
v___x_2110_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2108_, v_k_2109_);
lean_dec(v_k_2109_);
return v___x_2110_;
}
else
{
lean_object* v_k_2111_; lean_object* v_v_2112_; lean_object* v_p_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2121_; 
v_k_2111_ = lean_ctor_get(v_p_u2081_2107_, 0);
v_v_2112_ = lean_ctor_get(v_p_u2081_2107_, 1);
v_p_2113_ = lean_ctor_get(v_p_u2081_2107_, 2);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_p_u2081_2107_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2115_ = v_p_u2081_2107_;
v_isShared_2116_ = v_isSharedCheck_2121_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_p_2113_);
lean_inc(v_v_2112_);
lean_inc(v_k_2111_);
lean_dec(v_p_u2081_2107_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2121_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2117_ = l_Lean_Grind_CommRing_Poly_concat(v_p_2113_, v_p_u2082_2108_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 2, v___x_2117_);
v___x_2119_ = v___x_2115_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_k_2111_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_v_2112_);
lean_ctor_set(v_reuseFailAlloc_2120_, 2, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go(lean_object* v_k_2122_, lean_object* v_a_2123_){
_start:
{
if (lean_obj_tag(v_a_2123_) == 0)
{
lean_object* v_k_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2132_; 
v_k_2124_ = lean_ctor_get(v_a_2123_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_a_2123_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2126_ = v_a_2123_;
v_isShared_2127_ = v_isSharedCheck_2132_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_k_2124_);
lean_dec(v_a_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2132_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2128_ = lean_int_mul(v_k_2122_, v_k_2124_);
lean_dec(v_k_2124_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2128_);
v___x_2130_ = v___x_2126_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
else
{
lean_object* v_k_2133_; lean_object* v_v_2134_; lean_object* v_p_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2144_; 
v_k_2133_ = lean_ctor_get(v_a_2123_, 0);
v_v_2134_ = lean_ctor_get(v_a_2123_, 1);
v_p_2135_ = lean_ctor_get(v_a_2123_, 2);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_a_2123_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2137_ = v_a_2123_;
v_isShared_2138_ = v_isSharedCheck_2144_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_p_2135_);
lean_inc(v_v_2134_);
lean_inc(v_k_2133_);
lean_dec(v_a_2123_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2144_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2139_ = lean_int_mul(v_k_2122_, v_k_2133_);
lean_dec(v_k_2133_);
v___x_2140_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2122_, v_p_2135_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 2, v___x_2140_);
lean_ctor_set(v___x_2137_, 0, v___x_2139_);
v___x_2142_ = v___x_2137_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2139_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_go___boxed(lean_object* v_k_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2145_, v_a_2146_);
lean_dec(v_k_2145_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object* v_k_2148_, lean_object* v_p_2149_){
_start:
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2151_ = lean_int_dec_eq(v_k_2148_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2152_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2153_ = lean_int_dec_eq(v_k_2148_, v___x_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_Grind_CommRing_Poly_mulConst_go(v_k_2148_, v_p_2149_);
return v___x_2154_;
}
else
{
return v_p_2149_;
}
}
else
{
lean_object* v___x_2155_; 
lean_dec_ref(v_p_2149_);
v___x_2155_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst___boxed(lean_object* v_k_2156_, lean_object* v_p_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2156_, v_p_2157_);
lean_dec(v_k_2156_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go(lean_object* v_k_2159_, lean_object* v_m_2160_, lean_object* v_a_2161_){
_start:
{
if (lean_obj_tag(v_a_2161_) == 0)
{
lean_object* v_k_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v_k_2162_ = lean_ctor_get(v_a_2161_, 0);
lean_inc(v_k_2162_);
lean_dec_ref_known(v_a_2161_, 1);
v___x_2163_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2164_ = lean_int_dec_eq(v_k_2162_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = lean_int_mul(v_k_2159_, v_k_2162_);
lean_dec(v_k_2162_);
v___x_2166_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2165_);
lean_ctor_set(v___x_2167_, 1, v_m_2160_);
lean_ctor_set(v___x_2167_, 2, v___x_2166_);
return v___x_2167_;
}
else
{
lean_object* v___x_2168_; 
lean_dec(v_k_2162_);
lean_dec(v_m_2160_);
v___x_2168_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2168_;
}
}
else
{
lean_object* v_k_2169_; lean_object* v_v_2170_; lean_object* v_p_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2181_; 
v_k_2169_ = lean_ctor_get(v_a_2161_, 0);
v_v_2170_ = lean_ctor_get(v_a_2161_, 1);
v_p_2171_ = lean_ctor_get(v_a_2161_, 2);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_a_2161_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2173_ = v_a_2161_;
v_isShared_2174_ = v_isSharedCheck_2181_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_p_2171_);
lean_inc(v_v_2170_);
lean_inc(v_k_2169_);
lean_dec(v_a_2161_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2181_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2175_ = lean_int_mul(v_k_2159_, v_k_2169_);
lean_dec(v_k_2169_);
lean_inc(v_m_2160_);
v___x_2176_ = l_Lean_Grind_CommRing_Mon_mul(v_m_2160_, v_v_2170_);
v___x_2177_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2159_, v_m_2160_, v_p_2171_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 2, v___x_2177_);
lean_ctor_set(v___x_2173_, 1, v___x_2176_);
lean_ctor_set(v___x_2173_, 0, v___x_2175_);
v___x_2179_ = v___x_2173_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v___x_2176_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_go___boxed(lean_object* v_k_2182_, lean_object* v_m_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2182_, v_m_2183_, v_a_2184_);
lean_dec(v_k_2182_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object* v_k_2186_, lean_object* v_m_2187_, lean_object* v_p_2188_){
_start:
{
lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2189_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2190_ = lean_int_dec_eq(v_k_2186_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2191_ = lean_box(0);
v___x_2192_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2187_, v___x_2191_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_Grind_CommRing_Poly_mulMon_go(v_k_2186_, v_m_2187_, v_p_2188_);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; 
lean_dec(v_m_2187_);
v___x_2194_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2186_, v_p_2188_);
return v___x_2194_;
}
}
else
{
lean_object* v___x_2195_; 
lean_dec_ref(v_p_2188_);
lean_dec(v_m_2187_);
v___x_2195_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon___boxed(lean_object* v_k_2196_, lean_object* v_m_2197_, lean_object* v_p_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2196_, v_m_2197_, v_p_2198_);
lean_dec(v_k_2196_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go(lean_object* v_k_2200_, lean_object* v_m_2201_, lean_object* v_p_2202_, lean_object* v_acc_2203_){
_start:
{
if (lean_obj_tag(v_p_2202_) == 0)
{
lean_object* v_k_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v_k_2204_ = lean_ctor_get(v_p_2202_, 0);
lean_inc(v_k_2204_);
lean_dec_ref_known(v_p_2202_, 1);
v___x_2205_ = lean_int_mul(v_k_2200_, v_k_2204_);
lean_dec(v_k_2204_);
v___x_2206_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2205_, v_m_2201_, v_acc_2203_);
return v___x_2206_;
}
else
{
lean_object* v_k_2207_; lean_object* v_v_2208_; lean_object* v_p_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v_k_2207_ = lean_ctor_get(v_p_2202_, 0);
lean_inc(v_k_2207_);
v_v_2208_ = lean_ctor_get(v_p_2202_, 1);
lean_inc(v_v_2208_);
v_p_2209_ = lean_ctor_get(v_p_2202_, 2);
lean_inc_ref(v_p_2209_);
lean_dec_ref_known(v_p_2202_, 3);
v___x_2210_ = lean_int_mul(v_k_2200_, v_k_2207_);
lean_dec(v_k_2207_);
lean_inc(v_m_2201_);
v___x_2211_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_2201_, v_v_2208_);
v___x_2212_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2210_, v___x_2211_, v_acc_2203_);
v_p_2202_ = v_p_2209_;
v_acc_2203_ = v___x_2212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc_go___boxed(lean_object* v_k_2214_, lean_object* v_m_2215_, lean_object* v_p_2216_, lean_object* v_acc_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2214_, v_m_2215_, v_p_2216_, v_acc_2217_);
lean_dec(v_k_2214_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc(lean_object* v_k_2219_, lean_object* v_m_2220_, lean_object* v_p_2221_){
_start:
{
lean_object* v___x_2222_; uint8_t v___x_2223_; 
v___x_2222_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2223_ = lean_int_dec_eq(v_k_2219_, v___x_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; uint8_t v___x_2225_; 
v___x_2224_ = lean_box(0);
v___x_2225_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_2220_, v___x_2224_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2227_ = l_Lean_Grind_CommRing_Poly_mulMon__nc_go(v_k_2219_, v_m_2220_, v_p_2221_, v___x_2226_);
return v___x_2227_;
}
else
{
lean_object* v___x_2228_; 
lean_dec(v_m_2220_);
v___x_2228_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2219_, v_p_2221_);
return v___x_2228_;
}
}
else
{
lean_object* v___x_2229_; 
lean_dec_ref(v_p_2221_);
lean_dec(v_m_2220_);
v___x_2229_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon__nc___boxed(lean_object* v_k_2230_, lean_object* v_m_2231_, lean_object* v_p_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2230_, v_m_2231_, v_p_2232_);
lean_dec(v_k_2230_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length(lean_object* v_x_2234_){
_start:
{
if (lean_obj_tag(v_x_2234_) == 0)
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_unsigned_to_nat(0u);
return v___x_2235_;
}
else
{
lean_object* v_p_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_p_2236_ = lean_ctor_get(v_x_2234_, 2);
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = l_Lean_Grind_CommRing_Poly_length(v_p_2236_);
v___x_2239_ = lean_nat_add(v___x_2237_, v___x_2238_);
lean_dec(v___x_2238_);
return v___x_2239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length___boxed(lean_object* v_x_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Grind_CommRing_Poly_length(v_x_2240_);
lean_dec_ref(v_x_2240_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_go(lean_object* v_fuel_2242_, lean_object* v_p_u2081_2243_, lean_object* v_p_u2082_2244_){
_start:
{
lean_object* v_zero_2245_; uint8_t v_isZero_2246_; 
v_zero_2245_ = lean_unsigned_to_nat(0u);
v_isZero_2246_ = lean_nat_dec_eq(v_fuel_2242_, v_zero_2245_);
if (v_isZero_2246_ == 1)
{
lean_object* v___x_2247_; 
lean_dec(v_fuel_2242_);
v___x_2247_ = l_Lean_Grind_CommRing_Poly_concat(v_p_u2081_2243_, v_p_u2082_2244_);
return v___x_2247_;
}
else
{
if (lean_obj_tag(v_p_u2081_2243_) == 0)
{
lean_dec(v_fuel_2242_);
if (lean_obj_tag(v_p_u2082_2244_) == 0)
{
lean_object* v_k_2248_; lean_object* v_k_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2257_; 
v_k_2248_ = lean_ctor_get(v_p_u2081_2243_, 0);
lean_inc(v_k_2248_);
lean_dec_ref_known(v_p_u2081_2243_, 1);
v_k_2249_ = lean_ctor_get(v_p_u2082_2244_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_p_u2082_2244_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2251_ = v_p_u2082_2244_;
v_isShared_2252_ = v_isSharedCheck_2257_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_k_2249_);
lean_dec(v_p_u2082_2244_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2257_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v___x_2255_; 
v___x_2253_ = lean_int_add(v_k_2248_, v_k_2249_);
lean_dec(v_k_2249_);
lean_dec(v_k_2248_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2253_);
v___x_2255_ = v___x_2251_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
else
{
lean_object* v_k_2258_; lean_object* v___x_2259_; 
v_k_2258_ = lean_ctor_get(v_p_u2081_2243_, 0);
lean_inc(v_k_2258_);
lean_dec_ref_known(v_p_u2081_2243_, 1);
v___x_2259_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2082_2244_, v_k_2258_);
lean_dec(v_k_2258_);
return v___x_2259_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_2244_) == 0)
{
lean_object* v_k_2260_; lean_object* v___x_2261_; 
lean_dec(v_fuel_2242_);
v_k_2260_ = lean_ctor_get(v_p_u2082_2244_, 0);
lean_inc(v_k_2260_);
lean_dec_ref_known(v_p_u2082_2244_, 1);
v___x_2261_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_u2081_2243_, v_k_2260_);
lean_dec(v_k_2260_);
return v___x_2261_;
}
else
{
lean_object* v_k_2262_; lean_object* v_v_2263_; lean_object* v_p_2264_; lean_object* v_k_2265_; lean_object* v_v_2266_; lean_object* v_p_2267_; lean_object* v_one_2268_; lean_object* v_n_2269_; uint8_t v___x_2270_; 
v_k_2262_ = lean_ctor_get(v_p_u2081_2243_, 0);
v_v_2263_ = lean_ctor_get(v_p_u2081_2243_, 1);
v_p_2264_ = lean_ctor_get(v_p_u2081_2243_, 2);
v_k_2265_ = lean_ctor_get(v_p_u2082_2244_, 0);
v_v_2266_ = lean_ctor_get(v_p_u2082_2244_, 1);
v_p_2267_ = lean_ctor_get(v_p_u2082_2244_, 2);
v_one_2268_ = lean_unsigned_to_nat(1u);
v_n_2269_ = lean_nat_sub(v_fuel_2242_, v_one_2268_);
lean_dec(v_fuel_2242_);
v___x_2270_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2263_, v_v_2266_);
switch(v___x_2270_)
{
case 0:
{
lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2278_; 
lean_inc_ref(v_p_2267_);
lean_inc(v_v_2266_);
lean_inc(v_k_2265_);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_p_u2082_2244_);
if (v_isSharedCheck_2278_ == 0)
{
lean_object* v_unused_2279_; lean_object* v_unused_2280_; lean_object* v_unused_2281_; 
v_unused_2279_ = lean_ctor_get(v_p_u2082_2244_, 2);
lean_dec(v_unused_2279_);
v_unused_2280_ = lean_ctor_get(v_p_u2082_2244_, 1);
lean_dec(v_unused_2280_);
v_unused_2281_ = lean_ctor_get(v_p_u2082_2244_, 0);
lean_dec(v_unused_2281_);
v___x_2272_ = v_p_u2082_2244_;
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
else
{
lean_dec(v_p_u2082_2244_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2274_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2269_, v_p_u2081_2243_, v_p_2267_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 2, v___x_2274_);
v___x_2276_ = v___x_2272_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_k_2265_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_v_2266_);
lean_ctor_set(v_reuseFailAlloc_2277_, 2, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
case 1:
{
lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2293_; 
lean_inc_ref(v_p_2267_);
lean_inc(v_k_2265_);
lean_inc_ref(v_p_2264_);
lean_inc(v_v_2263_);
lean_inc(v_k_2262_);
lean_dec_ref_known(v_p_u2081_2243_, 3);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_p_u2082_2244_);
if (v_isSharedCheck_2293_ == 0)
{
lean_object* v_unused_2294_; lean_object* v_unused_2295_; lean_object* v_unused_2296_; 
v_unused_2294_ = lean_ctor_get(v_p_u2082_2244_, 2);
lean_dec(v_unused_2294_);
v_unused_2295_ = lean_ctor_get(v_p_u2082_2244_, 1);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_p_u2082_2244_, 0);
lean_dec(v_unused_2296_);
v___x_2283_ = v_p_u2082_2244_;
v_isShared_2284_ = v_isSharedCheck_2293_;
goto v_resetjp_2282_;
}
else
{
lean_dec(v_p_u2082_2244_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2293_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v_k_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v_k_2285_ = lean_int_add(v_k_2262_, v_k_2265_);
lean_dec(v_k_2265_);
lean_dec(v_k_2262_);
v___x_2286_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2287_ = lean_int_dec_eq(v_k_2285_, v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2288_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2269_, v_p_2264_, v_p_2267_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 2, v___x_2288_);
lean_ctor_set(v___x_2283_, 1, v_v_2263_);
lean_ctor_set(v___x_2283_, 0, v_k_2285_);
v___x_2290_ = v___x_2283_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_k_2285_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2291_, 2, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
else
{
lean_dec(v_k_2285_);
lean_del_object(v___x_2283_);
lean_dec(v_v_2263_);
v_fuel_2242_ = v_n_2269_;
v_p_u2081_2243_ = v_p_2264_;
v_p_u2082_2244_ = v_p_2267_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2304_; 
lean_inc_ref(v_p_2264_);
lean_inc(v_v_2263_);
lean_inc(v_k_2262_);
v_isSharedCheck_2304_ = !lean_is_exclusive(v_p_u2081_2243_);
if (v_isSharedCheck_2304_ == 0)
{
lean_object* v_unused_2305_; lean_object* v_unused_2306_; lean_object* v_unused_2307_; 
v_unused_2305_ = lean_ctor_get(v_p_u2081_2243_, 2);
lean_dec(v_unused_2305_);
v_unused_2306_ = lean_ctor_get(v_p_u2081_2243_, 1);
lean_dec(v_unused_2306_);
v_unused_2307_ = lean_ctor_get(v_p_u2081_2243_, 0);
lean_dec(v_unused_2307_);
v___x_2298_ = v_p_u2081_2243_;
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
else
{
lean_dec(v_p_u2081_2243_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2300_ = l_Lean_Grind_CommRing_Poly_combine_go(v_n_2269_, v_p_2264_, v_p_u2082_2244_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 2, v___x_2300_);
v___x_2302_ = v___x_2298_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2303_, 2, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object* v_p_u2081_2308_, lean_object* v_p_u2082_2309_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2310_ = l_Lean_Grind_CommRing_Poly_length(v_p_u2081_2308_);
v___x_2311_ = l_Lean_Grind_CommRing_Poly_length(v_p_u2082_2309_);
v___x_2312_ = lean_nat_add(v___x_2310_, v___x_2311_);
lean_dec(v___x_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_unsigned_to_nat(1u);
v___x_2314_ = lean_nat_add(v___x_2312_, v___x_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = l_Lean_Grind_CommRing_Poly_combine_go(v___x_2314_, v_p_u2081_2308_, v_p_u2082_2309_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t v_x_2316_, lean_object* v_h__1_2317_, lean_object* v_h__2_2318_, lean_object* v_h__3_2319_){
_start:
{
switch(v_x_2316_)
{
case 0:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_dec(v_h__2_2318_);
lean_dec(v_h__1_2317_);
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_apply_1(v_h__3_2319_, v___x_2320_);
return v___x_2321_;
}
case 1:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec(v_h__3_2319_);
lean_dec(v_h__2_2318_);
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_apply_1(v_h__1_2317_, v___x_2322_);
return v___x_2323_;
}
default: 
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
lean_dec(v_h__3_2319_);
lean_dec(v_h__1_2317_);
v___x_2324_ = lean_box(0);
v___x_2325_ = lean_apply_1(v_h__2_2318_, v___x_2324_);
return v___x_2325_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object* v_x_2326_, lean_object* v_h__1_2327_, lean_object* v_h__2_2328_, lean_object* v_h__3_2329_){
_start:
{
uint8_t v_x_33__boxed_2330_; lean_object* v_res_2331_; 
v_x_33__boxed_2330_ = lean_unbox(v_x_2326_);
v_res_2331_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(v_x_33__boxed_2330_, v_h__1_2327_, v_h__2_2328_, v_h__3_2329_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object* v_motive_2332_, uint8_t v_x_2333_, lean_object* v_h__1_2334_, lean_object* v_h__2_2335_, lean_object* v_h__3_2336_){
_start:
{
switch(v_x_2333_)
{
case 0:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec(v_h__2_2335_);
lean_dec(v_h__1_2334_);
v___x_2337_ = lean_box(0);
v___x_2338_ = lean_apply_1(v_h__3_2336_, v___x_2337_);
return v___x_2338_;
}
case 1:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
lean_dec(v_h__3_2336_);
lean_dec(v_h__2_2335_);
v___x_2339_ = lean_box(0);
v___x_2340_ = lean_apply_1(v_h__1_2334_, v___x_2339_);
return v___x_2340_;
}
default: 
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_dec(v_h__3_2336_);
lean_dec(v_h__1_2334_);
v___x_2341_ = lean_box(0);
v___x_2342_ = lean_apply_1(v_h__2_2335_, v___x_2341_);
return v___x_2342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object* v_motive_2343_, lean_object* v_x_2344_, lean_object* v_h__1_2345_, lean_object* v_h__2_2346_, lean_object* v_h__3_2347_){
_start:
{
uint8_t v_x_48__boxed_2348_; lean_object* v_res_2349_; 
v_x_48__boxed_2348_ = lean_unbox(v_x_2344_);
v_res_2349_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(v_motive_2343_, v_x_48__boxed_2348_, v_h__1_2345_, v_h__2_2346_, v_h__3_2347_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul_go(lean_object* v_p_u2082_2350_, lean_object* v_p_u2081_2351_, lean_object* v_acc_2352_){
_start:
{
if (lean_obj_tag(v_p_u2081_2351_) == 0)
{
lean_object* v_k_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_k_2353_ = lean_ctor_get(v_p_u2081_2351_, 0);
lean_inc(v_k_2353_);
lean_dec_ref_known(v_p_u2081_2351_, 1);
v___x_2354_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2353_, v_p_u2082_2350_);
lean_dec(v_k_2353_);
v___x_2355_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2352_, v___x_2354_);
return v___x_2355_;
}
else
{
lean_object* v_k_2356_; lean_object* v_v_2357_; lean_object* v_p_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_k_2356_ = lean_ctor_get(v_p_u2081_2351_, 0);
lean_inc(v_k_2356_);
v_v_2357_ = lean_ctor_get(v_p_u2081_2351_, 1);
lean_inc(v_v_2357_);
v_p_2358_ = lean_ctor_get(v_p_u2081_2351_, 2);
lean_inc_ref(v_p_2358_);
lean_dec_ref_known(v_p_u2081_2351_, 3);
lean_inc_ref(v_p_u2082_2350_);
v___x_2359_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_2356_, v_v_2357_, v_p_u2082_2350_);
lean_dec(v_k_2356_);
v___x_2360_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2352_, v___x_2359_);
v_p_u2081_2351_ = v_p_2358_;
v_acc_2352_ = v___x_2360_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul(lean_object* v_p_u2081_2362_, lean_object* v_p_u2082_2363_){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2365_ = l_Lean_Grind_CommRing_Poly_mul_go(v_p_u2082_2363_, v_p_u2081_2362_, v___x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc_go(lean_object* v_p_u2082_2366_, lean_object* v_p_u2081_2367_, lean_object* v_acc_2368_){
_start:
{
if (lean_obj_tag(v_p_u2081_2367_) == 0)
{
lean_object* v_k_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v_k_2369_ = lean_ctor_get(v_p_u2081_2367_, 0);
lean_inc(v_k_2369_);
lean_dec_ref_known(v_p_u2081_2367_, 1);
v___x_2370_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_2369_, v_p_u2082_2366_);
lean_dec(v_k_2369_);
v___x_2371_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2368_, v___x_2370_);
return v___x_2371_;
}
else
{
lean_object* v_k_2372_; lean_object* v_v_2373_; lean_object* v_p_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v_k_2372_ = lean_ctor_get(v_p_u2081_2367_, 0);
lean_inc(v_k_2372_);
v_v_2373_ = lean_ctor_get(v_p_u2081_2367_, 1);
lean_inc(v_v_2373_);
v_p_2374_ = lean_ctor_get(v_p_u2081_2367_, 2);
lean_inc_ref(v_p_2374_);
lean_dec_ref_known(v_p_u2081_2367_, 3);
lean_inc_ref(v_p_u2082_2366_);
v___x_2375_ = l_Lean_Grind_CommRing_Poly_mulMon__nc(v_k_2372_, v_v_2373_, v_p_u2082_2366_);
lean_dec(v_k_2372_);
v___x_2376_ = l_Lean_Grind_CommRing_Poly_combine(v_acc_2368_, v___x_2375_);
v_p_u2081_2367_ = v_p_2374_;
v_acc_2368_ = v___x_2376_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object* v_p_u2081_2378_, lean_object* v_p_u2082_2379_){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2381_ = l_Lean_Grind_CommRing_Poly_mul__nc_go(v_p_u2082_2379_, v_p_u2081_2378_, v___x_2380_);
return v___x_2381_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_pow___closed__0(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow(lean_object* v_p_2384_, lean_object* v_k_2385_){
_start:
{
lean_object* v_zero_2386_; uint8_t v_isZero_2387_; 
v_zero_2386_ = lean_unsigned_to_nat(0u);
v_isZero_2387_ = lean_nat_dec_eq(v_k_2385_, v_zero_2386_);
if (v_isZero_2387_ == 1)
{
lean_object* v___x_2388_; 
lean_dec_ref(v_p_2384_);
v___x_2388_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2388_;
}
else
{
lean_object* v_one_2389_; lean_object* v_n_2390_; uint8_t v___x_2391_; 
v_one_2389_ = lean_unsigned_to_nat(1u);
v_n_2390_ = lean_nat_sub(v_k_2385_, v_one_2389_);
v___x_2391_ = lean_nat_dec_eq(v_n_2390_, v_zero_2386_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
lean_inc_ref(v_p_2384_);
v___x_2392_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2384_, v_n_2390_);
lean_dec(v_n_2390_);
v___x_2393_ = l_Lean_Grind_CommRing_Poly_mul(v_p_2384_, v___x_2392_);
return v___x_2393_;
}
else
{
lean_dec(v_n_2390_);
return v_p_2384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow___boxed(lean_object* v_p_2394_, lean_object* v_k_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Grind_CommRing_Poly_pow(v_p_2394_, v_k_2395_);
lean_dec(v_k_2395_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc(lean_object* v_p_2397_, lean_object* v_k_2398_){
_start:
{
lean_object* v_zero_2399_; uint8_t v_isZero_2400_; 
v_zero_2399_ = lean_unsigned_to_nat(0u);
v_isZero_2400_ = lean_nat_dec_eq(v_k_2398_, v_zero_2399_);
if (v_isZero_2400_ == 1)
{
lean_object* v___x_2401_; 
lean_dec_ref(v_p_2397_);
v___x_2401_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2401_;
}
else
{
lean_object* v_one_2402_; lean_object* v_n_2403_; uint8_t v___x_2404_; 
v_one_2402_ = lean_unsigned_to_nat(1u);
v_n_2403_ = lean_nat_sub(v_k_2398_, v_one_2402_);
v___x_2404_ = lean_nat_dec_eq(v_n_2403_, v_zero_2399_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_inc_ref(v_p_2397_);
v___x_2405_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2397_, v_n_2403_);
lean_dec(v_n_2403_);
v___x_2406_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2405_, v_p_2397_);
return v___x_2406_;
}
else
{
lean_dec(v_n_2403_);
return v_p_2397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_pow__nc___boxed(lean_object* v_p_2407_, lean_object* v_k_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_Grind_CommRing_Poly_pow__nc(v_p_2407_, v_k_2408_);
lean_dec(v_k_2408_);
return v_res_2409_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2411_ = lean_int_neg(v___x_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly(lean_object* v_x_2412_){
_start:
{
switch(lean_obj_tag(v_x_2412_))
{
case 0:
{
lean_object* v_k_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
v_k_2413_ = lean_ctor_get(v_x_2412_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_x_2412_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v_x_2412_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_k_2413_);
lean_dec(v_x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_k_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
case 1:
{
lean_object* v_k_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2429_; 
v_k_2421_ = lean_ctor_get(v_x_2412_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v_x_2412_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2423_ = v_x_2412_;
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_k_2421_);
lean_dec(v_x_2412_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2425_ = lean_nat_to_int(v_k_2421_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set_tag(v___x_2423_, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2425_);
v___x_2427_ = v___x_2423_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
case 2:
{
lean_object* v_k_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
v_k_2430_ = lean_ctor_get(v_x_2412_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_x_2412_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v_x_2412_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_k_2430_);
lean_dec(v_x_2412_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set_tag(v___x_2432_, 0);
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_k_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
case 3:
{
lean_object* v_i_2438_; lean_object* v___x_2439_; 
v_i_2438_ = lean_ctor_get(v_x_2412_, 0);
lean_inc(v_i_2438_);
lean_dec_ref_known(v_x_2412_, 1);
v___x_2439_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2438_);
return v___x_2439_;
}
case 4:
{
lean_object* v_a_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_a_2440_ = lean_ctor_get(v_x_2412_, 0);
lean_inc_ref(v_a_2440_);
lean_dec_ref_known(v_x_2412_, 1);
v___x_2441_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2442_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2440_);
v___x_2443_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2441_, v___x_2442_);
return v___x_2443_;
}
case 5:
{
lean_object* v_a_2444_; lean_object* v_b_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_a_2444_ = lean_ctor_get(v_x_2412_, 0);
lean_inc_ref(v_a_2444_);
v_b_2445_ = lean_ctor_get(v_x_2412_, 1);
lean_inc_ref(v_b_2445_);
lean_dec_ref_known(v_x_2412_, 2);
v___x_2446_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2444_);
v___x_2447_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2445_);
v___x_2448_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2446_, v___x_2447_);
return v___x_2448_;
}
case 6:
{
lean_object* v_a_2449_; lean_object* v_b_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_a_2449_ = lean_ctor_get(v_x_2412_, 0);
lean_inc_ref(v_a_2449_);
v_b_2450_ = lean_ctor_get(v_x_2412_, 1);
lean_inc_ref(v_b_2450_);
lean_dec_ref_known(v_x_2412_, 2);
v___x_2451_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2449_);
v___x_2452_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2453_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2450_);
v___x_2454_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2452_, v___x_2453_);
v___x_2455_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2451_, v___x_2454_);
return v___x_2455_;
}
case 7:
{
lean_object* v_a_2456_; lean_object* v_b_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_a_2456_ = lean_ctor_get(v_x_2412_, 0);
lean_inc_ref(v_a_2456_);
v_b_2457_ = lean_ctor_get(v_x_2412_, 1);
lean_inc_ref(v_b_2457_);
lean_dec_ref_known(v_x_2412_, 2);
v___x_2458_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2456_);
v___x_2459_ = l_Lean_Grind_CommRing_Expr_toPoly(v_b_2457_);
v___x_2460_ = l_Lean_Grind_CommRing_Poly_mul(v___x_2458_, v___x_2459_);
return v___x_2460_;
}
default: 
{
lean_object* v_a_2461_; lean_object* v_k_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2494_; 
v_a_2461_ = lean_ctor_get(v_x_2412_, 0);
v_k_2462_ = lean_ctor_get(v_x_2412_, 1);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_x_2412_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2464_ = v_x_2412_;
v_isShared_2465_ = v_isSharedCheck_2494_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_k_2462_);
lean_inc(v_a_2461_);
lean_dec(v_x_2412_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2494_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v_n_2467_; lean_object* v___x_2470_; uint8_t v___x_2471_; 
v___x_2470_ = lean_unsigned_to_nat(0u);
v___x_2471_ = lean_nat_dec_eq(v_k_2462_, v___x_2470_);
if (v___x_2471_ == 0)
{
switch(lean_obj_tag(v_a_2461_))
{
case 0:
{
lean_object* v_k_2472_; 
lean_del_object(v___x_2464_);
v_k_2472_ = lean_ctor_get(v_a_2461_, 0);
lean_inc(v_k_2472_);
lean_dec_ref_known(v_a_2461_, 1);
v_n_2467_ = v_k_2472_;
goto v___jp_2466_;
}
case 2:
{
lean_object* v_k_2473_; 
lean_del_object(v___x_2464_);
v_k_2473_ = lean_ctor_get(v_a_2461_, 0);
lean_inc(v_k_2473_);
lean_dec_ref_known(v_a_2461_, 1);
v_n_2467_ = v_k_2473_;
goto v___jp_2466_;
}
case 1:
{
lean_object* v_k_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2483_; 
lean_del_object(v___x_2464_);
v_k_2474_ = lean_ctor_get(v_a_2461_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_a_2461_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2476_ = v_a_2461_;
v_isShared_2477_ = v_isSharedCheck_2483_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_k_2474_);
lean_dec(v_a_2461_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2483_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2478_ = lean_nat_to_int(v_k_2474_);
v___x_2479_ = l_Int_pow(v___x_2478_, v_k_2462_);
lean_dec(v_k_2462_);
lean_dec(v___x_2478_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set_tag(v___x_2476_, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2479_);
v___x_2481_ = v___x_2476_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
case 3:
{
lean_object* v_i_2484_; lean_object* v___x_2486_; 
v_i_2484_ = lean_ctor_get(v_a_2461_, 0);
lean_inc(v_i_2484_);
lean_dec_ref_known(v_a_2461_, 1);
if (v_isShared_2465_ == 0)
{
lean_ctor_set_tag(v___x_2464_, 0);
lean_ctor_set(v___x_2464_, 0, v_i_2484_);
v___x_2486_ = v___x_2464_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_i_2484_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_k_2462_);
v___x_2486_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = lean_box(0);
v___x_2488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2488_);
return v___x_2489_;
}
}
default: 
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
lean_del_object(v___x_2464_);
v___x_2491_ = l_Lean_Grind_CommRing_Expr_toPoly(v_a_2461_);
v___x_2492_ = l_Lean_Grind_CommRing_Poly_pow(v___x_2491_, v_k_2462_);
lean_dec(v_k_2462_);
return v___x_2492_;
}
}
}
else
{
lean_object* v___x_2493_; 
lean_del_object(v___x_2464_);
lean_dec(v_k_2462_);
lean_dec_ref(v_a_2461_);
v___x_2493_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2493_;
}
v___jp_2466_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = l_Int_pow(v_n_2467_, v_k_2462_);
lean_dec(v_k_2462_);
lean_dec(v_n_2467_);
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
return v___x_2469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf(lean_object* v_m_2495_, lean_object* v_x_2496_){
_start:
{
if (lean_obj_tag(v_m_2495_) == 0)
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_unsigned_to_nat(0u);
return v___x_2497_;
}
else
{
lean_object* v_p_2498_; lean_object* v_m_2499_; lean_object* v_x_2500_; lean_object* v_k_2501_; uint8_t v___x_2502_; 
v_p_2498_ = lean_ctor_get(v_m_2495_, 0);
v_m_2499_ = lean_ctor_get(v_m_2495_, 1);
v_x_2500_ = lean_ctor_get(v_p_2498_, 0);
v_k_2501_ = lean_ctor_get(v_p_2498_, 1);
v___x_2502_ = lean_nat_dec_eq(v_x_2500_, v_x_2496_);
if (v___x_2502_ == 0)
{
v_m_2495_ = v_m_2499_;
goto _start;
}
else
{
lean_inc(v_k_2501_);
return v_k_2501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_degreeOf___boxed(lean_object* v_m_2504_, lean_object* v_x_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_m_2504_, v_x_2505_);
lean_dec(v_x_2505_);
lean_dec(v_m_2504_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar(lean_object* v_m_2507_, lean_object* v_x_2508_){
_start:
{
if (lean_obj_tag(v_m_2507_) == 0)
{
return v_m_2507_;
}
else
{
lean_object* v_p_2509_; lean_object* v_m_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2520_; 
v_p_2509_ = lean_ctor_get(v_m_2507_, 0);
v_m_2510_ = lean_ctor_get(v_m_2507_, 1);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_m_2507_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2512_ = v_m_2507_;
v_isShared_2513_ = v_isSharedCheck_2520_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_m_2510_);
lean_inc(v_p_2509_);
lean_dec(v_m_2507_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2520_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v_x_2514_; uint8_t v___x_2515_; 
v_x_2514_ = lean_ctor_get(v_p_2509_, 0);
v___x_2515_ = lean_nat_dec_eq(v_x_2514_, v_x_2508_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2510_, v_x_2508_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 1, v___x_2516_);
v___x_2518_ = v___x_2512_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_p_2509_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
else
{
lean_del_object(v___x_2512_);
lean_dec_ref(v_p_2509_);
return v_m_2510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_cancelVar___boxed(lean_object* v_m_2521_, lean_object* v_x_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_m_2521_, v_x_2522_);
lean_dec(v_x_2522_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27(lean_object* v_c_2524_, lean_object* v_x_2525_, lean_object* v_p_2526_, lean_object* v_acc_2527_){
_start:
{
if (lean_obj_tag(v_p_2526_) == 0)
{
lean_object* v_k_2528_; lean_object* v___x_2529_; 
v_k_2528_ = lean_ctor_get(v_p_2526_, 0);
lean_inc(v_k_2528_);
lean_dec_ref_known(v_p_2526_, 1);
v___x_2529_ = l_Lean_Grind_CommRing_Poly_addConst(v_acc_2527_, v_k_2528_);
lean_dec(v_k_2528_);
return v___x_2529_;
}
else
{
lean_object* v_k_2530_; lean_object* v_v_2531_; lean_object* v_p_2532_; lean_object* v_n_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v_k_2530_ = lean_ctor_get(v_p_2526_, 0);
lean_inc(v_k_2530_);
v_v_2531_ = lean_ctor_get(v_p_2526_, 1);
lean_inc(v_v_2531_);
v_p_2532_ = lean_ctor_get(v_p_2526_, 2);
lean_inc_ref(v_p_2532_);
lean_dec_ref_known(v_p_2526_, 3);
v_n_2536_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_2531_, v_x_2525_);
v___x_2537_ = lean_unsigned_to_nat(0u);
v___x_2538_ = lean_nat_dec_lt(v___x_2537_, v_n_2536_);
if (v___x_2538_ == 0)
{
lean_dec(v_n_2536_);
goto v___jp_2533_;
}
else
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2539_ = l_Int_pow(v_c_2524_, v_n_2536_);
lean_dec(v_n_2536_);
v___x_2540_ = lean_int_emod(v_k_2530_, v___x_2539_);
v___x_2541_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2542_ = lean_int_dec_eq(v___x_2540_, v___x_2541_);
lean_dec(v___x_2540_);
if (v___x_2542_ == 0)
{
lean_dec(v___x_2539_);
goto v___jp_2533_;
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2543_ = lean_int_ediv(v_k_2530_, v___x_2539_);
lean_dec(v___x_2539_);
lean_dec(v_k_2530_);
v___x_2544_ = l_Lean_Grind_CommRing_Mon_cancelVar(v_v_2531_, v_x_2525_);
v___x_2545_ = l_Lean_Grind_CommRing_Poly_insert(v___x_2543_, v___x_2544_, v_acc_2527_);
v_p_2526_ = v_p_2532_;
v_acc_2527_ = v___x_2545_;
goto _start;
}
}
v___jp_2533_:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Lean_Grind_CommRing_Poly_insert(v_k_2530_, v_v_2531_, v_acc_2527_);
v_p_2526_ = v_p_2532_;
v_acc_2527_ = v___x_2534_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar_x27___boxed(lean_object* v_c_2547_, lean_object* v_x_2548_, lean_object* v_p_2549_, lean_object* v_acc_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2547_, v_x_2548_, v_p_2549_, v_acc_2550_);
lean_dec(v_x_2548_);
lean_dec(v_c_2547_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar(lean_object* v_c_2552_, lean_object* v_x_2553_, lean_object* v_p_2554_){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2556_ = l_Lean_Grind_CommRing_Poly_cancelVar_x27(v_c_2552_, v_x_2553_, v_p_2554_, v___x_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_cancelVar___boxed(lean_object* v_c_2557_, lean_object* v_x_2558_, lean_object* v_p_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Grind_CommRing_Poly_cancelVar(v_c_2557_, v_x_2558_, v_p_2559_);
lean_dec(v_x_2558_);
lean_dec(v_c_2557_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(lean_object* v_p_2561_, lean_object* v_acc_2562_){
_start:
{
lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2563_ = lean_unsigned_to_nat(1u);
v___x_2564_ = lean_nat_dec_eq(v_acc_2562_, v___x_2563_);
if (v___x_2564_ == 0)
{
if (lean_obj_tag(v_p_2561_) == 0)
{
lean_object* v_k_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v_k_2565_ = lean_ctor_get(v_p_2561_, 0);
v___x_2566_ = lean_nat_abs(v_k_2565_);
v___x_2567_ = lean_nat_gcd(v_acc_2562_, v___x_2566_);
lean_dec(v___x_2566_);
lean_dec(v_acc_2562_);
return v___x_2567_;
}
else
{
lean_object* v_k_2568_; lean_object* v_p_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v_k_2568_ = lean_ctor_get(v_p_2561_, 0);
v_p_2569_ = lean_ctor_get(v_p_2561_, 2);
v___x_2570_ = lean_nat_abs(v_k_2568_);
v___x_2571_ = lean_nat_gcd(v_acc_2562_, v___x_2570_);
lean_dec(v___x_2570_);
lean_dec(v_acc_2562_);
v_p_2561_ = v_p_2569_;
v_acc_2562_ = v___x_2571_;
goto _start;
}
}
else
{
return v_acc_2562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs_go___boxed(lean_object* v_p_2573_, lean_object* v_acc_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_2573_, v_acc_2574_);
lean_dec_ref(v_p_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs(lean_object* v_x_2576_){
_start:
{
if (lean_obj_tag(v_x_2576_) == 0)
{
lean_object* v_k_2577_; lean_object* v___x_2578_; 
v_k_2577_ = lean_ctor_get(v_x_2576_, 0);
v___x_2578_ = lean_nat_abs(v_k_2577_);
return v___x_2578_;
}
else
{
lean_object* v_k_2579_; lean_object* v_p_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v_k_2579_ = lean_ctor_get(v_x_2576_, 0);
v_p_2580_ = lean_ctor_get(v_x_2576_, 2);
v___x_2581_ = lean_nat_abs(v_k_2579_);
v___x_2582_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_2580_, v___x_2581_);
return v___x_2582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs___boxed(lean_object* v_x_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs(v_x_2583_);
lean_dec_ref(v_x_2583_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst(lean_object* v_p_2585_, lean_object* v_a_2586_){
_start:
{
if (lean_obj_tag(v_p_2585_) == 0)
{
lean_object* v_k_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2595_; 
v_k_2587_ = lean_ctor_get(v_p_2585_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_p_2585_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2589_ = v_p_2585_;
v_isShared_2590_ = v_isSharedCheck_2595_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_k_2587_);
lean_dec(v_p_2585_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2595_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2591_ = lean_int_ediv(v_k_2587_, v_a_2586_);
lean_dec(v_k_2587_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2591_);
v___x_2593_ = v___x_2589_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
else
{
lean_object* v_k_2596_; lean_object* v_v_2597_; lean_object* v_p_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2607_; 
v_k_2596_ = lean_ctor_get(v_p_2585_, 0);
v_v_2597_ = lean_ctor_get(v_p_2585_, 1);
v_p_2598_ = lean_ctor_get(v_p_2585_, 2);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_p_2585_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2600_ = v_p_2585_;
v_isShared_2601_ = v_isSharedCheck_2607_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_p_2598_);
lean_inc(v_v_2597_);
lean_inc(v_k_2596_);
lean_dec(v_p_2585_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2607_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2605_; 
v___x_2602_ = lean_int_ediv(v_k_2596_, v_a_2586_);
lean_dec(v_k_2596_);
v___x_2603_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_2598_, v_a_2586_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 2, v___x_2603_);
lean_ctor_set(v___x_2600_, 0, v___x_2602_);
v___x_2605_ = v___x_2600_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_v_2597_);
lean_ctor_set(v_reuseFailAlloc_2606_, 2, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst___boxed(lean_object* v_p_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_2608_, v_a_2609_);
lean_dec(v_a_2609_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(lean_object* v_x_2611_, lean_object* v_p_2612_, lean_object* v_max_2613_){
_start:
{
if (lean_obj_tag(v_p_2612_) == 0)
{
return v_max_2613_;
}
else
{
lean_object* v_v_2614_; lean_object* v_p_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v_v_2614_ = lean_ctor_get(v_p_2612_, 1);
v_p_2615_ = lean_ctor_get(v_p_2612_, 2);
v___x_2616_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_2614_, v_x_2611_);
v___x_2617_ = lean_nat_dec_le(v_max_2613_, v___x_2616_);
if (v___x_2617_ == 0)
{
lean_dec(v___x_2616_);
v_p_2612_ = v_p_2615_;
goto _start;
}
else
{
lean_dec(v_max_2613_);
v_p_2612_ = v_p_2615_;
v_max_2613_ = v___x_2616_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf_go___boxed(lean_object* v_x_2620_, lean_object* v_p_2621_, lean_object* v_max_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_2620_, v_p_2621_, v_max_2622_);
lean_dec_ref(v_p_2621_);
lean_dec(v_x_2620_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf(lean_object* v_p_2624_, lean_object* v_x_2625_){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = lean_unsigned_to_nat(0u);
v___x_2627_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_2625_, v_p_2624_, v___x_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf___boxed(lean_object* v_p_2628_, lean_object* v_x_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_2628_, v_x_2629_);
lean_dec(v_x_2629_);
lean_dec_ref(v_p_2628_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter___redArg(lean_object* v_x_2631_, lean_object* v_h__1_2632_, lean_object* v_h__2_2633_, lean_object* v_h__3_2634_, lean_object* v_h__4_2635_, lean_object* v_h__5_2636_, lean_object* v_h__6_2637_, lean_object* v_h__7_2638_, lean_object* v_h__8_2639_, lean_object* v_h__9_2640_){
_start:
{
switch(lean_obj_tag(v_x_2631_))
{
case 0:
{
lean_object* v_k_2641_; lean_object* v___x_2642_; 
lean_dec(v_h__9_2640_);
lean_dec(v_h__8_2639_);
lean_dec(v_h__7_2638_);
lean_dec(v_h__6_2637_);
lean_dec(v_h__5_2636_);
lean_dec(v_h__4_2635_);
lean_dec(v_h__3_2634_);
lean_dec(v_h__2_2633_);
v_k_2641_ = lean_ctor_get(v_x_2631_, 0);
lean_inc(v_k_2641_);
lean_dec_ref_known(v_x_2631_, 1);
v___x_2642_ = lean_apply_1(v_h__1_2632_, v_k_2641_);
return v___x_2642_;
}
case 1:
{
lean_object* v_k_2643_; lean_object* v___x_2644_; 
lean_dec(v_h__9_2640_);
lean_dec(v_h__8_2639_);
lean_dec(v_h__7_2638_);
lean_dec(v_h__6_2637_);
lean_dec(v_h__5_2636_);
lean_dec(v_h__4_2635_);
lean_dec(v_h__2_2633_);
lean_dec(v_h__1_2632_);
v_k_2643_ = lean_ctor_get(v_x_2631_, 0);
lean_inc(v_k_2643_);
lean_dec_ref_known(v_x_2631_, 1);
v___x_2644_ = lean_apply_1(v_h__3_2634_, v_k_2643_);
return v___x_2644_;
}
case 2:
{
lean_object* v_k_2645_; lean_object* v___x_2646_; 
lean_dec(v_h__9_2640_);
lean_dec(v_h__8_2639_);
lean_dec(v_h__7_2638_);
lean_dec(v_h__6_2637_);
lean_dec(v_h__5_2636_);
lean_dec(v_h__4_2635_);
lean_dec(v_h__3_2634_);
lean_dec(v_h__1_2632_);
v_k_2645_ = lean_ctor_get(v_x_2631_, 0);
lean_inc(v_k_2645_);
lean_dec_ref_known(v_x_2631_, 1);
v___x_2646_ = lean_apply_1(v_h__2_2633_, v_k_2645_);
return v___x_2646_;
}
case 3:
{
lean_object* v_i_2647_; lean_object* v___x_2648_; 
lean_dec(v_h__9_2640_);
lean_dec(v_h__8_2639_);
lean_dec(v_h__7_2638_);
lean_dec(v_h__6_2637_);
lean_dec(v_h__5_2636_);
lean_dec(v_h__3_2634_);
lean_dec(v_h__2_2633_);
lean_dec(v_h__1_2632_);
v_i_2647_ = lean_ctor_get(v_x_2631_, 0);
lean_inc(v_i_2647_);
lean_dec_ref_known(v_x_2631_, 1);
v___x_2648_ = lean_apply_1(v_h__4_2635_, v_i_2647_);
return v___x_2648_;
}
case 4:
{
lean_object* v_a_2649_; lean_object* v___x_2650_; 
lean_dec(v_h__9_2640_);
lean_dec(v_h__8_2639_);
lean_dec(v_h__6_2637_);
lean_dec(v_h__5_2636_);
lean_dec(v_h__4_2635_);
lean_dec(v_h__3_2634_);
lean_dec(v_h__2_2633_);
lean_dec(v_h__1_2632_);
v_a_2649_ = lean_ctor_get(v_x_2631_, 0);
lean_inc_ref(v_a_2649_);
lean_dec_ref_known(v_x_2631_, 1);
v___x_2650_ = lean_apply_1(v_h__7_2638_, v_a_2649_);
return v___x_2650_;
}
case 5:
{
lean_object* v_a_2651_; lean_object* v_b_2652_; lean_object* v___x_2653_; 
lean_dec(v_h__9_2640_);
lean_dec(v_h__8_2639_);
lean_dec(v_h__7_2638_);
lean_dec(v_h__6_2637_);
lean_dec(v_h__4_2635_);
lean_dec(v_h__3_2634_);
lean_dec(v_h__2_2633_);
lean_dec(v_h__1_2632_);
v_a_2651_ = lean_ctor_get(v_x_2631_, 0);
lean_inc_ref(v_a_2651_);
v_b_2652_ = lean_ctor_get(v_x_2631_, 1);
lean_inc_ref(v_b_2652_);
lean_dec_ref_known(v_x_2631_, 2);
v___x_2653_ = lean_apply_2(v_h__5_2636_, v_a_2651_, v_b_2652_);
return v___x_2653_;
}
case 6:
{
lean_object* v_a_2654_; lean_object* v_b_2655_; lean_object* v___x_2656_; 
lean_dec(v_h__9_2640_);
lean_dec(v_h__7_2638_);
lean_dec(v_h__6_2637_);
lean_dec(v_h__5_2636_);
lean_dec(v_h__4_2635_);
lean_dec(v_h__3_2634_);
lean_dec(v_h__2_2633_);
lean_dec(v_h__1_2632_);
v_a_2654_ = lean_ctor_get(v_x_2631_, 0);
lean_inc_ref(v_a_2654_);
v_b_2655_ = lean_ctor_get(v_x_2631_, 1);
lean_inc_ref(v_b_2655_);
lean_dec_ref_known(v_x_2631_, 2);
v___x_2656_ = lean_apply_2(v_h__8_2639_, v_a_2654_, v_b_2655_);
return v___x_2656_;
}
case 7:
{
lean_object* v_a_2657_; lean_object* v_b_2658_; lean_object* v___x_2659_; 
lean_dec(v_h__9_2640_);
lean_dec(v_h__8_2639_);
lean_dec(v_h__7_2638_);
lean_dec(v_h__5_2636_);
lean_dec(v_h__4_2635_);
lean_dec(v_h__3_2634_);
lean_dec(v_h__2_2633_);
lean_dec(v_h__1_2632_);
v_a_2657_ = lean_ctor_get(v_x_2631_, 0);
lean_inc_ref(v_a_2657_);
v_b_2658_ = lean_ctor_get(v_x_2631_, 1);
lean_inc_ref(v_b_2658_);
lean_dec_ref_known(v_x_2631_, 2);
v___x_2659_ = lean_apply_2(v_h__6_2637_, v_a_2657_, v_b_2658_);
return v___x_2659_;
}
default: 
{
lean_object* v_a_2660_; lean_object* v_k_2661_; lean_object* v___x_2662_; 
lean_dec(v_h__8_2639_);
lean_dec(v_h__7_2638_);
lean_dec(v_h__6_2637_);
lean_dec(v_h__5_2636_);
lean_dec(v_h__4_2635_);
lean_dec(v_h__3_2634_);
lean_dec(v_h__2_2633_);
lean_dec(v_h__1_2632_);
v_a_2660_ = lean_ctor_get(v_x_2631_, 0);
lean_inc_ref(v_a_2660_);
v_k_2661_ = lean_ctor_get(v_x_2631_, 1);
lean_inc(v_k_2661_);
lean_dec_ref_known(v_x_2631_, 2);
v___x_2662_ = lean_apply_2(v_h__9_2640_, v_a_2660_, v_k_2661_);
return v___x_2662_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__4_splitter(lean_object* v_motive_2663_, lean_object* v_x_2664_, lean_object* v_h__1_2665_, lean_object* v_h__2_2666_, lean_object* v_h__3_2667_, lean_object* v_h__4_2668_, lean_object* v_h__5_2669_, lean_object* v_h__6_2670_, lean_object* v_h__7_2671_, lean_object* v_h__8_2672_, lean_object* v_h__9_2673_){
_start:
{
switch(lean_obj_tag(v_x_2664_))
{
case 0:
{
lean_object* v_k_2674_; lean_object* v___x_2675_; 
lean_dec(v_h__9_2673_);
lean_dec(v_h__8_2672_);
lean_dec(v_h__7_2671_);
lean_dec(v_h__6_2670_);
lean_dec(v_h__5_2669_);
lean_dec(v_h__4_2668_);
lean_dec(v_h__3_2667_);
lean_dec(v_h__2_2666_);
v_k_2674_ = lean_ctor_get(v_x_2664_, 0);
lean_inc(v_k_2674_);
lean_dec_ref_known(v_x_2664_, 1);
v___x_2675_ = lean_apply_1(v_h__1_2665_, v_k_2674_);
return v___x_2675_;
}
case 1:
{
lean_object* v_k_2676_; lean_object* v___x_2677_; 
lean_dec(v_h__9_2673_);
lean_dec(v_h__8_2672_);
lean_dec(v_h__7_2671_);
lean_dec(v_h__6_2670_);
lean_dec(v_h__5_2669_);
lean_dec(v_h__4_2668_);
lean_dec(v_h__2_2666_);
lean_dec(v_h__1_2665_);
v_k_2676_ = lean_ctor_get(v_x_2664_, 0);
lean_inc(v_k_2676_);
lean_dec_ref_known(v_x_2664_, 1);
v___x_2677_ = lean_apply_1(v_h__3_2667_, v_k_2676_);
return v___x_2677_;
}
case 2:
{
lean_object* v_k_2678_; lean_object* v___x_2679_; 
lean_dec(v_h__9_2673_);
lean_dec(v_h__8_2672_);
lean_dec(v_h__7_2671_);
lean_dec(v_h__6_2670_);
lean_dec(v_h__5_2669_);
lean_dec(v_h__4_2668_);
lean_dec(v_h__3_2667_);
lean_dec(v_h__1_2665_);
v_k_2678_ = lean_ctor_get(v_x_2664_, 0);
lean_inc(v_k_2678_);
lean_dec_ref_known(v_x_2664_, 1);
v___x_2679_ = lean_apply_1(v_h__2_2666_, v_k_2678_);
return v___x_2679_;
}
case 3:
{
lean_object* v_i_2680_; lean_object* v___x_2681_; 
lean_dec(v_h__9_2673_);
lean_dec(v_h__8_2672_);
lean_dec(v_h__7_2671_);
lean_dec(v_h__6_2670_);
lean_dec(v_h__5_2669_);
lean_dec(v_h__3_2667_);
lean_dec(v_h__2_2666_);
lean_dec(v_h__1_2665_);
v_i_2680_ = lean_ctor_get(v_x_2664_, 0);
lean_inc(v_i_2680_);
lean_dec_ref_known(v_x_2664_, 1);
v___x_2681_ = lean_apply_1(v_h__4_2668_, v_i_2680_);
return v___x_2681_;
}
case 4:
{
lean_object* v_a_2682_; lean_object* v___x_2683_; 
lean_dec(v_h__9_2673_);
lean_dec(v_h__8_2672_);
lean_dec(v_h__6_2670_);
lean_dec(v_h__5_2669_);
lean_dec(v_h__4_2668_);
lean_dec(v_h__3_2667_);
lean_dec(v_h__2_2666_);
lean_dec(v_h__1_2665_);
v_a_2682_ = lean_ctor_get(v_x_2664_, 0);
lean_inc_ref(v_a_2682_);
lean_dec_ref_known(v_x_2664_, 1);
v___x_2683_ = lean_apply_1(v_h__7_2671_, v_a_2682_);
return v___x_2683_;
}
case 5:
{
lean_object* v_a_2684_; lean_object* v_b_2685_; lean_object* v___x_2686_; 
lean_dec(v_h__9_2673_);
lean_dec(v_h__8_2672_);
lean_dec(v_h__7_2671_);
lean_dec(v_h__6_2670_);
lean_dec(v_h__4_2668_);
lean_dec(v_h__3_2667_);
lean_dec(v_h__2_2666_);
lean_dec(v_h__1_2665_);
v_a_2684_ = lean_ctor_get(v_x_2664_, 0);
lean_inc_ref(v_a_2684_);
v_b_2685_ = lean_ctor_get(v_x_2664_, 1);
lean_inc_ref(v_b_2685_);
lean_dec_ref_known(v_x_2664_, 2);
v___x_2686_ = lean_apply_2(v_h__5_2669_, v_a_2684_, v_b_2685_);
return v___x_2686_;
}
case 6:
{
lean_object* v_a_2687_; lean_object* v_b_2688_; lean_object* v___x_2689_; 
lean_dec(v_h__9_2673_);
lean_dec(v_h__7_2671_);
lean_dec(v_h__6_2670_);
lean_dec(v_h__5_2669_);
lean_dec(v_h__4_2668_);
lean_dec(v_h__3_2667_);
lean_dec(v_h__2_2666_);
lean_dec(v_h__1_2665_);
v_a_2687_ = lean_ctor_get(v_x_2664_, 0);
lean_inc_ref(v_a_2687_);
v_b_2688_ = lean_ctor_get(v_x_2664_, 1);
lean_inc_ref(v_b_2688_);
lean_dec_ref_known(v_x_2664_, 2);
v___x_2689_ = lean_apply_2(v_h__8_2672_, v_a_2687_, v_b_2688_);
return v___x_2689_;
}
case 7:
{
lean_object* v_a_2690_; lean_object* v_b_2691_; lean_object* v___x_2692_; 
lean_dec(v_h__9_2673_);
lean_dec(v_h__8_2672_);
lean_dec(v_h__7_2671_);
lean_dec(v_h__5_2669_);
lean_dec(v_h__4_2668_);
lean_dec(v_h__3_2667_);
lean_dec(v_h__2_2666_);
lean_dec(v_h__1_2665_);
v_a_2690_ = lean_ctor_get(v_x_2664_, 0);
lean_inc_ref(v_a_2690_);
v_b_2691_ = lean_ctor_get(v_x_2664_, 1);
lean_inc_ref(v_b_2691_);
lean_dec_ref_known(v_x_2664_, 2);
v___x_2692_ = lean_apply_2(v_h__6_2670_, v_a_2690_, v_b_2691_);
return v___x_2692_;
}
default: 
{
lean_object* v_a_2693_; lean_object* v_k_2694_; lean_object* v___x_2695_; 
lean_dec(v_h__8_2672_);
lean_dec(v_h__7_2671_);
lean_dec(v_h__6_2670_);
lean_dec(v_h__5_2669_);
lean_dec(v_h__4_2668_);
lean_dec(v_h__3_2667_);
lean_dec(v_h__2_2666_);
lean_dec(v_h__1_2665_);
v_a_2693_ = lean_ctor_get(v_x_2664_, 0);
lean_inc_ref(v_a_2693_);
v_k_2694_ = lean_ctor_get(v_x_2664_, 1);
lean_inc(v_k_2694_);
lean_dec_ref_known(v_x_2664_, 2);
v___x_2695_ = lean_apply_2(v_h__9_2673_, v_a_2693_, v_k_2694_);
return v___x_2695_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter___redArg(lean_object* v_a_2696_, lean_object* v_h__1_2697_, lean_object* v_h__2_2698_, lean_object* v_h__3_2699_, lean_object* v_h__4_2700_, lean_object* v_h__5_2701_){
_start:
{
switch(lean_obj_tag(v_a_2696_))
{
case 0:
{
lean_object* v_k_2702_; lean_object* v___x_2703_; 
lean_dec(v_h__5_2701_);
lean_dec(v_h__4_2700_);
lean_dec(v_h__3_2699_);
lean_dec(v_h__2_2698_);
v_k_2702_ = lean_ctor_get(v_a_2696_, 0);
lean_inc(v_k_2702_);
lean_dec_ref_known(v_a_2696_, 1);
v___x_2703_ = lean_apply_1(v_h__1_2697_, v_k_2702_);
return v___x_2703_;
}
case 2:
{
lean_object* v_k_2704_; lean_object* v___x_2705_; 
lean_dec(v_h__5_2701_);
lean_dec(v_h__4_2700_);
lean_dec(v_h__3_2699_);
lean_dec(v_h__1_2697_);
v_k_2704_ = lean_ctor_get(v_a_2696_, 0);
lean_inc(v_k_2704_);
lean_dec_ref_known(v_a_2696_, 1);
v___x_2705_ = lean_apply_1(v_h__2_2698_, v_k_2704_);
return v___x_2705_;
}
case 1:
{
lean_object* v_k_2706_; lean_object* v___x_2707_; 
lean_dec(v_h__5_2701_);
lean_dec(v_h__4_2700_);
lean_dec(v_h__2_2698_);
lean_dec(v_h__1_2697_);
v_k_2706_ = lean_ctor_get(v_a_2696_, 0);
lean_inc(v_k_2706_);
lean_dec_ref_known(v_a_2696_, 1);
v___x_2707_ = lean_apply_1(v_h__3_2699_, v_k_2706_);
return v___x_2707_;
}
case 3:
{
lean_object* v_i_2708_; lean_object* v___x_2709_; 
lean_dec(v_h__5_2701_);
lean_dec(v_h__3_2699_);
lean_dec(v_h__2_2698_);
lean_dec(v_h__1_2697_);
v_i_2708_ = lean_ctor_get(v_a_2696_, 0);
lean_inc(v_i_2708_);
lean_dec_ref_known(v_a_2696_, 1);
v___x_2709_ = lean_apply_1(v_h__4_2700_, v_i_2708_);
return v___x_2709_;
}
default: 
{
lean_object* v___x_2710_; 
lean_dec(v_h__4_2700_);
lean_dec(v_h__3_2699_);
lean_dec(v_h__2_2698_);
lean_dec(v_h__1_2697_);
v___x_2710_ = lean_apply_5(v_h__5_2701_, v_a_2696_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPoly_match__1_splitter(lean_object* v_motive_2711_, lean_object* v_a_2712_, lean_object* v_h__1_2713_, lean_object* v_h__2_2714_, lean_object* v_h__3_2715_, lean_object* v_h__4_2716_, lean_object* v_h__5_2717_){
_start:
{
switch(lean_obj_tag(v_a_2712_))
{
case 0:
{
lean_object* v_k_2718_; lean_object* v___x_2719_; 
lean_dec(v_h__5_2717_);
lean_dec(v_h__4_2716_);
lean_dec(v_h__3_2715_);
lean_dec(v_h__2_2714_);
v_k_2718_ = lean_ctor_get(v_a_2712_, 0);
lean_inc(v_k_2718_);
lean_dec_ref_known(v_a_2712_, 1);
v___x_2719_ = lean_apply_1(v_h__1_2713_, v_k_2718_);
return v___x_2719_;
}
case 2:
{
lean_object* v_k_2720_; lean_object* v___x_2721_; 
lean_dec(v_h__5_2717_);
lean_dec(v_h__4_2716_);
lean_dec(v_h__3_2715_);
lean_dec(v_h__1_2713_);
v_k_2720_ = lean_ctor_get(v_a_2712_, 0);
lean_inc(v_k_2720_);
lean_dec_ref_known(v_a_2712_, 1);
v___x_2721_ = lean_apply_1(v_h__2_2714_, v_k_2720_);
return v___x_2721_;
}
case 1:
{
lean_object* v_k_2722_; lean_object* v___x_2723_; 
lean_dec(v_h__5_2717_);
lean_dec(v_h__4_2716_);
lean_dec(v_h__2_2714_);
lean_dec(v_h__1_2713_);
v_k_2722_ = lean_ctor_get(v_a_2712_, 0);
lean_inc(v_k_2722_);
lean_dec_ref_known(v_a_2712_, 1);
v___x_2723_ = lean_apply_1(v_h__3_2715_, v_k_2722_);
return v___x_2723_;
}
case 3:
{
lean_object* v_i_2724_; lean_object* v___x_2725_; 
lean_dec(v_h__5_2717_);
lean_dec(v_h__3_2715_);
lean_dec(v_h__2_2714_);
lean_dec(v_h__1_2713_);
v_i_2724_ = lean_ctor_get(v_a_2712_, 0);
lean_inc(v_i_2724_);
lean_dec_ref_known(v_a_2712_, 1);
v___x_2725_ = lean_apply_1(v_h__4_2716_, v_i_2724_);
return v___x_2725_;
}
default: 
{
lean_object* v___x_2726_; 
lean_dec(v_h__4_2716_);
lean_dec(v_h__3_2715_);
lean_dec(v_h__2_2714_);
lean_dec(v_h__1_2713_);
v___x_2726_ = lean_apply_5(v_h__5_2717_, v_a_2712_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_2726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPoly__nc(lean_object* v_x_2727_){
_start:
{
switch(lean_obj_tag(v_x_2727_))
{
case 0:
{
lean_object* v_k_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
v_k_2728_ = lean_ctor_get(v_x_2727_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_x_2727_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v_x_2727_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_k_2728_);
lean_dec(v_x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_k_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
case 1:
{
lean_object* v_k_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2744_; 
v_k_2736_ = lean_ctor_get(v_x_2727_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_x_2727_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2738_ = v_x_2727_;
v_isShared_2739_ = v_isSharedCheck_2744_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_k_2736_);
lean_dec(v_x_2727_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2744_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2740_ = lean_nat_to_int(v_k_2736_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set_tag(v___x_2738_, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2740_);
v___x_2742_ = v___x_2738_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
case 2:
{
lean_object* v_k_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
v_k_2745_ = lean_ctor_get(v_x_2727_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_x_2727_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v_x_2727_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_k_2745_);
lean_dec(v_x_2727_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
lean_ctor_set_tag(v___x_2747_, 0);
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_k_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
case 3:
{
lean_object* v_i_2753_; lean_object* v___x_2754_; 
v_i_2753_ = lean_ctor_get(v_x_2727_, 0);
lean_inc(v_i_2753_);
lean_dec_ref_known(v_x_2727_, 1);
v___x_2754_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2753_);
return v___x_2754_;
}
case 4:
{
lean_object* v_a_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_a_2755_ = lean_ctor_get(v_x_2727_, 0);
lean_inc_ref(v_a_2755_);
lean_dec_ref_known(v_x_2727_, 1);
v___x_2756_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2757_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2755_);
v___x_2758_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2756_, v___x_2757_);
return v___x_2758_;
}
case 5:
{
lean_object* v_a_2759_; lean_object* v_b_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v_a_2759_ = lean_ctor_get(v_x_2727_, 0);
lean_inc_ref(v_a_2759_);
v_b_2760_ = lean_ctor_get(v_x_2727_, 1);
lean_inc_ref(v_b_2760_);
lean_dec_ref_known(v_x_2727_, 2);
v___x_2761_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2759_);
v___x_2762_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2760_);
v___x_2763_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2761_, v___x_2762_);
return v___x_2763_;
}
case 6:
{
lean_object* v_a_2764_; lean_object* v_b_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v_a_2764_ = lean_ctor_get(v_x_2727_, 0);
lean_inc_ref(v_a_2764_);
v_b_2765_ = lean_ctor_get(v_x_2727_, 1);
lean_inc_ref(v_b_2765_);
lean_dec_ref_known(v_x_2727_, 2);
v___x_2766_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2764_);
v___x_2767_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_2768_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2765_);
v___x_2769_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_2767_, v___x_2768_);
v___x_2770_ = l_Lean_Grind_CommRing_Poly_combine(v___x_2766_, v___x_2769_);
return v___x_2770_;
}
case 7:
{
lean_object* v_a_2771_; lean_object* v_b_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_a_2771_ = lean_ctor_get(v_x_2727_, 0);
lean_inc_ref(v_a_2771_);
v_b_2772_ = lean_ctor_get(v_x_2727_, 1);
lean_inc_ref(v_b_2772_);
lean_dec_ref_known(v_x_2727_, 2);
v___x_2773_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2771_);
v___x_2774_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_b_2772_);
v___x_2775_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_2773_, v___x_2774_);
return v___x_2775_;
}
default: 
{
lean_object* v_a_2776_; lean_object* v_k_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2809_; 
v_a_2776_ = lean_ctor_get(v_x_2727_, 0);
v_k_2777_ = lean_ctor_get(v_x_2727_, 1);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_x_2727_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2779_ = v_x_2727_;
v_isShared_2780_ = v_isSharedCheck_2809_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_k_2777_);
lean_inc(v_a_2776_);
lean_dec(v_x_2727_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2809_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_n_2782_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2785_ = lean_unsigned_to_nat(0u);
v___x_2786_ = lean_nat_dec_eq(v_k_2777_, v___x_2785_);
if (v___x_2786_ == 0)
{
switch(lean_obj_tag(v_a_2776_))
{
case 0:
{
lean_object* v_k_2787_; 
lean_del_object(v___x_2779_);
v_k_2787_ = lean_ctor_get(v_a_2776_, 0);
lean_inc(v_k_2787_);
lean_dec_ref_known(v_a_2776_, 1);
v_n_2782_ = v_k_2787_;
goto v___jp_2781_;
}
case 2:
{
lean_object* v_k_2788_; 
lean_del_object(v___x_2779_);
v_k_2788_ = lean_ctor_get(v_a_2776_, 0);
lean_inc(v_k_2788_);
lean_dec_ref_known(v_a_2776_, 1);
v_n_2782_ = v_k_2788_;
goto v___jp_2781_;
}
case 1:
{
lean_object* v_k_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2798_; 
lean_del_object(v___x_2779_);
v_k_2789_ = lean_ctor_get(v_a_2776_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_a_2776_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2791_ = v_a_2776_;
v_isShared_2792_ = v_isSharedCheck_2798_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_k_2789_);
lean_dec(v_a_2776_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2798_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2793_ = lean_nat_to_int(v_k_2789_);
v___x_2794_ = l_Int_pow(v___x_2793_, v_k_2777_);
lean_dec(v_k_2777_);
lean_dec(v___x_2793_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2794_);
v___x_2796_ = v___x_2791_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
case 3:
{
lean_object* v_i_2799_; lean_object* v___x_2801_; 
v_i_2799_ = lean_ctor_get(v_a_2776_, 0);
lean_inc(v_i_2799_);
lean_dec_ref_known(v_a_2776_, 1);
if (v_isShared_2780_ == 0)
{
lean_ctor_set_tag(v___x_2779_, 0);
lean_ctor_set(v___x_2779_, 0, v_i_2799_);
v___x_2801_ = v___x_2779_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_i_2799_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_k_2777_);
v___x_2801_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2802_ = lean_box(0);
v___x_2803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2801_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2803_);
return v___x_2804_;
}
}
default: 
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_del_object(v___x_2779_);
v___x_2806_ = l_Lean_Grind_CommRing_Expr_toPoly__nc(v_a_2776_);
v___x_2807_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_2806_, v_k_2777_);
lean_dec(v_k_2777_);
return v___x_2807_;
}
}
}
else
{
lean_object* v___x_2808_; 
lean_del_object(v___x_2779_);
lean_dec(v_k_2777_);
lean_dec_ref(v_a_2776_);
v___x_2808_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_2808_;
}
v___jp_2781_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = l_Int_pow(v_n_2782_, v_k_2777_);
lean_dec(v_k_2777_);
lean_dec(v_n_2782_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
return v___x_2784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_normEq0(lean_object* v_p_2810_, lean_object* v_c_2811_){
_start:
{
if (lean_obj_tag(v_p_2810_) == 0)
{
lean_object* v_k_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v_k_2812_ = lean_ctor_get(v_p_2810_, 0);
v___x_2813_ = lean_nat_to_int(v_c_2811_);
v___x_2814_ = lean_int_emod(v_k_2812_, v___x_2813_);
lean_dec(v___x_2813_);
v___x_2815_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2816_ = lean_int_dec_eq(v___x_2814_, v___x_2815_);
lean_dec(v___x_2814_);
if (v___x_2816_ == 0)
{
return v_p_2810_;
}
else
{
lean_object* v___x_2817_; 
lean_dec_ref_known(v_p_2810_, 1);
v___x_2817_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2817_;
}
}
else
{
lean_object* v_k_2818_; lean_object* v_v_2819_; lean_object* v_p_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2833_; 
v_k_2818_ = lean_ctor_get(v_p_2810_, 0);
v_v_2819_ = lean_ctor_get(v_p_2810_, 1);
v_p_2820_ = lean_ctor_get(v_p_2810_, 2);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_p_2810_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2822_ = v_p_2810_;
v_isShared_2823_ = v_isSharedCheck_2833_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_p_2820_);
lean_inc(v_v_2819_);
lean_inc(v_k_2818_);
lean_dec(v_p_2810_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2833_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
lean_inc(v_c_2811_);
v___x_2824_ = lean_nat_to_int(v_c_2811_);
v___x_2825_ = lean_int_emod(v_k_2818_, v___x_2824_);
lean_dec(v___x_2824_);
v___x_2826_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2827_ = lean_int_dec_eq(v___x_2825_, v___x_2826_);
lean_dec(v___x_2825_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; lean_object* v___x_2830_; 
v___x_2828_ = l_Lean_Grind_CommRing_Poly_normEq0(v_p_2820_, v_c_2811_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 2, v___x_2828_);
v___x_2830_ = v___x_2822_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_k_2818_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_v_2819_);
lean_ctor_set(v_reuseFailAlloc_2831_, 2, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
else
{
lean_del_object(v___x_2822_);
lean_dec(v_v_2819_);
lean_dec(v_k_2818_);
v_p_2810_ = v_p_2820_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC(lean_object* v_p_2834_, lean_object* v_k_2835_, lean_object* v_c_2836_){
_start:
{
if (lean_obj_tag(v_p_2834_) == 0)
{
lean_object* v_k_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2847_; 
v_k_2837_ = lean_ctor_get(v_p_2834_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_p_2834_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2839_ = v_p_2834_;
v_isShared_2840_ = v_isSharedCheck_2847_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_k_2837_);
lean_dec(v_p_2834_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2847_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2841_ = lean_int_add(v_k_2837_, v_k_2835_);
lean_dec(v_k_2837_);
v___x_2842_ = lean_nat_to_int(v_c_2836_);
v___x_2843_ = lean_int_emod(v___x_2841_, v___x_2842_);
lean_dec(v___x_2842_);
lean_dec(v___x_2841_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2843_);
v___x_2845_ = v___x_2839_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
else
{
lean_object* v_k_2848_; lean_object* v_v_2849_; lean_object* v_p_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2858_; 
v_k_2848_ = lean_ctor_get(v_p_2834_, 0);
v_v_2849_ = lean_ctor_get(v_p_2834_, 1);
v_p_2850_ = lean_ctor_get(v_p_2834_, 2);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_p_2834_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2852_ = v_p_2834_;
v_isShared_2853_ = v_isSharedCheck_2858_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_p_2850_);
lean_inc(v_v_2849_);
lean_inc(v_k_2848_);
lean_dec(v_p_2834_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2858_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2854_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2850_, v_k_2835_, v_c_2836_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 2, v___x_2854_);
v___x_2856_ = v___x_2852_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_k_2848_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_v_2849_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_addConstC___boxed(lean_object* v_p_2859_, lean_object* v_k_2860_, lean_object* v_c_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_2859_, v_k_2860_, v_c_2861_);
lean_dec(v_k_2860_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC_go(lean_object* v_m_2863_, lean_object* v_c_2864_, lean_object* v_k_2865_, lean_object* v_a_2866_){
_start:
{
if (lean_obj_tag(v_a_2866_) == 0)
{
lean_object* v___x_2867_; 
lean_dec(v_c_2864_);
v___x_2867_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2867_, 0, v_k_2865_);
lean_ctor_set(v___x_2867_, 1, v_m_2863_);
lean_ctor_set(v___x_2867_, 2, v_a_2866_);
return v___x_2867_;
}
else
{
lean_object* v_k_2868_; lean_object* v_v_2869_; lean_object* v_p_2870_; uint8_t v___x_2871_; 
v_k_2868_ = lean_ctor_get(v_a_2866_, 0);
v_v_2869_ = lean_ctor_get(v_a_2866_, 1);
v_p_2870_ = lean_ctor_get(v_a_2866_, 2);
v___x_2871_ = l_Lean_Grind_CommRing_Mon_grevlex(v_m_2863_, v_v_2869_);
switch(v___x_2871_)
{
case 0:
{
lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2879_; 
lean_inc_ref(v_p_2870_);
lean_inc(v_v_2869_);
lean_inc(v_k_2868_);
v_isSharedCheck_2879_ = !lean_is_exclusive(v_a_2866_);
if (v_isSharedCheck_2879_ == 0)
{
lean_object* v_unused_2880_; lean_object* v_unused_2881_; lean_object* v_unused_2882_; 
v_unused_2880_ = lean_ctor_get(v_a_2866_, 2);
lean_dec(v_unused_2880_);
v_unused_2881_ = lean_ctor_get(v_a_2866_, 1);
lean_dec(v_unused_2881_);
v_unused_2882_ = lean_ctor_get(v_a_2866_, 0);
lean_dec(v_unused_2882_);
v___x_2873_ = v_a_2866_;
v_isShared_2874_ = v_isSharedCheck_2879_;
goto v_resetjp_2872_;
}
else
{
lean_dec(v_a_2866_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2879_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2875_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_2863_, v_c_2864_, v_k_2865_, v_p_2870_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 2, v___x_2875_);
v___x_2877_ = v___x_2873_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_k_2868_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_v_2869_);
lean_ctor_set(v_reuseFailAlloc_2878_, 2, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
case 1:
{
lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2894_; 
lean_inc_ref(v_p_2870_);
lean_inc(v_k_2868_);
v_isSharedCheck_2894_ = !lean_is_exclusive(v_a_2866_);
if (v_isSharedCheck_2894_ == 0)
{
lean_object* v_unused_2895_; lean_object* v_unused_2896_; lean_object* v_unused_2897_; 
v_unused_2895_ = lean_ctor_get(v_a_2866_, 2);
lean_dec(v_unused_2895_);
v_unused_2896_ = lean_ctor_get(v_a_2866_, 1);
lean_dec(v_unused_2896_);
v_unused_2897_ = lean_ctor_get(v_a_2866_, 0);
lean_dec(v_unused_2897_);
v___x_2884_ = v_a_2866_;
v_isShared_2885_ = v_isSharedCheck_2894_;
goto v_resetjp_2883_;
}
else
{
lean_dec(v_a_2866_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2894_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v_k_x27_x27_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v___x_2886_ = lean_int_add(v_k_2865_, v_k_2868_);
lean_dec(v_k_2868_);
lean_dec(v_k_2865_);
v___x_2887_ = lean_nat_to_int(v_c_2864_);
v_k_x27_x27_2888_ = lean_int_emod(v___x_2886_, v___x_2887_);
lean_dec(v___x_2887_);
lean_dec(v___x_2886_);
v___x_2889_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2890_ = lean_int_dec_eq(v_k_x27_x27_2888_, v___x_2889_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2892_; 
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 1, v_m_2863_);
lean_ctor_set(v___x_2884_, 0, v_k_x27_x27_2888_);
v___x_2892_ = v___x_2884_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_k_x27_x27_2888_);
lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_m_2863_);
lean_ctor_set(v_reuseFailAlloc_2893_, 2, v_p_2870_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
else
{
lean_dec(v_k_x27_x27_2888_);
lean_del_object(v___x_2884_);
lean_dec(v_m_2863_);
return v_p_2870_;
}
}
}
default: 
{
lean_object* v___x_2898_; 
lean_dec(v_c_2864_);
v___x_2898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2898_, 0, v_k_2865_);
lean_ctor_set(v___x_2898_, 1, v_m_2863_);
lean_ctor_set(v___x_2898_, 2, v_a_2866_);
return v___x_2898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC(lean_object* v_k_2899_, lean_object* v_m_2900_, lean_object* v_p_2901_, lean_object* v_c_2902_){
_start:
{
lean_object* v___x_2903_; lean_object* v_k_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
lean_inc(v_c_2902_);
v___x_2903_ = lean_nat_to_int(v_c_2902_);
v_k_2904_ = lean_int_emod(v_k_2899_, v___x_2903_);
lean_dec(v___x_2903_);
v___x_2905_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2906_ = lean_int_dec_eq(v_k_2904_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; 
v___x_2907_ = l_Lean_Grind_CommRing_Poly_insertC_go(v_m_2900_, v_c_2902_, v_k_2904_, v_p_2901_);
return v___x_2907_;
}
else
{
lean_dec(v_k_2904_);
lean_dec(v_c_2902_);
lean_dec(v_m_2900_);
return v_p_2901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_insertC___boxed(lean_object* v_k_2908_, lean_object* v_m_2909_, lean_object* v_p_2910_, lean_object* v_c_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_Grind_CommRing_Poly_insertC(v_k_2908_, v_m_2909_, v_p_2910_, v_c_2911_);
lean_dec(v_k_2908_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go(lean_object* v_k_2913_, lean_object* v_c_2914_, lean_object* v_a_2915_){
_start:
{
if (lean_obj_tag(v_a_2915_) == 0)
{
lean_object* v_k_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2926_; 
v_k_2916_ = lean_ctor_get(v_a_2915_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_a_2915_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2918_ = v_a_2915_;
v_isShared_2919_ = v_isSharedCheck_2926_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_k_2916_);
lean_dec(v_a_2915_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2926_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2924_; 
v___x_2920_ = lean_int_mul(v_k_2913_, v_k_2916_);
lean_dec(v_k_2916_);
v___x_2921_ = lean_nat_to_int(v_c_2914_);
v___x_2922_ = lean_int_emod(v___x_2920_, v___x_2921_);
lean_dec(v___x_2921_);
lean_dec(v___x_2920_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v___x_2922_);
v___x_2924_ = v___x_2918_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
else
{
lean_object* v_k_2927_; lean_object* v_v_2928_; lean_object* v_p_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2943_; 
v_k_2927_ = lean_ctor_get(v_a_2915_, 0);
v_v_2928_ = lean_ctor_get(v_a_2915_, 1);
v_p_2929_ = lean_ctor_get(v_a_2915_, 2);
v_isSharedCheck_2943_ = !lean_is_exclusive(v_a_2915_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2931_ = v_a_2915_;
v_isShared_2932_ = v_isSharedCheck_2943_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_p_2929_);
lean_inc(v_v_2928_);
lean_inc(v_k_2927_);
lean_dec(v_a_2915_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2943_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v_k_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v___x_2933_ = lean_int_mul(v_k_2913_, v_k_2927_);
lean_dec(v_k_2927_);
lean_inc(v_c_2914_);
v___x_2934_ = lean_nat_to_int(v_c_2914_);
v_k_2935_ = lean_int_emod(v___x_2933_, v___x_2934_);
lean_dec(v___x_2934_);
lean_dec(v___x_2933_);
v___x_2936_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2937_ = lean_int_dec_eq(v_k_2935_, v___x_2936_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2938_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_2913_, v_c_2914_, v_p_2929_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 2, v___x_2938_);
lean_ctor_set(v___x_2931_, 0, v_k_2935_);
v___x_2940_ = v___x_2931_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_k_2935_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_v_2928_);
lean_ctor_set(v_reuseFailAlloc_2941_, 2, v___x_2938_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
else
{
lean_dec(v_k_2935_);
lean_del_object(v___x_2931_);
lean_dec(v_v_2928_);
v_a_2915_ = v_p_2929_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC_go___boxed(lean_object* v_k_2944_, lean_object* v_c_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_2944_, v_c_2945_, v_a_2946_);
lean_dec(v_k_2944_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object* v_k_2948_, lean_object* v_p_2949_, lean_object* v_c_2950_){
_start:
{
lean_object* v___x_2951_; lean_object* v_k_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
lean_inc(v_c_2950_);
v___x_2951_ = lean_nat_to_int(v_c_2950_);
v_k_2952_ = lean_int_emod(v_k_2948_, v___x_2951_);
lean_dec(v___x_2951_);
v___x_2953_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2954_ = lean_int_dec_eq(v_k_2952_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; uint8_t v___x_2956_; 
v___x_2955_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_2956_ = lean_int_dec_eq(v_k_2952_, v___x_2955_);
lean_dec(v_k_2952_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Grind_CommRing_Poly_mulConstC_go(v_k_2948_, v_c_2950_, v_p_2949_);
return v___x_2957_;
}
else
{
lean_dec(v_c_2950_);
return v_p_2949_;
}
}
else
{
lean_object* v___x_2958_; 
lean_dec(v_k_2952_);
lean_dec(v_c_2950_);
lean_dec_ref(v_p_2949_);
v___x_2958_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConstC___boxed(lean_object* v_k_2959_, lean_object* v_p_2960_, lean_object* v_c_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_2959_, v_p_2960_, v_c_2961_);
lean_dec(v_k_2959_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go(lean_object* v_k_2963_, lean_object* v_m_2964_, lean_object* v_c_2965_, lean_object* v_a_2966_){
_start:
{
if (lean_obj_tag(v_a_2966_) == 0)
{
lean_object* v_k_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v_k_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v_k_2967_ = lean_ctor_get(v_a_2966_, 0);
lean_inc(v_k_2967_);
lean_dec_ref_known(v_a_2966_, 1);
v___x_2968_ = lean_int_mul(v_k_2963_, v_k_2967_);
lean_dec(v_k_2967_);
v___x_2969_ = lean_nat_to_int(v_c_2965_);
v_k_2970_ = lean_int_emod(v___x_2968_, v___x_2969_);
lean_dec(v___x_2969_);
lean_dec(v___x_2968_);
v___x_2971_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2972_ = lean_int_dec_eq(v_k_2970_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_2974_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2974_, 0, v_k_2970_);
lean_ctor_set(v___x_2974_, 1, v_m_2964_);
lean_ctor_set(v___x_2974_, 2, v___x_2973_);
return v___x_2974_;
}
else
{
lean_object* v___x_2975_; 
lean_dec(v_k_2970_);
lean_dec(v_m_2964_);
v___x_2975_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_2975_;
}
}
else
{
lean_object* v_k_2976_; lean_object* v_v_2977_; lean_object* v_p_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2993_; 
v_k_2976_ = lean_ctor_get(v_a_2966_, 0);
v_v_2977_ = lean_ctor_get(v_a_2966_, 1);
v_p_2978_ = lean_ctor_get(v_a_2966_, 2);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_a_2966_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2980_ = v_a_2966_;
v_isShared_2981_ = v_isSharedCheck_2993_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_p_2978_);
lean_inc(v_v_2977_);
lean_inc(v_k_2976_);
lean_dec(v_a_2966_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2993_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v_k_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; 
v___x_2982_ = lean_int_mul(v_k_2963_, v_k_2976_);
lean_dec(v_k_2976_);
lean_inc(v_c_2965_);
v___x_2983_ = lean_nat_to_int(v_c_2965_);
v_k_2984_ = lean_int_emod(v___x_2982_, v___x_2983_);
lean_dec(v___x_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_2986_ = lean_int_dec_eq(v_k_2984_, v___x_2985_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
lean_inc(v_m_2964_);
v___x_2987_ = l_Lean_Grind_CommRing_Mon_mul(v_m_2964_, v_v_2977_);
v___x_2988_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_2963_, v_m_2964_, v_c_2965_, v_p_2978_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 2, v___x_2988_);
lean_ctor_set(v___x_2980_, 1, v___x_2987_);
lean_ctor_set(v___x_2980_, 0, v_k_2984_);
v___x_2990_ = v___x_2980_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_k_2984_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_2991_, 2, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
else
{
lean_dec(v_k_2984_);
lean_del_object(v___x_2980_);
lean_dec(v_v_2977_);
v_a_2966_ = v_p_2978_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC_go___boxed(lean_object* v_k_2994_, lean_object* v_m_2995_, lean_object* v_c_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_2994_, v_m_2995_, v_c_2996_, v_a_2997_);
lean_dec(v_k_2994_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object* v_k_2999_, lean_object* v_m_3000_, lean_object* v_p_3001_, lean_object* v_c_3002_){
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
lean_object* v___x_3009_; 
lean_dec(v_k_3004_);
v___x_3009_ = l_Lean_Grind_CommRing_Poly_mulMonC_go(v_k_2999_, v_m_3000_, v_c_3002_, v_p_3001_);
return v___x_3009_;
}
else
{
lean_object* v___x_3010_; 
lean_dec(v_m_3000_);
v___x_3010_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3004_, v_p_3001_, v_c_3002_);
lean_dec(v_k_3004_);
return v___x_3010_;
}
}
else
{
lean_object* v___x_3011_; 
lean_dec(v_k_3004_);
lean_dec(v_c_3002_);
lean_dec_ref(v_p_3001_);
lean_dec(v_m_3000_);
v___x_3011_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC___boxed(lean_object* v_k_3012_, lean_object* v_m_3013_, lean_object* v_p_3014_, lean_object* v_c_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_3012_, v_m_3013_, v_p_3014_, v_c_3015_);
lean_dec(v_k_3012_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(lean_object* v_k_3017_, lean_object* v_m_3018_, lean_object* v_c_3019_, lean_object* v_p_3020_, lean_object* v_acc_3021_){
_start:
{
if (lean_obj_tag(v_p_3020_) == 0)
{
lean_object* v_k_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v_k_3022_ = lean_ctor_get(v_p_3020_, 0);
lean_inc(v_k_3022_);
lean_dec_ref_known(v_p_3020_, 1);
v___x_3023_ = lean_int_mul(v_k_3017_, v_k_3022_);
lean_dec(v_k_3022_);
v___x_3024_ = lean_nat_to_int(v_c_3019_);
v___x_3025_ = lean_int_emod(v___x_3023_, v___x_3024_);
lean_dec(v___x_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = l_Lean_Grind_CommRing_Poly_insert(v___x_3025_, v_m_3018_, v_acc_3021_);
return v___x_3026_;
}
else
{
lean_object* v_k_3027_; lean_object* v_v_3028_; lean_object* v_p_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v_k_3027_ = lean_ctor_get(v_p_3020_, 0);
lean_inc(v_k_3027_);
v_v_3028_ = lean_ctor_get(v_p_3020_, 1);
lean_inc(v_v_3028_);
v_p_3029_ = lean_ctor_get(v_p_3020_, 2);
lean_inc_ref(v_p_3029_);
lean_dec_ref_known(v_p_3020_, 3);
v___x_3030_ = lean_int_mul(v_k_3017_, v_k_3027_);
lean_dec(v_k_3027_);
lean_inc(v_c_3019_);
v___x_3031_ = lean_nat_to_int(v_c_3019_);
v___x_3032_ = lean_int_emod(v___x_3030_, v___x_3031_);
lean_dec(v___x_3031_);
lean_dec(v___x_3030_);
lean_inc(v_m_3018_);
v___x_3033_ = l_Lean_Grind_CommRing_Mon_mul__nc(v_m_3018_, v_v_3028_);
v___x_3034_ = l_Lean_Grind_CommRing_Poly_insert(v___x_3032_, v___x_3033_, v_acc_3021_);
v_p_3020_ = v_p_3029_;
v_acc_3021_ = v___x_3034_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc_go___boxed(lean_object* v_k_3036_, lean_object* v_m_3037_, lean_object* v_c_3038_, lean_object* v_p_3039_, lean_object* v_acc_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_3036_, v_m_3037_, v_c_3038_, v_p_3039_, v_acc_3040_);
lean_dec(v_k_3036_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc(lean_object* v_k_3042_, lean_object* v_m_3043_, lean_object* v_p_3044_, lean_object* v_c_3045_){
_start:
{
lean_object* v___x_3046_; lean_object* v_k_3047_; lean_object* v___x_3048_; uint8_t v___x_3049_; 
lean_inc(v_c_3045_);
v___x_3046_ = lean_nat_to_int(v_c_3045_);
v_k_3047_ = lean_int_emod(v_k_3042_, v___x_3046_);
lean_dec(v___x_3046_);
v___x_3048_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3049_ = lean_int_dec_eq(v_k_3047_, v___x_3048_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = lean_box(0);
v___x_3051_ = l_Lean_Grind_CommRing_instBEqMon_beq(v_m_3043_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
lean_dec(v_k_3047_);
v___x_3052_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3053_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc_go(v_k_3042_, v_m_3043_, v_c_3045_, v_p_3044_, v___x_3052_);
return v___x_3053_;
}
else
{
lean_object* v___x_3054_; 
lean_dec(v_m_3043_);
v___x_3054_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3047_, v_p_3044_, v_c_3045_);
lean_dec(v_k_3047_);
return v___x_3054_;
}
}
else
{
lean_object* v___x_3055_; 
lean_dec(v_k_3047_);
lean_dec(v_c_3045_);
lean_dec_ref(v_p_3044_);
lean_dec(v_m_3043_);
v___x_3055_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
return v___x_3055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMonC__nc___boxed(lean_object* v_k_3056_, lean_object* v_m_3057_, lean_object* v_p_3058_, lean_object* v_c_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3056_, v_m_3057_, v_p_3058_, v_c_3059_);
lean_dec(v_k_3056_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combineC(lean_object* v_p_u2081_3061_, lean_object* v_p_u2082_3062_, lean_object* v_c_3063_){
_start:
{
if (lean_obj_tag(v_p_u2081_3061_) == 0)
{
if (lean_obj_tag(v_p_u2082_3062_) == 0)
{
lean_object* v_k_3064_; lean_object* v_k_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3075_; 
v_k_3064_ = lean_ctor_get(v_p_u2081_3061_, 0);
lean_inc(v_k_3064_);
lean_dec_ref_known(v_p_u2081_3061_, 1);
v_k_3065_ = lean_ctor_get(v_p_u2082_3062_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v_p_u2082_3062_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3067_ = v_p_u2082_3062_;
v_isShared_3068_ = v_isSharedCheck_3075_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_k_3065_);
lean_dec(v_p_u2082_3062_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3075_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3069_ = lean_int_add(v_k_3064_, v_k_3065_);
lean_dec(v_k_3065_);
lean_dec(v_k_3064_);
v___x_3070_ = lean_nat_to_int(v_c_3063_);
v___x_3071_ = lean_int_emod(v___x_3069_, v___x_3070_);
lean_dec(v___x_3070_);
lean_dec(v___x_3069_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set(v___x_3067_, 0, v___x_3071_);
v___x_3073_ = v___x_3067_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
else
{
lean_object* v_k_3076_; lean_object* v___x_3077_; 
v_k_3076_ = lean_ctor_get(v_p_u2081_3061_, 0);
lean_inc(v_k_3076_);
lean_dec_ref_known(v_p_u2081_3061_, 1);
v___x_3077_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2082_3062_, v_k_3076_, v_c_3063_);
lean_dec(v_k_3076_);
return v___x_3077_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_3062_) == 0)
{
lean_object* v_k_3078_; lean_object* v___x_3079_; 
v_k_3078_ = lean_ctor_get(v_p_u2082_3062_, 0);
lean_inc(v_k_3078_);
lean_dec_ref_known(v_p_u2082_3062_, 1);
v___x_3079_ = l_Lean_Grind_CommRing_Poly_addConstC(v_p_u2081_3061_, v_k_3078_, v_c_3063_);
lean_dec(v_k_3078_);
return v___x_3079_;
}
else
{
lean_object* v_k_3080_; lean_object* v_v_3081_; lean_object* v_p_3082_; lean_object* v_k_3083_; lean_object* v_v_3084_; lean_object* v_p_3085_; uint8_t v___x_3086_; 
v_k_3080_ = lean_ctor_get(v_p_u2081_3061_, 0);
v_v_3081_ = lean_ctor_get(v_p_u2081_3061_, 1);
v_p_3082_ = lean_ctor_get(v_p_u2081_3061_, 2);
v_k_3083_ = lean_ctor_get(v_p_u2082_3062_, 0);
v_v_3084_ = lean_ctor_get(v_p_u2082_3062_, 1);
v_p_3085_ = lean_ctor_get(v_p_u2082_3062_, 2);
v___x_3086_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_3081_, v_v_3084_);
switch(v___x_3086_)
{
case 0:
{
lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3094_; 
lean_inc_ref(v_p_3085_);
lean_inc(v_v_3084_);
lean_inc(v_k_3083_);
v_isSharedCheck_3094_ = !lean_is_exclusive(v_p_u2082_3062_);
if (v_isSharedCheck_3094_ == 0)
{
lean_object* v_unused_3095_; lean_object* v_unused_3096_; lean_object* v_unused_3097_; 
v_unused_3095_ = lean_ctor_get(v_p_u2082_3062_, 2);
lean_dec(v_unused_3095_);
v_unused_3096_ = lean_ctor_get(v_p_u2082_3062_, 1);
lean_dec(v_unused_3096_);
v_unused_3097_ = lean_ctor_get(v_p_u2082_3062_, 0);
lean_dec(v_unused_3097_);
v___x_3088_ = v_p_u2082_3062_;
v_isShared_3089_ = v_isSharedCheck_3094_;
goto v_resetjp_3087_;
}
else
{
lean_dec(v_p_u2082_3062_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3094_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3090_; lean_object* v___x_3092_; 
v___x_3090_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_u2081_3061_, v_p_3085_, v_c_3063_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 2, v___x_3090_);
v___x_3092_ = v___x_3088_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_k_3083_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_v_3084_);
lean_ctor_set(v_reuseFailAlloc_3093_, 2, v___x_3090_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
case 1:
{
lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3111_; 
lean_inc_ref(v_p_3085_);
lean_inc(v_k_3083_);
lean_inc_ref(v_p_3082_);
lean_inc(v_v_3081_);
lean_inc(v_k_3080_);
lean_dec_ref_known(v_p_u2081_3061_, 3);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_p_u2082_3062_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; lean_object* v_unused_3113_; lean_object* v_unused_3114_; 
v_unused_3112_ = lean_ctor_get(v_p_u2082_3062_, 2);
lean_dec(v_unused_3112_);
v_unused_3113_ = lean_ctor_get(v_p_u2082_3062_, 1);
lean_dec(v_unused_3113_);
v_unused_3114_ = lean_ctor_get(v_p_u2082_3062_, 0);
lean_dec(v_unused_3114_);
v___x_3099_ = v_p_u2082_3062_;
v_isShared_3100_ = v_isSharedCheck_3111_;
goto v_resetjp_3098_;
}
else
{
lean_dec(v_p_u2082_3062_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3111_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v_k_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3101_ = lean_int_add(v_k_3080_, v_k_3083_);
lean_dec(v_k_3083_);
lean_dec(v_k_3080_);
lean_inc(v_c_3063_);
v___x_3102_ = lean_nat_to_int(v_c_3063_);
v_k_3103_ = lean_int_emod(v___x_3101_, v___x_3102_);
lean_dec(v___x_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3105_ = lean_int_dec_eq(v_k_3103_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3106_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3082_, v_p_3085_, v_c_3063_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 2, v___x_3106_);
lean_ctor_set(v___x_3099_, 1, v_v_3081_);
lean_ctor_set(v___x_3099_, 0, v_k_3103_);
v___x_3108_ = v___x_3099_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_k_3103_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
else
{
lean_dec(v_k_3103_);
lean_del_object(v___x_3099_);
lean_dec(v_v_3081_);
v_p_u2081_3061_ = v_p_3082_;
v_p_u2082_3062_ = v_p_3085_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3122_; 
lean_inc_ref(v_p_3082_);
lean_inc(v_v_3081_);
lean_inc(v_k_3080_);
v_isSharedCheck_3122_ = !lean_is_exclusive(v_p_u2081_3061_);
if (v_isSharedCheck_3122_ == 0)
{
lean_object* v_unused_3123_; lean_object* v_unused_3124_; lean_object* v_unused_3125_; 
v_unused_3123_ = lean_ctor_get(v_p_u2081_3061_, 2);
lean_dec(v_unused_3123_);
v_unused_3124_ = lean_ctor_get(v_p_u2081_3061_, 1);
lean_dec(v_unused_3124_);
v_unused_3125_ = lean_ctor_get(v_p_u2081_3061_, 0);
lean_dec(v_unused_3125_);
v___x_3116_ = v_p_u2081_3061_;
v_isShared_3117_ = v_isSharedCheck_3122_;
goto v_resetjp_3115_;
}
else
{
lean_dec(v_p_u2081_3061_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3122_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3118_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_3082_, v_p_u2082_3062_, v_c_3063_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 2, v___x_3118_);
v___x_3120_ = v___x_3116_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object* v_p_u2081_3126_, lean_object* v_p_u2082_3127_, lean_object* v_h__1_3128_, lean_object* v_h__2_3129_, lean_object* v_h__3_3130_, lean_object* v_h__4_3131_){
_start:
{
if (lean_obj_tag(v_p_u2081_3126_) == 0)
{
lean_dec(v_h__4_3131_);
lean_dec(v_h__3_3130_);
if (lean_obj_tag(v_p_u2082_3127_) == 0)
{
lean_object* v_k_3132_; lean_object* v_k_3133_; lean_object* v___x_3134_; 
lean_dec(v_h__2_3129_);
v_k_3132_ = lean_ctor_get(v_p_u2081_3126_, 0);
lean_inc(v_k_3132_);
lean_dec_ref_known(v_p_u2081_3126_, 1);
v_k_3133_ = lean_ctor_get(v_p_u2082_3127_, 0);
lean_inc(v_k_3133_);
lean_dec_ref_known(v_p_u2082_3127_, 1);
v___x_3134_ = lean_apply_2(v_h__1_3128_, v_k_3132_, v_k_3133_);
return v___x_3134_;
}
else
{
lean_object* v_k_3135_; lean_object* v_k_3136_; lean_object* v_v_3137_; lean_object* v_p_3138_; lean_object* v___x_3139_; 
lean_dec(v_h__1_3128_);
v_k_3135_ = lean_ctor_get(v_p_u2081_3126_, 0);
lean_inc(v_k_3135_);
lean_dec_ref_known(v_p_u2081_3126_, 1);
v_k_3136_ = lean_ctor_get(v_p_u2082_3127_, 0);
lean_inc(v_k_3136_);
v_v_3137_ = lean_ctor_get(v_p_u2082_3127_, 1);
lean_inc(v_v_3137_);
v_p_3138_ = lean_ctor_get(v_p_u2082_3127_, 2);
lean_inc_ref(v_p_3138_);
lean_dec_ref_known(v_p_u2082_3127_, 3);
v___x_3139_ = lean_apply_4(v_h__2_3129_, v_k_3135_, v_k_3136_, v_v_3137_, v_p_3138_);
return v___x_3139_;
}
}
else
{
lean_dec(v_h__2_3129_);
lean_dec(v_h__1_3128_);
if (lean_obj_tag(v_p_u2082_3127_) == 0)
{
lean_object* v_k_3140_; lean_object* v_v_3141_; lean_object* v_p_3142_; lean_object* v_k_3143_; lean_object* v___x_3144_; 
lean_dec(v_h__4_3131_);
v_k_3140_ = lean_ctor_get(v_p_u2081_3126_, 0);
lean_inc(v_k_3140_);
v_v_3141_ = lean_ctor_get(v_p_u2081_3126_, 1);
lean_inc(v_v_3141_);
v_p_3142_ = lean_ctor_get(v_p_u2081_3126_, 2);
lean_inc_ref(v_p_3142_);
lean_dec_ref_known(v_p_u2081_3126_, 3);
v_k_3143_ = lean_ctor_get(v_p_u2082_3127_, 0);
lean_inc(v_k_3143_);
lean_dec_ref_known(v_p_u2082_3127_, 1);
v___x_3144_ = lean_apply_4(v_h__3_3130_, v_k_3140_, v_v_3141_, v_p_3142_, v_k_3143_);
return v___x_3144_;
}
else
{
lean_object* v_k_3145_; lean_object* v_v_3146_; lean_object* v_p_3147_; lean_object* v_k_3148_; lean_object* v_v_3149_; lean_object* v_p_3150_; lean_object* v___x_3151_; 
lean_dec(v_h__3_3130_);
v_k_3145_ = lean_ctor_get(v_p_u2081_3126_, 0);
lean_inc(v_k_3145_);
v_v_3146_ = lean_ctor_get(v_p_u2081_3126_, 1);
lean_inc(v_v_3146_);
v_p_3147_ = lean_ctor_get(v_p_u2081_3126_, 2);
lean_inc_ref(v_p_3147_);
lean_dec_ref_known(v_p_u2081_3126_, 3);
v_k_3148_ = lean_ctor_get(v_p_u2082_3127_, 0);
lean_inc(v_k_3148_);
v_v_3149_ = lean_ctor_get(v_p_u2082_3127_, 1);
lean_inc(v_v_3149_);
v_p_3150_ = lean_ctor_get(v_p_u2082_3127_, 2);
lean_inc_ref(v_p_3150_);
lean_dec_ref_known(v_p_u2082_3127_, 3);
v___x_3151_ = lean_apply_6(v_h__4_3131_, v_k_3145_, v_v_3146_, v_p_3147_, v_k_3148_, v_v_3149_, v_p_3150_);
return v___x_3151_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object* v_motive_3152_, lean_object* v_p_u2081_3153_, lean_object* v_p_u2082_3154_, lean_object* v_h__1_3155_, lean_object* v_h__2_3156_, lean_object* v_h__3_3157_, lean_object* v_h__4_3158_){
_start:
{
if (lean_obj_tag(v_p_u2081_3153_) == 0)
{
lean_dec(v_h__4_3158_);
lean_dec(v_h__3_3157_);
if (lean_obj_tag(v_p_u2082_3154_) == 0)
{
lean_object* v_k_3159_; lean_object* v_k_3160_; lean_object* v___x_3161_; 
lean_dec(v_h__2_3156_);
v_k_3159_ = lean_ctor_get(v_p_u2081_3153_, 0);
lean_inc(v_k_3159_);
lean_dec_ref_known(v_p_u2081_3153_, 1);
v_k_3160_ = lean_ctor_get(v_p_u2082_3154_, 0);
lean_inc(v_k_3160_);
lean_dec_ref_known(v_p_u2082_3154_, 1);
v___x_3161_ = lean_apply_2(v_h__1_3155_, v_k_3159_, v_k_3160_);
return v___x_3161_;
}
else
{
lean_object* v_k_3162_; lean_object* v_k_3163_; lean_object* v_v_3164_; lean_object* v_p_3165_; lean_object* v___x_3166_; 
lean_dec(v_h__1_3155_);
v_k_3162_ = lean_ctor_get(v_p_u2081_3153_, 0);
lean_inc(v_k_3162_);
lean_dec_ref_known(v_p_u2081_3153_, 1);
v_k_3163_ = lean_ctor_get(v_p_u2082_3154_, 0);
lean_inc(v_k_3163_);
v_v_3164_ = lean_ctor_get(v_p_u2082_3154_, 1);
lean_inc(v_v_3164_);
v_p_3165_ = lean_ctor_get(v_p_u2082_3154_, 2);
lean_inc_ref(v_p_3165_);
lean_dec_ref_known(v_p_u2082_3154_, 3);
v___x_3166_ = lean_apply_4(v_h__2_3156_, v_k_3162_, v_k_3163_, v_v_3164_, v_p_3165_);
return v___x_3166_;
}
}
else
{
lean_dec(v_h__2_3156_);
lean_dec(v_h__1_3155_);
if (lean_obj_tag(v_p_u2082_3154_) == 0)
{
lean_object* v_k_3167_; lean_object* v_v_3168_; lean_object* v_p_3169_; lean_object* v_k_3170_; lean_object* v___x_3171_; 
lean_dec(v_h__4_3158_);
v_k_3167_ = lean_ctor_get(v_p_u2081_3153_, 0);
lean_inc(v_k_3167_);
v_v_3168_ = lean_ctor_get(v_p_u2081_3153_, 1);
lean_inc(v_v_3168_);
v_p_3169_ = lean_ctor_get(v_p_u2081_3153_, 2);
lean_inc_ref(v_p_3169_);
lean_dec_ref_known(v_p_u2081_3153_, 3);
v_k_3170_ = lean_ctor_get(v_p_u2082_3154_, 0);
lean_inc(v_k_3170_);
lean_dec_ref_known(v_p_u2082_3154_, 1);
v___x_3171_ = lean_apply_4(v_h__3_3157_, v_k_3167_, v_v_3168_, v_p_3169_, v_k_3170_);
return v___x_3171_;
}
else
{
lean_object* v_k_3172_; lean_object* v_v_3173_; lean_object* v_p_3174_; lean_object* v_k_3175_; lean_object* v_v_3176_; lean_object* v_p_3177_; lean_object* v___x_3178_; 
lean_dec(v_h__3_3157_);
v_k_3172_ = lean_ctor_get(v_p_u2081_3153_, 0);
lean_inc(v_k_3172_);
v_v_3173_ = lean_ctor_get(v_p_u2081_3153_, 1);
lean_inc(v_v_3173_);
v_p_3174_ = lean_ctor_get(v_p_u2081_3153_, 2);
lean_inc_ref(v_p_3174_);
lean_dec_ref_known(v_p_u2081_3153_, 3);
v_k_3175_ = lean_ctor_get(v_p_u2082_3154_, 0);
lean_inc(v_k_3175_);
v_v_3176_ = lean_ctor_get(v_p_u2082_3154_, 1);
lean_inc(v_v_3176_);
v_p_3177_ = lean_ctor_get(v_p_u2082_3154_, 2);
lean_inc_ref(v_p_3177_);
lean_dec_ref_known(v_p_u2082_3154_, 3);
v___x_3178_ = lean_apply_6(v_h__4_3158_, v_k_3172_, v_v_3173_, v_p_3174_, v_k_3175_, v_v_3176_, v_p_3177_);
return v___x_3178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC_go(lean_object* v_p_u2082_3179_, lean_object* v_c_3180_, lean_object* v_p_u2081_3181_, lean_object* v_acc_3182_){
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
v___x_3189_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_3186_, v_v_3187_, v_p_u2082_3179_, v_c_3180_);
lean_dec(v_k_3186_);
v___x_3190_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3182_, v___x_3189_, v_c_3180_);
v_p_u2081_3181_ = v_p_3188_;
v_acc_3182_ = v___x_3190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC(lean_object* v_p_u2081_3192_, lean_object* v_p_u2082_3193_, lean_object* v_c_3194_){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3196_ = l_Lean_Grind_CommRing_Poly_mulC_go(v_p_u2082_3193_, v_c_3194_, v_p_u2081_3192_, v___x_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc_go(lean_object* v_p_u2082_3197_, lean_object* v_c_3198_, lean_object* v_p_u2081_3199_, lean_object* v_acc_3200_){
_start:
{
if (lean_obj_tag(v_p_u2081_3199_) == 0)
{
lean_object* v_k_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v_k_3201_ = lean_ctor_get(v_p_u2081_3199_, 0);
lean_inc(v_k_3201_);
lean_dec_ref_known(v_p_u2081_3199_, 1);
lean_inc(v_c_3198_);
v___x_3202_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_3201_, v_p_u2082_3197_, v_c_3198_);
lean_dec(v_k_3201_);
v___x_3203_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3200_, v___x_3202_, v_c_3198_);
return v___x_3203_;
}
else
{
lean_object* v_k_3204_; lean_object* v_v_3205_; lean_object* v_p_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v_k_3204_ = lean_ctor_get(v_p_u2081_3199_, 0);
lean_inc(v_k_3204_);
v_v_3205_ = lean_ctor_get(v_p_u2081_3199_, 1);
lean_inc(v_v_3205_);
v_p_3206_ = lean_ctor_get(v_p_u2081_3199_, 2);
lean_inc_ref(v_p_3206_);
lean_dec_ref_known(v_p_u2081_3199_, 3);
lean_inc_n(v_c_3198_, 2);
lean_inc_ref(v_p_u2082_3197_);
v___x_3207_ = l_Lean_Grind_CommRing_Poly_mulMonC__nc(v_k_3204_, v_v_3205_, v_p_u2082_3197_, v_c_3198_);
lean_dec(v_k_3204_);
v___x_3208_ = l_Lean_Grind_CommRing_Poly_combineC(v_acc_3200_, v___x_3207_, v_c_3198_);
v_p_u2081_3199_ = v_p_3206_;
v_acc_3200_ = v___x_3208_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulC__nc(lean_object* v_p_u2081_3210_, lean_object* v_p_u2082_3211_, lean_object* v_c_3212_){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedPoly_default___closed__0);
v___x_3214_ = l_Lean_Grind_CommRing_Poly_mulC__nc_go(v_p_u2082_3211_, v_c_3212_, v_p_u2081_3210_, v___x_3213_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC(lean_object* v_p_3215_, lean_object* v_k_3216_, lean_object* v_c_3217_){
_start:
{
lean_object* v_zero_3218_; uint8_t v_isZero_3219_; 
v_zero_3218_ = lean_unsigned_to_nat(0u);
v_isZero_3219_ = lean_nat_dec_eq(v_k_3216_, v_zero_3218_);
if (v_isZero_3219_ == 1)
{
lean_object* v___x_3220_; 
lean_dec(v_c_3217_);
lean_dec_ref(v_p_3215_);
v___x_3220_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3220_;
}
else
{
lean_object* v_one_3221_; lean_object* v_n_3222_; uint8_t v___x_3223_; 
v_one_3221_ = lean_unsigned_to_nat(1u);
v_n_3222_ = lean_nat_sub(v_k_3216_, v_one_3221_);
v___x_3223_ = lean_nat_dec_eq(v_n_3222_, v_zero_3218_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_inc(v_c_3217_);
lean_inc_ref(v_p_3215_);
v___x_3224_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3215_, v_n_3222_, v_c_3217_);
lean_dec(v_n_3222_);
v___x_3225_ = l_Lean_Grind_CommRing_Poly_mulC(v_p_3215_, v___x_3224_, v_c_3217_);
return v___x_3225_;
}
else
{
lean_dec(v_n_3222_);
lean_dec(v_c_3217_);
return v_p_3215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC___boxed(lean_object* v_p_3226_, lean_object* v_k_3227_, lean_object* v_c_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_Grind_CommRing_Poly_powC(v_p_3226_, v_k_3227_, v_c_3228_);
lean_dec(v_k_3227_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc(lean_object* v_p_3230_, lean_object* v_k_3231_, lean_object* v_c_3232_){
_start:
{
lean_object* v_zero_3233_; uint8_t v_isZero_3234_; 
v_zero_3233_ = lean_unsigned_to_nat(0u);
v_isZero_3234_ = lean_nat_dec_eq(v_k_3231_, v_zero_3233_);
if (v_isZero_3234_ == 1)
{
lean_object* v___x_3235_; 
lean_dec(v_c_3232_);
lean_dec_ref(v_p_3230_);
v___x_3235_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3235_;
}
else
{
lean_object* v_one_3236_; lean_object* v_n_3237_; uint8_t v___x_3238_; 
v_one_3236_ = lean_unsigned_to_nat(1u);
v_n_3237_ = lean_nat_sub(v_k_3231_, v_one_3236_);
v___x_3238_ = lean_nat_dec_eq(v_n_3237_, v_zero_3233_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
lean_inc(v_c_3232_);
lean_inc_ref(v_p_3230_);
v___x_3239_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3230_, v_n_3237_, v_c_3232_);
lean_dec(v_n_3237_);
v___x_3240_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3239_, v_p_3230_, v_c_3232_);
return v___x_3240_;
}
else
{
lean_dec(v_n_3237_);
lean_dec(v_c_3232_);
return v_p_3230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_powC__nc___boxed(lean_object* v_p_3241_, lean_object* v_k_3242_, lean_object* v_c_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_Grind_CommRing_Poly_powC__nc(v_p_3241_, v_k_3242_, v_c_3243_);
lean_dec(v_k_3242_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC_go(lean_object* v_c_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v_k_3248_; 
switch(lean_obj_tag(v_a_3246_))
{
case 1:
{
lean_object* v_k_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3262_; 
v_k_3252_ = lean_ctor_get(v_a_3246_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v_a_3246_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3254_ = v_a_3246_;
v_isShared_3255_ = v_isSharedCheck_3262_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_k_3252_);
lean_dec(v_a_3246_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3262_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3256_ = lean_nat_to_int(v_k_3252_);
v___x_3257_ = lean_nat_to_int(v_c_3245_);
v___x_3258_ = lean_int_emod(v___x_3256_, v___x_3257_);
lean_dec(v___x_3257_);
lean_dec(v___x_3256_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set_tag(v___x_3254_, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3258_);
v___x_3260_ = v___x_3254_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
case 3:
{
lean_object* v_i_3263_; lean_object* v___x_3264_; 
lean_dec(v_c_3245_);
v_i_3263_ = lean_ctor_get(v_a_3246_, 0);
lean_inc(v_i_3263_);
lean_dec_ref_known(v_a_3246_, 1);
v___x_3264_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3263_);
return v___x_3264_;
}
case 4:
{
lean_object* v_a_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_a_3265_ = lean_ctor_get(v_a_3246_, 0);
lean_inc_ref(v_a_3265_);
lean_dec_ref_known(v_a_3246_, 1);
v___x_3266_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3245_);
v___x_3267_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3245_, v_a_3265_);
v___x_3268_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3266_, v___x_3267_, v_c_3245_);
return v___x_3268_;
}
case 5:
{
lean_object* v_a_3269_; lean_object* v_b_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_a_3269_ = lean_ctor_get(v_a_3246_, 0);
lean_inc_ref(v_a_3269_);
v_b_3270_ = lean_ctor_get(v_a_3246_, 1);
lean_inc_ref(v_b_3270_);
lean_dec_ref_known(v_a_3246_, 2);
lean_inc_n(v_c_3245_, 2);
v___x_3271_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3245_, v_a_3269_);
v___x_3272_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3245_, v_b_3270_);
v___x_3273_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3271_, v___x_3272_, v_c_3245_);
return v___x_3273_;
}
case 6:
{
lean_object* v_a_3274_; lean_object* v_b_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v_a_3274_ = lean_ctor_get(v_a_3246_, 0);
lean_inc_ref(v_a_3274_);
v_b_3275_ = lean_ctor_get(v_a_3246_, 1);
lean_inc_ref(v_b_3275_);
lean_dec_ref_known(v_a_3246_, 2);
lean_inc_n(v_c_3245_, 3);
v___x_3276_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3245_, v_a_3274_);
v___x_3277_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_3278_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3245_, v_b_3275_);
v___x_3279_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3277_, v___x_3278_, v_c_3245_);
v___x_3280_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3276_, v___x_3279_, v_c_3245_);
return v___x_3280_;
}
case 7:
{
lean_object* v_a_3281_; lean_object* v_b_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_a_3281_ = lean_ctor_get(v_a_3246_, 0);
lean_inc_ref(v_a_3281_);
v_b_3282_ = lean_ctor_get(v_a_3246_, 1);
lean_inc_ref(v_b_3282_);
lean_dec_ref_known(v_a_3246_, 2);
lean_inc_n(v_c_3245_, 2);
v___x_3283_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3245_, v_a_3281_);
v___x_3284_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3245_, v_b_3282_);
v___x_3285_ = l_Lean_Grind_CommRing_Poly_mulC(v___x_3283_, v___x_3284_, v_c_3245_);
return v___x_3285_;
}
case 8:
{
lean_object* v_a_3286_; lean_object* v_k_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3314_; 
v_a_3286_ = lean_ctor_get(v_a_3246_, 0);
v_k_3287_ = lean_ctor_get(v_a_3246_, 1);
v_isSharedCheck_3314_ = !lean_is_exclusive(v_a_3246_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3289_ = v_a_3246_;
v_isShared_3290_ = v_isSharedCheck_3314_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_k_3287_);
lean_inc(v_a_3286_);
lean_dec(v_a_3246_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3314_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3291_ = lean_unsigned_to_nat(0u);
v___x_3292_ = lean_nat_dec_eq(v_k_3287_, v___x_3291_);
if (v___x_3292_ == 0)
{
switch(lean_obj_tag(v_a_3286_))
{
case 0:
{
lean_object* v_k_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3303_; 
lean_del_object(v___x_3289_);
v_k_3293_ = lean_ctor_get(v_a_3286_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v_a_3286_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3295_ = v_a_3286_;
v_isShared_3296_ = v_isSharedCheck_3303_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_k_3293_);
lean_dec(v_a_3286_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3303_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3301_; 
v___x_3297_ = l_Int_pow(v_k_3293_, v_k_3287_);
lean_dec(v_k_3287_);
lean_dec(v_k_3293_);
v___x_3298_ = lean_nat_to_int(v_c_3245_);
v___x_3299_ = lean_int_emod(v___x_3297_, v___x_3298_);
lean_dec(v___x_3298_);
lean_dec(v___x_3297_);
if (v_isShared_3296_ == 0)
{
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
lean_object* v_i_3304_; lean_object* v___x_3306_; 
lean_dec(v_c_3245_);
v_i_3304_ = lean_ctor_get(v_a_3286_, 0);
lean_inc(v_i_3304_);
lean_dec_ref_known(v_a_3286_, 1);
if (v_isShared_3290_ == 0)
{
lean_ctor_set_tag(v___x_3289_, 0);
lean_ctor_set(v___x_3289_, 0, v_i_3304_);
v___x_3306_ = v___x_3289_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_i_3304_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_k_3287_);
v___x_3306_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = lean_box(0);
v___x_3308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3306_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3308_);
return v___x_3309_;
}
}
default: 
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
lean_del_object(v___x_3289_);
lean_inc(v_c_3245_);
v___x_3311_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3245_, v_a_3286_);
v___x_3312_ = l_Lean_Grind_CommRing_Poly_powC(v___x_3311_, v_k_3287_, v_c_3245_);
lean_dec(v_k_3287_);
return v___x_3312_;
}
}
}
else
{
lean_object* v___x_3313_; 
lean_del_object(v___x_3289_);
lean_dec(v_k_3287_);
lean_dec_ref(v_a_3286_);
lean_dec(v_c_3245_);
v___x_3313_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3313_;
}
}
}
default: 
{
lean_object* v_k_3315_; 
v_k_3315_ = lean_ctor_get(v_a_3246_, 0);
lean_inc(v_k_3315_);
lean_dec_ref(v_a_3246_);
v_k_3248_ = v_k_3315_;
goto v___jp_3247_;
}
}
v___jp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3249_ = lean_nat_to_int(v_c_3245_);
v___x_3250_ = lean_int_emod(v_k_3248_, v___x_3249_);
lean_dec(v___x_3249_);
lean_dec(v_k_3248_);
v___x_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
return v___x_3251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC(lean_object* v_e_3316_, lean_object* v_c_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_Grind_CommRing_Expr_toPolyC_go(v_c_3317_, v_e_3316_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(lean_object* v_c_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v_k_3322_; 
switch(lean_obj_tag(v_a_3320_))
{
case 1:
{
lean_object* v_k_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3336_; 
v_k_3326_ = lean_ctor_get(v_a_3320_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_a_3320_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3328_ = v_a_3320_;
v_isShared_3329_ = v_isSharedCheck_3336_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_k_3326_);
lean_dec(v_a_3320_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3336_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3330_ = lean_nat_to_int(v_k_3326_);
v___x_3331_ = lean_nat_to_int(v_c_3319_);
v___x_3332_ = lean_int_emod(v___x_3330_, v___x_3331_);
lean_dec(v___x_3331_);
lean_dec(v___x_3330_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set_tag(v___x_3328_, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3332_);
v___x_3334_ = v___x_3328_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
case 3:
{
lean_object* v_i_3337_; lean_object* v___x_3338_; 
lean_dec(v_c_3319_);
v_i_3337_ = lean_ctor_get(v_a_3320_, 0);
lean_inc(v_i_3337_);
lean_dec_ref_known(v_a_3320_, 1);
v___x_3338_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_3337_);
return v___x_3338_;
}
case 4:
{
lean_object* v_a_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v_a_3339_ = lean_ctor_get(v_a_3320_, 0);
lean_inc_ref(v_a_3339_);
lean_dec_ref_known(v_a_3320_, 1);
v___x_3340_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
lean_inc(v_c_3319_);
v___x_3341_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3319_, v_a_3339_);
v___x_3342_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3340_, v___x_3341_, v_c_3319_);
return v___x_3342_;
}
case 5:
{
lean_object* v_a_3343_; lean_object* v_b_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v_a_3343_ = lean_ctor_get(v_a_3320_, 0);
lean_inc_ref(v_a_3343_);
v_b_3344_ = lean_ctor_get(v_a_3320_, 1);
lean_inc_ref(v_b_3344_);
lean_dec_ref_known(v_a_3320_, 2);
lean_inc_n(v_c_3319_, 2);
v___x_3345_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3319_, v_a_3343_);
v___x_3346_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3319_, v_b_3344_);
v___x_3347_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3345_, v___x_3346_, v_c_3319_);
return v___x_3347_;
}
case 6:
{
lean_object* v_a_3348_; lean_object* v_b_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v_a_3348_ = lean_ctor_get(v_a_3320_, 0);
lean_inc_ref(v_a_3348_);
v_b_3349_ = lean_ctor_get(v_a_3320_, 1);
lean_inc_ref(v_b_3349_);
lean_dec_ref_known(v_a_3320_, 2);
lean_inc_n(v_c_3319_, 3);
v___x_3350_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3319_, v_a_3348_);
v___x_3351_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPoly___closed__0, &l_Lean_Grind_CommRing_Expr_toPoly___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPoly___closed__0);
v___x_3352_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3319_, v_b_3349_);
v___x_3353_ = l_Lean_Grind_CommRing_Poly_mulConstC(v___x_3351_, v___x_3352_, v_c_3319_);
v___x_3354_ = l_Lean_Grind_CommRing_Poly_combineC(v___x_3350_, v___x_3353_, v_c_3319_);
return v___x_3354_;
}
case 7:
{
lean_object* v_a_3355_; lean_object* v_b_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_a_3355_ = lean_ctor_get(v_a_3320_, 0);
lean_inc_ref(v_a_3355_);
v_b_3356_ = lean_ctor_get(v_a_3320_, 1);
lean_inc_ref(v_b_3356_);
lean_dec_ref_known(v_a_3320_, 2);
lean_inc_n(v_c_3319_, 2);
v___x_3357_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3319_, v_a_3355_);
v___x_3358_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3319_, v_b_3356_);
v___x_3359_ = l_Lean_Grind_CommRing_Poly_mulC__nc(v___x_3357_, v___x_3358_, v_c_3319_);
return v___x_3359_;
}
case 8:
{
lean_object* v_a_3360_; lean_object* v_k_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3388_; 
v_a_3360_ = lean_ctor_get(v_a_3320_, 0);
v_k_3361_ = lean_ctor_get(v_a_3320_, 1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_a_3320_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3363_ = v_a_3320_;
v_isShared_3364_ = v_isSharedCheck_3388_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_k_3361_);
lean_inc(v_a_3360_);
lean_dec(v_a_3320_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3388_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; uint8_t v___x_3366_; 
v___x_3365_ = lean_unsigned_to_nat(0u);
v___x_3366_ = lean_nat_dec_eq(v_k_3361_, v___x_3365_);
if (v___x_3366_ == 0)
{
switch(lean_obj_tag(v_a_3360_))
{
case 0:
{
lean_object* v_k_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3377_; 
lean_del_object(v___x_3363_);
v_k_3367_ = lean_ctor_get(v_a_3360_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v_a_3360_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3369_ = v_a_3360_;
v_isShared_3370_ = v_isSharedCheck_3377_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_k_3367_);
lean_dec(v_a_3360_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3377_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3371_ = l_Int_pow(v_k_3367_, v_k_3361_);
lean_dec(v_k_3361_);
lean_dec(v_k_3367_);
v___x_3372_ = lean_nat_to_int(v_c_3319_);
v___x_3373_ = lean_int_emod(v___x_3371_, v___x_3372_);
lean_dec(v___x_3372_);
lean_dec(v___x_3371_);
if (v_isShared_3370_ == 0)
{
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
lean_object* v_i_3378_; lean_object* v___x_3380_; 
lean_dec(v_c_3319_);
v_i_3378_ = lean_ctor_get(v_a_3360_, 0);
lean_inc(v_i_3378_);
lean_dec_ref_known(v_a_3360_, 1);
if (v_isShared_3364_ == 0)
{
lean_ctor_set_tag(v___x_3363_, 0);
lean_ctor_set(v___x_3363_, 0, v_i_3378_);
v___x_3380_ = v___x_3363_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_i_3378_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_k_3361_);
v___x_3380_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3381_ = lean_box(0);
v___x_3382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3380_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_3382_);
return v___x_3383_;
}
}
default: 
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
lean_del_object(v___x_3363_);
lean_inc(v_c_3319_);
v___x_3385_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3319_, v_a_3360_);
v___x_3386_ = l_Lean_Grind_CommRing_Poly_powC__nc(v___x_3385_, v_k_3361_, v_c_3319_);
lean_dec(v_k_3361_);
return v___x_3386_;
}
}
}
else
{
lean_object* v___x_3387_; 
lean_del_object(v___x_3363_);
lean_dec(v_k_3361_);
lean_dec_ref(v_a_3360_);
lean_dec(v_c_3319_);
v___x_3387_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_pow___closed__0, &l_Lean_Grind_CommRing_Poly_pow___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_pow___closed__0);
return v___x_3387_;
}
}
}
default: 
{
lean_object* v_k_3389_; 
v_k_3389_ = lean_ctor_get(v_a_3320_, 0);
lean_inc(v_k_3389_);
lean_dec_ref(v_a_3320_);
v_k_3322_ = v_k_3389_;
goto v___jp_3321_;
}
}
v___jp_3321_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_nat_to_int(v_c_3319_);
v___x_3324_ = lean_int_emod(v_k_3322_, v___x_3323_);
lean_dec(v___x_3323_);
lean_dec(v_k_3322_);
v___x_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
return v___x_3325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyC__nc(lean_object* v_e_3390_, lean_object* v_c_3391_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_Grind_CommRing_Expr_toPolyC__nc_go(v_c_3391_, v_e_3390_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter___redArg(lean_object* v_x_3393_, lean_object* v_h__1_3394_, lean_object* v_h__2_3395_, lean_object* v_h__3_3396_, lean_object* v_h__4_3397_, lean_object* v_h__5_3398_, lean_object* v_h__6_3399_, lean_object* v_h__7_3400_, lean_object* v_h__8_3401_, lean_object* v_h__9_3402_){
_start:
{
switch(lean_obj_tag(v_x_3393_))
{
case 0:
{
lean_object* v_k_3403_; lean_object* v___x_3404_; 
lean_dec(v_h__9_3402_);
lean_dec(v_h__8_3401_);
lean_dec(v_h__7_3400_);
lean_dec(v_h__6_3399_);
lean_dec(v_h__5_3398_);
lean_dec(v_h__4_3397_);
lean_dec(v_h__3_3396_);
lean_dec(v_h__2_3395_);
v_k_3403_ = lean_ctor_get(v_x_3393_, 0);
lean_inc(v_k_3403_);
lean_dec_ref_known(v_x_3393_, 1);
v___x_3404_ = lean_apply_1(v_h__1_3394_, v_k_3403_);
return v___x_3404_;
}
case 1:
{
lean_object* v_k_3405_; lean_object* v___x_3406_; 
lean_dec(v_h__9_3402_);
lean_dec(v_h__8_3401_);
lean_dec(v_h__7_3400_);
lean_dec(v_h__6_3399_);
lean_dec(v_h__5_3398_);
lean_dec(v_h__4_3397_);
lean_dec(v_h__3_3396_);
lean_dec(v_h__1_3394_);
v_k_3405_ = lean_ctor_get(v_x_3393_, 0);
lean_inc(v_k_3405_);
lean_dec_ref_known(v_x_3393_, 1);
v___x_3406_ = lean_apply_1(v_h__2_3395_, v_k_3405_);
return v___x_3406_;
}
case 2:
{
lean_object* v_k_3407_; lean_object* v___x_3408_; 
lean_dec(v_h__9_3402_);
lean_dec(v_h__8_3401_);
lean_dec(v_h__7_3400_);
lean_dec(v_h__6_3399_);
lean_dec(v_h__5_3398_);
lean_dec(v_h__4_3397_);
lean_dec(v_h__2_3395_);
lean_dec(v_h__1_3394_);
v_k_3407_ = lean_ctor_get(v_x_3393_, 0);
lean_inc(v_k_3407_);
lean_dec_ref_known(v_x_3393_, 1);
v___x_3408_ = lean_apply_1(v_h__3_3396_, v_k_3407_);
return v___x_3408_;
}
case 3:
{
lean_object* v_i_3409_; lean_object* v___x_3410_; 
lean_dec(v_h__9_3402_);
lean_dec(v_h__8_3401_);
lean_dec(v_h__7_3400_);
lean_dec(v_h__6_3399_);
lean_dec(v_h__5_3398_);
lean_dec(v_h__3_3396_);
lean_dec(v_h__2_3395_);
lean_dec(v_h__1_3394_);
v_i_3409_ = lean_ctor_get(v_x_3393_, 0);
lean_inc(v_i_3409_);
lean_dec_ref_known(v_x_3393_, 1);
v___x_3410_ = lean_apply_1(v_h__4_3397_, v_i_3409_);
return v___x_3410_;
}
case 4:
{
lean_object* v_a_3411_; lean_object* v___x_3412_; 
lean_dec(v_h__9_3402_);
lean_dec(v_h__8_3401_);
lean_dec(v_h__6_3399_);
lean_dec(v_h__5_3398_);
lean_dec(v_h__4_3397_);
lean_dec(v_h__3_3396_);
lean_dec(v_h__2_3395_);
lean_dec(v_h__1_3394_);
v_a_3411_ = lean_ctor_get(v_x_3393_, 0);
lean_inc_ref(v_a_3411_);
lean_dec_ref_known(v_x_3393_, 1);
v___x_3412_ = lean_apply_1(v_h__7_3400_, v_a_3411_);
return v___x_3412_;
}
case 5:
{
lean_object* v_a_3413_; lean_object* v_b_3414_; lean_object* v___x_3415_; 
lean_dec(v_h__9_3402_);
lean_dec(v_h__8_3401_);
lean_dec(v_h__7_3400_);
lean_dec(v_h__6_3399_);
lean_dec(v_h__4_3397_);
lean_dec(v_h__3_3396_);
lean_dec(v_h__2_3395_);
lean_dec(v_h__1_3394_);
v_a_3413_ = lean_ctor_get(v_x_3393_, 0);
lean_inc_ref(v_a_3413_);
v_b_3414_ = lean_ctor_get(v_x_3393_, 1);
lean_inc_ref(v_b_3414_);
lean_dec_ref_known(v_x_3393_, 2);
v___x_3415_ = lean_apply_2(v_h__5_3398_, v_a_3413_, v_b_3414_);
return v___x_3415_;
}
case 6:
{
lean_object* v_a_3416_; lean_object* v_b_3417_; lean_object* v___x_3418_; 
lean_dec(v_h__9_3402_);
lean_dec(v_h__7_3400_);
lean_dec(v_h__6_3399_);
lean_dec(v_h__5_3398_);
lean_dec(v_h__4_3397_);
lean_dec(v_h__3_3396_);
lean_dec(v_h__2_3395_);
lean_dec(v_h__1_3394_);
v_a_3416_ = lean_ctor_get(v_x_3393_, 0);
lean_inc_ref(v_a_3416_);
v_b_3417_ = lean_ctor_get(v_x_3393_, 1);
lean_inc_ref(v_b_3417_);
lean_dec_ref_known(v_x_3393_, 2);
v___x_3418_ = lean_apply_2(v_h__8_3401_, v_a_3416_, v_b_3417_);
return v___x_3418_;
}
case 7:
{
lean_object* v_a_3419_; lean_object* v_b_3420_; lean_object* v___x_3421_; 
lean_dec(v_h__9_3402_);
lean_dec(v_h__8_3401_);
lean_dec(v_h__7_3400_);
lean_dec(v_h__5_3398_);
lean_dec(v_h__4_3397_);
lean_dec(v_h__3_3396_);
lean_dec(v_h__2_3395_);
lean_dec(v_h__1_3394_);
v_a_3419_ = lean_ctor_get(v_x_3393_, 0);
lean_inc_ref(v_a_3419_);
v_b_3420_ = lean_ctor_get(v_x_3393_, 1);
lean_inc_ref(v_b_3420_);
lean_dec_ref_known(v_x_3393_, 2);
v___x_3421_ = lean_apply_2(v_h__6_3399_, v_a_3419_, v_b_3420_);
return v___x_3421_;
}
default: 
{
lean_object* v_a_3422_; lean_object* v_k_3423_; lean_object* v___x_3424_; 
lean_dec(v_h__8_3401_);
lean_dec(v_h__7_3400_);
lean_dec(v_h__6_3399_);
lean_dec(v_h__5_3398_);
lean_dec(v_h__4_3397_);
lean_dec(v_h__3_3396_);
lean_dec(v_h__2_3395_);
lean_dec(v_h__1_3394_);
v_a_3422_ = lean_ctor_get(v_x_3393_, 0);
lean_inc_ref(v_a_3422_);
v_k_3423_ = lean_ctor_get(v_x_3393_, 1);
lean_inc(v_k_3423_);
lean_dec_ref_known(v_x_3393_, 2);
v___x_3424_ = lean_apply_2(v_h__9_3402_, v_a_3422_, v_k_3423_);
return v___x_3424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__4_splitter(lean_object* v_motive_3425_, lean_object* v_x_3426_, lean_object* v_h__1_3427_, lean_object* v_h__2_3428_, lean_object* v_h__3_3429_, lean_object* v_h__4_3430_, lean_object* v_h__5_3431_, lean_object* v_h__6_3432_, lean_object* v_h__7_3433_, lean_object* v_h__8_3434_, lean_object* v_h__9_3435_){
_start:
{
switch(lean_obj_tag(v_x_3426_))
{
case 0:
{
lean_object* v_k_3436_; lean_object* v___x_3437_; 
lean_dec(v_h__9_3435_);
lean_dec(v_h__8_3434_);
lean_dec(v_h__7_3433_);
lean_dec(v_h__6_3432_);
lean_dec(v_h__5_3431_);
lean_dec(v_h__4_3430_);
lean_dec(v_h__3_3429_);
lean_dec(v_h__2_3428_);
v_k_3436_ = lean_ctor_get(v_x_3426_, 0);
lean_inc(v_k_3436_);
lean_dec_ref_known(v_x_3426_, 1);
v___x_3437_ = lean_apply_1(v_h__1_3427_, v_k_3436_);
return v___x_3437_;
}
case 1:
{
lean_object* v_k_3438_; lean_object* v___x_3439_; 
lean_dec(v_h__9_3435_);
lean_dec(v_h__8_3434_);
lean_dec(v_h__7_3433_);
lean_dec(v_h__6_3432_);
lean_dec(v_h__5_3431_);
lean_dec(v_h__4_3430_);
lean_dec(v_h__3_3429_);
lean_dec(v_h__1_3427_);
v_k_3438_ = lean_ctor_get(v_x_3426_, 0);
lean_inc(v_k_3438_);
lean_dec_ref_known(v_x_3426_, 1);
v___x_3439_ = lean_apply_1(v_h__2_3428_, v_k_3438_);
return v___x_3439_;
}
case 2:
{
lean_object* v_k_3440_; lean_object* v___x_3441_; 
lean_dec(v_h__9_3435_);
lean_dec(v_h__8_3434_);
lean_dec(v_h__7_3433_);
lean_dec(v_h__6_3432_);
lean_dec(v_h__5_3431_);
lean_dec(v_h__4_3430_);
lean_dec(v_h__2_3428_);
lean_dec(v_h__1_3427_);
v_k_3440_ = lean_ctor_get(v_x_3426_, 0);
lean_inc(v_k_3440_);
lean_dec_ref_known(v_x_3426_, 1);
v___x_3441_ = lean_apply_1(v_h__3_3429_, v_k_3440_);
return v___x_3441_;
}
case 3:
{
lean_object* v_i_3442_; lean_object* v___x_3443_; 
lean_dec(v_h__9_3435_);
lean_dec(v_h__8_3434_);
lean_dec(v_h__7_3433_);
lean_dec(v_h__6_3432_);
lean_dec(v_h__5_3431_);
lean_dec(v_h__3_3429_);
lean_dec(v_h__2_3428_);
lean_dec(v_h__1_3427_);
v_i_3442_ = lean_ctor_get(v_x_3426_, 0);
lean_inc(v_i_3442_);
lean_dec_ref_known(v_x_3426_, 1);
v___x_3443_ = lean_apply_1(v_h__4_3430_, v_i_3442_);
return v___x_3443_;
}
case 4:
{
lean_object* v_a_3444_; lean_object* v___x_3445_; 
lean_dec(v_h__9_3435_);
lean_dec(v_h__8_3434_);
lean_dec(v_h__6_3432_);
lean_dec(v_h__5_3431_);
lean_dec(v_h__4_3430_);
lean_dec(v_h__3_3429_);
lean_dec(v_h__2_3428_);
lean_dec(v_h__1_3427_);
v_a_3444_ = lean_ctor_get(v_x_3426_, 0);
lean_inc_ref(v_a_3444_);
lean_dec_ref_known(v_x_3426_, 1);
v___x_3445_ = lean_apply_1(v_h__7_3433_, v_a_3444_);
return v___x_3445_;
}
case 5:
{
lean_object* v_a_3446_; lean_object* v_b_3447_; lean_object* v___x_3448_; 
lean_dec(v_h__9_3435_);
lean_dec(v_h__8_3434_);
lean_dec(v_h__7_3433_);
lean_dec(v_h__6_3432_);
lean_dec(v_h__4_3430_);
lean_dec(v_h__3_3429_);
lean_dec(v_h__2_3428_);
lean_dec(v_h__1_3427_);
v_a_3446_ = lean_ctor_get(v_x_3426_, 0);
lean_inc_ref(v_a_3446_);
v_b_3447_ = lean_ctor_get(v_x_3426_, 1);
lean_inc_ref(v_b_3447_);
lean_dec_ref_known(v_x_3426_, 2);
v___x_3448_ = lean_apply_2(v_h__5_3431_, v_a_3446_, v_b_3447_);
return v___x_3448_;
}
case 6:
{
lean_object* v_a_3449_; lean_object* v_b_3450_; lean_object* v___x_3451_; 
lean_dec(v_h__9_3435_);
lean_dec(v_h__7_3433_);
lean_dec(v_h__6_3432_);
lean_dec(v_h__5_3431_);
lean_dec(v_h__4_3430_);
lean_dec(v_h__3_3429_);
lean_dec(v_h__2_3428_);
lean_dec(v_h__1_3427_);
v_a_3449_ = lean_ctor_get(v_x_3426_, 0);
lean_inc_ref(v_a_3449_);
v_b_3450_ = lean_ctor_get(v_x_3426_, 1);
lean_inc_ref(v_b_3450_);
lean_dec_ref_known(v_x_3426_, 2);
v___x_3451_ = lean_apply_2(v_h__8_3434_, v_a_3449_, v_b_3450_);
return v___x_3451_;
}
case 7:
{
lean_object* v_a_3452_; lean_object* v_b_3453_; lean_object* v___x_3454_; 
lean_dec(v_h__9_3435_);
lean_dec(v_h__8_3434_);
lean_dec(v_h__7_3433_);
lean_dec(v_h__5_3431_);
lean_dec(v_h__4_3430_);
lean_dec(v_h__3_3429_);
lean_dec(v_h__2_3428_);
lean_dec(v_h__1_3427_);
v_a_3452_ = lean_ctor_get(v_x_3426_, 0);
lean_inc_ref(v_a_3452_);
v_b_3453_ = lean_ctor_get(v_x_3426_, 1);
lean_inc_ref(v_b_3453_);
lean_dec_ref_known(v_x_3426_, 2);
v___x_3454_ = lean_apply_2(v_h__6_3432_, v_a_3452_, v_b_3453_);
return v___x_3454_;
}
default: 
{
lean_object* v_a_3455_; lean_object* v_k_3456_; lean_object* v___x_3457_; 
lean_dec(v_h__8_3434_);
lean_dec(v_h__7_3433_);
lean_dec(v_h__6_3432_);
lean_dec(v_h__5_3431_);
lean_dec(v_h__4_3430_);
lean_dec(v_h__3_3429_);
lean_dec(v_h__2_3428_);
lean_dec(v_h__1_3427_);
v_a_3455_ = lean_ctor_get(v_x_3426_, 0);
lean_inc_ref(v_a_3455_);
v_k_3456_ = lean_ctor_get(v_x_3426_, 1);
lean_inc(v_k_3456_);
lean_dec_ref_known(v_x_3426_, 2);
v___x_3457_ = lean_apply_2(v_h__9_3435_, v_a_3455_, v_k_3456_);
return v___x_3457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter___redArg(lean_object* v_a_3458_, lean_object* v_h__1_3459_, lean_object* v_h__2_3460_, lean_object* v_h__3_3461_){
_start:
{
switch(lean_obj_tag(v_a_3458_))
{
case 0:
{
lean_object* v_k_3462_; lean_object* v___x_3463_; 
lean_dec(v_h__3_3461_);
lean_dec(v_h__2_3460_);
v_k_3462_ = lean_ctor_get(v_a_3458_, 0);
lean_inc(v_k_3462_);
lean_dec_ref_known(v_a_3458_, 1);
v___x_3463_ = lean_apply_1(v_h__1_3459_, v_k_3462_);
return v___x_3463_;
}
case 3:
{
lean_object* v_i_3464_; lean_object* v___x_3465_; 
lean_dec(v_h__3_3461_);
lean_dec(v_h__1_3459_);
v_i_3464_ = lean_ctor_get(v_a_3458_, 0);
lean_inc(v_i_3464_);
lean_dec_ref_known(v_a_3458_, 1);
v___x_3465_ = lean_apply_1(v_h__2_3460_, v_i_3464_);
return v___x_3465_;
}
default: 
{
lean_object* v___x_3466_; 
lean_dec(v_h__2_3460_);
lean_dec(v_h__1_3459_);
v___x_3466_ = lean_apply_3(v_h__3_3461_, v_a_3458_, lean_box(0), lean_box(0));
return v___x_3466_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Expr_toPolyC_go_match__1_splitter(lean_object* v_motive_3467_, lean_object* v_a_3468_, lean_object* v_h__1_3469_, lean_object* v_h__2_3470_, lean_object* v_h__3_3471_){
_start:
{
switch(lean_obj_tag(v_a_3468_))
{
case 0:
{
lean_object* v_k_3472_; lean_object* v___x_3473_; 
lean_dec(v_h__3_3471_);
lean_dec(v_h__2_3470_);
v_k_3472_ = lean_ctor_get(v_a_3468_, 0);
lean_inc(v_k_3472_);
lean_dec_ref_known(v_a_3468_, 1);
v___x_3473_ = lean_apply_1(v_h__1_3469_, v_k_3472_);
return v___x_3473_;
}
case 3:
{
lean_object* v_i_3474_; lean_object* v___x_3475_; 
lean_dec(v_h__3_3471_);
lean_dec(v_h__1_3469_);
v_i_3474_ = lean_ctor_get(v_a_3468_, 0);
lean_inc(v_i_3474_);
lean_dec_ref_known(v_a_3468_, 1);
v___x_3475_ = lean_apply_1(v_h__2_3470_, v_i_3474_);
return v___x_3475_;
}
default: 
{
lean_object* v___x_3476_; 
lean_dec(v_h__2_3470_);
lean_dec(v_h__1_3469_);
v___x_3476_ = lean_apply_3(v_h__3_3471_, v_a_3468_, lean_box(0), lean_box(0));
return v___x_3476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter___redArg(lean_object* v_k_3477_, lean_object* v_h__1_3478_, lean_object* v_h__2_3479_, lean_object* v_h__3_3480_){
_start:
{
lean_object* v___x_3481_; uint8_t v___x_3482_; 
v___x_3481_ = lean_unsigned_to_nat(0u);
v___x_3482_ = lean_nat_dec_eq(v_k_3477_, v___x_3481_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; uint8_t v___x_3484_; 
lean_dec(v_h__1_3478_);
v___x_3483_ = lean_unsigned_to_nat(1u);
v___x_3484_ = lean_nat_dec_eq(v_k_3477_, v___x_3483_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; 
lean_dec(v_h__2_3479_);
v___x_3485_ = lean_apply_3(v_h__3_3480_, v_k_3477_, lean_box(0), lean_box(0));
return v___x_3485_;
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec(v_h__3_3480_);
lean_dec(v_k_3477_);
v___x_3486_ = lean_box(0);
v___x_3487_ = lean_apply_1(v_h__2_3479_, v___x_3486_);
return v___x_3487_;
}
}
else
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
lean_dec(v_h__3_3480_);
lean_dec(v_h__2_3479_);
lean_dec(v_k_3477_);
v___x_3488_ = lean_box(0);
v___x_3489_ = lean_apply_1(v_h__1_3478_, v___x_3488_);
return v___x_3489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Power_denote_match__1_splitter(lean_object* v_motive_3490_, lean_object* v_k_3491_, lean_object* v_h__1_3492_, lean_object* v_h__2_3493_, lean_object* v_h__3_3494_){
_start:
{
lean_object* v___x_3495_; uint8_t v___x_3496_; 
v___x_3495_ = lean_unsigned_to_nat(0u);
v___x_3496_ = lean_nat_dec_eq(v_k_3491_, v___x_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; uint8_t v___x_3498_; 
lean_dec(v_h__1_3492_);
v___x_3497_ = lean_unsigned_to_nat(1u);
v___x_3498_ = lean_nat_dec_eq(v_k_3491_, v___x_3497_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
lean_dec(v_h__2_3493_);
v___x_3499_ = lean_apply_3(v_h__3_3494_, v_k_3491_, lean_box(0), lean_box(0));
return v___x_3499_;
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
lean_dec(v_h__3_3494_);
lean_dec(v_k_3491_);
v___x_3500_ = lean_box(0);
v___x_3501_ = lean_apply_1(v_h__2_3493_, v___x_3500_);
return v___x_3501_;
}
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
lean_dec(v_h__3_3494_);
lean_dec(v_h__2_3493_);
lean_dec(v_k_3491_);
v___x_3502_ = lean_box(0);
v___x_3503_ = lean_apply_1(v_h__1_3492_, v___x_3502_);
return v___x_3503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter___redArg(lean_object* v_x_3504_, lean_object* v_h__1_3505_, lean_object* v_h__2_3506_){
_start:
{
if (lean_obj_tag(v_x_3504_) == 0)
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
lean_dec(v_h__2_3506_);
v___x_3507_ = lean_box(0);
v___x_3508_ = lean_apply_1(v_h__1_3505_, v___x_3507_);
return v___x_3508_;
}
else
{
lean_object* v_p_3509_; lean_object* v_m_3510_; lean_object* v___x_3511_; 
lean_dec(v_h__1_3505_);
v_p_3509_ = lean_ctor_get(v_x_3504_, 0);
lean_inc_ref(v_p_3509_);
v_m_3510_ = lean_ctor_get(v_x_3504_, 1);
lean_inc(v_m_3510_);
lean_dec_ref_known(v_x_3504_, 2);
v___x_3511_ = lean_apply_2(v_h__2_3506_, v_p_3509_, v_m_3510_);
return v___x_3511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_denote_match__1_splitter(lean_object* v_motive_3512_, lean_object* v_x_3513_, lean_object* v_h__1_3514_, lean_object* v_h__2_3515_){
_start:
{
if (lean_obj_tag(v_x_3513_) == 0)
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
lean_dec(v_h__2_3515_);
v___x_3516_ = lean_box(0);
v___x_3517_ = lean_apply_1(v_h__1_3514_, v___x_3516_);
return v___x_3517_;
}
else
{
lean_object* v_p_3518_; lean_object* v_m_3519_; lean_object* v___x_3520_; 
lean_dec(v_h__1_3514_);
v_p_3518_ = lean_ctor_get(v_x_3513_, 0);
lean_inc_ref(v_p_3518_);
v_m_3519_ = lean_ctor_get(v_x_3513_, 1);
lean_inc(v_m_3519_);
lean_dec_ref_known(v_x_3513_, 2);
v___x_3520_ = lean_apply_2(v_h__2_3515_, v_p_3518_, v_m_3519_);
return v___x_3520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter___redArg(lean_object* v_m_u2081_3521_, lean_object* v_h__1_3522_, lean_object* v_h__2_3523_, lean_object* v_h__3_3524_){
_start:
{
if (lean_obj_tag(v_m_u2081_3521_) == 0)
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
lean_dec(v_h__3_3524_);
lean_dec(v_h__2_3523_);
v___x_3525_ = lean_box(0);
v___x_3526_ = lean_apply_1(v_h__1_3522_, v___x_3525_);
return v___x_3526_;
}
else
{
lean_object* v_m_3527_; 
lean_dec(v_h__1_3522_);
v_m_3527_ = lean_ctor_get(v_m_u2081_3521_, 1);
if (lean_obj_tag(v_m_3527_) == 0)
{
lean_object* v_p_3528_; lean_object* v___x_3529_; 
lean_dec(v_h__3_3524_);
v_p_3528_ = lean_ctor_get(v_m_u2081_3521_, 0);
lean_inc_ref(v_p_3528_);
lean_dec_ref_known(v_m_u2081_3521_, 2);
v___x_3529_ = lean_apply_1(v_h__2_3523_, v_p_3528_);
return v___x_3529_;
}
else
{
lean_object* v_p_3530_; lean_object* v___x_3531_; 
lean_inc(v_m_3527_);
lean_dec(v_h__2_3523_);
v_p_3530_ = lean_ctor_get(v_m_u2081_3521_, 0);
lean_inc_ref(v_p_3530_);
lean_dec_ref_known(v_m_u2081_3521_, 2);
v___x_3531_ = lean_apply_3(v_h__3_3524_, v_p_3530_, v_m_3527_, lean_box(0));
return v___x_3531_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Mon_mul__nc_match__1_splitter(lean_object* v_motive_3532_, lean_object* v_m_u2081_3533_, lean_object* v_h__1_3534_, lean_object* v_h__2_3535_, lean_object* v_h__3_3536_){
_start:
{
if (lean_obj_tag(v_m_u2081_3533_) == 0)
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
lean_dec(v_h__3_3536_);
lean_dec(v_h__2_3535_);
v___x_3537_ = lean_box(0);
v___x_3538_ = lean_apply_1(v_h__1_3534_, v___x_3537_);
return v___x_3538_;
}
else
{
lean_object* v_m_3539_; 
lean_dec(v_h__1_3534_);
v_m_3539_ = lean_ctor_get(v_m_u2081_3533_, 1);
if (lean_obj_tag(v_m_3539_) == 0)
{
lean_object* v_p_3540_; lean_object* v___x_3541_; 
lean_dec(v_h__3_3536_);
v_p_3540_ = lean_ctor_get(v_m_u2081_3533_, 0);
lean_inc_ref(v_p_3540_);
lean_dec_ref_known(v_m_u2081_3533_, 2);
v___x_3541_ = lean_apply_1(v_h__2_3535_, v_p_3540_);
return v___x_3541_;
}
else
{
lean_object* v_p_3542_; lean_object* v___x_3543_; 
lean_inc(v_m_3539_);
lean_dec(v_h__2_3535_);
v_p_3542_ = lean_ctor_get(v_m_u2081_3533_, 0);
lean_inc_ref(v_p_3542_);
lean_dec_ref_known(v_m_u2081_3533_, 2);
v___x_3543_ = lean_apply_3(v_h__3_3536_, v_p_3542_, v_m_3539_, lean_box(0));
return v___x_3543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter___redArg(lean_object* v_p_3544_, lean_object* v_h__1_3545_, lean_object* v_h__2_3546_, lean_object* v_h__3_3547_){
_start:
{
if (lean_obj_tag(v_p_3544_) == 0)
{
lean_object* v_k_3548_; lean_object* v___x_3549_; uint8_t v___x_3550_; 
lean_dec(v_h__3_3547_);
v_k_3548_ = lean_ctor_get(v_p_3544_, 0);
lean_inc(v_k_3548_);
lean_dec_ref_known(v_p_3544_, 1);
v___x_3549_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3550_ = lean_int_dec_eq(v_k_3548_, v___x_3549_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; 
lean_dec(v_h__1_3545_);
v___x_3551_ = lean_apply_2(v_h__2_3546_, v_k_3548_, lean_box(0));
return v___x_3551_;
}
else
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
lean_dec(v_k_3548_);
lean_dec(v_h__2_3546_);
v___x_3552_ = lean_box(0);
v___x_3553_ = lean_apply_1(v_h__1_3545_, v___x_3552_);
return v___x_3553_;
}
}
else
{
lean_object* v_k_3554_; lean_object* v_v_3555_; lean_object* v_p_3556_; lean_object* v___x_3557_; 
lean_dec(v_h__2_3546_);
lean_dec(v_h__1_3545_);
v_k_3554_ = lean_ctor_get(v_p_3544_, 0);
lean_inc(v_k_3554_);
v_v_3555_ = lean_ctor_get(v_p_3544_, 1);
lean_inc(v_v_3555_);
v_p_3556_ = lean_ctor_get(v_p_3544_, 2);
lean_inc_ref(v_p_3556_);
lean_dec_ref_known(v_p_3544_, 3);
v___x_3557_ = lean_apply_3(v_h__3_3547_, v_k_3554_, v_v_3555_, v_p_3556_);
return v___x_3557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_x27_go_match__1_splitter(lean_object* v_motive_3558_, lean_object* v_p_3559_, lean_object* v_h__1_3560_, lean_object* v_h__2_3561_, lean_object* v_h__3_3562_){
_start:
{
if (lean_obj_tag(v_p_3559_) == 0)
{
lean_object* v_k_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
lean_dec(v_h__3_3562_);
v_k_3563_ = lean_ctor_get(v_p_3559_, 0);
lean_inc(v_k_3563_);
lean_dec_ref_known(v_p_3559_, 1);
v___x_3564_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3565_ = lean_int_dec_eq(v_k_3563_, v___x_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; 
lean_dec(v_h__1_3560_);
v___x_3566_ = lean_apply_2(v_h__2_3561_, v_k_3563_, lean_box(0));
return v___x_3566_;
}
else
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
lean_dec(v_k_3563_);
lean_dec(v_h__2_3561_);
v___x_3567_ = lean_box(0);
v___x_3568_ = lean_apply_1(v_h__1_3560_, v___x_3567_);
return v___x_3568_;
}
}
else
{
lean_object* v_k_3569_; lean_object* v_v_3570_; lean_object* v_p_3571_; lean_object* v___x_3572_; 
lean_dec(v_h__2_3561_);
lean_dec(v_h__1_3560_);
v_k_3569_ = lean_ctor_get(v_p_3559_, 0);
lean_inc(v_k_3569_);
v_v_3570_ = lean_ctor_get(v_p_3559_, 1);
lean_inc(v_v_3570_);
v_p_3571_ = lean_ctor_get(v_p_3559_, 2);
lean_inc_ref(v_p_3571_);
lean_dec_ref_known(v_p_3559_, 3);
v___x_3572_ = lean_apply_3(v_h__3_3562_, v_k_3569_, v_v_3570_, v_p_3571_);
return v___x_3572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object* v_p_3573_, lean_object* v_h__1_3574_, lean_object* v_h__2_3575_){
_start:
{
if (lean_obj_tag(v_p_3573_) == 0)
{
lean_object* v_k_3576_; lean_object* v___x_3577_; 
lean_dec(v_h__2_3575_);
v_k_3576_ = lean_ctor_get(v_p_3573_, 0);
lean_inc(v_k_3576_);
lean_dec_ref_known(v_p_3573_, 1);
v___x_3577_ = lean_apply_1(v_h__1_3574_, v_k_3576_);
return v___x_3577_;
}
else
{
lean_object* v_k_3578_; lean_object* v_v_3579_; lean_object* v_p_3580_; lean_object* v___x_3581_; 
lean_dec(v_h__1_3574_);
v_k_3578_ = lean_ctor_get(v_p_3573_, 0);
lean_inc(v_k_3578_);
v_v_3579_ = lean_ctor_get(v_p_3573_, 1);
lean_inc(v_v_3579_);
v_p_3580_ = lean_ctor_get(v_p_3573_, 2);
lean_inc_ref(v_p_3580_);
lean_dec_ref_known(v_p_3573_, 3);
v___x_3581_ = lean_apply_3(v_h__2_3575_, v_k_3578_, v_v_3579_, v_p_3580_);
return v___x_3581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object* v_motive_3582_, lean_object* v_p_3583_, lean_object* v_h__1_3584_, lean_object* v_h__2_3585_){
_start:
{
if (lean_obj_tag(v_p_3583_) == 0)
{
lean_object* v_k_3586_; lean_object* v___x_3587_; 
lean_dec(v_h__2_3585_);
v_k_3586_ = lean_ctor_get(v_p_3583_, 0);
lean_inc(v_k_3586_);
lean_dec_ref_known(v_p_3583_, 1);
v___x_3587_ = lean_apply_1(v_h__1_3584_, v_k_3586_);
return v___x_3587_;
}
else
{
lean_object* v_k_3588_; lean_object* v_v_3589_; lean_object* v_p_3590_; lean_object* v___x_3591_; 
lean_dec(v_h__1_3584_);
v_k_3588_ = lean_ctor_get(v_p_3583_, 0);
lean_inc(v_k_3588_);
v_v_3589_ = lean_ctor_get(v_p_3583_, 1);
lean_inc(v_v_3589_);
v_p_3590_ = lean_ctor_get(v_p_3583_, 2);
lean_inc_ref(v_p_3590_);
lean_dec_ref_known(v_p_3583_, 3);
v___x_3591_ = lean_apply_3(v_h__2_3585_, v_k_3588_, v_v_3589_, v_p_3590_);
return v___x_3591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object* v_k_3592_, lean_object* v_h__1_3593_, lean_object* v_h__2_3594_, lean_object* v_h__3_3595_){
_start:
{
lean_object* v_zero_3596_; uint8_t v_isZero_3597_; 
v_zero_3596_ = lean_unsigned_to_nat(0u);
v_isZero_3597_ = lean_nat_dec_eq(v_k_3592_, v_zero_3596_);
if (v_isZero_3597_ == 1)
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
lean_dec(v_h__3_3595_);
lean_dec(v_h__2_3594_);
v___x_3598_ = lean_box(0);
v___x_3599_ = lean_apply_1(v_h__1_3593_, v___x_3598_);
return v___x_3599_;
}
else
{
lean_object* v_one_3600_; lean_object* v_n_3601_; uint8_t v___x_3602_; 
lean_dec(v_h__1_3593_);
v_one_3600_ = lean_unsigned_to_nat(1u);
v_n_3601_ = lean_nat_sub(v_k_3592_, v_one_3600_);
v___x_3602_ = lean_nat_dec_eq(v_n_3601_, v_zero_3596_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; 
lean_dec(v_h__2_3594_);
v___x_3603_ = lean_apply_2(v_h__3_3595_, v_n_3601_, lean_box(0));
return v___x_3603_;
}
else
{
lean_object* v___x_3604_; lean_object* v___x_3605_; 
lean_dec(v_n_3601_);
lean_dec(v_h__3_3595_);
v___x_3604_ = lean_box(0);
v___x_3605_ = lean_apply_1(v_h__2_3594_, v___x_3604_);
return v___x_3605_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object* v_k_3606_, lean_object* v_h__1_3607_, lean_object* v_h__2_3608_, lean_object* v_h__3_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(v_k_3606_, v_h__1_3607_, v_h__2_3608_, v_h__3_3609_);
lean_dec(v_k_3606_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object* v_motive_3611_, lean_object* v_k_3612_, lean_object* v_h__1_3613_, lean_object* v_h__2_3614_, lean_object* v_h__3_3615_){
_start:
{
lean_object* v_zero_3616_; uint8_t v_isZero_3617_; 
v_zero_3616_ = lean_unsigned_to_nat(0u);
v_isZero_3617_ = lean_nat_dec_eq(v_k_3612_, v_zero_3616_);
if (v_isZero_3617_ == 1)
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
lean_dec(v_h__3_3615_);
lean_dec(v_h__2_3614_);
v___x_3618_ = lean_box(0);
v___x_3619_ = lean_apply_1(v_h__1_3613_, v___x_3618_);
return v___x_3619_;
}
else
{
lean_object* v_one_3620_; lean_object* v_n_3621_; uint8_t v___x_3622_; 
lean_dec(v_h__1_3613_);
v_one_3620_ = lean_unsigned_to_nat(1u);
v_n_3621_ = lean_nat_sub(v_k_3612_, v_one_3620_);
v___x_3622_ = lean_nat_dec_eq(v_n_3621_, v_zero_3616_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; 
lean_dec(v_h__2_3614_);
v___x_3623_ = lean_apply_2(v_h__3_3615_, v_n_3621_, lean_box(0));
return v___x_3623_;
}
else
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
lean_dec(v_n_3621_);
lean_dec(v_h__3_3615_);
v___x_3624_ = lean_box(0);
v___x_3625_ = lean_apply_1(v_h__2_3614_, v___x_3624_);
return v___x_3625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object* v_motive_3626_, lean_object* v_k_3627_, lean_object* v_h__1_3628_, lean_object* v_h__2_3629_, lean_object* v_h__3_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(v_motive_3626_, v_k_3627_, v_h__1_3628_, v_h__2_3629_, v_h__3_3630_);
lean_dec(v_k_3627_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_toExpr(lean_object* v_pw_3632_){
_start:
{
lean_object* v_x_3633_; lean_object* v_k_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3645_; 
v_x_3633_ = lean_ctor_get(v_pw_3632_, 0);
v_k_3634_ = lean_ctor_get(v_pw_3632_, 1);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_pw_3632_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3636_ = v_pw_3632_;
v_isShared_3637_ = v_isSharedCheck_3645_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_k_3634_);
lean_inc(v_x_3633_);
lean_dec(v_pw_3632_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3645_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3638_ = lean_unsigned_to_nat(1u);
v___x_3639_ = lean_nat_dec_eq(v_k_3634_, v___x_3638_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; lean_object* v___x_3642_; 
v___x_3640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3640_, 0, v_x_3633_);
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 8);
lean_ctor_set(v___x_3636_, 0, v___x_3640_);
v___x_3642_ = v___x_3636_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3640_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_k_3634_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
else
{
lean_object* v___x_3644_; 
lean_del_object(v___x_3636_);
lean_dec(v_k_3634_);
v___x_3644_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3644_, 0, v_x_3633_);
return v___x_3644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_toExpr_go(lean_object* v_m_3646_, lean_object* v_acc_3647_){
_start:
{
if (lean_obj_tag(v_m_3646_) == 0)
{
return v_acc_3647_;
}
else
{
lean_object* v_p_3648_; lean_object* v_m_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3658_; 
v_p_3648_ = lean_ctor_get(v_m_3646_, 0);
v_m_3649_ = lean_ctor_get(v_m_3646_, 1);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_m_3646_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3651_ = v_m_3646_;
v_isShared_3652_ = v_isSharedCheck_3658_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_m_3649_);
lean_inc(v_p_3648_);
lean_dec(v_m_3646_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3658_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3653_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_3648_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set_tag(v___x_3651_, 7);
lean_ctor_set(v___x_3651_, 1, v___x_3653_);
lean_ctor_set(v___x_3651_, 0, v_acc_3647_);
v___x_3655_ = v___x_3651_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_acc_3647_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v___x_3653_);
v___x_3655_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
v_m_3646_ = v_m_3649_;
v_acc_3647_ = v___x_3655_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_toExpr(lean_object* v_m_3661_){
_start:
{
if (lean_obj_tag(v_m_3661_) == 0)
{
lean_object* v___x_3662_; 
v___x_3662_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__0, &l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0);
return v___x_3662_;
}
else
{
lean_object* v_p_3663_; lean_object* v_m_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v_p_3663_ = lean_ctor_get(v_m_3661_, 0);
lean_inc_ref(v_p_3663_);
v_m_3664_ = lean_ctor_get(v_m_3661_, 1);
lean_inc(v_m_3664_);
lean_dec_ref_known(v_m_3661_, 2);
v___x_3665_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_3663_);
v___x_3666_ = l_Lean_Grind_CommRing_Mon_toExpr_go(v_m_3664_, v___x_3665_);
return v___x_3666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr_goTerm(lean_object* v_k_3667_, lean_object* v_m_3668_){
_start:
{
lean_object* v___x_3669_; uint8_t v___x_3670_; 
v___x_3669_ = lean_obj_once(&l_Lean_Grind_CommRing_instReprExpr_repr___closed__4, &l_Lean_Grind_CommRing_instReprExpr_repr___closed__4_once, _init_l_Lean_Grind_CommRing_instReprExpr_repr___closed__4);
v___x_3670_ = lean_int_dec_eq(v_k_3667_, v___x_3669_);
if (v___x_3670_ == 0)
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3671_, 0, v_k_3667_);
v___x_3672_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_3668_);
v___x_3673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3671_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
return v___x_3673_;
}
else
{
lean_object* v___x_3674_; 
lean_dec(v_k_3667_);
v___x_3674_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_3668_);
return v___x_3674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr_go(lean_object* v_p_3675_, lean_object* v_acc_3676_){
_start:
{
if (lean_obj_tag(v_p_3675_) == 0)
{
lean_object* v_k_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3687_; 
v_k_3677_ = lean_ctor_get(v_p_3675_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_p_3675_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3679_ = v_p_3675_;
v_isShared_3680_ = v_isSharedCheck_3687_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_k_3677_);
lean_dec(v_p_3675_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3687_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3681_; uint8_t v___x_3682_; 
v___x_3681_ = lean_obj_once(&l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0, &l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0_once, _init_l_Lean_Grind_CommRing_instInhabitedExpr_default___closed__0);
v___x_3682_ = lean_int_dec_eq(v_k_3677_, v___x_3681_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3684_; 
if (v_isShared_3680_ == 0)
{
v___x_3684_ = v___x_3679_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_k_3677_);
v___x_3684_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3685_; 
v___x_3685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3685_, 0, v_acc_3676_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
return v___x_3685_;
}
}
else
{
lean_del_object(v___x_3679_);
lean_dec(v_k_3677_);
return v_acc_3676_;
}
}
}
else
{
lean_object* v_k_3688_; lean_object* v_v_3689_; lean_object* v_p_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v_k_3688_ = lean_ctor_get(v_p_3675_, 0);
lean_inc(v_k_3688_);
v_v_3689_ = lean_ctor_get(v_p_3675_, 1);
lean_inc(v_v_3689_);
v_p_3690_ = lean_ctor_get(v_p_3675_, 2);
lean_inc_ref(v_p_3690_);
lean_dec_ref_known(v_p_3675_, 3);
v___x_3691_ = l_Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_3688_, v_v_3689_);
v___x_3692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3692_, 0, v_acc_3676_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v_p_3675_ = v_p_3690_;
v_acc_3676_ = v___x_3692_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr(lean_object* v_p_3694_){
_start:
{
if (lean_obj_tag(v_p_3694_) == 0)
{
lean_object* v_k_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
v_k_3695_ = lean_ctor_get(v_p_3694_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_p_3694_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v_p_3694_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_k_3695_);
lean_dec(v_p_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_k_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
else
{
lean_object* v_k_3703_; lean_object* v_v_3704_; lean_object* v_p_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_k_3703_ = lean_ctor_get(v_p_3694_, 0);
lean_inc(v_k_3703_);
v_v_3704_ = lean_ctor_get(v_p_3694_, 1);
lean_inc(v_v_3704_);
v_p_3705_ = lean_ctor_get(v_p_3694_, 2);
lean_inc_ref(v_p_3705_);
lean_dec_ref_known(v_p_3694_, 3);
v___x_3706_ = l_Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_3703_, v_v_3704_);
v___x_3707_ = l_Lean_Grind_CommRing_Poly_toExpr_go(v_p_3705_, v___x_3706_);
return v___x_3707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteList___redArg(lean_object* v_inst_3708_, lean_object* v_ctx_3709_, lean_object* v_x_3710_){
_start:
{
if (lean_obj_tag(v_x_3710_) == 0)
{
lean_object* v_toSemiring_3711_; lean_object* v_ofNat_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v_toSemiring_3711_ = lean_ctor_get(v_inst_3708_, 0);
lean_inc_ref(v_toSemiring_3711_);
lean_dec_ref(v_inst_3708_);
v_ofNat_3712_ = lean_ctor_get(v_toSemiring_3711_, 3);
lean_inc(v_ofNat_3712_);
lean_dec_ref(v_toSemiring_3711_);
v___x_3713_ = lean_unsigned_to_nat(0u);
v___x_3714_ = lean_apply_1(v_ofNat_3712_, v___x_3713_);
return v___x_3714_;
}
else
{
lean_object* v_toSemiring_3715_; lean_object* v_toAdd_3716_; lean_object* v_head_3717_; lean_object* v_tail_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v_toSemiring_3715_ = lean_ctor_get(v_inst_3708_, 0);
v_toAdd_3716_ = lean_ctor_get(v_toSemiring_3715_, 0);
lean_inc(v_toAdd_3716_);
v_head_3717_ = lean_ctor_get(v_x_3710_, 0);
lean_inc(v_head_3717_);
v_tail_3718_ = lean_ctor_get(v_x_3710_, 1);
lean_inc(v_tail_3718_);
lean_dec_ref_known(v_x_3710_, 2);
lean_inc_ref(v_inst_3708_);
v___x_3719_ = l_Lean_Grind_CommRing_Poly_denote___redArg(v_inst_3708_, v_ctx_3709_, v_head_3717_);
v___x_3720_ = l_Lean_Grind_CommRing_Poly_denoteList___redArg(v_inst_3708_, v_ctx_3709_, v_tail_3718_);
v___x_3721_ = lean_apply_2(v_toAdd_3716_, v___x_3719_, v___x_3720_);
return v___x_3721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteList___redArg___boxed(lean_object* v_inst_3722_, lean_object* v_ctx_3723_, lean_object* v_x_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_Grind_CommRing_Poly_denoteList___redArg(v_inst_3722_, v_ctx_3723_, v_x_3724_);
lean_dec_ref(v_ctx_3723_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteList(lean_object* v_00_u03b1_3726_, lean_object* v_inst_3727_, lean_object* v_ctx_3728_, lean_object* v_x_3729_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Grind_CommRing_Poly_denoteList___redArg(v_inst_3727_, v_ctx_3728_, v_x_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteList___boxed(lean_object* v_00_u03b1_3731_, lean_object* v_inst_3732_, lean_object* v_ctx_3733_, lean_object* v_x_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Lean_Grind_CommRing_Poly_denoteList(v_00_u03b1_3731_, v_inst_3732_, v_ctx_3733_, v_x_3734_);
lean_dec_ref(v_ctx_3733_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(lean_object* v_inst_3736_, lean_object* v_ctx_3737_, lean_object* v_m_3738_, lean_object* v_acc_3739_){
_start:
{
if (lean_obj_tag(v_m_3738_) == 0)
{
lean_dec_ref(v_inst_3736_);
return v_acc_3739_;
}
else
{
lean_object* v_toSemiring_3740_; lean_object* v_toMul_3741_; lean_object* v_ofNat_3742_; lean_object* v_npow_3743_; lean_object* v_p_3744_; lean_object* v_m_3745_; lean_object* v___y_3747_; lean_object* v_x_3750_; lean_object* v_k_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; 
v_toSemiring_3740_ = lean_ctor_get(v_inst_3736_, 0);
v_toMul_3741_ = lean_ctor_get(v_toSemiring_3740_, 1);
v_ofNat_3742_ = lean_ctor_get(v_toSemiring_3740_, 3);
v_npow_3743_ = lean_ctor_get(v_toSemiring_3740_, 5);
v_p_3744_ = lean_ctor_get(v_m_3738_, 0);
lean_inc_ref(v_p_3744_);
v_m_3745_ = lean_ctor_get(v_m_3738_, 1);
lean_inc(v_m_3745_);
lean_dec_ref_known(v_m_3738_, 2);
v_x_3750_ = lean_ctor_get(v_p_3744_, 0);
lean_inc(v_x_3750_);
v_k_3751_ = lean_ctor_get(v_p_3744_, 1);
lean_inc(v_k_3751_);
lean_dec_ref(v_p_3744_);
v___x_3752_ = lean_unsigned_to_nat(0u);
v___x_3753_ = lean_nat_dec_eq(v_k_3751_, v___x_3752_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3754_ = lean_unsigned_to_nat(1u);
v___x_3755_ = lean_nat_dec_eq(v_k_3751_, v___x_3754_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3756_ = l_Lean_RArray_getImpl___redArg(v_ctx_3737_, v_x_3750_);
lean_dec(v_x_3750_);
lean_inc(v_npow_3743_);
v___x_3757_ = lean_apply_2(v_npow_3743_, v___x_3756_, v_k_3751_);
v___y_3747_ = v___x_3757_;
goto v___jp_3746_;
}
else
{
lean_object* v___x_3758_; 
lean_dec(v_k_3751_);
v___x_3758_ = l_Lean_RArray_getImpl___redArg(v_ctx_3737_, v_x_3750_);
lean_dec(v_x_3750_);
v___y_3747_ = v___x_3758_;
goto v___jp_3746_;
}
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
lean_dec(v_k_3751_);
lean_dec(v_x_3750_);
v___x_3759_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3742_);
v___x_3760_ = lean_apply_1(v_ofNat_3742_, v___x_3759_);
v___y_3747_ = v___x_3760_;
goto v___jp_3746_;
}
v___jp_3746_:
{
lean_object* v___x_3748_; 
lean_inc(v_toMul_3741_);
v___x_3748_ = lean_apply_2(v_toMul_3741_, v_acc_3739_, v___y_3747_);
v_m_3738_ = v_m_3745_;
v_acc_3739_ = v___x_3748_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg___boxed(lean_object* v_inst_3761_, lean_object* v_ctx_3762_, lean_object* v_m_3763_, lean_object* v_acc_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3761_, v_ctx_3762_, v_m_3763_, v_acc_3764_);
lean_dec_ref(v_ctx_3762_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(lean_object* v_00_u03b1_3766_, lean_object* v_inst_3767_, lean_object* v_ctx_3768_, lean_object* v_m_3769_, lean_object* v_acc_3770_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3767_, v_ctx_3768_, v_m_3769_, v_acc_3770_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___boxed(lean_object* v_00_u03b1_3772_, lean_object* v_inst_3773_, lean_object* v_ctx_3774_, lean_object* v_m_3775_, lean_object* v_acc_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go(v_00_u03b1_3772_, v_inst_3773_, v_ctx_3774_, v_m_3775_, v_acc_3776_);
lean_dec_ref(v_ctx_3774_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(lean_object* v_inst_3778_, lean_object* v_ctx_3779_, lean_object* v_m_3780_){
_start:
{
if (lean_obj_tag(v_m_3780_) == 0)
{
lean_object* v_toSemiring_3781_; lean_object* v_ofNat_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v_toSemiring_3781_ = lean_ctor_get(v_inst_3778_, 0);
lean_inc_ref(v_toSemiring_3781_);
lean_dec_ref(v_inst_3778_);
v_ofNat_3782_ = lean_ctor_get(v_toSemiring_3781_, 3);
lean_inc(v_ofNat_3782_);
lean_dec_ref(v_toSemiring_3781_);
v___x_3783_ = lean_unsigned_to_nat(1u);
v___x_3784_ = lean_apply_1(v_ofNat_3782_, v___x_3783_);
return v___x_3784_;
}
else
{
lean_object* v_toSemiring_3785_; lean_object* v_p_3786_; lean_object* v_m_3787_; lean_object* v_ofNat_3788_; lean_object* v_npow_3789_; lean_object* v_x_3790_; lean_object* v_k_3791_; lean_object* v___x_3792_; uint8_t v___x_3793_; 
v_toSemiring_3785_ = lean_ctor_get(v_inst_3778_, 0);
v_p_3786_ = lean_ctor_get(v_m_3780_, 0);
lean_inc_ref(v_p_3786_);
v_m_3787_ = lean_ctor_get(v_m_3780_, 1);
lean_inc(v_m_3787_);
lean_dec_ref_known(v_m_3780_, 2);
v_ofNat_3788_ = lean_ctor_get(v_toSemiring_3785_, 3);
v_npow_3789_ = lean_ctor_get(v_toSemiring_3785_, 5);
v_x_3790_ = lean_ctor_get(v_p_3786_, 0);
lean_inc(v_x_3790_);
v_k_3791_ = lean_ctor_get(v_p_3786_, 1);
lean_inc(v_k_3791_);
lean_dec_ref(v_p_3786_);
v___x_3792_ = lean_unsigned_to_nat(0u);
v___x_3793_ = lean_nat_dec_eq(v_k_3791_, v___x_3792_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; uint8_t v___x_3795_; 
v___x_3794_ = lean_unsigned_to_nat(1u);
v___x_3795_ = lean_nat_dec_eq(v_k_3791_, v___x_3794_);
if (v___x_3795_ == 0)
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3796_ = l_Lean_RArray_getImpl___redArg(v_ctx_3779_, v_x_3790_);
lean_dec(v_x_3790_);
lean_inc(v_npow_3789_);
v___x_3797_ = lean_apply_2(v_npow_3789_, v___x_3796_, v_k_3791_);
v___x_3798_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3778_, v_ctx_3779_, v_m_3787_, v___x_3797_);
return v___x_3798_;
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
lean_dec(v_k_3791_);
v___x_3799_ = l_Lean_RArray_getImpl___redArg(v_ctx_3779_, v_x_3790_);
lean_dec(v_x_3790_);
v___x_3800_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3778_, v_ctx_3779_, v_m_3787_, v___x_3799_);
return v___x_3800_;
}
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
lean_dec(v_k_3791_);
lean_dec(v_x_3790_);
v___x_3801_ = lean_unsigned_to_nat(1u);
lean_inc(v_ofNat_3788_);
v___x_3802_ = lean_apply_1(v_ofNat_3788_, v___x_3801_);
v___x_3803_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule_go___redArg(v_inst_3778_, v_ctx_3779_, v_m_3787_, v___x_3802_);
return v___x_3803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3804_, lean_object* v_ctx_3805_, lean_object* v_m_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3804_, v_ctx_3805_, v_m_3806_);
lean_dec_ref(v_ctx_3805_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule(lean_object* v_00_u03b1_3808_, lean_object* v_inst_3809_, lean_object* v_ctx_3810_, lean_object* v_m_3811_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3809_, v_ctx_3810_, v_m_3811_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3813_, lean_object* v_inst_3814_, lean_object* v_ctx_3815_, lean_object* v_m_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule(v_00_u03b1_3813_, v_inst_3814_, v_ctx_3815_, v_m_3816_);
lean_dec_ref(v_ctx_3815_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(lean_object* v_inst_3818_, lean_object* v_ctx_3819_, lean_object* v_p_3820_){
_start:
{
lean_object* v___x_3821_; 
lean_inc_ref(v_inst_3818_);
v___x_3821_ = l_Lean_Grind_Ring_toIntModule___redArg(v_inst_3818_);
if (lean_obj_tag(v_p_3820_) == 0)
{
lean_object* v_toSemiring_3822_; lean_object* v_zsmul_3823_; lean_object* v_ofNat_3824_; lean_object* v_k_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v_toSemiring_3822_ = lean_ctor_get(v_inst_3818_, 0);
lean_inc_ref(v_toSemiring_3822_);
lean_dec_ref(v_inst_3818_);
v_zsmul_3823_ = lean_ctor_get(v___x_3821_, 2);
lean_inc(v_zsmul_3823_);
lean_dec_ref(v___x_3821_);
v_ofNat_3824_ = lean_ctor_get(v_toSemiring_3822_, 3);
lean_inc(v_ofNat_3824_);
lean_dec_ref(v_toSemiring_3822_);
v_k_3825_ = lean_ctor_get(v_p_3820_, 0);
lean_inc(v_k_3825_);
lean_dec_ref_known(v_p_3820_, 1);
v___x_3826_ = lean_unsigned_to_nat(1u);
v___x_3827_ = lean_apply_1(v_ofNat_3824_, v___x_3826_);
v___x_3828_ = lean_apply_2(v_zsmul_3823_, v_k_3825_, v___x_3827_);
return v___x_3828_;
}
else
{
lean_object* v_toSemiring_3829_; lean_object* v_zsmul_3830_; lean_object* v_toAdd_3831_; lean_object* v_k_3832_; lean_object* v_v_3833_; lean_object* v_p_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v_toSemiring_3829_ = lean_ctor_get(v_inst_3818_, 0);
v_zsmul_3830_ = lean_ctor_get(v___x_3821_, 2);
lean_inc(v_zsmul_3830_);
lean_dec_ref(v___x_3821_);
v_toAdd_3831_ = lean_ctor_get(v_toSemiring_3829_, 0);
lean_inc(v_toAdd_3831_);
v_k_3832_ = lean_ctor_get(v_p_3820_, 0);
lean_inc(v_k_3832_);
v_v_3833_ = lean_ctor_get(v_p_3820_, 1);
lean_inc(v_v_3833_);
v_p_3834_ = lean_ctor_get(v_p_3820_, 2);
lean_inc_ref(v_p_3834_);
lean_dec_ref_known(v_p_3820_, 3);
lean_inc_ref(v_inst_3818_);
v___x_3835_ = l_Lean_Grind_CommRing_Mon_denoteAsIntModule___redArg(v_inst_3818_, v_ctx_3819_, v_v_3833_);
v___x_3836_ = lean_apply_2(v_zsmul_3830_, v_k_3832_, v___x_3835_);
v___x_3837_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3818_, v_ctx_3819_, v_p_3834_);
v___x_3838_ = lean_apply_2(v_toAdd_3831_, v___x_3836_, v___x_3837_);
return v___x_3838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg___boxed(lean_object* v_inst_3839_, lean_object* v_ctx_3840_, lean_object* v_p_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3839_, v_ctx_3840_, v_p_3841_);
lean_dec_ref(v_ctx_3840_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule(lean_object* v_00_u03b1_3843_, lean_object* v_inst_3844_, lean_object* v_ctx_3845_, lean_object* v_p_3846_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule___redArg(v_inst_3844_, v_ctx_3845_, v_p_3846_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteAsIntModule___boxed(lean_object* v_00_u03b1_3848_, lean_object* v_inst_3849_, lean_object* v_ctx_3850_, lean_object* v_p_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModule(v_00_u03b1_3848_, v_inst_3849_, v_ctx_3850_, v_p_3851_);
lean_dec_ref(v_ctx_3850_);
return v_res_3852_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__gcd__cert(lean_object* v_a_3853_, lean_object* v_b_3854_, lean_object* v_p_u2081_3855_, lean_object* v_p_u2082_3856_, lean_object* v_p_3857_){
_start:
{
if (lean_obj_tag(v_p_u2081_3855_) == 0)
{
if (lean_obj_tag(v_p_u2082_3856_) == 0)
{
if (lean_obj_tag(v_p_3857_) == 0)
{
lean_object* v_k_3858_; lean_object* v_k_3859_; lean_object* v_k_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v_k_3858_ = lean_ctor_get(v_p_u2081_3855_, 0);
v_k_3859_ = lean_ctor_get(v_p_u2082_3856_, 0);
v_k_3860_ = lean_ctor_get(v_p_3857_, 0);
v___x_3861_ = lean_int_mul(v_a_3853_, v_k_3858_);
v___x_3862_ = lean_int_mul(v_b_3854_, v_k_3859_);
v___x_3863_ = lean_int_add(v___x_3861_, v___x_3862_);
lean_dec(v___x_3862_);
lean_dec(v___x_3861_);
v___x_3864_ = lean_int_dec_eq(v_k_3860_, v___x_3863_);
lean_dec(v___x_3863_);
return v___x_3864_;
}
else
{
uint8_t v___x_3865_; 
v___x_3865_ = 0;
return v___x_3865_;
}
}
else
{
uint8_t v___x_3866_; 
v___x_3866_ = 0;
return v___x_3866_;
}
}
else
{
uint8_t v___x_3867_; 
v___x_3867_ = 0;
return v___x_3867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__gcd__cert___boxed(lean_object* v_a_3868_, lean_object* v_b_3869_, lean_object* v_p_u2081_3870_, lean_object* v_p_u2082_3871_, lean_object* v_p_3872_){
_start:
{
uint8_t v_res_3873_; lean_object* v_r_3874_; 
v_res_3873_ = l_Lean_Grind_CommRing_eq__gcd__cert(v_a_3868_, v_b_3869_, v_p_u2081_3870_, v_p_u2082_3871_, v_p_3872_);
lean_dec_ref(v_p_3872_);
lean_dec_ref(v_p_u2082_3871_);
lean_dec_ref(v_p_u2081_3870_);
lean_dec(v_b_3869_);
lean_dec(v_a_3868_);
v_r_3874_ = lean_box(v_res_3873_);
return v_r_3874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter___redArg(lean_object* v_p_3875_, lean_object* v_h__1_3876_, lean_object* v_h__2_3877_){
_start:
{
if (lean_obj_tag(v_p_3875_) == 0)
{
lean_object* v_k_3878_; lean_object* v___x_3879_; 
lean_dec(v_h__1_3876_);
v_k_3878_ = lean_ctor_get(v_p_3875_, 0);
lean_inc(v_k_3878_);
lean_dec_ref_known(v_p_3875_, 1);
v___x_3879_ = lean_apply_1(v_h__2_3877_, v_k_3878_);
return v___x_3879_;
}
else
{
lean_object* v_k_3880_; lean_object* v_v_3881_; lean_object* v_p_3882_; lean_object* v___x_3883_; 
lean_dec(v_h__2_3877_);
v_k_3880_ = lean_ctor_get(v_p_3875_, 0);
lean_inc(v_k_3880_);
v_v_3881_ = lean_ctor_get(v_p_3875_, 1);
lean_inc(v_v_3881_);
v_p_3882_ = lean_ctor_get(v_p_3875_, 2);
lean_inc_ref(v_p_3882_);
lean_dec_ref_known(v_p_3875_, 3);
v___x_3883_ = lean_apply_3(v_h__1_3876_, v_k_3880_, v_v_3881_, v_p_3882_);
return v___x_3883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSolver_0__Lean_Grind_CommRing_eq__gcd__cert_match__1_splitter(lean_object* v_motive_3884_, lean_object* v_p_3885_, lean_object* v_h__1_3886_, lean_object* v_h__2_3887_){
_start:
{
if (lean_obj_tag(v_p_3885_) == 0)
{
lean_object* v_k_3888_; lean_object* v___x_3889_; 
lean_dec(v_h__1_3886_);
v_k_3888_ = lean_ctor_get(v_p_3885_, 0);
lean_inc(v_k_3888_);
lean_dec_ref_known(v_p_3885_, 1);
v___x_3889_ = lean_apply_1(v_h__2_3887_, v_k_3888_);
return v___x_3889_;
}
else
{
lean_object* v_k_3890_; lean_object* v_v_3891_; lean_object* v_p_3892_; lean_object* v___x_3893_; 
lean_dec(v_h__2_3887_);
v_k_3890_ = lean_ctor_get(v_p_3885_, 0);
lean_inc(v_k_3890_);
v_v_3891_ = lean_ctor_get(v_p_3885_, 1);
lean_inc(v_v_3891_);
v_p_3892_ = lean_ctor_get(v_p_3885_, 2);
lean_inc_ref(v_p_3892_);
lean_dec_ref_known(v_p_3885_, 3);
v___x_3893_ = lean_apply_3(v_h__1_3886_, v_k_3890_, v_v_3891_, v_p_3892_);
return v___x_3893_;
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
