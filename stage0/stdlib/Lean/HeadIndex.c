// Lean compiler output
// Module: Lean.HeadIndex
// Imports: public import Lean.Expr
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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqLiteral_beq(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t l_Lean_Literal_hash(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_instReprLiteral_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_fvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_fvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_mvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_mvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_const_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_proj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_proj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_sort_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_sort_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lam_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lam_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_forallE_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_forallE_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedHeadIndex_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedHeadIndex_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedHeadIndex_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedHeadIndex_default = (const lean_object*)&l_Lean_instInhabitedHeadIndex_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedHeadIndex = (const lean_object*)&l_Lean_instInhabitedHeadIndex_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_instBEqHeadIndex_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqHeadIndex_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqHeadIndex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqHeadIndex_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqHeadIndex___closed__0 = (const lean_object*)&l_Lean_instBEqHeadIndex___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqHeadIndex = (const lean_object*)&l_Lean_instBEqHeadIndex___closed__0_value;
static const lean_string_object l_Lean_instReprHeadIndex_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.HeadIndex.sort"};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__0 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprHeadIndex_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprHeadIndex_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__1 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__1_value;
static const lean_string_object l_Lean_instReprHeadIndex_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.HeadIndex.lam"};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__2 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__2_value;
static const lean_ctor_object l_Lean_instReprHeadIndex_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprHeadIndex_repr___closed__2_value)}};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__3 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__3_value;
static const lean_string_object l_Lean_instReprHeadIndex_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.HeadIndex.forallE"};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__4 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprHeadIndex_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprHeadIndex_repr___closed__4_value)}};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__5 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__5_value;
static const lean_string_object l_Lean_instReprHeadIndex_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.HeadIndex.fvar"};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__6 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__6_value;
static const lean_ctor_object l_Lean_instReprHeadIndex_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprHeadIndex_repr___closed__6_value)}};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__7 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__7_value;
static const lean_ctor_object l_Lean_instReprHeadIndex_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprHeadIndex_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__8 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__8_value;
static lean_once_cell_t l_Lean_instReprHeadIndex_repr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprHeadIndex_repr___closed__9;
static lean_once_cell_t l_Lean_instReprHeadIndex_repr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprHeadIndex_repr___closed__10;
static const lean_string_object l_Lean_instReprHeadIndex_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.HeadIndex.mvar"};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__11 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__11_value;
static const lean_ctor_object l_Lean_instReprHeadIndex_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprHeadIndex_repr___closed__11_value)}};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__12 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__12_value;
static const lean_ctor_object l_Lean_instReprHeadIndex_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprHeadIndex_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__13 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__13_value;
static const lean_string_object l_Lean_instReprHeadIndex_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.HeadIndex.const"};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__14 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__14_value;
static const lean_ctor_object l_Lean_instReprHeadIndex_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprHeadIndex_repr___closed__14_value)}};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__15 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__15_value;
static const lean_ctor_object l_Lean_instReprHeadIndex_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprHeadIndex_repr___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__16 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__16_value;
static const lean_string_object l_Lean_instReprHeadIndex_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.HeadIndex.proj"};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__17 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__17_value;
static const lean_ctor_object l_Lean_instReprHeadIndex_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprHeadIndex_repr___closed__17_value)}};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__18 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__18_value;
static const lean_ctor_object l_Lean_instReprHeadIndex_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprHeadIndex_repr___closed__18_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__19 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__19_value;
static const lean_string_object l_Lean_instReprHeadIndex_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.HeadIndex.lit"};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__20 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__20_value;
static const lean_ctor_object l_Lean_instReprHeadIndex_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprHeadIndex_repr___closed__20_value)}};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__21 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__21_value;
static const lean_ctor_object l_Lean_instReprHeadIndex_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprHeadIndex_repr___closed__21_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprHeadIndex_repr___closed__22 = (const lean_object*)&l_Lean_instReprHeadIndex_repr___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_instReprHeadIndex_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprHeadIndex_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprHeadIndex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprHeadIndex_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprHeadIndex___closed__0 = (const lean_object*)&l_Lean_instReprHeadIndex___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprHeadIndex = (const lean_object*)&l_Lean_instReprHeadIndex___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_HeadIndex_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableHeadIndex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_HeadIndex_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableHeadIndex___closed__0 = (const lean_object*)&l_Lean_instHashableHeadIndex___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableHeadIndex = (const lean_object*)&l_Lean_instHashableHeadIndex___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0 = (const lean_object*)&l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1 = (const lean_object*)&l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2 = (const lean_object*)&l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(lean_object*);
static const lean_string_object l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.HeadIndex"};
static const lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0 = (const lean_object*)&l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0_value;
static const lean_string_object l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "_private.Lean.HeadIndex.0.Lean.Expr.toHeadIndexSlow"};
static const lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1 = (const lean_object*)&l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1_value;
static const lean_string_object l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected expression kind"};
static const lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2 = (const lean_object*)&l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2_value;
static lean_once_cell_t l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_HeadIndex_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 0:
{
lean_object* v_fvarId_7_; lean_object* v___x_8_; 
v_fvarId_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_fvarId_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_fvarId_7_);
return v___x_8_;
}
case 1:
{
lean_object* v_mvarId_9_; lean_object* v___x_10_; 
v_mvarId_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_mvarId_9_);
lean_dec_ref_known(v_t_5_, 1);
v___x_10_ = lean_apply_1(v_k_6_, v_mvarId_9_);
return v___x_10_;
}
case 2:
{
lean_object* v_constName_11_; lean_object* v___x_12_; 
v_constName_11_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_constName_11_);
lean_dec_ref_known(v_t_5_, 1);
v___x_12_ = lean_apply_1(v_k_6_, v_constName_11_);
return v___x_12_;
}
case 3:
{
lean_object* v_structName_13_; lean_object* v_idx_14_; lean_object* v___x_15_; 
v_structName_13_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_structName_13_);
v_idx_14_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_idx_14_);
lean_dec_ref_known(v_t_5_, 2);
v___x_15_ = lean_apply_2(v_k_6_, v_structName_13_, v_idx_14_);
return v___x_15_;
}
case 4:
{
lean_object* v_litVal_16_; lean_object* v___x_17_; 
v_litVal_16_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_litVal_16_);
lean_dec_ref_known(v_t_5_, 1);
v___x_17_ = lean_apply_1(v_k_6_, v_litVal_16_);
return v___x_17_;
}
default: 
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorElim(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorElim___boxed(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_HeadIndex_ctorElim(v_motive_24_, v_ctorIdx_25_, v_t_26_, v_h_27_, v_k_28_);
lean_dec(v_ctorIdx_25_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_fvar_elim___redArg(lean_object* v_t_30_, lean_object* v_fvar_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_30_, v_fvar_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_fvar_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_fvar_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_34_, v_fvar_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_mvar_elim___redArg(lean_object* v_t_38_, lean_object* v_mvar_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_38_, v_mvar_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_mvar_elim(lean_object* v_motive_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_mvar_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_42_, v_mvar_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_const_elim___redArg(lean_object* v_t_46_, lean_object* v_const_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_46_, v_const_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_const_elim(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_const_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_50_, v_const_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_proj_elim___redArg(lean_object* v_t_54_, lean_object* v_proj_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_54_, v_proj_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_proj_elim(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_proj_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_58_, v_proj_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lit_elim___redArg(lean_object* v_t_62_, lean_object* v_lit_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_62_, v_lit_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lit_elim(lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_lit_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_66_, v_lit_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_sort_elim___redArg(lean_object* v_t_70_, lean_object* v_sort_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_70_, v_sort_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_sort_elim(lean_object* v_motive_73_, lean_object* v_t_74_, lean_object* v_h_75_, lean_object* v_sort_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_74_, v_sort_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lam_elim___redArg(lean_object* v_t_78_, lean_object* v_lam_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_78_, v_lam_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lam_elim(lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_lam_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_82_, v_lam_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_forallE_elim___redArg(lean_object* v_t_86_, lean_object* v_forallE_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_86_, v_forallE_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_forallE_elim(lean_object* v_motive_89_, lean_object* v_t_90_, lean_object* v_h_91_, lean_object* v_forallE_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_90_, v_forallE_92_);
return v___x_93_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqHeadIndex_beq(lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
switch(lean_obj_tag(v_x_98_))
{
case 0:
{
if (lean_obj_tag(v_x_99_) == 0)
{
lean_object* v_fvarId_100_; lean_object* v_fvarId_101_; uint8_t v___x_102_; 
v_fvarId_100_ = lean_ctor_get(v_x_98_, 0);
v_fvarId_101_ = lean_ctor_get(v_x_99_, 0);
v___x_102_ = l_Lean_instBEqFVarId_beq(v_fvarId_100_, v_fvarId_101_);
return v___x_102_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = 0;
return v___x_103_;
}
}
case 1:
{
if (lean_obj_tag(v_x_99_) == 1)
{
lean_object* v_mvarId_104_; lean_object* v_mvarId_105_; uint8_t v___x_106_; 
v_mvarId_104_ = lean_ctor_get(v_x_98_, 0);
v_mvarId_105_ = lean_ctor_get(v_x_99_, 0);
v___x_106_ = l_Lean_instBEqMVarId_beq(v_mvarId_104_, v_mvarId_105_);
return v___x_106_;
}
else
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
}
case 2:
{
if (lean_obj_tag(v_x_99_) == 2)
{
lean_object* v_constName_108_; lean_object* v_constName_109_; uint8_t v___x_110_; 
v_constName_108_ = lean_ctor_get(v_x_98_, 0);
v_constName_109_ = lean_ctor_get(v_x_99_, 0);
v___x_110_ = lean_name_eq(v_constName_108_, v_constName_109_);
return v___x_110_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
}
case 3:
{
if (lean_obj_tag(v_x_99_) == 3)
{
lean_object* v_structName_112_; lean_object* v_idx_113_; lean_object* v_structName_114_; lean_object* v_idx_115_; uint8_t v___x_116_; 
v_structName_112_ = lean_ctor_get(v_x_98_, 0);
v_idx_113_ = lean_ctor_get(v_x_98_, 1);
v_structName_114_ = lean_ctor_get(v_x_99_, 0);
v_idx_115_ = lean_ctor_get(v_x_99_, 1);
v___x_116_ = lean_name_eq(v_structName_112_, v_structName_114_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
uint8_t v___x_117_; 
v___x_117_ = lean_nat_dec_eq(v_idx_113_, v_idx_115_);
return v___x_117_;
}
}
else
{
uint8_t v___x_118_; 
v___x_118_ = 0;
return v___x_118_;
}
}
case 4:
{
if (lean_obj_tag(v_x_99_) == 4)
{
lean_object* v_litVal_119_; lean_object* v_litVal_120_; uint8_t v___x_121_; 
v_litVal_119_ = lean_ctor_get(v_x_98_, 0);
v_litVal_120_ = lean_ctor_get(v_x_99_, 0);
v___x_121_ = l_Lean_instBEqLiteral_beq(v_litVal_119_, v_litVal_120_);
return v___x_121_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
}
case 5:
{
if (lean_obj_tag(v_x_99_) == 5)
{
uint8_t v___x_123_; 
v___x_123_ = 1;
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 0;
return v___x_124_;
}
}
case 6:
{
if (lean_obj_tag(v_x_99_) == 6)
{
uint8_t v___x_125_; 
v___x_125_ = 1;
return v___x_125_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 0;
return v___x_126_;
}
}
default: 
{
if (lean_obj_tag(v_x_99_) == 7)
{
uint8_t v___x_127_; 
v___x_127_ = 1;
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 0;
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqHeadIndex_beq___boxed(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Lean_instBEqHeadIndex_beq(v_x_129_, v_x_130_);
lean_dec(v_x_130_);
lean_dec(v_x_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
static lean_object* _init_l_Lean_instReprHeadIndex_repr___closed__9(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(2u);
v___x_151_ = lean_nat_to_int(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_instReprHeadIndex_repr___closed__10(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = lean_nat_to_int(v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprHeadIndex_repr(lean_object* v_x_178_, lean_object* v_prec_179_){
_start:
{
lean_object* v___y_181_; lean_object* v___y_188_; lean_object* v___y_195_; 
switch(lean_obj_tag(v_x_178_))
{
case 0:
{
lean_object* v_fvarId_201_; lean_object* v___y_203_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_fvarId_201_ = lean_ctor_get(v_x_178_, 0);
lean_inc(v_fvarId_201_);
lean_dec_ref_known(v_x_178_, 1);
v___x_212_ = lean_unsigned_to_nat(1024u);
v___x_213_ = lean_nat_dec_le(v___x_212_, v_prec_179_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_203_ = v___x_214_;
goto v___jp_202_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_203_ = v___x_215_;
goto v___jp_202_;
}
v___jp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_204_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__8));
v___x_205_ = lean_unsigned_to_nat(1024u);
v___x_206_ = l_Lean_Name_reprPrec(v_fvarId_201_, v___x_205_);
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_204_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_inc(v___y_203_);
v___x_208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_208_, 0, v___y_203_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_209_);
v___x_211_ = l_Repr_addAppParen(v___x_210_, v_prec_179_);
return v___x_211_;
}
}
case 1:
{
lean_object* v_mvarId_216_; lean_object* v___y_218_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_mvarId_216_ = lean_ctor_get(v_x_178_, 0);
lean_inc(v_mvarId_216_);
lean_dec_ref_known(v_x_178_, 1);
v___x_227_ = lean_unsigned_to_nat(1024u);
v___x_228_ = lean_nat_dec_le(v___x_227_, v_prec_179_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
v___x_229_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_218_ = v___x_229_;
goto v___jp_217_;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_218_ = v___x_230_;
goto v___jp_217_;
}
v___jp_217_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_219_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__13));
v___x_220_ = lean_unsigned_to_nat(1024u);
v___x_221_ = l_Lean_Name_reprPrec(v_mvarId_216_, v___x_220_);
v___x_222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_219_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
lean_inc(v___y_218_);
v___x_223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_223_, 0, v___y_218_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = 0;
v___x_225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_224_);
v___x_226_ = l_Repr_addAppParen(v___x_225_, v_prec_179_);
return v___x_226_;
}
}
case 2:
{
lean_object* v_constName_231_; lean_object* v___y_233_; lean_object* v___x_242_; uint8_t v___x_243_; 
v_constName_231_ = lean_ctor_get(v_x_178_, 0);
lean_inc(v_constName_231_);
lean_dec_ref_known(v_x_178_, 1);
v___x_242_ = lean_unsigned_to_nat(1024u);
v___x_243_ = lean_nat_dec_le(v___x_242_, v_prec_179_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
v___x_244_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_233_ = v___x_244_;
goto v___jp_232_;
}
else
{
lean_object* v___x_245_; 
v___x_245_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_233_ = v___x_245_;
goto v___jp_232_;
}
v___jp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_234_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__16));
v___x_235_ = lean_unsigned_to_nat(1024u);
v___x_236_ = l_Lean_Name_reprPrec(v_constName_231_, v___x_235_);
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_234_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
lean_inc(v___y_233_);
v___x_238_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_238_, 0, v___y_233_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = 0;
v___x_240_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set_uint8(v___x_240_, sizeof(void*)*1, v___x_239_);
v___x_241_ = l_Repr_addAppParen(v___x_240_, v_prec_179_);
return v___x_241_;
}
}
case 3:
{
lean_object* v_structName_246_; lean_object* v_idx_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_272_; 
v_structName_246_ = lean_ctor_get(v_x_178_, 0);
v_idx_247_ = lean_ctor_get(v_x_178_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_272_ == 0)
{
v___x_249_ = v_x_178_;
v_isShared_250_ = v_isSharedCheck_272_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_idx_247_);
lean_inc(v_structName_246_);
lean_dec(v_x_178_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_272_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___y_252_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1024u);
v___x_269_ = lean_nat_dec_le(v___x_268_, v_prec_179_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_252_ = v___x_270_;
goto v___jp_251_;
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_252_ = v___x_271_;
goto v___jp_251_;
}
v___jp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_253_ = lean_box(1);
v___x_254_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__19));
v___x_255_ = lean_unsigned_to_nat(1024u);
v___x_256_ = l_Lean_Name_reprPrec(v_structName_246_, v___x_255_);
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 5);
lean_ctor_set(v___x_249_, 1, v___x_256_);
lean_ctor_set(v___x_249_, 0, v___x_254_);
v___x_258_ = v___x_249_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_256_);
v___x_258_ = v_reuseFailAlloc_267_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_253_);
v___x_260_ = l_Nat_reprFast(v_idx_247_);
v___x_261_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_259_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
lean_inc(v___y_252_);
v___x_263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_263_, 0, v___y_252_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = 0;
v___x_265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_264_);
v___x_266_ = l_Repr_addAppParen(v___x_265_, v_prec_179_);
return v___x_266_;
}
}
}
}
case 4:
{
lean_object* v_litVal_273_; lean_object* v___y_275_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_litVal_273_ = lean_ctor_get(v_x_178_, 0);
lean_inc_ref(v_litVal_273_);
lean_dec_ref_known(v_x_178_, 1);
v___x_284_ = lean_unsigned_to_nat(1024u);
v___x_285_ = lean_nat_dec_le(v___x_284_, v_prec_179_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
v___x_286_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_275_ = v___x_286_;
goto v___jp_274_;
}
else
{
lean_object* v___x_287_; 
v___x_287_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_275_ = v___x_287_;
goto v___jp_274_;
}
v___jp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_276_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__22));
v___x_277_ = lean_unsigned_to_nat(1024u);
v___x_278_ = l_Lean_instReprLiteral_repr(v_litVal_273_, v___x_277_);
v___x_279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_276_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
lean_inc(v___y_275_);
v___x_280_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_280_, 0, v___y_275_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = 0;
v___x_282_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*1, v___x_281_);
v___x_283_ = l_Repr_addAppParen(v___x_282_, v_prec_179_);
return v___x_283_;
}
}
case 5:
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(1024u);
v___x_289_ = lean_nat_dec_le(v___x_288_, v_prec_179_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_181_ = v___x_290_;
goto v___jp_180_;
}
else
{
lean_object* v___x_291_; 
v___x_291_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_181_ = v___x_291_;
goto v___jp_180_;
}
}
case 6:
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_unsigned_to_nat(1024u);
v___x_293_ = lean_nat_dec_le(v___x_292_, v_prec_179_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_188_ = v___x_294_;
goto v___jp_187_;
}
else
{
lean_object* v___x_295_; 
v___x_295_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_188_ = v___x_295_;
goto v___jp_187_;
}
}
default: 
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(1024u);
v___x_297_ = lean_nat_dec_le(v___x_296_, v_prec_179_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_195_ = v___x_298_;
goto v___jp_194_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_195_ = v___x_299_;
goto v___jp_194_;
}
}
}
v___jp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_182_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__1));
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
v___jp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_189_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__3));
lean_inc(v___y_188_);
v___x_190_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_190_, 0, v___y_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = 0;
v___x_192_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*1, v___x_191_);
v___x_193_ = l_Repr_addAppParen(v___x_192_, v_prec_179_);
return v___x_193_;
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_196_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__5));
lean_inc(v___y_195_);
v___x_197_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_197_, 0, v___y_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = 0;
v___x_199_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*1, v___x_198_);
v___x_200_ = l_Repr_addAppParen(v___x_199_, v_prec_179_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprHeadIndex_repr___boxed(lean_object* v_x_300_, lean_object* v_prec_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_instReprHeadIndex_repr(v_x_300_, v_prec_301_);
lean_dec(v_prec_301_);
return v_res_302_;
}
}
LEAN_EXPORT uint64_t l_Lean_HeadIndex_hash(lean_object* v_x_305_){
_start:
{
switch(lean_obj_tag(v_x_305_))
{
case 0:
{
lean_object* v_fvarId_306_; uint64_t v___x_307_; uint64_t v___x_308_; uint64_t v___x_309_; 
v_fvarId_306_ = lean_ctor_get(v_x_305_, 0);
v___x_307_ = 11ULL;
v___x_308_ = l_Lean_instHashableFVarId_hash(v_fvarId_306_);
v___x_309_ = lean_uint64_mix_hash(v___x_307_, v___x_308_);
return v___x_309_;
}
case 1:
{
lean_object* v_mvarId_310_; uint64_t v___x_311_; uint64_t v___x_312_; uint64_t v___x_313_; 
v_mvarId_310_ = lean_ctor_get(v_x_305_, 0);
v___x_311_ = 13ULL;
v___x_312_ = l_Lean_instHashableMVarId_hash(v_mvarId_310_);
v___x_313_ = lean_uint64_mix_hash(v___x_311_, v___x_312_);
return v___x_313_;
}
case 2:
{
lean_object* v_constName_314_; uint64_t v___x_315_; 
v_constName_314_ = lean_ctor_get(v_x_305_, 0);
v___x_315_ = 17ULL;
if (lean_obj_tag(v_constName_314_) == 0)
{
uint64_t v___x_316_; 
v___x_316_ = 2279351621866777156ULL;
return v___x_316_;
}
else
{
uint64_t v_hash_317_; uint64_t v___x_318_; 
v_hash_317_ = lean_ctor_get_uint64(v_constName_314_, sizeof(void*)*2);
v___x_318_ = lean_uint64_mix_hash(v___x_315_, v_hash_317_);
return v___x_318_;
}
}
case 3:
{
lean_object* v_structName_319_; lean_object* v_idx_320_; uint64_t v___x_321_; uint64_t v___y_323_; 
v_structName_319_ = lean_ctor_get(v_x_305_, 0);
v_idx_320_ = lean_ctor_get(v_x_305_, 1);
v___x_321_ = 19ULL;
if (lean_obj_tag(v_structName_319_) == 0)
{
uint64_t v___x_327_; 
v___x_327_ = 1723ULL;
v___y_323_ = v___x_327_;
goto v___jp_322_;
}
else
{
uint64_t v_hash_328_; 
v_hash_328_ = lean_ctor_get_uint64(v_structName_319_, sizeof(void*)*2);
v___y_323_ = v_hash_328_;
goto v___jp_322_;
}
v___jp_322_:
{
uint64_t v___x_324_; uint64_t v___x_325_; uint64_t v___x_326_; 
v___x_324_ = lean_uint64_of_nat(v_idx_320_);
v___x_325_ = lean_uint64_mix_hash(v___y_323_, v___x_324_);
v___x_326_ = lean_uint64_mix_hash(v___x_321_, v___x_325_);
return v___x_326_;
}
}
case 4:
{
lean_object* v_litVal_329_; uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; 
v_litVal_329_ = lean_ctor_get(v_x_305_, 0);
v___x_330_ = 23ULL;
v___x_331_ = l_Lean_Literal_hash(v_litVal_329_);
v___x_332_ = lean_uint64_mix_hash(v___x_330_, v___x_331_);
return v___x_332_;
}
case 5:
{
uint64_t v___x_333_; 
v___x_333_ = 29ULL;
return v___x_333_;
}
case 6:
{
uint64_t v___x_334_; 
v___x_334_ = 31ULL;
return v___x_334_;
}
default: 
{
uint64_t v___x_335_; 
v___x_335_ = 37ULL;
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_hash___boxed(lean_object* v_x_336_){
_start:
{
uint64_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Lean_HeadIndex_hash(v_x_336_);
lean_dec(v_x_336_);
v_r_338_ = lean_box_uint64(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
switch(lean_obj_tag(v_a_341_))
{
case 5:
{
lean_object* v_fn_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_fn_343_ = lean_ctor_get(v_a_341_, 0);
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = lean_nat_add(v_a_342_, v___x_344_);
lean_dec(v_a_342_);
v_a_341_ = v_fn_343_;
v_a_342_ = v___x_345_;
goto _start;
}
case 8:
{
lean_object* v_body_347_; 
v_body_347_ = lean_ctor_get(v_a_341_, 3);
v_a_341_ = v_body_347_;
goto _start;
}
case 10:
{
lean_object* v_expr_349_; 
v_expr_349_ = lean_ctor_get(v_a_341_, 1);
v_a_341_ = v_expr_349_;
goto _start;
}
default: 
{
return v_a_342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go___boxed(lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(v_a_351_, v_a_352_);
lean_dec_ref(v_a_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs(lean_object* v_e_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(v_e_354_, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs___boxed(lean_object* v_e_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Expr_headNumArgs(v_e_357_);
lean_dec_ref(v_e_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(lean_object* v_x_365_){
_start:
{
switch(lean_obj_tag(v_x_365_))
{
case 2:
{
lean_object* v_mvarId_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_mvarId_366_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_mvarId_366_);
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v_mvarId_366_);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
case 1:
{
lean_object* v_fvarId_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_fvarId_369_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_fvarId_369_);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v_fvarId_369_);
v___x_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
case 4:
{
lean_object* v_declName_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_declName_372_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_declName_372_);
v___x_373_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_373_, 0, v_declName_372_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
case 11:
{
lean_object* v_typeName_375_; lean_object* v_idx_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_typeName_375_ = lean_ctor_get(v_x_365_, 0);
v_idx_376_ = lean_ctor_get(v_x_365_, 1);
lean_inc(v_idx_376_);
lean_inc(v_typeName_375_);
v___x_377_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_377_, 0, v_typeName_375_);
lean_ctor_set(v___x_377_, 1, v_idx_376_);
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
case 3:
{
lean_object* v___x_379_; 
v___x_379_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0));
return v___x_379_;
}
case 6:
{
lean_object* v___x_380_; 
v___x_380_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1));
return v___x_380_;
}
case 7:
{
lean_object* v___x_381_; 
v___x_381_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2));
return v___x_381_;
}
case 9:
{
lean_object* v_a_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_a_382_ = lean_ctor_get(v_x_365_, 0);
lean_inc_ref(v_a_382_);
v___x_383_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_383_, 0, v_a_382_);
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
case 5:
{
lean_object* v_fn_385_; 
v_fn_385_ = lean_ctor_get(v_x_365_, 0);
v_x_365_ = v_fn_385_;
goto _start;
}
case 8:
{
lean_object* v_body_387_; 
v_body_387_ = lean_ctor_get(v_x_365_, 3);
v_x_365_ = v_body_387_;
goto _start;
}
case 10:
{
lean_object* v_expr_389_; 
v_expr_389_ = lean_ctor_get(v_x_365_, 1);
v_x_365_ = v_expr_389_;
goto _start;
}
default: 
{
lean_object* v___x_391_; 
v___x_391_ = lean_box(0);
return v___x_391_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___boxed(lean_object* v_x_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(v_x_392_);
lean_dec_ref(v_x_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(lean_object* v_msg_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_instInhabitedHeadIndex_default));
v___x_396_ = lean_panic_fn_borrowed(v___x_395_, v_msg_394_);
return v___x_396_;
}
}
static lean_object* _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_400_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2));
v___x_401_ = lean_unsigned_to_nat(31u);
v___x_402_ = lean_unsigned_to_nat(104u);
v___x_403_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1));
v___x_404_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0));
v___x_405_ = l_mkPanicMessageWithDecl(v___x_404_, v___x_403_, v___x_402_, v___x_401_, v___x_400_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(lean_object* v_x_406_){
_start:
{
switch(lean_obj_tag(v_x_406_))
{
case 2:
{
lean_object* v_mvarId_407_; lean_object* v___x_408_; 
v_mvarId_407_ = lean_ctor_get(v_x_406_, 0);
lean_inc(v_mvarId_407_);
lean_dec_ref_known(v_x_406_, 1);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v_mvarId_407_);
return v___x_408_;
}
case 1:
{
lean_object* v_fvarId_409_; lean_object* v___x_410_; 
v_fvarId_409_ = lean_ctor_get(v_x_406_, 0);
lean_inc(v_fvarId_409_);
lean_dec_ref_known(v_x_406_, 1);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v_fvarId_409_);
return v___x_410_;
}
case 4:
{
lean_object* v_declName_411_; lean_object* v___x_412_; 
v_declName_411_ = lean_ctor_get(v_x_406_, 0);
lean_inc(v_declName_411_);
lean_dec_ref_known(v_x_406_, 2);
v___x_412_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_412_, 0, v_declName_411_);
return v___x_412_;
}
case 11:
{
lean_object* v_typeName_413_; lean_object* v_idx_414_; lean_object* v___x_415_; 
v_typeName_413_ = lean_ctor_get(v_x_406_, 0);
lean_inc(v_typeName_413_);
v_idx_414_ = lean_ctor_get(v_x_406_, 1);
lean_inc(v_idx_414_);
lean_dec_ref_known(v_x_406_, 3);
v___x_415_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_415_, 0, v_typeName_413_);
lean_ctor_set(v___x_415_, 1, v_idx_414_);
return v___x_415_;
}
case 3:
{
lean_object* v___x_416_; 
lean_dec_ref_known(v_x_406_, 1);
v___x_416_ = lean_box(5);
return v___x_416_;
}
case 6:
{
lean_object* v___x_417_; 
lean_dec_ref_known(v_x_406_, 3);
v___x_417_ = lean_box(6);
return v___x_417_;
}
case 7:
{
lean_object* v___x_418_; 
lean_dec_ref_known(v_x_406_, 3);
v___x_418_ = lean_box(7);
return v___x_418_;
}
case 9:
{
lean_object* v_a_419_; lean_object* v___x_420_; 
v_a_419_ = lean_ctor_get(v_x_406_, 0);
lean_inc_ref(v_a_419_);
lean_dec_ref_known(v_x_406_, 1);
v___x_420_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_420_, 0, v_a_419_);
return v___x_420_;
}
case 5:
{
lean_object* v_fn_421_; 
v_fn_421_ = lean_ctor_get(v_x_406_, 0);
lean_inc_ref(v_fn_421_);
lean_dec_ref_known(v_x_406_, 2);
v_x_406_ = v_fn_421_;
goto _start;
}
case 8:
{
lean_object* v_value_423_; lean_object* v_body_424_; lean_object* v___x_425_; 
v_value_423_ = lean_ctor_get(v_x_406_, 2);
lean_inc_ref(v_value_423_);
v_body_424_ = lean_ctor_get(v_x_406_, 3);
lean_inc_ref(v_body_424_);
lean_dec_ref_known(v_x_406_, 4);
v___x_425_ = lean_expr_instantiate1(v_body_424_, v_value_423_);
lean_dec_ref(v_value_423_);
lean_dec_ref(v_body_424_);
v_x_406_ = v___x_425_;
goto _start;
}
case 10:
{
lean_object* v_expr_427_; 
v_expr_427_ = lean_ctor_get(v_x_406_, 1);
lean_inc_ref(v_expr_427_);
lean_dec_ref_known(v_x_406_, 2);
v_x_406_ = v_expr_427_;
goto _start;
}
default: 
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec_ref(v_x_406_);
v___x_429_ = lean_obj_once(&l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3, &l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3_once, _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3);
v___x_430_ = l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(v___x_429_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_toHeadIndex(lean_object* v_e_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(v_e_431_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_433_; 
v___x_433_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(v_e_431_);
return v___x_433_;
}
else
{
lean_object* v_val_434_; 
lean_dec_ref(v_e_431_);
v_val_434_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v___x_432_, 1);
return v_val_434_;
}
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_HeadIndex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_HeadIndex(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_HeadIndex(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_HeadIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_HeadIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_HeadIndex(builtin);
}
#ifdef __cplusplus
}
#endif
