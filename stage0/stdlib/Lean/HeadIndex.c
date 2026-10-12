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
uint8_t l_Lean_instBEqHeadIndex_beq(lean_object* v_x_98_, lean_object* v_x_99_){
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
LEAN_EXPORT void l_Lean_instBEqHeadIndex_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_98_ = stack[0].m_obj;
lean_object* v_x_99_ = stack[1].m_obj;
uint8_t v_res_129_;
v_res_129_ = l_Lean_instBEqHeadIndex_beq(v_x_98_, v_x_99_);
stack->m_num = v_res_129_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqHeadIndex_beq___boxed(lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lean_instBEqHeadIndex_beq(v_x_130_, v_x_131_);
lean_dec(v_x_131_);
lean_dec(v_x_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
static lean_object* _init_l_Lean_instReprHeadIndex_repr___closed__9(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(2u);
v___x_152_ = lean_nat_to_int(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_instReprHeadIndex_repr___closed__10(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_nat_to_int(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprHeadIndex_repr(lean_object* v_x_179_, lean_object* v_prec_180_){
_start:
{
lean_object* v___y_182_; lean_object* v___y_189_; lean_object* v___y_196_; 
switch(lean_obj_tag(v_x_179_))
{
case 0:
{
lean_object* v_fvarId_202_; lean_object* v___y_204_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_fvarId_202_ = lean_ctor_get(v_x_179_, 0);
lean_inc(v_fvarId_202_);
lean_dec_ref_known(v_x_179_, 1);
v___x_213_ = lean_unsigned_to_nat(1024u);
v___x_214_ = lean_nat_dec_le(v___x_213_, v_prec_180_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_204_ = v___x_215_;
goto v___jp_203_;
}
else
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_204_ = v___x_216_;
goto v___jp_203_;
}
v___jp_203_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_205_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__8));
v___x_206_ = lean_unsigned_to_nat(1024u);
v___x_207_ = l_Lean_Name_reprPrec(v_fvarId_202_, v___x_206_);
v___x_208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_205_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
lean_inc(v___y_204_);
v___x_209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_209_, 0, v___y_204_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = 0;
v___x_211_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*1, v___x_210_);
v___x_212_ = l_Repr_addAppParen(v___x_211_, v_prec_180_);
return v___x_212_;
}
}
case 1:
{
lean_object* v_mvarId_217_; lean_object* v___y_219_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_mvarId_217_ = lean_ctor_get(v_x_179_, 0);
lean_inc(v_mvarId_217_);
lean_dec_ref_known(v_x_179_, 1);
v___x_228_ = lean_unsigned_to_nat(1024u);
v___x_229_ = lean_nat_dec_le(v___x_228_, v_prec_180_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
v___x_230_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_219_ = v___x_230_;
goto v___jp_218_;
}
else
{
lean_object* v___x_231_; 
v___x_231_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_219_ = v___x_231_;
goto v___jp_218_;
}
v___jp_218_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_220_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__13));
v___x_221_ = lean_unsigned_to_nat(1024u);
v___x_222_ = l_Lean_Name_reprPrec(v_mvarId_217_, v___x_221_);
v___x_223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_220_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
lean_inc(v___y_219_);
v___x_224_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_224_, 0, v___y_219_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = 0;
v___x_226_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1, v___x_225_);
v___x_227_ = l_Repr_addAppParen(v___x_226_, v_prec_180_);
return v___x_227_;
}
}
case 2:
{
lean_object* v_constName_232_; lean_object* v___y_234_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_constName_232_ = lean_ctor_get(v_x_179_, 0);
lean_inc(v_constName_232_);
lean_dec_ref_known(v_x_179_, 1);
v___x_243_ = lean_unsigned_to_nat(1024u);
v___x_244_ = lean_nat_dec_le(v___x_243_, v_prec_180_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; 
v___x_245_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_234_ = v___x_245_;
goto v___jp_233_;
}
else
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_234_ = v___x_246_;
goto v___jp_233_;
}
v___jp_233_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_235_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__16));
v___x_236_ = lean_unsigned_to_nat(1024u);
v___x_237_ = l_Lean_Name_reprPrec(v_constName_232_, v___x_236_);
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_235_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
lean_inc(v___y_234_);
v___x_239_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_239_, 0, v___y_234_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = 0;
v___x_241_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set_uint8(v___x_241_, sizeof(void*)*1, v___x_240_);
v___x_242_ = l_Repr_addAppParen(v___x_241_, v_prec_180_);
return v___x_242_;
}
}
case 3:
{
lean_object* v_structName_247_; lean_object* v_idx_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_273_; 
v_structName_247_ = lean_ctor_get(v_x_179_, 0);
v_idx_248_ = lean_ctor_get(v_x_179_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_273_ == 0)
{
v___x_250_ = v_x_179_;
v_isShared_251_ = v_isSharedCheck_273_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_idx_248_);
lean_inc(v_structName_247_);
lean_dec(v_x_179_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_273_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___y_253_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_unsigned_to_nat(1024u);
v___x_270_ = lean_nat_dec_le(v___x_269_, v_prec_180_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_253_ = v___x_271_;
goto v___jp_252_;
}
else
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_253_ = v___x_272_;
goto v___jp_252_;
}
v___jp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_254_ = lean_box(1);
v___x_255_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__19));
v___x_256_ = lean_unsigned_to_nat(1024u);
v___x_257_ = l_Lean_Name_reprPrec(v_structName_247_, v___x_256_);
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 5);
lean_ctor_set(v___x_250_, 1, v___x_257_);
lean_ctor_set(v___x_250_, 0, v___x_255_);
v___x_259_ = v___x_250_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_268_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_254_);
v___x_261_ = l_Nat_reprFast(v_idx_248_);
v___x_262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
v___x_263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_260_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
lean_inc(v___y_253_);
v___x_264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_264_, 0, v___y_253_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = 0;
v___x_266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*1, v___x_265_);
v___x_267_ = l_Repr_addAppParen(v___x_266_, v_prec_180_);
return v___x_267_;
}
}
}
}
case 4:
{
lean_object* v_litVal_274_; lean_object* v___y_276_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_litVal_274_ = lean_ctor_get(v_x_179_, 0);
lean_inc_ref(v_litVal_274_);
lean_dec_ref_known(v_x_179_, 1);
v___x_285_ = lean_unsigned_to_nat(1024u);
v___x_286_ = lean_nat_dec_le(v___x_285_, v_prec_180_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
v___x_287_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_276_ = v___x_287_;
goto v___jp_275_;
}
else
{
lean_object* v___x_288_; 
v___x_288_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_276_ = v___x_288_;
goto v___jp_275_;
}
v___jp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_277_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__22));
v___x_278_ = lean_unsigned_to_nat(1024u);
v___x_279_ = l_Lean_instReprLiteral_repr(v_litVal_274_, v___x_278_);
v___x_280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_277_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
lean_inc(v___y_276_);
v___x_281_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_281_, 0, v___y_276_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = 0;
v___x_283_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*1, v___x_282_);
v___x_284_ = l_Repr_addAppParen(v___x_283_, v_prec_180_);
return v___x_284_;
}
}
case 5:
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(1024u);
v___x_290_ = lean_nat_dec_le(v___x_289_, v_prec_180_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
v___x_291_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_182_ = v___x_291_;
goto v___jp_181_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_182_ = v___x_292_;
goto v___jp_181_;
}
}
case 6:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(1024u);
v___x_294_ = lean_nat_dec_le(v___x_293_, v_prec_180_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_189_ = v___x_295_;
goto v___jp_188_;
}
else
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_189_ = v___x_296_;
goto v___jp_188_;
}
}
default: 
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(1024u);
v___x_298_ = lean_nat_dec_le(v___x_297_, v_prec_180_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_196_ = v___x_299_;
goto v___jp_195_;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_196_ = v___x_300_;
goto v___jp_195_;
}
}
}
v___jp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_183_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__1));
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
v___jp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_190_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__3));
lean_inc(v___y_189_);
v___x_191_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_191_, 0, v___y_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = 0;
v___x_193_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*1, v___x_192_);
v___x_194_ = l_Repr_addAppParen(v___x_193_, v_prec_180_);
return v___x_194_;
}
v___jp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_197_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__5));
lean_inc(v___y_196_);
v___x_198_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_198_, 0, v___y_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = 0;
v___x_200_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*1, v___x_199_);
v___x_201_ = l_Repr_addAppParen(v___x_200_, v_prec_180_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprHeadIndex_repr___boxed(lean_object* v_x_301_, lean_object* v_prec_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_instReprHeadIndex_repr(v_x_301_, v_prec_302_);
lean_dec(v_prec_302_);
return v_res_303_;
}
}
uint64_t l_Lean_HeadIndex_hash(lean_object* v_x_306_){
_start:
{
switch(lean_obj_tag(v_x_306_))
{
case 0:
{
lean_object* v_fvarId_307_; uint64_t v___x_308_; uint64_t v___x_309_; uint64_t v___x_310_; 
v_fvarId_307_ = lean_ctor_get(v_x_306_, 0);
v___x_308_ = 11ULL;
v___x_309_ = l_Lean_instHashableFVarId_hash(v_fvarId_307_);
v___x_310_ = lean_uint64_mix_hash(v___x_308_, v___x_309_);
return v___x_310_;
}
case 1:
{
lean_object* v_mvarId_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; 
v_mvarId_311_ = lean_ctor_get(v_x_306_, 0);
v___x_312_ = 13ULL;
v___x_313_ = l_Lean_instHashableMVarId_hash(v_mvarId_311_);
v___x_314_ = lean_uint64_mix_hash(v___x_312_, v___x_313_);
return v___x_314_;
}
case 2:
{
lean_object* v_constName_315_; uint64_t v___x_316_; 
v_constName_315_ = lean_ctor_get(v_x_306_, 0);
v___x_316_ = 17ULL;
if (lean_obj_tag(v_constName_315_) == 0)
{
uint64_t v___x_317_; 
v___x_317_ = 2279351621866777156ULL;
return v___x_317_;
}
else
{
uint64_t v_hash_318_; uint64_t v___x_319_; 
v_hash_318_ = lean_ctor_get_uint64(v_constName_315_, sizeof(void*)*2);
v___x_319_ = lean_uint64_mix_hash(v___x_316_, v_hash_318_);
return v___x_319_;
}
}
case 3:
{
lean_object* v_structName_320_; lean_object* v_idx_321_; uint64_t v___x_322_; uint64_t v___y_324_; 
v_structName_320_ = lean_ctor_get(v_x_306_, 0);
v_idx_321_ = lean_ctor_get(v_x_306_, 1);
v___x_322_ = 19ULL;
if (lean_obj_tag(v_structName_320_) == 0)
{
uint64_t v___x_328_; 
v___x_328_ = 1723ULL;
v___y_324_ = v___x_328_;
goto v___jp_323_;
}
else
{
uint64_t v_hash_329_; 
v_hash_329_ = lean_ctor_get_uint64(v_structName_320_, sizeof(void*)*2);
v___y_324_ = v_hash_329_;
goto v___jp_323_;
}
v___jp_323_:
{
uint64_t v___x_325_; uint64_t v___x_326_; uint64_t v___x_327_; 
v___x_325_ = lean_uint64_of_nat(v_idx_321_);
v___x_326_ = lean_uint64_mix_hash(v___y_324_, v___x_325_);
v___x_327_ = lean_uint64_mix_hash(v___x_322_, v___x_326_);
return v___x_327_;
}
}
case 4:
{
lean_object* v_litVal_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; 
v_litVal_330_ = lean_ctor_get(v_x_306_, 0);
v___x_331_ = 23ULL;
v___x_332_ = l_Lean_Literal_hash(v_litVal_330_);
v___x_333_ = lean_uint64_mix_hash(v___x_331_, v___x_332_);
return v___x_333_;
}
case 5:
{
uint64_t v___x_334_; 
v___x_334_ = 29ULL;
return v___x_334_;
}
case 6:
{
uint64_t v___x_335_; 
v___x_335_ = 31ULL;
return v___x_335_;
}
default: 
{
uint64_t v___x_336_; 
v___x_336_ = 37ULL;
return v___x_336_;
}
}
}
}
LEAN_EXPORT void l_Lean_HeadIndex_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_306_ = stack[0].m_obj;
uint64_t v_res_337_;
v_res_337_ = l_Lean_HeadIndex_hash(v_x_306_);
stack->m_num = v_res_337_;
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_hash___boxed(lean_object* v_x_338_){
_start:
{
uint64_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_Lean_HeadIndex_hash(v_x_338_);
lean_dec(v_x_338_);
v_r_340_ = lean_box_uint64(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
switch(lean_obj_tag(v_a_343_))
{
case 5:
{
lean_object* v_fn_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_fn_345_ = lean_ctor_get(v_a_343_, 0);
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_add(v_a_344_, v___x_346_);
lean_dec(v_a_344_);
v_a_343_ = v_fn_345_;
v_a_344_ = v___x_347_;
goto _start;
}
case 8:
{
lean_object* v_body_349_; 
v_body_349_ = lean_ctor_get(v_a_343_, 3);
v_a_343_ = v_body_349_;
goto _start;
}
case 10:
{
lean_object* v_expr_351_; 
v_expr_351_ = lean_ctor_get(v_a_343_, 1);
v_a_343_ = v_expr_351_;
goto _start;
}
default: 
{
return v_a_344_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go___boxed(lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(v_a_353_, v_a_354_);
lean_dec_ref(v_a_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs(lean_object* v_e_356_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(v_e_356_, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs___boxed(lean_object* v_e_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Expr_headNumArgs(v_e_359_);
lean_dec_ref(v_e_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(lean_object* v_x_367_){
_start:
{
switch(lean_obj_tag(v_x_367_))
{
case 2:
{
lean_object* v_mvarId_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_mvarId_368_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_mvarId_368_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v_mvarId_368_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
case 1:
{
lean_object* v_fvarId_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_fvarId_371_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_fvarId_371_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v_fvarId_371_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
case 4:
{
lean_object* v_declName_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_declName_374_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_declName_374_);
v___x_375_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_375_, 0, v_declName_374_);
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
case 11:
{
lean_object* v_typeName_377_; lean_object* v_idx_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_typeName_377_ = lean_ctor_get(v_x_367_, 0);
v_idx_378_ = lean_ctor_get(v_x_367_, 1);
lean_inc(v_idx_378_);
lean_inc(v_typeName_377_);
v___x_379_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_379_, 0, v_typeName_377_);
lean_ctor_set(v___x_379_, 1, v_idx_378_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
case 3:
{
lean_object* v___x_381_; 
v___x_381_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0));
return v___x_381_;
}
case 6:
{
lean_object* v___x_382_; 
v___x_382_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1));
return v___x_382_;
}
case 7:
{
lean_object* v___x_383_; 
v___x_383_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2));
return v___x_383_;
}
case 9:
{
lean_object* v_a_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_a_384_ = lean_ctor_get(v_x_367_, 0);
lean_inc_ref(v_a_384_);
v___x_385_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_385_, 0, v_a_384_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
case 5:
{
lean_object* v_fn_387_; 
v_fn_387_ = lean_ctor_get(v_x_367_, 0);
v_x_367_ = v_fn_387_;
goto _start;
}
case 8:
{
lean_object* v_body_389_; 
v_body_389_ = lean_ctor_get(v_x_367_, 3);
v_x_367_ = v_body_389_;
goto _start;
}
case 10:
{
lean_object* v_expr_391_; 
v_expr_391_ = lean_ctor_get(v_x_367_, 1);
v_x_367_ = v_expr_391_;
goto _start;
}
default: 
{
lean_object* v___x_393_; 
v___x_393_ = lean_box(0);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___boxed(lean_object* v_x_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(v_x_394_);
lean_dec_ref(v_x_394_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(lean_object* v_msg_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_instInhabitedHeadIndex_default));
v___x_398_ = lean_panic_fn_borrowed(v___x_397_, v_msg_396_);
return v___x_398_;
}
}
static lean_object* _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_402_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2));
v___x_403_ = lean_unsigned_to_nat(31u);
v___x_404_ = lean_unsigned_to_nat(104u);
v___x_405_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1));
v___x_406_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0));
v___x_407_ = l_mkPanicMessageWithDecl(v___x_406_, v___x_405_, v___x_404_, v___x_403_, v___x_402_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(lean_object* v_x_408_){
_start:
{
switch(lean_obj_tag(v_x_408_))
{
case 2:
{
lean_object* v_mvarId_409_; lean_object* v___x_410_; 
v_mvarId_409_ = lean_ctor_get(v_x_408_, 0);
lean_inc(v_mvarId_409_);
lean_dec_ref_known(v_x_408_, 1);
v___x_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_410_, 0, v_mvarId_409_);
return v___x_410_;
}
case 1:
{
lean_object* v_fvarId_411_; lean_object* v___x_412_; 
v_fvarId_411_ = lean_ctor_get(v_x_408_, 0);
lean_inc(v_fvarId_411_);
lean_dec_ref_known(v_x_408_, 1);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v_fvarId_411_);
return v___x_412_;
}
case 4:
{
lean_object* v_declName_413_; lean_object* v___x_414_; 
v_declName_413_ = lean_ctor_get(v_x_408_, 0);
lean_inc(v_declName_413_);
lean_dec_ref_known(v_x_408_, 2);
v___x_414_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_414_, 0, v_declName_413_);
return v___x_414_;
}
case 11:
{
lean_object* v_typeName_415_; lean_object* v_idx_416_; lean_object* v___x_417_; 
v_typeName_415_ = lean_ctor_get(v_x_408_, 0);
lean_inc(v_typeName_415_);
v_idx_416_ = lean_ctor_get(v_x_408_, 1);
lean_inc(v_idx_416_);
lean_dec_ref_known(v_x_408_, 3);
v___x_417_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_417_, 0, v_typeName_415_);
lean_ctor_set(v___x_417_, 1, v_idx_416_);
return v___x_417_;
}
case 3:
{
lean_object* v___x_418_; 
lean_dec_ref_known(v_x_408_, 1);
v___x_418_ = lean_box(5);
return v___x_418_;
}
case 6:
{
lean_object* v___x_419_; 
lean_dec_ref_known(v_x_408_, 3);
v___x_419_ = lean_box(6);
return v___x_419_;
}
case 7:
{
lean_object* v___x_420_; 
lean_dec_ref_known(v_x_408_, 3);
v___x_420_ = lean_box(7);
return v___x_420_;
}
case 9:
{
lean_object* v_a_421_; lean_object* v___x_422_; 
v_a_421_ = lean_ctor_get(v_x_408_, 0);
lean_inc_ref(v_a_421_);
lean_dec_ref_known(v_x_408_, 1);
v___x_422_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_422_, 0, v_a_421_);
return v___x_422_;
}
case 5:
{
lean_object* v_fn_423_; 
v_fn_423_ = lean_ctor_get(v_x_408_, 0);
lean_inc_ref(v_fn_423_);
lean_dec_ref_known(v_x_408_, 2);
v_x_408_ = v_fn_423_;
goto _start;
}
case 8:
{
lean_object* v_value_425_; lean_object* v_body_426_; lean_object* v___x_427_; 
v_value_425_ = lean_ctor_get(v_x_408_, 2);
lean_inc_ref(v_value_425_);
v_body_426_ = lean_ctor_get(v_x_408_, 3);
lean_inc_ref(v_body_426_);
lean_dec_ref_known(v_x_408_, 4);
v___x_427_ = lean_expr_instantiate1(v_body_426_, v_value_425_);
lean_dec_ref(v_value_425_);
lean_dec_ref(v_body_426_);
v_x_408_ = v___x_427_;
goto _start;
}
case 10:
{
lean_object* v_expr_429_; 
v_expr_429_ = lean_ctor_get(v_x_408_, 1);
lean_inc_ref(v_expr_429_);
lean_dec_ref_known(v_x_408_, 2);
v_x_408_ = v_expr_429_;
goto _start;
}
default: 
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec_ref(v_x_408_);
v___x_431_ = lean_obj_once(&l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3, &l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3_once, _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3);
v___x_432_ = l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(v___x_431_);
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_toHeadIndex(lean_object* v_e_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(v_e_433_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v___x_435_; 
v___x_435_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(v_e_433_);
return v___x_435_;
}
else
{
lean_object* v_val_436_; 
lean_dec_ref(v_e_433_);
v_val_436_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_434_, 1);
return v_val_436_;
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
