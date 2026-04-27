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
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_HeadIndex_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_HeadIndex_hash___closed__0;
static lean_once_cell_t l_Lean_HeadIndex_hash___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_HeadIndex_hash___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorIdx(lean_object* v_x_1_){
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
default: 
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(7u);
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorIdx___boxed(lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_HeadIndex_ctorIdx(v_x_10_);
lean_dec(v_x_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorElim___redArg(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
switch(lean_obj_tag(v_t_12_))
{
case 0:
{
lean_object* v_fvarId_14_; lean_object* v___x_15_; 
v_fvarId_14_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_fvarId_14_);
lean_dec_ref(v_t_12_);
v___x_15_ = lean_apply_1(v_k_13_, v_fvarId_14_);
return v___x_15_;
}
case 1:
{
lean_object* v_mvarId_16_; lean_object* v___x_17_; 
v_mvarId_16_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_mvarId_16_);
lean_dec_ref(v_t_12_);
v___x_17_ = lean_apply_1(v_k_13_, v_mvarId_16_);
return v___x_17_;
}
case 2:
{
lean_object* v_constName_18_; lean_object* v___x_19_; 
v_constName_18_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_constName_18_);
lean_dec_ref(v_t_12_);
v___x_19_ = lean_apply_1(v_k_13_, v_constName_18_);
return v___x_19_;
}
case 3:
{
lean_object* v_structName_20_; lean_object* v_idx_21_; lean_object* v___x_22_; 
v_structName_20_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_structName_20_);
v_idx_21_ = lean_ctor_get(v_t_12_, 1);
lean_inc(v_idx_21_);
lean_dec_ref(v_t_12_);
v___x_22_ = lean_apply_2(v_k_13_, v_structName_20_, v_idx_21_);
return v___x_22_;
}
case 4:
{
lean_object* v_litVal_23_; lean_object* v___x_24_; 
v_litVal_23_ = lean_ctor_get(v_t_12_, 0);
lean_inc_ref(v_litVal_23_);
lean_dec_ref(v_t_12_);
v___x_24_ = lean_apply_1(v_k_13_, v_litVal_23_);
return v___x_24_;
}
default: 
{
lean_dec(v_t_12_);
return v_k_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorElim(lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_27_, v_k_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorElim___boxed(lean_object* v_motive_31_, lean_object* v_ctorIdx_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_k_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_HeadIndex_ctorElim(v_motive_31_, v_ctorIdx_32_, v_t_33_, v_h_34_, v_k_35_);
lean_dec(v_ctorIdx_32_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_fvar_elim___redArg(lean_object* v_t_37_, lean_object* v_fvar_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_37_, v_fvar_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_fvar_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_fvar_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_41_, v_fvar_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_mvar_elim___redArg(lean_object* v_t_45_, lean_object* v_mvar_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_45_, v_mvar_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_mvar_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_mvar_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_49_, v_mvar_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_const_elim___redArg(lean_object* v_t_53_, lean_object* v_const_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_53_, v_const_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_const_elim(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_const_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_57_, v_const_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_proj_elim___redArg(lean_object* v_t_61_, lean_object* v_proj_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_61_, v_proj_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_proj_elim(lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_proj_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_65_, v_proj_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lit_elim___redArg(lean_object* v_t_69_, lean_object* v_lit_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_69_, v_lit_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lit_elim(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_lit_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_73_, v_lit_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_sort_elim___redArg(lean_object* v_t_77_, lean_object* v_sort_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_77_, v_sort_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_sort_elim(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_sort_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_81_, v_sort_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lam_elim___redArg(lean_object* v_t_85_, lean_object* v_lam_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_85_, v_lam_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lam_elim(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_lam_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_89_, v_lam_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_forallE_elim___redArg(lean_object* v_t_93_, lean_object* v_forallE_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_93_, v_forallE_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_forallE_elim(lean_object* v_motive_96_, lean_object* v_t_97_, lean_object* v_h_98_, lean_object* v_forallE_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_97_, v_forallE_99_);
return v___x_100_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqHeadIndex_beq(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
switch(lean_obj_tag(v_x_105_))
{
case 0:
{
if (lean_obj_tag(v_x_106_) == 0)
{
lean_object* v_fvarId_107_; lean_object* v_fvarId_108_; uint8_t v___x_109_; 
v_fvarId_107_ = lean_ctor_get(v_x_105_, 0);
v_fvarId_108_ = lean_ctor_get(v_x_106_, 0);
v___x_109_ = l_Lean_instBEqFVarId_beq(v_fvarId_107_, v_fvarId_108_);
return v___x_109_;
}
else
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
}
case 1:
{
if (lean_obj_tag(v_x_106_) == 1)
{
lean_object* v_mvarId_111_; lean_object* v_mvarId_112_; uint8_t v___x_113_; 
v_mvarId_111_ = lean_ctor_get(v_x_105_, 0);
v_mvarId_112_ = lean_ctor_get(v_x_106_, 0);
v___x_113_ = l_Lean_instBEqMVarId_beq(v_mvarId_111_, v_mvarId_112_);
return v___x_113_;
}
else
{
uint8_t v___x_114_; 
v___x_114_ = 0;
return v___x_114_;
}
}
case 2:
{
if (lean_obj_tag(v_x_106_) == 2)
{
lean_object* v_constName_115_; lean_object* v_constName_116_; uint8_t v___x_117_; 
v_constName_115_ = lean_ctor_get(v_x_105_, 0);
v_constName_116_ = lean_ctor_get(v_x_106_, 0);
v___x_117_ = lean_name_eq(v_constName_115_, v_constName_116_);
return v___x_117_;
}
else
{
uint8_t v___x_118_; 
v___x_118_ = 0;
return v___x_118_;
}
}
case 3:
{
if (lean_obj_tag(v_x_106_) == 3)
{
lean_object* v_structName_119_; lean_object* v_idx_120_; lean_object* v_structName_121_; lean_object* v_idx_122_; uint8_t v___x_123_; 
v_structName_119_ = lean_ctor_get(v_x_105_, 0);
v_idx_120_ = lean_ctor_get(v_x_105_, 1);
v_structName_121_ = lean_ctor_get(v_x_106_, 0);
v_idx_122_ = lean_ctor_get(v_x_106_, 1);
v___x_123_ = lean_name_eq(v_structName_119_, v_structName_121_);
if (v___x_123_ == 0)
{
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = lean_nat_dec_eq(v_idx_120_, v_idx_122_);
return v___x_124_;
}
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
}
case 4:
{
if (lean_obj_tag(v_x_106_) == 4)
{
lean_object* v_litVal_126_; lean_object* v_litVal_127_; uint8_t v___x_128_; 
v_litVal_126_ = lean_ctor_get(v_x_105_, 0);
v_litVal_127_ = lean_ctor_get(v_x_106_, 0);
v___x_128_ = l_Lean_instBEqLiteral_beq(v_litVal_126_, v_litVal_127_);
return v___x_128_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 0;
return v___x_129_;
}
}
case 5:
{
if (lean_obj_tag(v_x_106_) == 5)
{
uint8_t v___x_130_; 
v___x_130_ = 1;
return v___x_130_;
}
else
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
}
case 6:
{
if (lean_obj_tag(v_x_106_) == 6)
{
uint8_t v___x_132_; 
v___x_132_ = 1;
return v___x_132_;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
}
default: 
{
if (lean_obj_tag(v_x_106_) == 7)
{
uint8_t v___x_134_; 
v___x_134_ = 1;
return v___x_134_;
}
else
{
uint8_t v___x_135_; 
v___x_135_ = 0;
return v___x_135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqHeadIndex_beq___boxed(lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Lean_instBEqHeadIndex_beq(v_x_136_, v_x_137_);
lean_dec(v_x_137_);
lean_dec(v_x_136_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
static lean_object* _init_l_Lean_instReprHeadIndex_repr___closed__9(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(2u);
v___x_158_ = lean_nat_to_int(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_instReprHeadIndex_repr___closed__10(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(1u);
v___x_160_ = lean_nat_to_int(v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprHeadIndex_repr(lean_object* v_x_185_, lean_object* v_prec_186_){
_start:
{
lean_object* v___y_188_; lean_object* v___y_195_; lean_object* v___y_202_; 
switch(lean_obj_tag(v_x_185_))
{
case 0:
{
lean_object* v_fvarId_208_; lean_object* v___y_210_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_fvarId_208_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_fvarId_208_);
lean_dec_ref(v_x_185_);
v___x_219_ = lean_unsigned_to_nat(1024u);
v___x_220_ = lean_nat_dec_le(v___x_219_, v_prec_186_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_210_ = v___x_221_;
goto v___jp_209_;
}
else
{
lean_object* v___x_222_; 
v___x_222_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_210_ = v___x_222_;
goto v___jp_209_;
}
v___jp_209_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_211_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__8));
v___x_212_ = lean_unsigned_to_nat(1024u);
v___x_213_ = l_Lean_Name_reprPrec(v_fvarId_208_, v___x_212_);
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_211_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
lean_inc(v___y_210_);
v___x_215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_215_, 0, v___y_210_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = 0;
v___x_217_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*1, v___x_216_);
v___x_218_ = l_Repr_addAppParen(v___x_217_, v_prec_186_);
return v___x_218_;
}
}
case 1:
{
lean_object* v_mvarId_223_; lean_object* v___y_225_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_mvarId_223_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_mvarId_223_);
lean_dec_ref(v_x_185_);
v___x_234_ = lean_unsigned_to_nat(1024u);
v___x_235_ = lean_nat_dec_le(v___x_234_, v_prec_186_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
v___x_236_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_225_ = v___x_236_;
goto v___jp_224_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_225_ = v___x_237_;
goto v___jp_224_;
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_226_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__13));
v___x_227_ = lean_unsigned_to_nat(1024u);
v___x_228_ = l_Lean_Name_reprPrec(v_mvarId_223_, v___x_227_);
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_226_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
lean_inc(v___y_225_);
v___x_230_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_230_, 0, v___y_225_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = 0;
v___x_232_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*1, v___x_231_);
v___x_233_ = l_Repr_addAppParen(v___x_232_, v_prec_186_);
return v___x_233_;
}
}
case 2:
{
lean_object* v_constName_238_; lean_object* v___y_240_; lean_object* v___x_249_; uint8_t v___x_250_; 
v_constName_238_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_constName_238_);
lean_dec_ref(v_x_185_);
v___x_249_ = lean_unsigned_to_nat(1024u);
v___x_250_ = lean_nat_dec_le(v___x_249_, v_prec_186_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
v___x_251_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_240_ = v___x_251_;
goto v___jp_239_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_240_ = v___x_252_;
goto v___jp_239_;
}
v___jp_239_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_241_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__16));
v___x_242_ = lean_unsigned_to_nat(1024u);
v___x_243_ = l_Lean_Name_reprPrec(v_constName_238_, v___x_242_);
v___x_244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_241_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
lean_inc(v___y_240_);
v___x_245_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_245_, 0, v___y_240_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = 0;
v___x_247_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*1, v___x_246_);
v___x_248_ = l_Repr_addAppParen(v___x_247_, v_prec_186_);
return v___x_248_;
}
}
case 3:
{
lean_object* v_structName_253_; lean_object* v_idx_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_279_; 
v_structName_253_ = lean_ctor_get(v_x_185_, 0);
v_idx_254_ = lean_ctor_get(v_x_185_, 1);
v_isSharedCheck_279_ = !lean_is_exclusive(v_x_185_);
if (v_isSharedCheck_279_ == 0)
{
v___x_256_ = v_x_185_;
v_isShared_257_ = v_isSharedCheck_279_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_idx_254_);
lean_inc(v_structName_253_);
lean_dec(v_x_185_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_279_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___y_259_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(1024u);
v___x_276_ = lean_nat_dec_le(v___x_275_, v_prec_186_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_259_ = v___x_277_;
goto v___jp_258_;
}
else
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_259_ = v___x_278_;
goto v___jp_258_;
}
v___jp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_260_ = lean_box(1);
v___x_261_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__19));
v___x_262_ = lean_unsigned_to_nat(1024u);
v___x_263_ = l_Lean_Name_reprPrec(v_structName_253_, v___x_262_);
if (v_isShared_257_ == 0)
{
lean_ctor_set_tag(v___x_256_, 5);
lean_ctor_set(v___x_256_, 1, v___x_263_);
lean_ctor_set(v___x_256_, 0, v___x_261_);
v___x_265_ = v___x_256_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_263_);
v___x_265_ = v_reuseFailAlloc_274_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_260_);
v___x_267_ = l_Nat_reprFast(v_idx_254_);
v___x_268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
v___x_269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_266_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
lean_inc(v___y_259_);
v___x_270_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_270_, 0, v___y_259_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = 0;
v___x_272_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*1, v___x_271_);
v___x_273_ = l_Repr_addAppParen(v___x_272_, v_prec_186_);
return v___x_273_;
}
}
}
}
case 4:
{
lean_object* v_litVal_280_; lean_object* v___y_282_; lean_object* v___x_291_; uint8_t v___x_292_; 
v_litVal_280_ = lean_ctor_get(v_x_185_, 0);
lean_inc_ref(v_litVal_280_);
lean_dec_ref(v_x_185_);
v___x_291_ = lean_unsigned_to_nat(1024u);
v___x_292_ = lean_nat_dec_le(v___x_291_, v_prec_186_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
v___x_293_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_282_ = v___x_293_;
goto v___jp_281_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_282_ = v___x_294_;
goto v___jp_281_;
}
v___jp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_283_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__22));
v___x_284_ = lean_unsigned_to_nat(1024u);
v___x_285_ = l_Lean_instReprLiteral_repr(v_litVal_280_, v___x_284_);
v___x_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_283_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
lean_inc(v___y_282_);
v___x_287_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_287_, 0, v___y_282_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = 0;
v___x_289_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*1, v___x_288_);
v___x_290_ = l_Repr_addAppParen(v___x_289_, v_prec_186_);
return v___x_290_;
}
}
case 5:
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(1024u);
v___x_296_ = lean_nat_dec_le(v___x_295_, v_prec_186_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_188_ = v___x_297_;
goto v___jp_187_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_188_ = v___x_298_;
goto v___jp_187_;
}
}
case 6:
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(1024u);
v___x_300_ = lean_nat_dec_le(v___x_299_, v_prec_186_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_195_ = v___x_301_;
goto v___jp_194_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_195_ = v___x_302_;
goto v___jp_194_;
}
}
default: 
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(1024u);
v___x_304_ = lean_nat_dec_le(v___x_303_, v_prec_186_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
v___y_202_ = v___x_305_;
goto v___jp_201_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
v___y_202_ = v___x_306_;
goto v___jp_201_;
}
}
}
v___jp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_189_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__1));
lean_inc(v___y_188_);
v___x_190_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_190_, 0, v___y_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = 0;
v___x_192_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*1, v___x_191_);
v___x_193_ = l_Repr_addAppParen(v___x_192_, v_prec_186_);
return v___x_193_;
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_196_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__3));
lean_inc(v___y_195_);
v___x_197_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_197_, 0, v___y_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = 0;
v___x_199_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*1, v___x_198_);
v___x_200_ = l_Repr_addAppParen(v___x_199_, v_prec_186_);
return v___x_200_;
}
v___jp_201_:
{
lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_203_ = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__5));
lean_inc(v___y_202_);
v___x_204_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_204_, 0, v___y_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = 0;
v___x_206_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*1, v___x_205_);
v___x_207_ = l_Repr_addAppParen(v___x_206_, v_prec_186_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprHeadIndex_repr___boxed(lean_object* v_x_307_, lean_object* v_prec_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_instReprHeadIndex_repr(v_x_307_, v_prec_308_);
lean_dec(v_prec_308_);
return v_res_309_;
}
}
static uint64_t _init_l_Lean_HeadIndex_hash___closed__0(void){
_start:
{
lean_object* v___x_312_; uint64_t v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(1723u);
v___x_313_ = lean_uint64_of_nat(v___x_312_);
return v___x_313_;
}
}
static uint64_t _init_l_Lean_HeadIndex_hash___closed__1(void){
_start:
{
uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; 
v___x_314_ = lean_uint64_once(&l_Lean_HeadIndex_hash___closed__0, &l_Lean_HeadIndex_hash___closed__0_once, _init_l_Lean_HeadIndex_hash___closed__0);
v___x_315_ = 17ULL;
v___x_316_ = lean_uint64_mix_hash(v___x_315_, v___x_314_);
return v___x_316_;
}
}
LEAN_EXPORT uint64_t l_Lean_HeadIndex_hash(lean_object* v_x_317_){
_start:
{
switch(lean_obj_tag(v_x_317_))
{
case 0:
{
lean_object* v_fvarId_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; 
v_fvarId_318_ = lean_ctor_get(v_x_317_, 0);
v___x_319_ = 11ULL;
v___x_320_ = l_Lean_instHashableFVarId_hash(v_fvarId_318_);
v___x_321_ = lean_uint64_mix_hash(v___x_319_, v___x_320_);
return v___x_321_;
}
case 1:
{
lean_object* v_mvarId_322_; uint64_t v___x_323_; uint64_t v___x_324_; uint64_t v___x_325_; 
v_mvarId_322_ = lean_ctor_get(v_x_317_, 0);
v___x_323_ = 13ULL;
v___x_324_ = l_Lean_instHashableMVarId_hash(v_mvarId_322_);
v___x_325_ = lean_uint64_mix_hash(v___x_323_, v___x_324_);
return v___x_325_;
}
case 2:
{
lean_object* v_constName_326_; uint64_t v___x_327_; 
v_constName_326_ = lean_ctor_get(v_x_317_, 0);
v___x_327_ = 17ULL;
if (lean_obj_tag(v_constName_326_) == 0)
{
uint64_t v___x_328_; 
v___x_328_ = lean_uint64_once(&l_Lean_HeadIndex_hash___closed__1, &l_Lean_HeadIndex_hash___closed__1_once, _init_l_Lean_HeadIndex_hash___closed__1);
return v___x_328_;
}
else
{
uint64_t v_hash_329_; uint64_t v___x_330_; 
v_hash_329_ = lean_ctor_get_uint64(v_constName_326_, sizeof(void*)*2);
v___x_330_ = lean_uint64_mix_hash(v___x_327_, v_hash_329_);
return v___x_330_;
}
}
case 3:
{
lean_object* v_structName_331_; lean_object* v_idx_332_; uint64_t v___x_333_; uint64_t v___y_335_; 
v_structName_331_ = lean_ctor_get(v_x_317_, 0);
v_idx_332_ = lean_ctor_get(v_x_317_, 1);
v___x_333_ = 19ULL;
if (lean_obj_tag(v_structName_331_) == 0)
{
uint64_t v___x_339_; 
v___x_339_ = lean_uint64_once(&l_Lean_HeadIndex_hash___closed__0, &l_Lean_HeadIndex_hash___closed__0_once, _init_l_Lean_HeadIndex_hash___closed__0);
v___y_335_ = v___x_339_;
goto v___jp_334_;
}
else
{
uint64_t v_hash_340_; 
v_hash_340_ = lean_ctor_get_uint64(v_structName_331_, sizeof(void*)*2);
v___y_335_ = v_hash_340_;
goto v___jp_334_;
}
v___jp_334_:
{
uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; 
v___x_336_ = lean_uint64_of_nat(v_idx_332_);
v___x_337_ = lean_uint64_mix_hash(v___y_335_, v___x_336_);
v___x_338_ = lean_uint64_mix_hash(v___x_333_, v___x_337_);
return v___x_338_;
}
}
case 4:
{
lean_object* v_litVal_341_; uint64_t v___x_342_; uint64_t v___x_343_; uint64_t v___x_344_; 
v_litVal_341_ = lean_ctor_get(v_x_317_, 0);
v___x_342_ = 23ULL;
v___x_343_ = l_Lean_Literal_hash(v_litVal_341_);
v___x_344_ = lean_uint64_mix_hash(v___x_342_, v___x_343_);
return v___x_344_;
}
case 5:
{
uint64_t v___x_345_; 
v___x_345_ = 29ULL;
return v___x_345_;
}
case 6:
{
uint64_t v___x_346_; 
v___x_346_ = 31ULL;
return v___x_346_;
}
default: 
{
uint64_t v___x_347_; 
v___x_347_ = 37ULL;
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_hash___boxed(lean_object* v_x_348_){
_start:
{
uint64_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Lean_HeadIndex_hash(v_x_348_);
lean_dec(v_x_348_);
v_r_350_ = lean_box_uint64(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
switch(lean_obj_tag(v_a_353_))
{
case 5:
{
lean_object* v_fn_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_fn_355_ = lean_ctor_get(v_a_353_, 0);
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_nat_add(v_a_354_, v___x_356_);
lean_dec(v_a_354_);
v_a_353_ = v_fn_355_;
v_a_354_ = v___x_357_;
goto _start;
}
case 8:
{
lean_object* v_body_359_; 
v_body_359_ = lean_ctor_get(v_a_353_, 3);
v_a_353_ = v_body_359_;
goto _start;
}
case 10:
{
lean_object* v_expr_361_; 
v_expr_361_ = lean_ctor_get(v_a_353_, 1);
v_a_353_ = v_expr_361_;
goto _start;
}
default: 
{
return v_a_354_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go___boxed(lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(v_a_363_, v_a_364_);
lean_dec_ref(v_a_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs(lean_object* v_e_366_){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(v_e_366_, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs___boxed(lean_object* v_e_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Expr_headNumArgs(v_e_369_);
lean_dec_ref(v_e_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(lean_object* v_x_377_){
_start:
{
switch(lean_obj_tag(v_x_377_))
{
case 2:
{
lean_object* v_mvarId_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_mvarId_378_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_mvarId_378_);
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v_mvarId_378_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
case 1:
{
lean_object* v_fvarId_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_fvarId_381_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_fvarId_381_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v_fvarId_381_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
case 4:
{
lean_object* v_declName_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_declName_384_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_declName_384_);
v___x_385_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_385_, 0, v_declName_384_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
case 11:
{
lean_object* v_typeName_387_; lean_object* v_idx_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_typeName_387_ = lean_ctor_get(v_x_377_, 0);
v_idx_388_ = lean_ctor_get(v_x_377_, 1);
lean_inc(v_idx_388_);
lean_inc(v_typeName_387_);
v___x_389_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_389_, 0, v_typeName_387_);
lean_ctor_set(v___x_389_, 1, v_idx_388_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
case 3:
{
lean_object* v___x_391_; 
v___x_391_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0));
return v___x_391_;
}
case 6:
{
lean_object* v___x_392_; 
v___x_392_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1));
return v___x_392_;
}
case 7:
{
lean_object* v___x_393_; 
v___x_393_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2));
return v___x_393_;
}
case 9:
{
lean_object* v_a_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_a_394_ = lean_ctor_get(v_x_377_, 0);
lean_inc_ref(v_a_394_);
v___x_395_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_395_, 0, v_a_394_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
case 5:
{
lean_object* v_fn_397_; 
v_fn_397_ = lean_ctor_get(v_x_377_, 0);
v_x_377_ = v_fn_397_;
goto _start;
}
case 8:
{
lean_object* v_body_399_; 
v_body_399_ = lean_ctor_get(v_x_377_, 3);
v_x_377_ = v_body_399_;
goto _start;
}
case 10:
{
lean_object* v_expr_401_; 
v_expr_401_ = lean_ctor_get(v_x_377_, 1);
v_x_377_ = v_expr_401_;
goto _start;
}
default: 
{
lean_object* v___x_403_; 
v___x_403_ = lean_box(0);
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___boxed(lean_object* v_x_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(v_x_404_);
lean_dec_ref(v_x_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(lean_object* v_msg_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l_Lean_instInhabitedHeadIndex_default));
v___x_408_ = lean_panic_fn_borrowed(v___x_407_, v_msg_406_);
return v___x_408_;
}
}
static lean_object* _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_412_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2));
v___x_413_ = lean_unsigned_to_nat(31u);
v___x_414_ = lean_unsigned_to_nat(104u);
v___x_415_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1));
v___x_416_ = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0));
v___x_417_ = l_mkPanicMessageWithDecl(v___x_416_, v___x_415_, v___x_414_, v___x_413_, v___x_412_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(lean_object* v_x_418_){
_start:
{
switch(lean_obj_tag(v_x_418_))
{
case 2:
{
lean_object* v_mvarId_419_; lean_object* v___x_420_; 
v_mvarId_419_ = lean_ctor_get(v_x_418_, 0);
lean_inc(v_mvarId_419_);
lean_dec_ref(v_x_418_);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v_mvarId_419_);
return v___x_420_;
}
case 1:
{
lean_object* v_fvarId_421_; lean_object* v___x_422_; 
v_fvarId_421_ = lean_ctor_get(v_x_418_, 0);
lean_inc(v_fvarId_421_);
lean_dec_ref(v_x_418_);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v_fvarId_421_);
return v___x_422_;
}
case 4:
{
lean_object* v_declName_423_; lean_object* v___x_424_; 
v_declName_423_ = lean_ctor_get(v_x_418_, 0);
lean_inc(v_declName_423_);
lean_dec_ref(v_x_418_);
v___x_424_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_424_, 0, v_declName_423_);
return v___x_424_;
}
case 11:
{
lean_object* v_typeName_425_; lean_object* v_idx_426_; lean_object* v___x_427_; 
v_typeName_425_ = lean_ctor_get(v_x_418_, 0);
lean_inc(v_typeName_425_);
v_idx_426_ = lean_ctor_get(v_x_418_, 1);
lean_inc(v_idx_426_);
lean_dec_ref(v_x_418_);
v___x_427_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_427_, 0, v_typeName_425_);
lean_ctor_set(v___x_427_, 1, v_idx_426_);
return v___x_427_;
}
case 3:
{
lean_object* v___x_428_; 
lean_dec_ref(v_x_418_);
v___x_428_ = lean_box(5);
return v___x_428_;
}
case 6:
{
lean_object* v___x_429_; 
lean_dec_ref(v_x_418_);
v___x_429_ = lean_box(6);
return v___x_429_;
}
case 7:
{
lean_object* v___x_430_; 
lean_dec_ref(v_x_418_);
v___x_430_ = lean_box(7);
return v___x_430_;
}
case 9:
{
lean_object* v_a_431_; lean_object* v___x_432_; 
v_a_431_ = lean_ctor_get(v_x_418_, 0);
lean_inc_ref(v_a_431_);
lean_dec_ref(v_x_418_);
v___x_432_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_432_, 0, v_a_431_);
return v___x_432_;
}
case 5:
{
lean_object* v_fn_433_; 
v_fn_433_ = lean_ctor_get(v_x_418_, 0);
lean_inc_ref(v_fn_433_);
lean_dec_ref(v_x_418_);
v_x_418_ = v_fn_433_;
goto _start;
}
case 8:
{
lean_object* v_value_435_; lean_object* v_body_436_; lean_object* v___x_437_; 
v_value_435_ = lean_ctor_get(v_x_418_, 2);
lean_inc_ref(v_value_435_);
v_body_436_ = lean_ctor_get(v_x_418_, 3);
lean_inc_ref(v_body_436_);
lean_dec_ref(v_x_418_);
v___x_437_ = lean_expr_instantiate1(v_body_436_, v_value_435_);
lean_dec_ref(v_value_435_);
lean_dec_ref(v_body_436_);
v_x_418_ = v___x_437_;
goto _start;
}
case 10:
{
lean_object* v_expr_439_; 
v_expr_439_ = lean_ctor_get(v_x_418_, 1);
lean_inc_ref(v_expr_439_);
lean_dec_ref(v_x_418_);
v_x_418_ = v_expr_439_;
goto _start;
}
default: 
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec_ref(v_x_418_);
v___x_441_ = lean_obj_once(&l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3, &l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3_once, _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3);
v___x_442_ = l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(v___x_441_);
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_toHeadIndex(lean_object* v_e_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(v_e_443_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v___x_445_; 
v___x_445_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(v_e_443_);
return v___x_445_;
}
else
{
lean_object* v_val_446_; 
lean_dec_ref(v_e_443_);
v_val_446_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_val_446_);
lean_dec_ref(v___x_444_);
return v_val_446_;
}
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_HeadIndex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
