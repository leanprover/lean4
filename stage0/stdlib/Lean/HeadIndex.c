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
extern lean_object* l_Lean_instInhabitedFVarId_default;
static lean_once_cell_t l_Lean_instInhabitedHeadIndex_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedHeadIndex_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedHeadIndex_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedHeadIndex;
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqLiteral_beq(lean_object*, lean_object*);
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
lean_object* lean_nat_to_int(lean_object*);
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_instReprLiteral_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprHeadIndex_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprHeadIndex_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprHeadIndex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprHeadIndex_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprHeadIndex___closed__0 = (const lean_object*)&l_Lean_instReprHeadIndex___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprHeadIndex = (const lean_object*)&l_Lean_instReprHeadIndex___closed__0_value;
uint64_t lean_uint64_of_nat(lean_object*);
static lean_once_cell_t l_Lean_HeadIndex_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_HeadIndex_hash___closed__0;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_once_cell_t l_Lean_HeadIndex_hash___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_HeadIndex_hash___closed__1;
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t l_Lean_Literal_hash(lean_object*);
LEAN_EXPORT uint64_t l_Lean_HeadIndex_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableHeadIndex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_HeadIndex_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableHeadIndex___closed__0 = (const lean_object*)&l_Lean_instHashableHeadIndex___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableHeadIndex = (const lean_object*)&l_Lean_instHashableHeadIndex___closed__0_value;
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(lean_object*);
static const lean_string_object l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.HeadIndex"};
static const lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0 = (const lean_object*)&l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0_value;
static const lean_string_object l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "_private.Lean.HeadIndex.0.Lean.Expr.toHeadIndexSlow"};
static const lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1 = (const lean_object*)&l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1_value;
static const lean_string_object l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected expression kind"};
static const lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2 = (const lean_object*)&l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
default: 
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_HeadIndex_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_apply_2(x_2, x_9, x_10);
return x_11;
}
case 4:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_1(x_2, x_12);
return x_13;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_HeadIndex_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_HeadIndex_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_fvar_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HeadIndex_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_fvar_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HeadIndex_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_mvar_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HeadIndex_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_mvar_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HeadIndex_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_const_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HeadIndex_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_const_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HeadIndex_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_proj_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HeadIndex_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_proj_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HeadIndex_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lit_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HeadIndex_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lit_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HeadIndex_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_sort_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HeadIndex_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_sort_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HeadIndex_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lam_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HeadIndex_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_lam_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HeadIndex_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_forallE_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HeadIndex_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_forallE_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HeadIndex_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_instInhabitedHeadIndex_default___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedFVarId_default;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedHeadIndex_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instInhabitedHeadIndex_default___closed__0, &l_Lean_instInhabitedHeadIndex_default___closed__0_once, _init_l_Lean_instInhabitedHeadIndex_default___closed__0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedHeadIndex(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedHeadIndex_default;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqHeadIndex_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_instBEqFVarId_beq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 0);
x_9 = l_Lean_instBEqMVarId_beq(x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_name_eq(x_11, x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_name_eq(x_15, x_17);
if (x_19 == 0)
{
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_eq(x_16, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_2, 0);
x_24 = l_Lean_instBEqLiteral_beq(x_22, x_23);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
else
{
uint8_t x_27; 
x_27 = 0;
return x_27;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
uint8_t x_28; 
x_28 = 1;
return x_28;
}
else
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
default: 
{
if (lean_obj_tag(x_2) == 7)
{
uint8_t x_30; 
x_30 = 1;
return x_30;
}
else
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqHeadIndex_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instBEqHeadIndex_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instReprHeadIndex_repr___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instReprHeadIndex_repr___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprHeadIndex_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_35; uint8_t x_36; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec_ref(x_1);
x_35 = lean_unsigned_to_nat(1024u);
x_36 = lean_nat_dec_le(x_35, x_2);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
x_25 = x_37;
goto block_34;
}
else
{
lean_object* x_38; 
x_38 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
x_25 = x_38;
goto block_34;
}
block_34:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_26 = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__8));
x_27 = lean_unsigned_to_nat(1024u);
x_28 = l_Lean_Name_reprPrec(x_24, x_27);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = 0;
x_32 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = l_Repr_addAppParen(x_32, x_2);
return x_33;
}
}
case 1:
{
lean_object* x_39; lean_object* x_40; lean_object* x_50; uint8_t x_51; 
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec_ref(x_1);
x_50 = lean_unsigned_to_nat(1024u);
x_51 = lean_nat_dec_le(x_50, x_2);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
x_40 = x_52;
goto block_49;
}
else
{
lean_object* x_53; 
x_53 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
x_40 = x_53;
goto block_49;
}
block_49:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_41 = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__13));
x_42 = lean_unsigned_to_nat(1024u);
x_43 = l_Lean_Name_reprPrec(x_39, x_42);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
x_46 = 0;
x_47 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = l_Repr_addAppParen(x_47, x_2);
return x_48;
}
}
case 2:
{
lean_object* x_54; lean_object* x_55; lean_object* x_65; uint8_t x_66; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
lean_dec_ref(x_1);
x_65 = lean_unsigned_to_nat(1024u);
x_66 = lean_nat_dec_le(x_65, x_2);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
x_55 = x_67;
goto block_64;
}
else
{
lean_object* x_68; 
x_68 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
x_55 = x_68;
goto block_64;
}
block_64:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_56 = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__16));
x_57 = lean_unsigned_to_nat(1024u);
x_58 = l_Lean_Name_reprPrec(x_54, x_57);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
x_61 = 0;
x_62 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = l_Repr_addAppParen(x_62, x_2);
return x_63;
}
}
case 3:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_87; uint8_t x_88; 
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_71 = x_1;
} else {
 lean_dec_ref(x_1);
 x_71 = lean_box(0);
}
x_87 = lean_unsigned_to_nat(1024u);
x_88 = lean_nat_dec_le(x_87, x_2);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
x_72 = x_89;
goto block_86;
}
else
{
lean_object* x_90; 
x_90 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
x_72 = x_90;
goto block_86;
}
block_86:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_73 = lean_box(1);
x_74 = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__19));
x_75 = lean_unsigned_to_nat(1024u);
x_76 = l_Lean_Name_reprPrec(x_69, x_75);
if (lean_is_scalar(x_71)) {
 x_77 = lean_alloc_ctor(5, 2, 0);
} else {
 x_77 = x_71;
 lean_ctor_set_tag(x_77, 5);
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
x_79 = l_Nat_reprFast(x_70);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_81);
x_83 = 0;
x_84 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
x_85 = l_Repr_addAppParen(x_84, x_2);
return x_85;
}
}
case 4:
{
lean_object* x_91; lean_object* x_92; lean_object* x_102; uint8_t x_103; 
x_91 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_91);
lean_dec_ref(x_1);
x_102 = lean_unsigned_to_nat(1024u);
x_103 = lean_nat_dec_le(x_102, x_2);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
x_92 = x_104;
goto block_101;
}
else
{
lean_object* x_105; 
x_105 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
x_92 = x_105;
goto block_101;
}
block_101:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; 
x_93 = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__22));
x_94 = lean_unsigned_to_nat(1024u);
x_95 = l_Lean_instReprLiteral_repr(x_91, x_94);
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
x_98 = 0;
x_99 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
x_100 = l_Repr_addAppParen(x_99, x_2);
return x_100;
}
}
case 5:
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_unsigned_to_nat(1024u);
x_107 = lean_nat_dec_le(x_106, x_2);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
x_3 = x_108;
goto block_9;
}
else
{
lean_object* x_109; 
x_109 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
x_3 = x_109;
goto block_9;
}
}
case 6:
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_unsigned_to_nat(1024u);
x_111 = lean_nat_dec_le(x_110, x_2);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
x_10 = x_112;
goto block_16;
}
else
{
lean_object* x_113; 
x_113 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
x_10 = x_113;
goto block_16;
}
}
default: 
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_unsigned_to_nat(1024u);
x_115 = lean_nat_dec_le(x_114, x_2);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__9, &l_Lean_instReprHeadIndex_repr___closed__9_once, _init_l_Lean_instReprHeadIndex_repr___closed__9);
x_17 = x_116;
goto block_23;
}
else
{
lean_object* x_117; 
x_117 = lean_obj_once(&l_Lean_instReprHeadIndex_repr___closed__10, &l_Lean_instReprHeadIndex_repr___closed__10_once, _init_l_Lean_instReprHeadIndex_repr___closed__10);
x_17 = x_117;
goto block_23;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__1));
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__3));
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = ((lean_object*)(l_Lean_instReprHeadIndex_repr___closed__5));
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprHeadIndex_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instReprHeadIndex_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static uint64_t _init_l_Lean_HeadIndex_hash___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_Lean_HeadIndex_hash___closed__1(void) {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = lean_uint64_once(&l_Lean_HeadIndex_hash___closed__0, &l_Lean_HeadIndex_hash___closed__0_once, _init_l_Lean_HeadIndex_hash___closed__0);
x_2 = 17;
x_3 = lean_uint64_mix_hash(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_HeadIndex_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 11;
x_4 = l_Lean_instHashableFVarId_hash(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 13;
x_8 = l_Lean_instHashableMVarId_hash(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; uint64_t x_11; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = 17;
if (lean_obj_tag(x_10) == 0)
{
uint64_t x_12; 
x_12 = lean_uint64_once(&l_Lean_HeadIndex_hash___closed__1, &l_Lean_HeadIndex_hash___closed__1_once, _init_l_Lean_HeadIndex_hash___closed__1);
return x_12;
}
else
{
uint64_t x_13; uint64_t x_14; 
x_13 = lean_ctor_get_uint64(x_10, sizeof(void*)*2);
x_14 = lean_uint64_mix_hash(x_11, x_13);
return x_14;
}
}
case 3:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = 19;
if (lean_obj_tag(x_15) == 0)
{
uint64_t x_23; 
x_23 = lean_uint64_once(&l_Lean_HeadIndex_hash___closed__0, &l_Lean_HeadIndex_hash___closed__0_once, _init_l_Lean_HeadIndex_hash___closed__0);
x_18 = x_23;
goto block_22;
}
else
{
uint64_t x_24; 
x_24 = lean_ctor_get_uint64(x_15, sizeof(void*)*2);
x_18 = x_24;
goto block_22;
}
block_22:
{
uint64_t x_19; uint64_t x_20; uint64_t x_21; 
x_19 = lean_uint64_of_nat(x_16);
x_20 = lean_uint64_mix_hash(x_18, x_19);
x_21 = lean_uint64_mix_hash(x_17, x_20);
return x_21;
}
}
case 4:
{
lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = 23;
x_27 = l_Lean_Literal_hash(x_25);
x_28 = lean_uint64_mix_hash(x_26, x_27);
return x_28;
}
case 5:
{
uint64_t x_29; 
x_29 = 29;
return x_29;
}
case 6:
{
uint64_t x_30; 
x_30 = 31;
return x_30;
}
default: 
{
uint64_t x_31; 
x_31 = 37;
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_HeadIndex_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
case 8:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 3);
x_1 = x_7;
goto _start;
}
case 10:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 1);
x_1 = x_9;
goto _start;
}
default: 
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_headNumArgs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
case 4:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
case 11:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
x_13 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
case 3:
{
lean_object* x_15; 
x_15 = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0));
return x_15;
}
case 6:
{
lean_object* x_16; 
x_16 = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1));
return x_16;
}
case 7:
{
lean_object* x_17; 
x_17 = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2));
return x_17;
}
case 9:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_18);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
case 5:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 0);
x_1 = x_21;
goto _start;
}
case 8:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_1, 3);
x_1 = x_23;
goto _start;
}
case 10:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 1);
x_1 = x_25;
goto _start;
}
default: 
{
lean_object* x_27; 
x_27 = lean_box(0);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedHeadIndex_default;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2));
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_unsigned_to_nat(104u);
x_4 = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1));
x_5 = ((lean_object*)(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 4:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
case 11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
case 3:
{
lean_object* x_11; 
lean_dec_ref(x_1);
x_11 = lean_box(5);
return x_11;
}
case 6:
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = lean_box(6);
return x_12;
}
case 7:
{
lean_object* x_13; 
lean_dec_ref(x_1);
x_13 = lean_box(7);
return x_13;
}
case 9:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
case 5:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_1 = x_16;
goto _start;
}
case 8:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_19);
lean_dec_ref(x_1);
x_20 = lean_expr_instantiate1(x_19, x_18);
lean_dec_ref(x_18);
lean_dec_ref(x_19);
x_1 = x_20;
goto _start;
}
case 10:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_1 = x_22;
goto _start;
}
default: 
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_1);
x_24 = lean_obj_once(&l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3, &l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3_once, _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3);
x_25 = l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_toHeadIndex(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(x_1);
return x_3;
}
else
{
lean_object* x_4; 
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
return x_4;
}
}
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
l_Lean_instInhabitedHeadIndex_default = _init_l_Lean_instInhabitedHeadIndex_default();
lean_mark_persistent(l_Lean_instInhabitedHeadIndex_default);
l_Lean_instInhabitedHeadIndex = _init_l_Lean_instInhabitedHeadIndex();
lean_mark_persistent(l_Lean_instInhabitedHeadIndex);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
