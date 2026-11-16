// Lean compiler output
// Module: Lean.Data.Markdown.Block
// Imports: public import Init.Data.Hashable public import Std.Data.HashMap public import Init.Data.String.Subslice public import Init.Data.String.Lemmas.Order import Init.Data.String.OrderInstances import Init.Data.String.Iterate import Init.While import Init.Data.String.TakeDrop public import Init.Data.String.FindPos public import Lean.Data.Markdown.Inline public import Lean.Data.Markdown.InlineSource
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
lean_object* l_Lean_Markdown_subsliceClamped___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_Inline_extentOf_x3f___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_span___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_LinkDestination_extent___redArg(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Nat_sub___boxed(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_Lines_singleton___redArg(lean_object*);
lean_object* l_Lean_Markdown_InlineSource_ofLines(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_instDecidableEqColumns_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instDecidableEqColumns_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_instDecidableEqColumns(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instDecidableEqColumns___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Markdown_instReprColumns_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Markdown_instReprColumns_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Markdown_instReprColumns_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Markdown_instReprColumns_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "count"};
static const lean_object* l_Lean_Markdown_instReprColumns_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Markdown_instReprColumns_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Markdown_instReprColumns_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Markdown_instReprColumns_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Markdown_instReprColumns_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Markdown_instReprColumns_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Markdown_instReprColumns_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Markdown_instReprColumns_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Markdown_instReprColumns_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Markdown_instReprColumns_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Markdown_instReprColumns_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Markdown_instReprColumns_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instReprColumns_repr___redArg___closed__7;
static const lean_string_object l_Lean_Markdown_instReprColumns_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Markdown_instReprColumns_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Markdown_instReprColumns_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instReprColumns_repr___redArg___closed__9;
static lean_once_cell_t l_Lean_Markdown_instReprColumns_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instReprColumns_repr___redArg___closed__10;
static const lean_ctor_object l_Lean_Markdown_instReprColumns_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Markdown_instReprColumns_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Markdown_instReprColumns_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Markdown_instReprColumns_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Markdown_instReprColumns_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprColumns_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprColumns_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprColumns_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_instReprColumns___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instReprColumns_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instReprColumns___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprColumns___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instReprColumns = (const lean_object*)&l_Lean_Markdown_instReprColumns___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedColumns_default;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedColumns;
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_instOfNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_instLE;
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_instLT;
LEAN_EXPORT uint8_t l_Lean_Markdown_Columns_instDecidableLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_instDecidableLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_Columns_instDecidableLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_instDecidableLt___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_Columns_instAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_Columns_instAdd___closed__0 = (const lean_object*)&l_Lean_Markdown_Columns_instAdd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_Columns_instAdd = (const lean_object*)&l_Lean_Markdown_Columns_instAdd___closed__0_value;
static const lean_closure_object l_Lean_Markdown_Columns_instSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_Columns_instSub___closed__0 = (const lean_object*)&l_Lean_Markdown_Columns_instSub___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_Columns_instSub = (const lean_object*)&l_Lean_Markdown_Columns_instSub___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_space(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_space___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_tabWidth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_tabWidth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_tab(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_tab___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_star_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_star_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_star_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_star_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_hyphen_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_hyphen_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_hyphen_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_hyphen_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_plus_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_plus_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_plus_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_plus_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Markdown_instReprBulletKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Markdown.BulletKind.star"};
static const lean_object* l_Lean_Markdown_instReprBulletKind_repr___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprBulletKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_Markdown_instReprBulletKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprBulletKind_repr___closed__0_value)}};
static const lean_object* l_Lean_Markdown_instReprBulletKind_repr___closed__1 = (const lean_object*)&l_Lean_Markdown_instReprBulletKind_repr___closed__1_value;
static const lean_string_object l_Lean_Markdown_instReprBulletKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Markdown.BulletKind.hyphen"};
static const lean_object* l_Lean_Markdown_instReprBulletKind_repr___closed__2 = (const lean_object*)&l_Lean_Markdown_instReprBulletKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_Markdown_instReprBulletKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprBulletKind_repr___closed__2_value)}};
static const lean_object* l_Lean_Markdown_instReprBulletKind_repr___closed__3 = (const lean_object*)&l_Lean_Markdown_instReprBulletKind_repr___closed__3_value;
static const lean_string_object l_Lean_Markdown_instReprBulletKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Markdown.BulletKind.plus"};
static const lean_object* l_Lean_Markdown_instReprBulletKind_repr___closed__4 = (const lean_object*)&l_Lean_Markdown_instReprBulletKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_Markdown_instReprBulletKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprBulletKind_repr___closed__4_value)}};
static const lean_object* l_Lean_Markdown_instReprBulletKind_repr___closed__5 = (const lean_object*)&l_Lean_Markdown_instReprBulletKind_repr___closed__5_value;
static lean_once_cell_t l_Lean_Markdown_instReprBulletKind_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instReprBulletKind_repr___closed__6;
static lean_once_cell_t l_Lean_Markdown_instReprBulletKind_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instReprBulletKind_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprBulletKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprBulletKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_instReprBulletKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instReprBulletKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instReprBulletKind___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprBulletKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instReprBulletKind = (const lean_object*)&l_Lean_Markdown_instReprBulletKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Markdown_instBEqBulletKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_instBEqBulletKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_instBEqBulletKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instBEqBulletKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instBEqBulletKind___closed__0 = (const lean_object*)&l_Lean_Markdown_instBEqBulletKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instBEqBulletKind = (const lean_object*)&l_Lean_Markdown_instBEqBulletKind___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Markdown_instHashableBulletKind_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_instHashableBulletKind_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Markdown_instHashableBulletKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instHashableBulletKind_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instHashableBulletKind___closed__0 = (const lean_object*)&l_Lean_Markdown_instHashableBulletKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instHashableBulletKind = (const lean_object*)&l_Lean_Markdown_instHashableBulletKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_dot_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_dot_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_dot_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_dot_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_rparen_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_rparen_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_rparen_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_rparen_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Markdown_instReprOrderedDelim_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Markdown.OrderedDelim.dot"};
static const lean_object* l_Lean_Markdown_instReprOrderedDelim_repr___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprOrderedDelim_repr___closed__0_value;
static const lean_ctor_object l_Lean_Markdown_instReprOrderedDelim_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprOrderedDelim_repr___closed__0_value)}};
static const lean_object* l_Lean_Markdown_instReprOrderedDelim_repr___closed__1 = (const lean_object*)&l_Lean_Markdown_instReprOrderedDelim_repr___closed__1_value;
static const lean_string_object l_Lean_Markdown_instReprOrderedDelim_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Markdown.OrderedDelim.rparen"};
static const lean_object* l_Lean_Markdown_instReprOrderedDelim_repr___closed__2 = (const lean_object*)&l_Lean_Markdown_instReprOrderedDelim_repr___closed__2_value;
static const lean_ctor_object l_Lean_Markdown_instReprOrderedDelim_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprOrderedDelim_repr___closed__2_value)}};
static const lean_object* l_Lean_Markdown_instReprOrderedDelim_repr___closed__3 = (const lean_object*)&l_Lean_Markdown_instReprOrderedDelim_repr___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprOrderedDelim_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprOrderedDelim_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_instReprOrderedDelim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instReprOrderedDelim_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instReprOrderedDelim___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprOrderedDelim___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instReprOrderedDelim = (const lean_object*)&l_Lean_Markdown_instReprOrderedDelim___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Markdown_instBEqOrderedDelim_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_instBEqOrderedDelim_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_instBEqOrderedDelim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instBEqOrderedDelim_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instBEqOrderedDelim___closed__0 = (const lean_object*)&l_Lean_Markdown_instBEqOrderedDelim___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instBEqOrderedDelim = (const lean_object*)&l_Lean_Markdown_instBEqOrderedDelim___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Markdown_instHashableOrderedDelim_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_instHashableOrderedDelim_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Markdown_instHashableOrderedDelim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instHashableOrderedDelim_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instHashableOrderedDelim___closed__0 = (const lean_object*)&l_Lean_Markdown_instHashableOrderedDelim___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instHashableOrderedDelim = (const lean_object*)&l_Lean_Markdown_instHashableOrderedDelim___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_bullet_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_bullet_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ordered_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ordered_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Markdown_instReprListKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Markdown.ListKind.bullet"};
static const lean_object* l_Lean_Markdown_instReprListKind_repr___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprListKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_Markdown_instReprListKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprListKind_repr___closed__0_value)}};
static const lean_object* l_Lean_Markdown_instReprListKind_repr___closed__1 = (const lean_object*)&l_Lean_Markdown_instReprListKind_repr___closed__1_value;
static const lean_ctor_object l_Lean_Markdown_instReprListKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprListKind_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Markdown_instReprListKind_repr___closed__2 = (const lean_object*)&l_Lean_Markdown_instReprListKind_repr___closed__2_value;
static const lean_string_object l_Lean_Markdown_instReprListKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Markdown.ListKind.ordered"};
static const lean_object* l_Lean_Markdown_instReprListKind_repr___closed__3 = (const lean_object*)&l_Lean_Markdown_instReprListKind_repr___closed__3_value;
static const lean_ctor_object l_Lean_Markdown_instReprListKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprListKind_repr___closed__3_value)}};
static const lean_object* l_Lean_Markdown_instReprListKind_repr___closed__4 = (const lean_object*)&l_Lean_Markdown_instReprListKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_Markdown_instReprListKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprListKind_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Markdown_instReprListKind_repr___closed__5 = (const lean_object*)&l_Lean_Markdown_instReprListKind_repr___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprListKind_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprListKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_instReprListKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instReprListKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instReprListKind___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprListKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instReprListKind = (const lean_object*)&l_Lean_Markdown_instReprListKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Markdown_instBEqListKind_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instBEqListKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_instBEqListKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instBEqListKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instBEqListKind___closed__0 = (const lean_object*)&l_Lean_Markdown_instBEqListKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instBEqListKind = (const lean_object*)&l_Lean_Markdown_instBEqListKind___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Markdown_instHashableListKind_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instHashableListKind_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Markdown_instHashableListKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instHashableListKind_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instHashableListKind___closed__0 = (const lean_object*)&l_Lean_Markdown_instHashableListKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instHashableListKind = (const lean_object*)&l_Lean_Markdown_instHashableListKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_backtick_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_backtick_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_backtick_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_backtick_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_tilde_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_tilde_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_tilde_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_tilde_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Markdown_instReprFenceChar_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Markdown.FenceChar.backtick"};
static const lean_object* l_Lean_Markdown_instReprFenceChar_repr___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprFenceChar_repr___closed__0_value;
static const lean_ctor_object l_Lean_Markdown_instReprFenceChar_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprFenceChar_repr___closed__0_value)}};
static const lean_object* l_Lean_Markdown_instReprFenceChar_repr___closed__1 = (const lean_object*)&l_Lean_Markdown_instReprFenceChar_repr___closed__1_value;
static const lean_string_object l_Lean_Markdown_instReprFenceChar_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Markdown.FenceChar.tilde"};
static const lean_object* l_Lean_Markdown_instReprFenceChar_repr___closed__2 = (const lean_object*)&l_Lean_Markdown_instReprFenceChar_repr___closed__2_value;
static const lean_ctor_object l_Lean_Markdown_instReprFenceChar_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprFenceChar_repr___closed__2_value)}};
static const lean_object* l_Lean_Markdown_instReprFenceChar_repr___closed__3 = (const lean_object*)&l_Lean_Markdown_instReprFenceChar_repr___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprFenceChar_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprFenceChar_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_instReprFenceChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instReprFenceChar_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instReprFenceChar___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprFenceChar___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instReprFenceChar = (const lean_object*)&l_Lean_Markdown_instReprFenceChar___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Markdown_instBEqFenceChar_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_instBEqFenceChar_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_instBEqFenceChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instBEqFenceChar_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instBEqFenceChar___closed__0 = (const lean_object*)&l_Lean_Markdown_instBEqFenceChar___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instBEqFenceChar = (const lean_object*)&l_Lean_Markdown_instBEqFenceChar___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Markdown_instHashableFenceChar_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_instHashableFenceChar_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Markdown_instHashableFenceChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instHashableFenceChar_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instHashableFenceChar___closed__0 = (const lean_object*)&l_Lean_Markdown_instHashableFenceChar___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instHashableFenceChar = (const lean_object*)&l_Lean_Markdown_instHashableFenceChar___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Markdown_instInhabitedFenceChar_default;
LEAN_EXPORT uint8_t l_Lean_Markdown_instInhabitedFenceChar;
static const lean_ctor_object l_Lean_Markdown_FenceChar_ofChar_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Markdown_FenceChar_ofChar_x3f___closed__0 = (const lean_object*)&l_Lean_Markdown_FenceChar_ofChar_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Markdown_FenceChar_ofChar_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Markdown_FenceChar_ofChar_x3f___closed__1 = (const lean_object*)&l_Lean_Markdown_FenceChar_ofChar_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ofChar_x3f(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ofChar_x3f___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Markdown_FenceChar_toChar(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_toChar___boxed(lean_object*);
static const lean_ctor_object l_Lean_Markdown_instInhabitedFenceInfo_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Markdown_instInhabitedFenceInfo_default___redArg___closed__0 = (const lean_object*)&l_Lean_Markdown_instInhabitedFenceInfo_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Markdown_instInhabitedFenceInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instInhabitedFenceInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedVerbatimLine_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedVerbatimLine_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedVerbatimLine(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedVerbatimLine___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Markdown_VerbatimLine_text_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Markdown_VerbatimLine_text___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Markdown_VerbatimLine_text___closed__0 = (const lean_object*)&l_Lean_Markdown_VerbatimLine_text___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_VerbatimLine_text(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_VerbatimLine_text___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_paragraph_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_paragraph_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_paragraph_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_atxHeading_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_atxHeading_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_atxHeading_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_setextHeading_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_setextHeading_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_setextHeading_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_fencedCode_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_fencedCode_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_fencedCode_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_indentedCode_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_indentedCode_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_indentedCode_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_html_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_html_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_html_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_blockquote_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_blockquote_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_blockquote_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_list_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_list_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_list_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_listItem_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_listItem_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_listItem_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_linkRefDef_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_linkRefDef_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_linkRefDef_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_thematicBreak_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_thematicBreak_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_thematicBreak_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_instInhabitedRaw_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_instInhabitedRaw_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_instInhabitedRaw(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_instInhabitedRaw___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_ListKind_sameKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_sameKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_paragraph_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_paragraph_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_paragraph_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_atxHeading_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_atxHeading_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_atxHeading_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_setextHeading_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_setextHeading_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_setextHeading_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_fencedCode_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_fencedCode_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_fencedCode_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_indentedCode_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_indentedCode_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_indentedCode_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_html_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_html_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_html_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_blockquote_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_blockquote_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_blockquote_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_list_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_list_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_list_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_listItem_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_listItem_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_listItem_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_linkRefDef_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_linkRefDef_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_linkRefDef_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_thematicBreak_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_thematicBreak_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_thematicBreak_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Markdown_instInhabitedBlock_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Markdown_instInhabitedBlock_default___redArg___closed__0 = (const lean_object*)&l_Lean_Markdown_instInhabitedBlock_default___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Markdown_instInhabitedBlock_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Markdown_instInhabitedBlock_default___redArg___closed__0_value)}};
static const lean_object* l_Lean_Markdown_instInhabitedBlock_default___redArg___closed__1 = (const lean_object*)&l_Lean_Markdown_instInhabitedBlock_default___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Markdown_instInhabitedBlock_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instInhabitedBlock_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_VerbatimLine_span_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_VerbatimLine_span_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_VerbatimLine_span_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_VerbatimLine_span_x3f___boxed(lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_extent_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_extent_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_instDecidableEqColumns_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_eq(v_x_1_, v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instDecidableEqColumns_decEq___boxed(lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_Lean_Markdown_instDecidableEqColumns_decEq(v_x_4_, v_x_5_);
lean_dec(v_x_5_);
lean_dec(v_x_4_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_instDecidableEqColumns(lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
uint8_t v___x_10_; 
v___x_10_ = lean_nat_dec_eq(v_x_8_, v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instDecidableEqColumns___boxed(lean_object* v_x_11_, lean_object* v_x_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Markdown_instDecidableEqColumns(v_x_11_, v_x_12_);
lean_dec(v_x_12_);
lean_dec(v_x_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Markdown_instReprColumns_repr_spec__0(lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_nat_to_int(v_a_15_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_Markdown_instReprColumns_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(9u);
v___x_31_ = lean_nat_to_int(v___x_30_);
return v___x_31_;
}
}
static lean_object* _init_l_Lean_Markdown_instReprColumns_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Lean_Markdown_instReprColumns_repr___redArg___closed__0));
v___x_34_ = lean_string_length(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Lean_Markdown_instReprColumns_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_obj_once(&l_Lean_Markdown_instReprColumns_repr___redArg___closed__9, &l_Lean_Markdown_instReprColumns_repr___redArg___closed__9_once, _init_l_Lean_Markdown_instReprColumns_repr___redArg___closed__9);
v___x_36_ = lean_nat_to_int(v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprColumns_repr___redArg(lean_object* v_x_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_42_ = ((lean_object*)(l_Lean_Markdown_instReprColumns_repr___redArg___closed__6));
v___x_43_ = lean_obj_once(&l_Lean_Markdown_instReprColumns_repr___redArg___closed__7, &l_Lean_Markdown_instReprColumns_repr___redArg___closed__7_once, _init_l_Lean_Markdown_instReprColumns_repr___redArg___closed__7);
v___x_44_ = l_Nat_reprFast(v_x_41_);
v___x_45_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
v___x_46_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_43_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
v___x_47_ = 0;
v___x_48_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_48_, 0, v___x_46_);
lean_ctor_set_uint8(v___x_48_, sizeof(void*)*1, v___x_47_);
v___x_49_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_42_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_obj_once(&l_Lean_Markdown_instReprColumns_repr___redArg___closed__10, &l_Lean_Markdown_instReprColumns_repr___redArg___closed__10_once, _init_l_Lean_Markdown_instReprColumns_repr___redArg___closed__10);
v___x_51_ = ((lean_object*)(l_Lean_Markdown_instReprColumns_repr___redArg___closed__11));
v___x_52_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_49_);
v___x_53_ = ((lean_object*)(l_Lean_Markdown_instReprColumns_repr___redArg___closed__12));
v___x_54_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
v___x_55_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_50_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set_uint8(v___x_56_, sizeof(void*)*1, v___x_47_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprColumns_repr(lean_object* v_x_57_, lean_object* v_prec_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Markdown_instReprColumns_repr___redArg(v_x_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprColumns_repr___boxed(lean_object* v_x_60_, lean_object* v_prec_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Markdown_instReprColumns_repr(v_x_60_, v_prec_61_);
lean_dec(v_prec_61_);
return v_res_62_;
}
}
static lean_object* _init_l_Lean_Markdown_instInhabitedColumns_default(void){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_unsigned_to_nat(0u);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Markdown_instInhabitedColumns(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_unsigned_to_nat(0u);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_instOfNat(lean_object* v_n_67_){
_start:
{
lean_inc(v_n_67_);
return v_n_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_instOfNat___boxed(lean_object* v_n_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Markdown_Columns_instOfNat(v_n_68_);
lean_dec(v_n_68_);
return v_res_69_;
}
}
static lean_object* _init_l_Lean_Markdown_Columns_instLE(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Markdown_Columns_instLT(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_box(0);
return v___x_71_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_Columns_instDecidableLe(lean_object* v_a_72_, lean_object* v_b_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = lean_nat_dec_le(v_a_72_, v_b_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_instDecidableLe___boxed(lean_object* v_a_75_, lean_object* v_b_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Lean_Markdown_Columns_instDecidableLe(v_a_75_, v_b_76_);
lean_dec(v_b_76_);
lean_dec(v_a_75_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_Columns_instDecidableLt(lean_object* v_a_79_, lean_object* v_b_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_add(v_a_79_, v___x_81_);
v___x_83_ = lean_nat_dec_le(v___x_82_, v_b_80_);
lean_dec(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_instDecidableLt___boxed(lean_object* v_a_84_, lean_object* v_b_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Lean_Markdown_Columns_instDecidableLt(v_a_84_, v_b_85_);
lean_dec(v_b_85_);
lean_dec(v_a_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_space(lean_object* v_c_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_nat_add(v_c_92_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_space___boxed(lean_object* v_c_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Markdown_Columns_space(v_c_95_);
lean_dec(v_c_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_tabWidth(lean_object* v_c_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = lean_unsigned_to_nat(4u);
v___x_99_ = lean_nat_mod(v_c_97_, v___x_98_);
v___x_100_ = lean_nat_sub(v___x_98_, v___x_99_);
lean_dec(v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_tabWidth___boxed(lean_object* v_c_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Markdown_Columns_tabWidth(v_c_101_);
lean_dec(v_c_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_tab(lean_object* v_c_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = lean_unsigned_to_nat(4u);
v___x_105_ = lean_nat_mod(v_c_103_, v___x_104_);
v___x_106_ = lean_nat_sub(v___x_104_, v___x_105_);
lean_dec(v___x_105_);
v___x_107_ = lean_nat_add(v_c_103_, v___x_106_);
lean_dec(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Columns_tab___boxed(lean_object* v_c_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Markdown_Columns_tab(v_c_108_);
lean_dec(v_c_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_ctorIdx___impl(uint8_t v_x_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_box(v_x_110_);
v___x_112_ = lean_obj_tag_nat(v___x_111_);
lean_dec(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_ctorIdx___impl___boxed(lean_object* v_x_113_){
_start:
{
uint8_t v_x_4__boxed_114_; lean_object* v_res_115_; 
v_x_4__boxed_114_ = lean_unbox(v_x_113_);
v_res_115_ = l_Lean_Markdown_BulletKind_ctorIdx___impl(v_x_4__boxed_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_ctorElim___redArg(lean_object* v_k_116_){
_start:
{
lean_inc(v_k_116_);
return v_k_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_ctorElim___redArg___boxed(lean_object* v_k_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Markdown_BulletKind_ctorElim___redArg(v_k_117_);
lean_dec(v_k_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_ctorElim(lean_object* v_motive_119_, lean_object* v_ctorIdx_120_, uint8_t v_t_121_, lean_object* v_h_122_, lean_object* v_k_123_){
_start:
{
lean_inc(v_k_123_);
return v_k_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_ctorElim___boxed(lean_object* v_motive_124_, lean_object* v_ctorIdx_125_, lean_object* v_t_126_, lean_object* v_h_127_, lean_object* v_k_128_){
_start:
{
uint8_t v_t_boxed_129_; lean_object* v_res_130_; 
v_t_boxed_129_ = lean_unbox(v_t_126_);
v_res_130_ = l_Lean_Markdown_BulletKind_ctorElim(v_motive_124_, v_ctorIdx_125_, v_t_boxed_129_, v_h_127_, v_k_128_);
lean_dec(v_k_128_);
lean_dec(v_ctorIdx_125_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_star_elim___redArg(lean_object* v_star_131_){
_start:
{
lean_inc(v_star_131_);
return v_star_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_star_elim___redArg___boxed(lean_object* v_star_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Markdown_BulletKind_star_elim___redArg(v_star_132_);
lean_dec(v_star_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_star_elim(lean_object* v_motive_134_, uint8_t v_t_135_, lean_object* v_h_136_, lean_object* v_star_137_){
_start:
{
lean_inc(v_star_137_);
return v_star_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_star_elim___boxed(lean_object* v_motive_138_, lean_object* v_t_139_, lean_object* v_h_140_, lean_object* v_star_141_){
_start:
{
uint8_t v_t_boxed_142_; lean_object* v_res_143_; 
v_t_boxed_142_ = lean_unbox(v_t_139_);
v_res_143_ = l_Lean_Markdown_BulletKind_star_elim(v_motive_138_, v_t_boxed_142_, v_h_140_, v_star_141_);
lean_dec(v_star_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_hyphen_elim___redArg(lean_object* v_hyphen_144_){
_start:
{
lean_inc(v_hyphen_144_);
return v_hyphen_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_hyphen_elim___redArg___boxed(lean_object* v_hyphen_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Markdown_BulletKind_hyphen_elim___redArg(v_hyphen_145_);
lean_dec(v_hyphen_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_hyphen_elim(lean_object* v_motive_147_, uint8_t v_t_148_, lean_object* v_h_149_, lean_object* v_hyphen_150_){
_start:
{
lean_inc(v_hyphen_150_);
return v_hyphen_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_hyphen_elim___boxed(lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_hyphen_154_){
_start:
{
uint8_t v_t_boxed_155_; lean_object* v_res_156_; 
v_t_boxed_155_ = lean_unbox(v_t_152_);
v_res_156_ = l_Lean_Markdown_BulletKind_hyphen_elim(v_motive_151_, v_t_boxed_155_, v_h_153_, v_hyphen_154_);
lean_dec(v_hyphen_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_plus_elim___redArg(lean_object* v_plus_157_){
_start:
{
lean_inc(v_plus_157_);
return v_plus_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_plus_elim___redArg___boxed(lean_object* v_plus_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Markdown_BulletKind_plus_elim___redArg(v_plus_158_);
lean_dec(v_plus_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_plus_elim(lean_object* v_motive_160_, uint8_t v_t_161_, lean_object* v_h_162_, lean_object* v_plus_163_){
_start:
{
lean_inc(v_plus_163_);
return v_plus_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BulletKind_plus_elim___boxed(lean_object* v_motive_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_plus_167_){
_start:
{
uint8_t v_t_boxed_168_; lean_object* v_res_169_; 
v_t_boxed_168_ = lean_unbox(v_t_165_);
v_res_169_ = l_Lean_Markdown_BulletKind_plus_elim(v_motive_164_, v_t_boxed_168_, v_h_166_, v_plus_167_);
lean_dec(v_plus_167_);
return v_res_169_;
}
}
static lean_object* _init_l_Lean_Markdown_instReprBulletKind_repr___closed__6(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(2u);
v___x_180_ = lean_nat_to_int(v___x_179_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Markdown_instReprBulletKind_repr___closed__7(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_to_int(v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprBulletKind_repr(uint8_t v_x_183_, lean_object* v_prec_184_){
_start:
{
lean_object* v___y_186_; lean_object* v___y_193_; lean_object* v___y_200_; 
switch(v_x_183_)
{
case 0:
{
lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_206_ = lean_unsigned_to_nat(1024u);
v___x_207_ = lean_nat_dec_le(v___x_206_, v_prec_184_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
v___x_208_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__6, &l_Lean_Markdown_instReprBulletKind_repr___closed__6_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__6);
v___y_186_ = v___x_208_;
goto v___jp_185_;
}
else
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__7, &l_Lean_Markdown_instReprBulletKind_repr___closed__7_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__7);
v___y_186_ = v___x_209_;
goto v___jp_185_;
}
}
case 1:
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(1024u);
v___x_211_ = lean_nat_dec_le(v___x_210_, v_prec_184_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
v___x_212_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__6, &l_Lean_Markdown_instReprBulletKind_repr___closed__6_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__6);
v___y_193_ = v___x_212_;
goto v___jp_192_;
}
else
{
lean_object* v___x_213_; 
v___x_213_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__7, &l_Lean_Markdown_instReprBulletKind_repr___closed__7_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__7);
v___y_193_ = v___x_213_;
goto v___jp_192_;
}
}
default: 
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(1024u);
v___x_215_ = lean_nat_dec_le(v___x_214_, v_prec_184_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__6, &l_Lean_Markdown_instReprBulletKind_repr___closed__6_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__6);
v___y_200_ = v___x_216_;
goto v___jp_199_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__7, &l_Lean_Markdown_instReprBulletKind_repr___closed__7_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__7);
v___y_200_ = v___x_217_;
goto v___jp_199_;
}
}
}
v___jp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_187_ = ((lean_object*)(l_Lean_Markdown_instReprBulletKind_repr___closed__1));
lean_inc(v___y_186_);
v___x_188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_188_, 0, v___y_186_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = 0;
v___x_190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_189_);
v___x_191_ = l_Repr_addAppParen(v___x_190_, v_prec_184_);
return v___x_191_;
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_194_ = ((lean_object*)(l_Lean_Markdown_instReprBulletKind_repr___closed__3));
lean_inc(v___y_193_);
v___x_195_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_195_, 0, v___y_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = 0;
v___x_197_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*1, v___x_196_);
v___x_198_ = l_Repr_addAppParen(v___x_197_, v_prec_184_);
return v___x_198_;
}
v___jp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_201_ = ((lean_object*)(l_Lean_Markdown_instReprBulletKind_repr___closed__5));
lean_inc(v___y_200_);
v___x_202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_202_, 0, v___y_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = 0;
v___x_204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_204_, sizeof(void*)*1, v___x_203_);
v___x_205_ = l_Repr_addAppParen(v___x_204_, v_prec_184_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprBulletKind_repr___boxed(lean_object* v_x_218_, lean_object* v_prec_219_){
_start:
{
uint8_t v_x_171__boxed_220_; lean_object* v_res_221_; 
v_x_171__boxed_220_ = lean_unbox(v_x_218_);
v_res_221_ = l_Lean_Markdown_instReprBulletKind_repr(v_x_171__boxed_220_, v_prec_219_);
lean_dec(v_prec_219_);
return v_res_221_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_instBEqBulletKind_beq(uint8_t v_x_224_, uint8_t v_y_225_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_226_ = lean_box(v_x_224_);
v___x_227_ = lean_obj_tag_nat(v___x_226_);
lean_dec(v___x_226_);
v___x_228_ = lean_box(v_y_225_);
v___x_229_ = lean_obj_tag_nat(v___x_228_);
lean_dec(v___x_228_);
v___x_230_ = lean_nat_dec_eq(v___x_227_, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instBEqBulletKind_beq___boxed(lean_object* v_x_231_, lean_object* v_y_232_){
_start:
{
uint8_t v_x_24__boxed_233_; uint8_t v_y_25__boxed_234_; uint8_t v_res_235_; lean_object* v_r_236_; 
v_x_24__boxed_233_ = lean_unbox(v_x_231_);
v_y_25__boxed_234_ = lean_unbox(v_y_232_);
v_res_235_ = l_Lean_Markdown_instBEqBulletKind_beq(v_x_24__boxed_233_, v_y_25__boxed_234_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT uint64_t l_Lean_Markdown_instHashableBulletKind_hash(uint8_t v_x_239_){
_start:
{
switch(v_x_239_)
{
case 0:
{
uint64_t v___x_240_; 
v___x_240_ = 0ULL;
return v___x_240_;
}
case 1:
{
uint64_t v___x_241_; 
v___x_241_ = 1ULL;
return v___x_241_;
}
default: 
{
uint64_t v___x_242_; 
v___x_242_ = 2ULL;
return v___x_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instHashableBulletKind_hash___boxed(lean_object* v_x_243_){
_start:
{
uint8_t v_x_40__boxed_244_; uint64_t v_res_245_; lean_object* v_r_246_; 
v_x_40__boxed_244_ = lean_unbox(v_x_243_);
v_res_245_ = l_Lean_Markdown_instHashableBulletKind_hash(v_x_40__boxed_244_);
v_r_246_ = lean_box_uint64(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_ctorIdx___impl(uint8_t v_x_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_box(v_x_249_);
v___x_251_ = lean_obj_tag_nat(v___x_250_);
lean_dec(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_ctorIdx___impl___boxed(lean_object* v_x_252_){
_start:
{
uint8_t v_x_4__boxed_253_; lean_object* v_res_254_; 
v_x_4__boxed_253_ = lean_unbox(v_x_252_);
v_res_254_ = l_Lean_Markdown_OrderedDelim_ctorIdx___impl(v_x_4__boxed_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_ctorElim___redArg(lean_object* v_k_255_){
_start:
{
lean_inc(v_k_255_);
return v_k_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_ctorElim___redArg___boxed(lean_object* v_k_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Markdown_OrderedDelim_ctorElim___redArg(v_k_256_);
lean_dec(v_k_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_ctorElim(lean_object* v_motive_258_, lean_object* v_ctorIdx_259_, uint8_t v_t_260_, lean_object* v_h_261_, lean_object* v_k_262_){
_start:
{
lean_inc(v_k_262_);
return v_k_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_ctorElim___boxed(lean_object* v_motive_263_, lean_object* v_ctorIdx_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_k_267_){
_start:
{
uint8_t v_t_boxed_268_; lean_object* v_res_269_; 
v_t_boxed_268_ = lean_unbox(v_t_265_);
v_res_269_ = l_Lean_Markdown_OrderedDelim_ctorElim(v_motive_263_, v_ctorIdx_264_, v_t_boxed_268_, v_h_266_, v_k_267_);
lean_dec(v_k_267_);
lean_dec(v_ctorIdx_264_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_dot_elim___redArg(lean_object* v_dot_270_){
_start:
{
lean_inc(v_dot_270_);
return v_dot_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_dot_elim___redArg___boxed(lean_object* v_dot_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Markdown_OrderedDelim_dot_elim___redArg(v_dot_271_);
lean_dec(v_dot_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_dot_elim(lean_object* v_motive_273_, uint8_t v_t_274_, lean_object* v_h_275_, lean_object* v_dot_276_){
_start:
{
lean_inc(v_dot_276_);
return v_dot_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_dot_elim___boxed(lean_object* v_motive_277_, lean_object* v_t_278_, lean_object* v_h_279_, lean_object* v_dot_280_){
_start:
{
uint8_t v_t_boxed_281_; lean_object* v_res_282_; 
v_t_boxed_281_ = lean_unbox(v_t_278_);
v_res_282_ = l_Lean_Markdown_OrderedDelim_dot_elim(v_motive_277_, v_t_boxed_281_, v_h_279_, v_dot_280_);
lean_dec(v_dot_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_rparen_elim___redArg(lean_object* v_rparen_283_){
_start:
{
lean_inc(v_rparen_283_);
return v_rparen_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_rparen_elim___redArg___boxed(lean_object* v_rparen_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Markdown_OrderedDelim_rparen_elim___redArg(v_rparen_284_);
lean_dec(v_rparen_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_rparen_elim(lean_object* v_motive_286_, uint8_t v_t_287_, lean_object* v_h_288_, lean_object* v_rparen_289_){
_start:
{
lean_inc(v_rparen_289_);
return v_rparen_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OrderedDelim_rparen_elim___boxed(lean_object* v_motive_290_, lean_object* v_t_291_, lean_object* v_h_292_, lean_object* v_rparen_293_){
_start:
{
uint8_t v_t_boxed_294_; lean_object* v_res_295_; 
v_t_boxed_294_ = lean_unbox(v_t_291_);
v_res_295_ = l_Lean_Markdown_OrderedDelim_rparen_elim(v_motive_290_, v_t_boxed_294_, v_h_292_, v_rparen_293_);
lean_dec(v_rparen_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprOrderedDelim_repr(uint8_t v_x_302_, lean_object* v_prec_303_){
_start:
{
lean_object* v___y_305_; lean_object* v___y_312_; 
if (v_x_302_ == 0)
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(1024u);
v___x_319_ = lean_nat_dec_le(v___x_318_, v_prec_303_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
v___x_320_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__6, &l_Lean_Markdown_instReprBulletKind_repr___closed__6_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__6);
v___y_305_ = v___x_320_;
goto v___jp_304_;
}
else
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__7, &l_Lean_Markdown_instReprBulletKind_repr___closed__7_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__7);
v___y_305_ = v___x_321_;
goto v___jp_304_;
}
}
else
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(1024u);
v___x_323_ = lean_nat_dec_le(v___x_322_, v_prec_303_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
v___x_324_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__6, &l_Lean_Markdown_instReprBulletKind_repr___closed__6_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__6);
v___y_312_ = v___x_324_;
goto v___jp_311_;
}
else
{
lean_object* v___x_325_; 
v___x_325_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__7, &l_Lean_Markdown_instReprBulletKind_repr___closed__7_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__7);
v___y_312_ = v___x_325_;
goto v___jp_311_;
}
}
v___jp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_306_ = ((lean_object*)(l_Lean_Markdown_instReprOrderedDelim_repr___closed__1));
lean_inc(v___y_305_);
v___x_307_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_307_, 0, v___y_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = 0;
v___x_309_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*1, v___x_308_);
v___x_310_ = l_Repr_addAppParen(v___x_309_, v_prec_303_);
return v___x_310_;
}
v___jp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_313_ = ((lean_object*)(l_Lean_Markdown_instReprOrderedDelim_repr___closed__3));
lean_inc(v___y_312_);
v___x_314_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_314_, 0, v___y_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = 0;
v___x_316_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*1, v___x_315_);
v___x_317_ = l_Repr_addAppParen(v___x_316_, v_prec_303_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprOrderedDelim_repr___boxed(lean_object* v_x_326_, lean_object* v_prec_327_){
_start:
{
uint8_t v_x_113__boxed_328_; lean_object* v_res_329_; 
v_x_113__boxed_328_ = lean_unbox(v_x_326_);
v_res_329_ = l_Lean_Markdown_instReprOrderedDelim_repr(v_x_113__boxed_328_, v_prec_327_);
lean_dec(v_prec_327_);
return v_res_329_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_instBEqOrderedDelim_beq(uint8_t v_x_332_, uint8_t v_y_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_334_ = lean_box(v_x_332_);
v___x_335_ = lean_obj_tag_nat(v___x_334_);
lean_dec(v___x_334_);
v___x_336_ = lean_box(v_y_333_);
v___x_337_ = lean_obj_tag_nat(v___x_336_);
lean_dec(v___x_336_);
v___x_338_ = lean_nat_dec_eq(v___x_335_, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instBEqOrderedDelim_beq___boxed(lean_object* v_x_339_, lean_object* v_y_340_){
_start:
{
uint8_t v_x_24__boxed_341_; uint8_t v_y_25__boxed_342_; uint8_t v_res_343_; lean_object* v_r_344_; 
v_x_24__boxed_341_ = lean_unbox(v_x_339_);
v_y_25__boxed_342_ = lean_unbox(v_y_340_);
v_res_343_ = l_Lean_Markdown_instBEqOrderedDelim_beq(v_x_24__boxed_341_, v_y_25__boxed_342_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT uint64_t l_Lean_Markdown_instHashableOrderedDelim_hash(uint8_t v_x_347_){
_start:
{
if (v_x_347_ == 0)
{
uint64_t v___x_348_; 
v___x_348_ = 0ULL;
return v___x_348_;
}
else
{
uint64_t v___x_349_; 
v___x_349_ = 1ULL;
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instHashableOrderedDelim_hash___boxed(lean_object* v_x_350_){
_start:
{
uint8_t v_x_28__boxed_351_; uint64_t v_res_352_; lean_object* v_r_353_; 
v_x_28__boxed_351_ = lean_unbox(v_x_350_);
v_res_352_ = l_Lean_Markdown_instHashableOrderedDelim_hash(v_x_28__boxed_351_);
v_r_353_ = lean_box_uint64(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ctorIdx___impl(lean_object* v_x_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_tag_nat(v_x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ctorIdx___impl___boxed(lean_object* v_x_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Markdown_ListKind_ctorIdx___impl(v_x_358_);
lean_dec_ref(v_x_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ctorElim___redArg(lean_object* v_t_360_, lean_object* v_k_361_){
_start:
{
if (lean_obj_tag(v_t_360_) == 0)
{
uint8_t v_kind_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_kind_362_ = lean_ctor_get_uint8(v_t_360_, 0);
lean_dec_ref_known(v_t_360_, 0);
v___x_363_ = lean_box(v_kind_362_);
v___x_364_ = lean_apply_1(v_k_361_, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v_start_365_; uint8_t v_delim_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_start_365_ = lean_ctor_get(v_t_360_, 0);
lean_inc(v_start_365_);
v_delim_366_ = lean_ctor_get_uint8(v_t_360_, sizeof(void*)*1);
lean_dec_ref_known(v_t_360_, 1);
v___x_367_ = lean_box(v_delim_366_);
v___x_368_ = lean_apply_2(v_k_361_, v_start_365_, v___x_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ctorElim(lean_object* v_motive_369_, lean_object* v_ctorIdx_370_, lean_object* v_t_371_, lean_object* v_h_372_, lean_object* v_k_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Markdown_ListKind_ctorElim___redArg(v_t_371_, v_k_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ctorElim___boxed(lean_object* v_motive_375_, lean_object* v_ctorIdx_376_, lean_object* v_t_377_, lean_object* v_h_378_, lean_object* v_k_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Markdown_ListKind_ctorElim(v_motive_375_, v_ctorIdx_376_, v_t_377_, v_h_378_, v_k_379_);
lean_dec(v_ctorIdx_376_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_bullet_elim___redArg(lean_object* v_t_381_, lean_object* v_bullet_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Markdown_ListKind_ctorElim___redArg(v_t_381_, v_bullet_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_bullet_elim(lean_object* v_motive_384_, lean_object* v_t_385_, lean_object* v_h_386_, lean_object* v_bullet_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Markdown_ListKind_ctorElim___redArg(v_t_385_, v_bullet_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ordered_elim___redArg(lean_object* v_t_389_, lean_object* v_ordered_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Markdown_ListKind_ctorElim___redArg(v_t_389_, v_ordered_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_ordered_elim(lean_object* v_motive_392_, lean_object* v_t_393_, lean_object* v_h_394_, lean_object* v_ordered_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Markdown_ListKind_ctorElim___redArg(v_t_393_, v_ordered_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprListKind_repr(lean_object* v_x_409_, lean_object* v_prec_410_){
_start:
{
if (lean_obj_tag(v_x_409_) == 0)
{
uint8_t v_kind_411_; lean_object* v___y_413_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_kind_411_ = lean_ctor_get_uint8(v_x_409_, 0);
lean_dec_ref_known(v_x_409_, 0);
v___x_422_ = lean_unsigned_to_nat(1024u);
v___x_423_ = lean_nat_dec_le(v___x_422_, v_prec_410_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
v___x_424_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__6, &l_Lean_Markdown_instReprBulletKind_repr___closed__6_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__6);
v___y_413_ = v___x_424_;
goto v___jp_412_;
}
else
{
lean_object* v___x_425_; 
v___x_425_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__7, &l_Lean_Markdown_instReprBulletKind_repr___closed__7_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__7);
v___y_413_ = v___x_425_;
goto v___jp_412_;
}
v___jp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_414_ = ((lean_object*)(l_Lean_Markdown_instReprListKind_repr___closed__2));
v___x_415_ = lean_unsigned_to_nat(1024u);
v___x_416_ = l_Lean_Markdown_instReprBulletKind_repr(v_kind_411_, v___x_415_);
v___x_417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_414_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
lean_inc(v___y_413_);
v___x_418_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_418_, 0, v___y_413_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = 0;
v___x_420_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*1, v___x_419_);
v___x_421_ = l_Repr_addAppParen(v___x_420_, v_prec_410_);
return v___x_421_;
}
}
else
{
lean_object* v_start_426_; uint8_t v_delim_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_452_; 
v_start_426_ = lean_ctor_get(v_x_409_, 0);
v_delim_427_ = lean_ctor_get_uint8(v_x_409_, sizeof(void*)*1);
v_isSharedCheck_452_ = !lean_is_exclusive(v_x_409_);
if (v_isSharedCheck_452_ == 0)
{
v___x_429_ = v_x_409_;
v_isShared_430_ = v_isSharedCheck_452_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_start_426_);
lean_dec(v_x_409_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_452_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___y_432_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_unsigned_to_nat(1024u);
v___x_449_ = lean_nat_dec_le(v___x_448_, v_prec_410_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__6, &l_Lean_Markdown_instReprBulletKind_repr___closed__6_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__6);
v___y_432_ = v___x_450_;
goto v___jp_431_;
}
else
{
lean_object* v___x_451_; 
v___x_451_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__7, &l_Lean_Markdown_instReprBulletKind_repr___closed__7_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__7);
v___y_432_ = v___x_451_;
goto v___jp_431_;
}
v___jp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; lean_object* v___x_445_; 
v___x_433_ = lean_box(1);
v___x_434_ = ((lean_object*)(l_Lean_Markdown_instReprListKind_repr___closed__5));
v___x_435_ = l_Nat_reprFast(v_start_426_);
v___x_436_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
v___x_437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_434_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_433_);
v___x_439_ = lean_unsigned_to_nat(1024u);
v___x_440_ = l_Lean_Markdown_instReprOrderedDelim_repr(v_delim_427_, v___x_439_);
v___x_441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_438_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
lean_inc(v___y_432_);
v___x_442_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_442_, 0, v___y_432_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = 0;
if (v_isShared_430_ == 0)
{
lean_ctor_set_tag(v___x_429_, 6);
lean_ctor_set(v___x_429_, 0, v___x_442_);
v___x_445_ = v___x_429_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_442_);
v___x_445_ = v_reuseFailAlloc_447_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; 
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*1, v___x_443_);
v___x_446_ = l_Repr_addAppParen(v___x_445_, v_prec_410_);
return v___x_446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprListKind_repr___boxed(lean_object* v_x_453_, lean_object* v_prec_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Markdown_instReprListKind_repr(v_x_453_, v_prec_454_);
lean_dec(v_prec_454_);
return v_res_455_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_instBEqListKind_beq(lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
if (lean_obj_tag(v_x_459_) == 0)
{
uint8_t v_kind_460_; uint8_t v_kind_461_; uint8_t v___x_462_; 
v_kind_460_ = lean_ctor_get_uint8(v_x_458_, 0);
v_kind_461_ = lean_ctor_get_uint8(v_x_459_, 0);
v___x_462_ = l_Lean_Markdown_instBEqBulletKind_beq(v_kind_460_, v_kind_461_);
return v___x_462_;
}
else
{
uint8_t v___x_463_; 
v___x_463_ = 0;
return v___x_463_;
}
}
else
{
if (lean_obj_tag(v_x_459_) == 1)
{
lean_object* v_start_464_; uint8_t v_delim_465_; lean_object* v_start_466_; uint8_t v_delim_467_; uint8_t v___x_468_; 
v_start_464_ = lean_ctor_get(v_x_458_, 0);
v_delim_465_ = lean_ctor_get_uint8(v_x_458_, sizeof(void*)*1);
v_start_466_ = lean_ctor_get(v_x_459_, 0);
v_delim_467_ = lean_ctor_get_uint8(v_x_459_, sizeof(void*)*1);
v___x_468_ = lean_nat_dec_eq(v_start_464_, v_start_466_);
if (v___x_468_ == 0)
{
return v___x_468_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = l_Lean_Markdown_instBEqOrderedDelim_beq(v_delim_465_, v_delim_467_);
return v___x_469_;
}
}
else
{
uint8_t v___x_470_; 
v___x_470_ = 0;
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instBEqListKind_beq___boxed(lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
uint8_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = l_Lean_Markdown_instBEqListKind_beq(v_x_471_, v_x_472_);
lean_dec_ref(v_x_472_);
lean_dec_ref(v_x_471_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT uint64_t l_Lean_Markdown_instHashableListKind_hash(lean_object* v_x_477_){
_start:
{
if (lean_obj_tag(v_x_477_) == 0)
{
uint8_t v_kind_478_; uint64_t v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; 
v_kind_478_ = lean_ctor_get_uint8(v_x_477_, 0);
v___x_479_ = 0ULL;
v___x_480_ = l_Lean_Markdown_instHashableBulletKind_hash(v_kind_478_);
v___x_481_ = lean_uint64_mix_hash(v___x_479_, v___x_480_);
return v___x_481_;
}
else
{
lean_object* v_start_482_; uint8_t v_delim_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v___x_487_; uint64_t v___x_488_; 
v_start_482_ = lean_ctor_get(v_x_477_, 0);
v_delim_483_ = lean_ctor_get_uint8(v_x_477_, sizeof(void*)*1);
v___x_484_ = 1ULL;
v___x_485_ = lean_uint64_of_nat(v_start_482_);
v___x_486_ = lean_uint64_mix_hash(v___x_484_, v___x_485_);
v___x_487_ = l_Lean_Markdown_instHashableOrderedDelim_hash(v_delim_483_);
v___x_488_ = lean_uint64_mix_hash(v___x_486_, v___x_487_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instHashableListKind_hash___boxed(lean_object* v_x_489_){
_start:
{
uint64_t v_res_490_; lean_object* v_r_491_; 
v_res_490_ = l_Lean_Markdown_instHashableListKind_hash(v_x_489_);
lean_dec_ref(v_x_489_);
v_r_491_ = lean_box_uint64(v_res_490_);
return v_r_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ctorIdx___impl(uint8_t v_x_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_box(v_x_494_);
v___x_496_ = lean_obj_tag_nat(v___x_495_);
lean_dec(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ctorIdx___impl___boxed(lean_object* v_x_497_){
_start:
{
uint8_t v_x_4__boxed_498_; lean_object* v_res_499_; 
v_x_4__boxed_498_ = lean_unbox(v_x_497_);
v_res_499_ = l_Lean_Markdown_FenceChar_ctorIdx___impl(v_x_4__boxed_498_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ctorElim___redArg(lean_object* v_k_500_){
_start:
{
lean_inc(v_k_500_);
return v_k_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ctorElim___redArg___boxed(lean_object* v_k_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Markdown_FenceChar_ctorElim___redArg(v_k_501_);
lean_dec(v_k_501_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ctorElim(lean_object* v_motive_503_, lean_object* v_ctorIdx_504_, uint8_t v_t_505_, lean_object* v_h_506_, lean_object* v_k_507_){
_start:
{
lean_inc(v_k_507_);
return v_k_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ctorElim___boxed(lean_object* v_motive_508_, lean_object* v_ctorIdx_509_, lean_object* v_t_510_, lean_object* v_h_511_, lean_object* v_k_512_){
_start:
{
uint8_t v_t_boxed_513_; lean_object* v_res_514_; 
v_t_boxed_513_ = lean_unbox(v_t_510_);
v_res_514_ = l_Lean_Markdown_FenceChar_ctorElim(v_motive_508_, v_ctorIdx_509_, v_t_boxed_513_, v_h_511_, v_k_512_);
lean_dec(v_k_512_);
lean_dec(v_ctorIdx_509_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_backtick_elim___redArg(lean_object* v_backtick_515_){
_start:
{
lean_inc(v_backtick_515_);
return v_backtick_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_backtick_elim___redArg___boxed(lean_object* v_backtick_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Markdown_FenceChar_backtick_elim___redArg(v_backtick_516_);
lean_dec(v_backtick_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_backtick_elim(lean_object* v_motive_518_, uint8_t v_t_519_, lean_object* v_h_520_, lean_object* v_backtick_521_){
_start:
{
lean_inc(v_backtick_521_);
return v_backtick_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_backtick_elim___boxed(lean_object* v_motive_522_, lean_object* v_t_523_, lean_object* v_h_524_, lean_object* v_backtick_525_){
_start:
{
uint8_t v_t_boxed_526_; lean_object* v_res_527_; 
v_t_boxed_526_ = lean_unbox(v_t_523_);
v_res_527_ = l_Lean_Markdown_FenceChar_backtick_elim(v_motive_522_, v_t_boxed_526_, v_h_524_, v_backtick_525_);
lean_dec(v_backtick_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_tilde_elim___redArg(lean_object* v_tilde_528_){
_start:
{
lean_inc(v_tilde_528_);
return v_tilde_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_tilde_elim___redArg___boxed(lean_object* v_tilde_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Markdown_FenceChar_tilde_elim___redArg(v_tilde_529_);
lean_dec(v_tilde_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_tilde_elim(lean_object* v_motive_531_, uint8_t v_t_532_, lean_object* v_h_533_, lean_object* v_tilde_534_){
_start:
{
lean_inc(v_tilde_534_);
return v_tilde_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_tilde_elim___boxed(lean_object* v_motive_535_, lean_object* v_t_536_, lean_object* v_h_537_, lean_object* v_tilde_538_){
_start:
{
uint8_t v_t_boxed_539_; lean_object* v_res_540_; 
v_t_boxed_539_ = lean_unbox(v_t_536_);
v_res_540_ = l_Lean_Markdown_FenceChar_tilde_elim(v_motive_535_, v_t_boxed_539_, v_h_537_, v_tilde_538_);
lean_dec(v_tilde_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprFenceChar_repr(uint8_t v_x_547_, lean_object* v_prec_548_){
_start:
{
lean_object* v___y_550_; lean_object* v___y_557_; 
if (v_x_547_ == 0)
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = lean_unsigned_to_nat(1024u);
v___x_564_ = lean_nat_dec_le(v___x_563_, v_prec_548_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__6, &l_Lean_Markdown_instReprBulletKind_repr___closed__6_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__6);
v___y_550_ = v___x_565_;
goto v___jp_549_;
}
else
{
lean_object* v___x_566_; 
v___x_566_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__7, &l_Lean_Markdown_instReprBulletKind_repr___closed__7_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__7);
v___y_550_ = v___x_566_;
goto v___jp_549_;
}
}
else
{
lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(1024u);
v___x_568_ = lean_nat_dec_le(v___x_567_, v_prec_548_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
v___x_569_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__6, &l_Lean_Markdown_instReprBulletKind_repr___closed__6_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__6);
v___y_557_ = v___x_569_;
goto v___jp_556_;
}
else
{
lean_object* v___x_570_; 
v___x_570_ = lean_obj_once(&l_Lean_Markdown_instReprBulletKind_repr___closed__7, &l_Lean_Markdown_instReprBulletKind_repr___closed__7_once, _init_l_Lean_Markdown_instReprBulletKind_repr___closed__7);
v___y_557_ = v___x_570_;
goto v___jp_556_;
}
}
v___jp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_551_ = ((lean_object*)(l_Lean_Markdown_instReprFenceChar_repr___closed__1));
lean_inc(v___y_550_);
v___x_552_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_552_, 0, v___y_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = 0;
v___x_554_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*1, v___x_553_);
v___x_555_ = l_Repr_addAppParen(v___x_554_, v_prec_548_);
return v___x_555_;
}
v___jp_556_:
{
lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_558_ = ((lean_object*)(l_Lean_Markdown_instReprFenceChar_repr___closed__3));
lean_inc(v___y_557_);
v___x_559_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_559_, 0, v___y_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = 0;
v___x_561_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*1, v___x_560_);
v___x_562_ = l_Repr_addAppParen(v___x_561_, v_prec_548_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprFenceChar_repr___boxed(lean_object* v_x_571_, lean_object* v_prec_572_){
_start:
{
uint8_t v_x_113__boxed_573_; lean_object* v_res_574_; 
v_x_113__boxed_573_ = lean_unbox(v_x_571_);
v_res_574_ = l_Lean_Markdown_instReprFenceChar_repr(v_x_113__boxed_573_, v_prec_572_);
lean_dec(v_prec_572_);
return v_res_574_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_instBEqFenceChar_beq(uint8_t v_x_577_, uint8_t v_y_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_579_ = lean_box(v_x_577_);
v___x_580_ = lean_obj_tag_nat(v___x_579_);
lean_dec(v___x_579_);
v___x_581_ = lean_box(v_y_578_);
v___x_582_ = lean_obj_tag_nat(v___x_581_);
lean_dec(v___x_581_);
v___x_583_ = lean_nat_dec_eq(v___x_580_, v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instBEqFenceChar_beq___boxed(lean_object* v_x_584_, lean_object* v_y_585_){
_start:
{
uint8_t v_x_24__boxed_586_; uint8_t v_y_25__boxed_587_; uint8_t v_res_588_; lean_object* v_r_589_; 
v_x_24__boxed_586_ = lean_unbox(v_x_584_);
v_y_25__boxed_587_ = lean_unbox(v_y_585_);
v_res_588_ = l_Lean_Markdown_instBEqFenceChar_beq(v_x_24__boxed_586_, v_y_25__boxed_587_);
v_r_589_ = lean_box(v_res_588_);
return v_r_589_;
}
}
LEAN_EXPORT uint64_t l_Lean_Markdown_instHashableFenceChar_hash(uint8_t v_x_592_){
_start:
{
if (v_x_592_ == 0)
{
uint64_t v___x_593_; 
v___x_593_ = 0ULL;
return v___x_593_;
}
else
{
uint64_t v___x_594_; 
v___x_594_ = 1ULL;
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instHashableFenceChar_hash___boxed(lean_object* v_x_595_){
_start:
{
uint8_t v_x_28__boxed_596_; uint64_t v_res_597_; lean_object* v_r_598_; 
v_x_28__boxed_596_ = lean_unbox(v_x_595_);
v_res_597_ = l_Lean_Markdown_instHashableFenceChar_hash(v_x_28__boxed_596_);
v_r_598_ = lean_box_uint64(v_res_597_);
return v_r_598_;
}
}
static uint8_t _init_l_Lean_Markdown_instInhabitedFenceChar_default(void){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = 0;
return v___x_601_;
}
}
static uint8_t _init_l_Lean_Markdown_instInhabitedFenceChar(void){
_start:
{
uint8_t v___x_602_; 
v___x_602_ = 0;
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ofChar_x3f(uint32_t v_x_609_){
_start:
{
uint32_t v___x_610_; uint8_t v___x_611_; 
v___x_610_ = 96;
v___x_611_ = lean_uint32_dec_eq(v_x_609_, v___x_610_);
if (v___x_611_ == 0)
{
uint32_t v___x_612_; uint8_t v___x_613_; 
v___x_612_ = 126;
v___x_613_ = lean_uint32_dec_eq(v_x_609_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
v___x_614_ = lean_box(0);
return v___x_614_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = ((lean_object*)(l_Lean_Markdown_FenceChar_ofChar_x3f___closed__0));
return v___x_615_;
}
}
else
{
lean_object* v___x_616_; 
v___x_616_ = ((lean_object*)(l_Lean_Markdown_FenceChar_ofChar_x3f___closed__1));
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_ofChar_x3f___boxed(lean_object* v_x_617_){
_start:
{
uint32_t v_x_67__boxed_618_; lean_object* v_res_619_; 
v_x_67__boxed_618_ = lean_unbox_uint32(v_x_617_);
lean_dec(v_x_617_);
v_res_619_ = l_Lean_Markdown_FenceChar_ofChar_x3f(v_x_67__boxed_618_);
return v_res_619_;
}
}
LEAN_EXPORT uint32_t l_Lean_Markdown_FenceChar_toChar(uint8_t v_x_620_){
_start:
{
if (v_x_620_ == 0)
{
uint32_t v___x_621_; 
v___x_621_ = 96;
return v___x_621_;
}
else
{
uint32_t v___x_622_; 
v___x_622_ = 126;
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_FenceChar_toChar___boxed(lean_object* v_x_623_){
_start:
{
uint8_t v_x_22__boxed_624_; uint32_t v_res_625_; lean_object* v_r_626_; 
v_x_22__boxed_624_ = lean_unbox(v_x_623_);
v_res_625_ = l_Lean_Markdown_FenceChar_toChar(v_x_22__boxed_624_);
v_r_626_ = lean_box_uint32(v_res_625_);
return v_r_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo_default___redArg(){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = ((lean_object*)(l_Lean_Markdown_instInhabitedFenceInfo_default___redArg___closed__0));
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo_default___redArg___boxed(lean_object* v___dummy_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Markdown_instInhabitedFenceInfo_default___redArg();
return v_res_634_;
}
}
static lean_object* _init_l_Lean_Markdown_instInhabitedFenceInfo_default___closed__0(void){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Markdown_instInhabitedFenceInfo_default___redArg();
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo_default(lean_object* v_s_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Lean_Markdown_instInhabitedFenceInfo_default___closed__0, &l_Lean_Markdown_instInhabitedFenceInfo_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedFenceInfo_default___closed__0);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo_default___boxed(lean_object* v_s_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Markdown_instInhabitedFenceInfo_default(v_s_638_);
lean_dec_ref(v_s_638_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo___redArg(){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = lean_obj_once(&l_Lean_Markdown_instInhabitedFenceInfo_default___closed__0, &l_Lean_Markdown_instInhabitedFenceInfo_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedFenceInfo_default___closed__0);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo___redArg___boxed(lean_object* v___dummy_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Markdown_instInhabitedFenceInfo___redArg();
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo(lean_object* v_a_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = lean_obj_once(&l_Lean_Markdown_instInhabitedFenceInfo_default___closed__0, &l_Lean_Markdown_instInhabitedFenceInfo_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedFenceInfo_default___closed__0);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedFenceInfo___boxed(lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Markdown_instInhabitedFenceInfo(v_a_646_);
lean_dec_ref(v_a_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedVerbatimLine_default(lean_object* v_s_648_){
_start:
{
lean_object* v_startInclusive_649_; lean_object* v_endExclusive_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_startInclusive_649_ = lean_ctor_get(v_s_648_, 1);
v_endExclusive_650_ = lean_ctor_get(v_s_648_, 2);
v___x_651_ = lean_nat_sub(v_endExclusive_650_, v_startInclusive_649_);
lean_inc(v___x_651_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedVerbatimLine_default___boxed(lean_object* v_s_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Markdown_instInhabitedVerbatimLine_default(v_s_655_);
lean_dec_ref(v_s_655_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedVerbatimLine(lean_object* v_a_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Markdown_instInhabitedVerbatimLine_default(v_a_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedVerbatimLine___boxed(lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_Markdown_instInhabitedVerbatimLine(v_a_659_);
lean_dec_ref(v_a_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Markdown_VerbatimLine_text_spec__0(lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
lean_object* v_zero_663_; uint8_t v_isZero_664_; 
v_zero_663_ = lean_unsigned_to_nat(0u);
v_isZero_664_ = lean_nat_dec_eq(v_x_661_, v_zero_663_);
if (v_isZero_664_ == 1)
{
lean_dec(v_x_661_);
return v_x_662_;
}
else
{
uint32_t v___x_665_; lean_object* v_one_666_; lean_object* v_n_667_; lean_object* v___x_668_; 
v___x_665_ = 32;
v_one_666_ = lean_unsigned_to_nat(1u);
v_n_667_ = lean_nat_sub(v_x_661_, v_one_666_);
lean_dec(v_x_661_);
v___x_668_ = lean_string_push(v_x_662_, v___x_665_);
v_x_661_ = v_n_667_;
v_x_662_ = v___x_668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_VerbatimLine_text(lean_object* v_s_671_, lean_object* v_line_672_){
_start:
{
lean_object* v_source_673_; lean_object* v_leadingSpaces_674_; lean_object* v_startInclusive_675_; lean_object* v_endExclusive_676_; lean_object* v_str_677_; lean_object* v_startInclusive_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_source_673_ = lean_ctor_get(v_line_672_, 0);
lean_inc_ref(v_source_673_);
v_leadingSpaces_674_ = lean_ctor_get(v_line_672_, 1);
lean_inc(v_leadingSpaces_674_);
lean_dec_ref(v_line_672_);
v_startInclusive_675_ = lean_ctor_get(v_source_673_, 0);
lean_inc(v_startInclusive_675_);
v_endExclusive_676_ = lean_ctor_get(v_source_673_, 1);
lean_inc(v_endExclusive_676_);
lean_dec_ref(v_source_673_);
v_str_677_ = lean_ctor_get(v_s_671_, 0);
v_startInclusive_678_ = lean_ctor_get(v_s_671_, 1);
v___x_679_ = ((lean_object*)(l_Lean_Markdown_VerbatimLine_text___closed__0));
v___x_680_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Markdown_VerbatimLine_text_spec__0(v_leadingSpaces_674_, v___x_679_);
v___x_681_ = lean_nat_add(v_startInclusive_678_, v_startInclusive_675_);
lean_dec(v_startInclusive_675_);
v___x_682_ = lean_nat_add(v_startInclusive_678_, v_endExclusive_676_);
lean_dec(v_endExclusive_676_);
v___x_683_ = lean_string_utf8_extract_fast(v_str_677_, v___x_681_, v___x_682_);
lean_dec(v___x_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_string_append(v___x_680_, v___x_683_);
lean_dec_ref(v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_VerbatimLine_text___boxed(lean_object* v_s_685_, lean_object* v_line_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Markdown_VerbatimLine_text(v_s_685_, v_line_686_);
lean_dec_ref(v_s_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorIdx___impl___redArg(lean_object* v_x_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = lean_obj_tag_nat(v_x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorIdx___impl___redArg___boxed(lean_object* v_x_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Markdown_Block_Raw_ctorIdx___impl___redArg(v_x_690_);
lean_dec_ref(v_x_690_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorIdx___impl(lean_object* v_s_692_, lean_object* v_x_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = lean_obj_tag_nat(v_x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorIdx___impl___boxed(lean_object* v_s_695_, lean_object* v_x_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Markdown_Block_Raw_ctorIdx___impl(v_s_695_, v_x_696_);
lean_dec_ref(v_x_696_);
lean_dec_ref(v_s_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorElim___redArg(lean_object* v_t_698_, lean_object* v_k_699_){
_start:
{
switch(lean_obj_tag(v_t_698_))
{
case 1:
{
lean_object* v_level_700_; lean_object* v_hashes_701_; lean_object* v_content_702_; lean_object* v_closeHashes_x3f_703_; lean_object* v___x_704_; 
v_level_700_ = lean_ctor_get(v_t_698_, 0);
lean_inc(v_level_700_);
v_hashes_701_ = lean_ctor_get(v_t_698_, 1);
lean_inc_ref(v_hashes_701_);
v_content_702_ = lean_ctor_get(v_t_698_, 2);
lean_inc_ref(v_content_702_);
v_closeHashes_x3f_703_ = lean_ctor_get(v_t_698_, 3);
lean_inc(v_closeHashes_x3f_703_);
lean_dec_ref_known(v_t_698_, 4);
v___x_704_ = lean_apply_4(v_k_699_, v_level_700_, v_hashes_701_, v_content_702_, v_closeHashes_x3f_703_);
return v___x_704_;
}
case 2:
{
lean_object* v_level_705_; lean_object* v_content_706_; lean_object* v_underline_707_; lean_object* v___x_708_; 
v_level_705_ = lean_ctor_get(v_t_698_, 0);
lean_inc(v_level_705_);
v_content_706_ = lean_ctor_get(v_t_698_, 1);
lean_inc_ref(v_content_706_);
v_underline_707_ = lean_ctor_get(v_t_698_, 2);
lean_inc_ref(v_underline_707_);
lean_dec_ref_known(v_t_698_, 3);
v___x_708_ = lean_apply_3(v_k_699_, v_level_705_, v_content_706_, v_underline_707_);
return v___x_708_;
}
case 3:
{
lean_object* v_info_709_; lean_object* v_openFence_710_; lean_object* v_closeFence_x3f_711_; lean_object* v_lines_712_; lean_object* v___x_713_; 
v_info_709_ = lean_ctor_get(v_t_698_, 0);
lean_inc_ref(v_info_709_);
v_openFence_710_ = lean_ctor_get(v_t_698_, 1);
lean_inc_ref(v_openFence_710_);
v_closeFence_x3f_711_ = lean_ctor_get(v_t_698_, 2);
lean_inc(v_closeFence_x3f_711_);
v_lines_712_ = lean_ctor_get(v_t_698_, 3);
lean_inc_ref(v_lines_712_);
lean_dec_ref_known(v_t_698_, 4);
v___x_713_ = lean_apply_4(v_k_699_, v_info_709_, v_openFence_710_, v_closeFence_x3f_711_, v_lines_712_);
return v___x_713_;
}
case 6:
{
lean_object* v_markers_714_; lean_object* v_children_715_; lean_object* v___x_716_; 
v_markers_714_ = lean_ctor_get(v_t_698_, 0);
lean_inc_ref(v_markers_714_);
v_children_715_ = lean_ctor_get(v_t_698_, 1);
lean_inc_ref(v_children_715_);
lean_dec_ref_known(v_t_698_, 2);
v___x_716_ = lean_apply_2(v_k_699_, v_markers_714_, v_children_715_);
return v___x_716_;
}
case 7:
{
lean_object* v_kind_717_; uint8_t v_tight_718_; lean_object* v_items_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_kind_717_ = lean_ctor_get(v_t_698_, 0);
lean_inc_ref(v_kind_717_);
v_tight_718_ = lean_ctor_get_uint8(v_t_698_, sizeof(void*)*2);
v_items_719_ = lean_ctor_get(v_t_698_, 1);
lean_inc_ref(v_items_719_);
lean_dec_ref_known(v_t_698_, 2);
v___x_720_ = lean_box(v_tight_718_);
v___x_721_ = lean_apply_3(v_k_699_, v_kind_717_, v___x_720_, v_items_719_);
return v___x_721_;
}
case 8:
{
lean_object* v_marker_722_; lean_object* v_children_723_; lean_object* v___x_724_; 
v_marker_722_ = lean_ctor_get(v_t_698_, 0);
lean_inc_ref(v_marker_722_);
v_children_723_ = lean_ctor_get(v_t_698_, 1);
lean_inc_ref(v_children_723_);
lean_dec_ref_known(v_t_698_, 2);
v___x_724_ = lean_apply_2(v_k_699_, v_marker_722_, v_children_723_);
return v___x_724_;
}
default: 
{
lean_object* v_content_725_; lean_object* v___x_726_; 
v_content_725_ = lean_ctor_get(v_t_698_, 0);
lean_inc_ref(v_content_725_);
lean_dec_ref(v_t_698_);
v___x_726_ = lean_apply_1(v_k_699_, v_content_725_);
return v___x_726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorElim(lean_object* v_s_727_, lean_object* v_motive__1_728_, lean_object* v_ctorIdx_729_, lean_object* v_t_730_, lean_object* v_h_731_, lean_object* v_k_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_730_, v_k_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_ctorElim___boxed(lean_object* v_s_734_, lean_object* v_motive__1_735_, lean_object* v_ctorIdx_736_, lean_object* v_t_737_, lean_object* v_h_738_, lean_object* v_k_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Markdown_Block_Raw_ctorElim(v_s_734_, v_motive__1_735_, v_ctorIdx_736_, v_t_737_, v_h_738_, v_k_739_);
lean_dec(v_ctorIdx_736_);
lean_dec_ref(v_s_734_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_paragraph_elim___redArg(lean_object* v_t_741_, lean_object* v_paragraph_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_741_, v_paragraph_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_paragraph_elim(lean_object* v_s_744_, lean_object* v_motive__1_745_, lean_object* v_t_746_, lean_object* v_h_747_, lean_object* v_paragraph_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_746_, v_paragraph_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_paragraph_elim___boxed(lean_object* v_s_750_, lean_object* v_motive__1_751_, lean_object* v_t_752_, lean_object* v_h_753_, lean_object* v_paragraph_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Markdown_Block_Raw_paragraph_elim(v_s_750_, v_motive__1_751_, v_t_752_, v_h_753_, v_paragraph_754_);
lean_dec_ref(v_s_750_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_atxHeading_elim___redArg(lean_object* v_t_756_, lean_object* v_atxHeading_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_756_, v_atxHeading_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_atxHeading_elim(lean_object* v_s_759_, lean_object* v_motive__1_760_, lean_object* v_t_761_, lean_object* v_h_762_, lean_object* v_atxHeading_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_761_, v_atxHeading_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_atxHeading_elim___boxed(lean_object* v_s_765_, lean_object* v_motive__1_766_, lean_object* v_t_767_, lean_object* v_h_768_, lean_object* v_atxHeading_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Markdown_Block_Raw_atxHeading_elim(v_s_765_, v_motive__1_766_, v_t_767_, v_h_768_, v_atxHeading_769_);
lean_dec_ref(v_s_765_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_setextHeading_elim___redArg(lean_object* v_t_771_, lean_object* v_setextHeading_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_771_, v_setextHeading_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_setextHeading_elim(lean_object* v_s_774_, lean_object* v_motive__1_775_, lean_object* v_t_776_, lean_object* v_h_777_, lean_object* v_setextHeading_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_776_, v_setextHeading_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_setextHeading_elim___boxed(lean_object* v_s_780_, lean_object* v_motive__1_781_, lean_object* v_t_782_, lean_object* v_h_783_, lean_object* v_setextHeading_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Markdown_Block_Raw_setextHeading_elim(v_s_780_, v_motive__1_781_, v_t_782_, v_h_783_, v_setextHeading_784_);
lean_dec_ref(v_s_780_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_fencedCode_elim___redArg(lean_object* v_t_786_, lean_object* v_fencedCode_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_786_, v_fencedCode_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_fencedCode_elim(lean_object* v_s_789_, lean_object* v_motive__1_790_, lean_object* v_t_791_, lean_object* v_h_792_, lean_object* v_fencedCode_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_791_, v_fencedCode_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_fencedCode_elim___boxed(lean_object* v_s_795_, lean_object* v_motive__1_796_, lean_object* v_t_797_, lean_object* v_h_798_, lean_object* v_fencedCode_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_Markdown_Block_Raw_fencedCode_elim(v_s_795_, v_motive__1_796_, v_t_797_, v_h_798_, v_fencedCode_799_);
lean_dec_ref(v_s_795_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_indentedCode_elim___redArg(lean_object* v_t_801_, lean_object* v_indentedCode_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_801_, v_indentedCode_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_indentedCode_elim(lean_object* v_s_804_, lean_object* v_motive__1_805_, lean_object* v_t_806_, lean_object* v_h_807_, lean_object* v_indentedCode_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_806_, v_indentedCode_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_indentedCode_elim___boxed(lean_object* v_s_810_, lean_object* v_motive__1_811_, lean_object* v_t_812_, lean_object* v_h_813_, lean_object* v_indentedCode_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Markdown_Block_Raw_indentedCode_elim(v_s_810_, v_motive__1_811_, v_t_812_, v_h_813_, v_indentedCode_814_);
lean_dec_ref(v_s_810_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_html_elim___redArg(lean_object* v_t_816_, lean_object* v_html_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_816_, v_html_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_html_elim(lean_object* v_s_819_, lean_object* v_motive__1_820_, lean_object* v_t_821_, lean_object* v_h_822_, lean_object* v_html_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_821_, v_html_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_html_elim___boxed(lean_object* v_s_825_, lean_object* v_motive__1_826_, lean_object* v_t_827_, lean_object* v_h_828_, lean_object* v_html_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Markdown_Block_Raw_html_elim(v_s_825_, v_motive__1_826_, v_t_827_, v_h_828_, v_html_829_);
lean_dec_ref(v_s_825_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_blockquote_elim___redArg(lean_object* v_t_831_, lean_object* v_blockquote_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_831_, v_blockquote_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_blockquote_elim(lean_object* v_s_834_, lean_object* v_motive__1_835_, lean_object* v_t_836_, lean_object* v_h_837_, lean_object* v_blockquote_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_836_, v_blockquote_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_blockquote_elim___boxed(lean_object* v_s_840_, lean_object* v_motive__1_841_, lean_object* v_t_842_, lean_object* v_h_843_, lean_object* v_blockquote_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Markdown_Block_Raw_blockquote_elim(v_s_840_, v_motive__1_841_, v_t_842_, v_h_843_, v_blockquote_844_);
lean_dec_ref(v_s_840_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_list_elim___redArg(lean_object* v_t_846_, lean_object* v_list_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_846_, v_list_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_list_elim(lean_object* v_s_849_, lean_object* v_motive__1_850_, lean_object* v_t_851_, lean_object* v_h_852_, lean_object* v_list_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_851_, v_list_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_list_elim___boxed(lean_object* v_s_855_, lean_object* v_motive__1_856_, lean_object* v_t_857_, lean_object* v_h_858_, lean_object* v_list_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Markdown_Block_Raw_list_elim(v_s_855_, v_motive__1_856_, v_t_857_, v_h_858_, v_list_859_);
lean_dec_ref(v_s_855_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_listItem_elim___redArg(lean_object* v_t_861_, lean_object* v_listItem_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_861_, v_listItem_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_listItem_elim(lean_object* v_s_864_, lean_object* v_motive__1_865_, lean_object* v_t_866_, lean_object* v_h_867_, lean_object* v_listItem_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_866_, v_listItem_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_listItem_elim___boxed(lean_object* v_s_870_, lean_object* v_motive__1_871_, lean_object* v_t_872_, lean_object* v_h_873_, lean_object* v_listItem_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Markdown_Block_Raw_listItem_elim(v_s_870_, v_motive__1_871_, v_t_872_, v_h_873_, v_listItem_874_);
lean_dec_ref(v_s_870_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_linkRefDef_elim___redArg(lean_object* v_t_876_, lean_object* v_linkRefDef_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_876_, v_linkRefDef_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_linkRefDef_elim(lean_object* v_s_879_, lean_object* v_motive__1_880_, lean_object* v_t_881_, lean_object* v_h_882_, lean_object* v_linkRefDef_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_881_, v_linkRefDef_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_linkRefDef_elim___boxed(lean_object* v_s_885_, lean_object* v_motive__1_886_, lean_object* v_t_887_, lean_object* v_h_888_, lean_object* v_linkRefDef_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Markdown_Block_Raw_linkRefDef_elim(v_s_885_, v_motive__1_886_, v_t_887_, v_h_888_, v_linkRefDef_889_);
lean_dec_ref(v_s_885_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_thematicBreak_elim___redArg(lean_object* v_t_891_, lean_object* v_thematicBreak_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_891_, v_thematicBreak_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_thematicBreak_elim(lean_object* v_s_894_, lean_object* v_motive__1_895_, lean_object* v_t_896_, lean_object* v_h_897_, lean_object* v_thematicBreak_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_Markdown_Block_Raw_ctorElim___redArg(v_t_896_, v_thematicBreak_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_Raw_thematicBreak_elim___boxed(lean_object* v_s_900_, lean_object* v_motive__1_901_, lean_object* v_t_902_, lean_object* v_h_903_, lean_object* v_thematicBreak_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_Markdown_Block_Raw_thematicBreak_elim(v_s_900_, v_motive__1_901_, v_t_902_, v_h_903_, v_thematicBreak_904_);
lean_dec_ref(v_s_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_instInhabitedRaw_default(lean_object* v_s_906_){
_start:
{
lean_object* v_startInclusive_907_; lean_object* v_endExclusive_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_startInclusive_907_ = lean_ctor_get(v_s_906_, 1);
v_endExclusive_908_ = lean_ctor_get(v_s_906_, 2);
v___x_909_ = lean_nat_sub(v_endExclusive_908_, v_startInclusive_907_);
lean_inc(v___x_909_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_910_);
v___x_912_ = l_Lean_Markdown_InlineSource_ofLines(v_s_906_, v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_instInhabitedRaw_default___boxed(lean_object* v_s_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Markdown_Block_instInhabitedRaw_default(v_s_914_);
lean_dec_ref(v_s_914_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_instInhabitedRaw(lean_object* v_a_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_Markdown_Block_instInhabitedRaw_default(v_a_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_instInhabitedRaw___boxed(lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Markdown_Block_instInhabitedRaw(v_a_918_);
lean_dec_ref(v_a_918_);
return v_res_919_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_ListKind_sameKind(lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
if (lean_obj_tag(v_x_921_) == 0)
{
uint8_t v_kind_922_; uint8_t v_kind_923_; uint8_t v___x_924_; 
v_kind_922_ = lean_ctor_get_uint8(v_x_920_, 0);
v_kind_923_ = lean_ctor_get_uint8(v_x_921_, 0);
v___x_924_ = l_Lean_Markdown_instBEqBulletKind_beq(v_kind_922_, v_kind_923_);
return v___x_924_;
}
else
{
uint8_t v___x_925_; 
v___x_925_ = 0;
return v___x_925_;
}
}
else
{
if (lean_obj_tag(v_x_921_) == 1)
{
uint8_t v_delim_926_; uint8_t v_delim_927_; uint8_t v___x_928_; 
v_delim_926_ = lean_ctor_get_uint8(v_x_920_, sizeof(void*)*1);
v_delim_927_ = lean_ctor_get_uint8(v_x_921_, sizeof(void*)*1);
v___x_928_ = l_Lean_Markdown_instBEqOrderedDelim_beq(v_delim_926_, v_delim_927_);
return v___x_928_;
}
else
{
uint8_t v___x_929_; 
v___x_929_ = 0;
return v___x_929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ListKind_sameKind___boxed(lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
uint8_t v_res_932_; lean_object* v_r_933_; 
v_res_932_ = l_Lean_Markdown_ListKind_sameKind(v_x_930_, v_x_931_);
lean_dec_ref(v_x_931_);
lean_dec_ref(v_x_930_);
v_r_933_ = lean_box(v_res_932_);
return v_r_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorIdx___impl___redArg(lean_object* v_x_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = lean_obj_tag_nat(v_x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorIdx___impl___redArg___boxed(lean_object* v_x_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Markdown_Block_ctorIdx___impl___redArg(v_x_936_);
lean_dec_ref(v_x_936_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorIdx___impl(lean_object* v_s_938_, lean_object* v_x_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = lean_obj_tag_nat(v_x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorIdx___impl___boxed(lean_object* v_s_941_, lean_object* v_x_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Markdown_Block_ctorIdx___impl(v_s_941_, v_x_942_);
lean_dec_ref(v_x_942_);
lean_dec_ref(v_s_941_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorElim___redArg(lean_object* v_t_944_, lean_object* v_k_945_){
_start:
{
switch(lean_obj_tag(v_t_944_))
{
case 1:
{
lean_object* v_level_946_; lean_object* v_hashes_947_; lean_object* v_content_948_; lean_object* v_closeHashes_x3f_949_; lean_object* v___x_950_; 
v_level_946_ = lean_ctor_get(v_t_944_, 0);
lean_inc(v_level_946_);
v_hashes_947_ = lean_ctor_get(v_t_944_, 1);
lean_inc_ref(v_hashes_947_);
v_content_948_ = lean_ctor_get(v_t_944_, 2);
lean_inc_ref(v_content_948_);
v_closeHashes_x3f_949_ = lean_ctor_get(v_t_944_, 3);
lean_inc(v_closeHashes_x3f_949_);
lean_dec_ref_known(v_t_944_, 4);
v___x_950_ = lean_apply_4(v_k_945_, v_level_946_, v_hashes_947_, v_content_948_, v_closeHashes_x3f_949_);
return v___x_950_;
}
case 2:
{
lean_object* v_level_951_; lean_object* v_content_952_; lean_object* v_underline_953_; lean_object* v___x_954_; 
v_level_951_ = lean_ctor_get(v_t_944_, 0);
lean_inc(v_level_951_);
v_content_952_ = lean_ctor_get(v_t_944_, 1);
lean_inc_ref(v_content_952_);
v_underline_953_ = lean_ctor_get(v_t_944_, 2);
lean_inc_ref(v_underline_953_);
lean_dec_ref_known(v_t_944_, 3);
v___x_954_ = lean_apply_3(v_k_945_, v_level_951_, v_content_952_, v_underline_953_);
return v___x_954_;
}
case 3:
{
lean_object* v_info_955_; lean_object* v_openFence_956_; lean_object* v_closeFence_x3f_957_; lean_object* v_lines_958_; lean_object* v___x_959_; 
v_info_955_ = lean_ctor_get(v_t_944_, 0);
lean_inc_ref(v_info_955_);
v_openFence_956_ = lean_ctor_get(v_t_944_, 1);
lean_inc_ref(v_openFence_956_);
v_closeFence_x3f_957_ = lean_ctor_get(v_t_944_, 2);
lean_inc(v_closeFence_x3f_957_);
v_lines_958_ = lean_ctor_get(v_t_944_, 3);
lean_inc_ref(v_lines_958_);
lean_dec_ref_known(v_t_944_, 4);
v___x_959_ = lean_apply_4(v_k_945_, v_info_955_, v_openFence_956_, v_closeFence_x3f_957_, v_lines_958_);
return v___x_959_;
}
case 6:
{
lean_object* v_markers_960_; lean_object* v_children_961_; lean_object* v___x_962_; 
v_markers_960_ = lean_ctor_get(v_t_944_, 0);
lean_inc_ref(v_markers_960_);
v_children_961_ = lean_ctor_get(v_t_944_, 1);
lean_inc_ref(v_children_961_);
lean_dec_ref_known(v_t_944_, 2);
v___x_962_ = lean_apply_2(v_k_945_, v_markers_960_, v_children_961_);
return v___x_962_;
}
case 7:
{
lean_object* v_kind_963_; uint8_t v_tight_964_; lean_object* v_items_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_kind_963_ = lean_ctor_get(v_t_944_, 0);
lean_inc_ref(v_kind_963_);
v_tight_964_ = lean_ctor_get_uint8(v_t_944_, sizeof(void*)*2);
v_items_965_ = lean_ctor_get(v_t_944_, 1);
lean_inc_ref(v_items_965_);
lean_dec_ref_known(v_t_944_, 2);
v___x_966_ = lean_box(v_tight_964_);
v___x_967_ = lean_apply_3(v_k_945_, v_kind_963_, v___x_966_, v_items_965_);
return v___x_967_;
}
case 8:
{
lean_object* v_marker_968_; lean_object* v_children_969_; lean_object* v___x_970_; 
v_marker_968_ = lean_ctor_get(v_t_944_, 0);
lean_inc_ref(v_marker_968_);
v_children_969_ = lean_ctor_get(v_t_944_, 1);
lean_inc_ref(v_children_969_);
lean_dec_ref_known(v_t_944_, 2);
v___x_970_ = lean_apply_2(v_k_945_, v_marker_968_, v_children_969_);
return v___x_970_;
}
default: 
{
lean_object* v_content_971_; lean_object* v___x_972_; 
v_content_971_ = lean_ctor_get(v_t_944_, 0);
lean_inc_ref(v_content_971_);
lean_dec_ref(v_t_944_);
v___x_972_ = lean_apply_1(v_k_945_, v_content_971_);
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorElim(lean_object* v_s_973_, lean_object* v_motive__1_974_, lean_object* v_ctorIdx_975_, lean_object* v_t_976_, lean_object* v_h_977_, lean_object* v_k_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_976_, v_k_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_ctorElim___boxed(lean_object* v_s_980_, lean_object* v_motive__1_981_, lean_object* v_ctorIdx_982_, lean_object* v_t_983_, lean_object* v_h_984_, lean_object* v_k_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Markdown_Block_ctorElim(v_s_980_, v_motive__1_981_, v_ctorIdx_982_, v_t_983_, v_h_984_, v_k_985_);
lean_dec(v_ctorIdx_982_);
lean_dec_ref(v_s_980_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_paragraph_elim___redArg(lean_object* v_t_987_, lean_object* v_paragraph_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_987_, v_paragraph_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_paragraph_elim(lean_object* v_s_990_, lean_object* v_motive__1_991_, lean_object* v_t_992_, lean_object* v_h_993_, lean_object* v_paragraph_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_992_, v_paragraph_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_paragraph_elim___boxed(lean_object* v_s_996_, lean_object* v_motive__1_997_, lean_object* v_t_998_, lean_object* v_h_999_, lean_object* v_paragraph_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Markdown_Block_paragraph_elim(v_s_996_, v_motive__1_997_, v_t_998_, v_h_999_, v_paragraph_1000_);
lean_dec_ref(v_s_996_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_atxHeading_elim___redArg(lean_object* v_t_1002_, lean_object* v_atxHeading_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1002_, v_atxHeading_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_atxHeading_elim(lean_object* v_s_1005_, lean_object* v_motive__1_1006_, lean_object* v_t_1007_, lean_object* v_h_1008_, lean_object* v_atxHeading_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1007_, v_atxHeading_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_atxHeading_elim___boxed(lean_object* v_s_1011_, lean_object* v_motive__1_1012_, lean_object* v_t_1013_, lean_object* v_h_1014_, lean_object* v_atxHeading_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Markdown_Block_atxHeading_elim(v_s_1011_, v_motive__1_1012_, v_t_1013_, v_h_1014_, v_atxHeading_1015_);
lean_dec_ref(v_s_1011_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_setextHeading_elim___redArg(lean_object* v_t_1017_, lean_object* v_setextHeading_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1017_, v_setextHeading_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_setextHeading_elim(lean_object* v_s_1020_, lean_object* v_motive__1_1021_, lean_object* v_t_1022_, lean_object* v_h_1023_, lean_object* v_setextHeading_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1022_, v_setextHeading_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_setextHeading_elim___boxed(lean_object* v_s_1026_, lean_object* v_motive__1_1027_, lean_object* v_t_1028_, lean_object* v_h_1029_, lean_object* v_setextHeading_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_Markdown_Block_setextHeading_elim(v_s_1026_, v_motive__1_1027_, v_t_1028_, v_h_1029_, v_setextHeading_1030_);
lean_dec_ref(v_s_1026_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_fencedCode_elim___redArg(lean_object* v_t_1032_, lean_object* v_fencedCode_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1032_, v_fencedCode_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_fencedCode_elim(lean_object* v_s_1035_, lean_object* v_motive__1_1036_, lean_object* v_t_1037_, lean_object* v_h_1038_, lean_object* v_fencedCode_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1037_, v_fencedCode_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_fencedCode_elim___boxed(lean_object* v_s_1041_, lean_object* v_motive__1_1042_, lean_object* v_t_1043_, lean_object* v_h_1044_, lean_object* v_fencedCode_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Markdown_Block_fencedCode_elim(v_s_1041_, v_motive__1_1042_, v_t_1043_, v_h_1044_, v_fencedCode_1045_);
lean_dec_ref(v_s_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_indentedCode_elim___redArg(lean_object* v_t_1047_, lean_object* v_indentedCode_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1047_, v_indentedCode_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_indentedCode_elim(lean_object* v_s_1050_, lean_object* v_motive__1_1051_, lean_object* v_t_1052_, lean_object* v_h_1053_, lean_object* v_indentedCode_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1052_, v_indentedCode_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_indentedCode_elim___boxed(lean_object* v_s_1056_, lean_object* v_motive__1_1057_, lean_object* v_t_1058_, lean_object* v_h_1059_, lean_object* v_indentedCode_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Markdown_Block_indentedCode_elim(v_s_1056_, v_motive__1_1057_, v_t_1058_, v_h_1059_, v_indentedCode_1060_);
lean_dec_ref(v_s_1056_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_html_elim___redArg(lean_object* v_t_1062_, lean_object* v_html_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1062_, v_html_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_html_elim(lean_object* v_s_1065_, lean_object* v_motive__1_1066_, lean_object* v_t_1067_, lean_object* v_h_1068_, lean_object* v_html_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1067_, v_html_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_html_elim___boxed(lean_object* v_s_1071_, lean_object* v_motive__1_1072_, lean_object* v_t_1073_, lean_object* v_h_1074_, lean_object* v_html_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Markdown_Block_html_elim(v_s_1071_, v_motive__1_1072_, v_t_1073_, v_h_1074_, v_html_1075_);
lean_dec_ref(v_s_1071_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_blockquote_elim___redArg(lean_object* v_t_1077_, lean_object* v_blockquote_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1077_, v_blockquote_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_blockquote_elim(lean_object* v_s_1080_, lean_object* v_motive__1_1081_, lean_object* v_t_1082_, lean_object* v_h_1083_, lean_object* v_blockquote_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1082_, v_blockquote_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_blockquote_elim___boxed(lean_object* v_s_1086_, lean_object* v_motive__1_1087_, lean_object* v_t_1088_, lean_object* v_h_1089_, lean_object* v_blockquote_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Markdown_Block_blockquote_elim(v_s_1086_, v_motive__1_1087_, v_t_1088_, v_h_1089_, v_blockquote_1090_);
lean_dec_ref(v_s_1086_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_list_elim___redArg(lean_object* v_t_1092_, lean_object* v_list_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1092_, v_list_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_list_elim(lean_object* v_s_1095_, lean_object* v_motive__1_1096_, lean_object* v_t_1097_, lean_object* v_h_1098_, lean_object* v_list_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1097_, v_list_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_list_elim___boxed(lean_object* v_s_1101_, lean_object* v_motive__1_1102_, lean_object* v_t_1103_, lean_object* v_h_1104_, lean_object* v_list_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_Markdown_Block_list_elim(v_s_1101_, v_motive__1_1102_, v_t_1103_, v_h_1104_, v_list_1105_);
lean_dec_ref(v_s_1101_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_listItem_elim___redArg(lean_object* v_t_1107_, lean_object* v_listItem_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1107_, v_listItem_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_listItem_elim(lean_object* v_s_1110_, lean_object* v_motive__1_1111_, lean_object* v_t_1112_, lean_object* v_h_1113_, lean_object* v_listItem_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1112_, v_listItem_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_listItem_elim___boxed(lean_object* v_s_1116_, lean_object* v_motive__1_1117_, lean_object* v_t_1118_, lean_object* v_h_1119_, lean_object* v_listItem_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_Markdown_Block_listItem_elim(v_s_1116_, v_motive__1_1117_, v_t_1118_, v_h_1119_, v_listItem_1120_);
lean_dec_ref(v_s_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_linkRefDef_elim___redArg(lean_object* v_t_1122_, lean_object* v_linkRefDef_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1122_, v_linkRefDef_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_linkRefDef_elim(lean_object* v_s_1125_, lean_object* v_motive__1_1126_, lean_object* v_t_1127_, lean_object* v_h_1128_, lean_object* v_linkRefDef_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1127_, v_linkRefDef_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_linkRefDef_elim___boxed(lean_object* v_s_1131_, lean_object* v_motive__1_1132_, lean_object* v_t_1133_, lean_object* v_h_1134_, lean_object* v_linkRefDef_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_Markdown_Block_linkRefDef_elim(v_s_1131_, v_motive__1_1132_, v_t_1133_, v_h_1134_, v_linkRefDef_1135_);
lean_dec_ref(v_s_1131_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_thematicBreak_elim___redArg(lean_object* v_t_1137_, lean_object* v_thematicBreak_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1137_, v_thematicBreak_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_thematicBreak_elim(lean_object* v_s_1140_, lean_object* v_motive__1_1141_, lean_object* v_t_1142_, lean_object* v_h_1143_, lean_object* v_thematicBreak_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_Markdown_Block_ctorElim___redArg(v_t_1142_, v_thematicBreak_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_thematicBreak_elim___boxed(lean_object* v_s_1146_, lean_object* v_motive__1_1147_, lean_object* v_t_1148_, lean_object* v_h_1149_, lean_object* v_thematicBreak_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_Markdown_Block_thematicBreak_elim(v_s_1146_, v_motive__1_1147_, v_t_1148_, v_h_1149_, v_thematicBreak_1150_);
lean_dec_ref(v_s_1146_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock_default___redArg(){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = ((lean_object*)(l_Lean_Markdown_instInhabitedBlock_default___redArg___closed__1));
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock_default___redArg___boxed(lean_object* v___dummy_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Markdown_instInhabitedBlock_default___redArg();
return v_res_1159_;
}
}
static lean_object* _init_l_Lean_Markdown_instInhabitedBlock_default___closed__0(void){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_Markdown_instInhabitedBlock_default___redArg();
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock_default(lean_object* v_s_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_obj_once(&l_Lean_Markdown_instInhabitedBlock_default___closed__0, &l_Lean_Markdown_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedBlock_default___closed__0);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock_default___boxed(lean_object* v_s_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Markdown_instInhabitedBlock_default(v_s_1163_);
lean_dec_ref(v_s_1163_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock___redArg(){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_obj_once(&l_Lean_Markdown_instInhabitedBlock_default___closed__0, &l_Lean_Markdown_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedBlock_default___closed__0);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock___redArg___boxed(lean_object* v___dummy_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Markdown_instInhabitedBlock___redArg();
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock(lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_obj_once(&l_Lean_Markdown_instInhabitedBlock_default___closed__0, &l_Lean_Markdown_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedBlock_default___closed__0);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlock___boxed(lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Markdown_instInhabitedBlock(v_a_1171_);
lean_dec_ref(v_a_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f___redArg(lean_object* v_rs_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = lean_array_get_size(v_rs_1173_);
v___x_1176_ = lean_nat_dec_lt(v___x_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_box(0);
return v___x_1177_;
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1178_ = lean_unsigned_to_nat(1u);
v___x_1179_ = lean_nat_sub(v___x_1175_, v___x_1178_);
v___x_1180_ = lean_nat_dec_lt(v___x_1179_, v___x_1175_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
lean_dec(v___x_1179_);
v___x_1181_ = lean_box(0);
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1182_ = lean_array_fget_borrowed(v_rs_1173_, v___x_1174_);
v___x_1183_ = lean_array_fget_borrowed(v_rs_1173_, v___x_1179_);
lean_dec(v___x_1179_);
lean_inc(v___x_1183_);
lean_inc(v___x_1182_);
v___x_1184_ = l_Lean_Markdown_span___redArg(v___x_1182_, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f___redArg___boxed(lean_object* v_rs_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f___redArg(v_rs_1186_);
lean_dec_ref(v_rs_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f(lean_object* v_s_1188_, lean_object* v_rs_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f___redArg(v_rs_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f___boxed(lean_object* v_s_1191_, lean_object* v_rs_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f(v_s_1191_, v_rs_1192_);
lean_dec_ref(v_rs_1192_);
lean_dec_ref(v_s_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_VerbatimLine_span_x3f___redArg(lean_object* v_lines_1194_){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1195_ = lean_unsigned_to_nat(0u);
v___x_1196_ = lean_array_get_size(v_lines_1194_);
v___x_1197_ = lean_nat_dec_lt(v___x_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_box(0);
return v___x_1198_;
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1199_ = lean_unsigned_to_nat(1u);
v___x_1200_ = lean_nat_sub(v___x_1196_, v___x_1199_);
v___x_1201_ = lean_nat_dec_lt(v___x_1200_, v___x_1196_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; 
lean_dec(v___x_1200_);
v___x_1202_ = lean_box(0);
return v___x_1202_;
}
else
{
lean_object* v___x_1203_; lean_object* v_source_1204_; lean_object* v___x_1205_; lean_object* v_source_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1203_ = lean_array_fget_borrowed(v_lines_1194_, v___x_1195_);
v_source_1204_ = lean_ctor_get(v___x_1203_, 0);
v___x_1205_ = lean_array_fget_borrowed(v_lines_1194_, v___x_1200_);
lean_dec(v___x_1200_);
v_source_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc_ref(v_source_1206_);
lean_inc_ref(v_source_1204_);
v___x_1207_ = l_Lean_Markdown_span___redArg(v_source_1204_, v_source_1206_);
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_VerbatimLine_span_x3f___redArg___boxed(lean_object* v_lines_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_VerbatimLine_span_x3f___redArg(v_lines_1209_);
lean_dec_ref(v_lines_1209_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_VerbatimLine_span_x3f(lean_object* v_s_1211_, lean_object* v_lines_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_VerbatimLine_span_x3f___redArg(v_lines_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_VerbatimLine_span_x3f___boxed(lean_object* v_s_1214_, lean_object* v_lines_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_VerbatimLine_span_x3f(v_s_1214_, v_lines_1215_);
lean_dec_ref(v_lines_1215_);
lean_dec_ref(v_s_1214_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0(lean_object* v_s_1219_, lean_object* v_as_1220_, lean_object* v_start_1221_, lean_object* v_stop_1222_){
_start:
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0___closed__0));
v___x_1224_ = lean_nat_dec_lt(v_start_1221_, v_stop_1222_);
if (v___x_1224_ == 0)
{
return v___x_1223_;
}
else
{
lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = lean_array_get_size(v_as_1220_);
v___x_1226_ = lean_nat_dec_le(v_stop_1222_, v___x_1225_);
if (v___x_1226_ == 0)
{
uint8_t v___x_1227_; 
v___x_1227_ = lean_nat_dec_lt(v_start_1221_, v___x_1225_);
if (v___x_1227_ == 0)
{
return v___x_1223_;
}
else
{
size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = lean_usize_of_nat(v_start_1221_);
v___x_1229_ = lean_usize_of_nat(v___x_1225_);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0_spec__0(v_s_1219_, v_as_1220_, v___x_1228_, v___x_1229_, v___x_1223_);
return v___x_1230_;
}
}
else
{
size_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = lean_usize_of_nat(v_start_1221_);
v___x_1232_ = lean_usize_of_nat(v_stop_1222_);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0_spec__0(v_s_1219_, v_as_1220_, v___x_1231_, v___x_1232_, v___x_1223_);
return v___x_1233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_extent_x3f(lean_object* v_s_1234_, lean_object* v_x_1235_){
_start:
{
lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1242_; lean_object* v___y_1243_; 
switch(lean_obj_tag(v_x_1235_))
{
case 0:
{
lean_object* v_content_1246_; lean_object* v___x_1247_; 
v_content_1246_ = lean_ctor_get(v_x_1235_, 0);
lean_inc_ref(v_content_1246_);
lean_dec_ref_known(v_x_1235_, 1);
v___x_1247_ = l_Lean_Markdown_Inline_extentOf_x3f___redArg(v_content_1246_);
lean_dec_ref(v_content_1246_);
return v___x_1247_;
}
case 1:
{
lean_object* v_hashes_1248_; lean_object* v_content_1249_; lean_object* v_closeHashes_x3f_1250_; lean_object* v___y_1252_; 
v_hashes_1248_ = lean_ctor_get(v_x_1235_, 1);
lean_inc_ref(v_hashes_1248_);
v_content_1249_ = lean_ctor_get(v_x_1235_, 2);
lean_inc_ref(v_content_1249_);
v_closeHashes_x3f_1250_ = lean_ctor_get(v_x_1235_, 3);
lean_inc(v_closeHashes_x3f_1250_);
lean_dec_ref_known(v_x_1235_, 4);
if (lean_obj_tag(v_closeHashes_x3f_1250_) == 0)
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_Markdown_Inline_extentOf_x3f___redArg(v_content_1249_);
lean_dec_ref(v_content_1249_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_box(0);
v___y_1252_ = v___x_1258_;
goto v___jp_1251_;
}
else
{
lean_object* v_val_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1267_; 
v_val_1259_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1261_ = v___x_1257_;
v_isShared_1262_ = v_isSharedCheck_1267_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_val_1259_);
lean_dec(v___x_1257_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1267_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v_endExclusive_1263_; lean_object* v___x_1265_; 
v_endExclusive_1263_ = lean_ctor_get(v_val_1259_, 1);
lean_inc(v_endExclusive_1263_);
lean_dec(v_val_1259_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v_endExclusive_1263_);
v___x_1265_ = v___x_1261_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_endExclusive_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
v___y_1252_ = v___x_1265_;
goto v___jp_1251_;
}
}
}
}
else
{
lean_object* v_val_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref(v_content_1249_);
v_val_1268_ = lean_ctor_get(v_closeHashes_x3f_1250_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_closeHashes_x3f_1250_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1270_ = v_closeHashes_x3f_1250_;
v_isShared_1271_ = v_isSharedCheck_1276_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_val_1268_);
lean_dec(v_closeHashes_x3f_1250_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1276_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v_endExclusive_1272_; lean_object* v___x_1274_; 
v_endExclusive_1272_ = lean_ctor_get(v_val_1268_, 1);
lean_inc(v_endExclusive_1272_);
lean_dec(v_val_1268_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v_endExclusive_1272_);
v___x_1274_ = v___x_1270_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_endExclusive_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
v___y_1252_ = v___x_1274_;
goto v___jp_1251_;
}
}
}
v___jp_1251_:
{
if (lean_obj_tag(v___y_1252_) == 0)
{
lean_object* v_startInclusive_1253_; lean_object* v_endExclusive_1254_; 
v_startInclusive_1253_ = lean_ctor_get(v_hashes_1248_, 0);
lean_inc(v_startInclusive_1253_);
v_endExclusive_1254_ = lean_ctor_get(v_hashes_1248_, 1);
lean_inc(v_endExclusive_1254_);
lean_dec_ref(v_hashes_1248_);
v___y_1237_ = v_startInclusive_1253_;
v___y_1238_ = v_endExclusive_1254_;
goto v___jp_1236_;
}
else
{
lean_object* v_startInclusive_1255_; lean_object* v_val_1256_; 
v_startInclusive_1255_ = lean_ctor_get(v_hashes_1248_, 0);
lean_inc(v_startInclusive_1255_);
lean_dec_ref(v_hashes_1248_);
v_val_1256_ = lean_ctor_get(v___y_1252_, 0);
lean_inc(v_val_1256_);
lean_dec_ref_known(v___y_1252_, 1);
v___y_1237_ = v_startInclusive_1255_;
v___y_1238_ = v_val_1256_;
goto v___jp_1236_;
}
}
}
case 2:
{
lean_object* v_content_1277_; lean_object* v_underline_1278_; lean_object* v___y_1280_; lean_object* v___x_1284_; 
v_content_1277_ = lean_ctor_get(v_x_1235_, 1);
lean_inc_ref(v_content_1277_);
v_underline_1278_ = lean_ctor_get(v_x_1235_, 2);
lean_inc_ref(v_underline_1278_);
lean_dec_ref_known(v_x_1235_, 3);
v___x_1284_ = l_Lean_Markdown_Inline_extentOf_x3f___redArg(v_content_1277_);
lean_dec_ref(v_content_1277_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_startInclusive_1285_; 
v_startInclusive_1285_ = lean_ctor_get(v_underline_1278_, 0);
lean_inc(v_startInclusive_1285_);
v___y_1280_ = v_startInclusive_1285_;
goto v___jp_1279_;
}
else
{
lean_object* v_val_1286_; lean_object* v_startInclusive_1287_; 
v_val_1286_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_val_1286_);
lean_dec_ref_known(v___x_1284_, 1);
v_startInclusive_1287_ = lean_ctor_get(v_val_1286_, 0);
lean_inc(v_startInclusive_1287_);
lean_dec(v_val_1286_);
v___y_1280_ = v_startInclusive_1287_;
goto v___jp_1279_;
}
v___jp_1279_:
{
lean_object* v_endExclusive_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_endExclusive_1281_ = lean_ctor_get(v_underline_1278_, 1);
lean_inc(v_endExclusive_1281_);
lean_dec_ref(v_underline_1278_);
v___x_1282_ = l_Lean_Markdown_subsliceClamped___redArg(v___y_1280_, v_endExclusive_1281_);
v___x_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
return v___x_1283_;
}
}
case 3:
{
lean_object* v_openFence_1288_; lean_object* v_closeFence_x3f_1289_; lean_object* v_lines_1290_; lean_object* v___y_1292_; 
v_openFence_1288_ = lean_ctor_get(v_x_1235_, 1);
lean_inc_ref(v_openFence_1288_);
v_closeFence_x3f_1289_ = lean_ctor_get(v_x_1235_, 2);
lean_inc(v_closeFence_x3f_1289_);
v_lines_1290_ = lean_ctor_get(v_x_1235_, 3);
lean_inc_ref(v_lines_1290_);
lean_dec_ref_known(v_x_1235_, 4);
if (lean_obj_tag(v_closeFence_x3f_1289_) == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1297_ = lean_array_get_size(v_lines_1290_);
v___x_1298_ = lean_unsigned_to_nat(1u);
v___x_1299_ = lean_nat_sub(v___x_1297_, v___x_1298_);
v___x_1300_ = lean_nat_dec_lt(v___x_1299_, v___x_1297_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; 
lean_dec(v___x_1299_);
lean_dec_ref(v_lines_1290_);
v___x_1301_ = lean_box(0);
v___y_1292_ = v___x_1301_;
goto v___jp_1291_;
}
else
{
lean_object* v___x_1302_; lean_object* v_source_1303_; lean_object* v_endExclusive_1304_; lean_object* v___x_1305_; 
v___x_1302_ = lean_array_fget(v_lines_1290_, v___x_1299_);
lean_dec(v___x_1299_);
lean_dec_ref(v_lines_1290_);
v_source_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc_ref(v_source_1303_);
lean_dec(v___x_1302_);
v_endExclusive_1304_ = lean_ctor_get(v_source_1303_, 1);
lean_inc(v_endExclusive_1304_);
lean_dec_ref(v_source_1303_);
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_endExclusive_1304_);
v___y_1292_ = v___x_1305_;
goto v___jp_1291_;
}
}
else
{
lean_object* v_val_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1314_; 
lean_dec_ref(v_lines_1290_);
v_val_1306_ = lean_ctor_get(v_closeFence_x3f_1289_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_closeFence_x3f_1289_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1308_ = v_closeFence_x3f_1289_;
v_isShared_1309_ = v_isSharedCheck_1314_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_val_1306_);
lean_dec(v_closeFence_x3f_1289_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1314_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v_endExclusive_1310_; lean_object* v___x_1312_; 
v_endExclusive_1310_ = lean_ctor_get(v_val_1306_, 1);
lean_inc(v_endExclusive_1310_);
lean_dec(v_val_1306_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v_endExclusive_1310_);
v___x_1312_ = v___x_1308_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_endExclusive_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
v___y_1292_ = v___x_1312_;
goto v___jp_1291_;
}
}
}
v___jp_1291_:
{
if (lean_obj_tag(v___y_1292_) == 0)
{
lean_object* v_startInclusive_1293_; lean_object* v_endExclusive_1294_; 
v_startInclusive_1293_ = lean_ctor_get(v_openFence_1288_, 0);
lean_inc(v_startInclusive_1293_);
v_endExclusive_1294_ = lean_ctor_get(v_openFence_1288_, 1);
lean_inc(v_endExclusive_1294_);
lean_dec_ref(v_openFence_1288_);
v___y_1242_ = v_startInclusive_1293_;
v___y_1243_ = v_endExclusive_1294_;
goto v___jp_1241_;
}
else
{
lean_object* v_startInclusive_1295_; lean_object* v_val_1296_; 
v_startInclusive_1295_ = lean_ctor_get(v_openFence_1288_, 0);
lean_inc(v_startInclusive_1295_);
lean_dec_ref(v_openFence_1288_);
v_val_1296_ = lean_ctor_get(v___y_1292_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v___y_1292_, 1);
v___y_1242_ = v_startInclusive_1295_;
v___y_1243_ = v_val_1296_;
goto v___jp_1241_;
}
}
}
case 6:
{
lean_object* v_markers_1315_; lean_object* v_children_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_markers_1315_ = lean_ctor_get(v_x_1235_, 0);
lean_inc_ref(v_markers_1315_);
v_children_1316_ = lean_ctor_get(v_x_1235_, 1);
lean_inc_ref(v_children_1316_);
lean_dec_ref_known(v_x_1235_, 2);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_array_get_size(v_markers_1315_);
v___x_1319_ = lean_nat_dec_lt(v___x_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
lean_dec_ref(v_children_1316_);
lean_dec_ref(v_markers_1315_);
v___x_1320_ = lean_box(0);
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1321_ = lean_unsigned_to_nat(1u);
v___x_1322_ = lean_nat_sub(v___x_1318_, v___x_1321_);
v___x_1323_ = lean_nat_dec_lt(v___x_1322_, v___x_1318_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec(v___x_1322_);
lean_dec_ref(v_children_1316_);
lean_dec_ref(v_markers_1315_);
v___x_1324_ = lean_box(0);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; lean_object* v___y_1327_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1325_ = lean_array_fget(v_markers_1315_, v___x_1317_);
v___x_1331_ = lean_array_fget(v_markers_1315_, v___x_1322_);
lean_dec(v___x_1322_);
lean_dec_ref(v_markers_1315_);
v___x_1332_ = lean_array_get_size(v_children_1316_);
v___x_1333_ = l_Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0(v_s_1234_, v_children_1316_, v___x_1317_, v___x_1332_);
lean_dec_ref(v_children_1316_);
v___x_1334_ = l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f___redArg(v___x_1333_);
lean_dec_ref(v___x_1333_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_endExclusive_1335_; 
v_endExclusive_1335_ = lean_ctor_get(v___x_1331_, 1);
lean_inc(v_endExclusive_1335_);
lean_dec(v___x_1331_);
v___y_1327_ = v_endExclusive_1335_;
goto v___jp_1326_;
}
else
{
lean_object* v_val_1336_; lean_object* v_endExclusive_1337_; lean_object* v_endExclusive_1338_; uint8_t v___x_1339_; 
v_val_1336_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_val_1336_);
lean_dec_ref_known(v___x_1334_, 1);
v_endExclusive_1337_ = lean_ctor_get(v___x_1331_, 1);
lean_inc(v_endExclusive_1337_);
lean_dec(v___x_1331_);
v_endExclusive_1338_ = lean_ctor_get(v_val_1336_, 1);
lean_inc(v_endExclusive_1338_);
lean_dec(v_val_1336_);
v___x_1339_ = lean_nat_dec_le(v_endExclusive_1338_, v_endExclusive_1337_);
if (v___x_1339_ == 0)
{
lean_dec(v_endExclusive_1337_);
v___y_1327_ = v_endExclusive_1338_;
goto v___jp_1326_;
}
else
{
lean_dec(v_endExclusive_1338_);
v___y_1327_ = v_endExclusive_1337_;
goto v___jp_1326_;
}
}
v___jp_1326_:
{
lean_object* v_startInclusive_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_startInclusive_1328_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_startInclusive_1328_);
lean_dec(v___x_1325_);
v___x_1329_ = l_Lean_Markdown_subsliceClamped___redArg(v_startInclusive_1328_, v___y_1327_);
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
}
}
}
case 7:
{
lean_object* v_items_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_items_1340_ = lean_ctor_get(v_x_1235_, 1);
lean_inc_ref(v_items_1340_);
lean_dec_ref_known(v_x_1235_, 2);
v___x_1341_ = lean_unsigned_to_nat(0u);
v___x_1342_ = lean_array_get_size(v_items_1340_);
v___x_1343_ = l_Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0(v_s_1234_, v_items_1340_, v___x_1341_, v___x_1342_);
lean_dec_ref(v_items_1340_);
v___x_1344_ = l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f___redArg(v___x_1343_);
lean_dec_ref(v___x_1343_);
return v___x_1344_;
}
case 8:
{
lean_object* v_marker_1345_; lean_object* v_children_1346_; lean_object* v___y_1348_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_marker_1345_ = lean_ctor_get(v_x_1235_, 0);
lean_inc_ref(v_marker_1345_);
v_children_1346_ = lean_ctor_get(v_x_1235_, 1);
lean_inc_ref(v_children_1346_);
lean_dec_ref_known(v_x_1235_, 2);
v___x_1352_ = lean_unsigned_to_nat(0u);
v___x_1353_ = lean_array_get_size(v_children_1346_);
v___x_1354_ = l_Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0(v_s_1234_, v_children_1346_, v___x_1352_, v___x_1353_);
lean_dec_ref(v_children_1346_);
v___x_1355_ = l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_span_x3f___redArg(v___x_1354_);
lean_dec_ref(v___x_1354_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_endExclusive_1356_; 
v_endExclusive_1356_ = lean_ctor_get(v_marker_1345_, 1);
lean_inc(v_endExclusive_1356_);
v___y_1348_ = v_endExclusive_1356_;
goto v___jp_1347_;
}
else
{
lean_object* v_val_1357_; lean_object* v_endExclusive_1358_; 
v_val_1357_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_val_1357_);
lean_dec_ref_known(v___x_1355_, 1);
v_endExclusive_1358_ = lean_ctor_get(v_val_1357_, 1);
lean_inc(v_endExclusive_1358_);
lean_dec(v_val_1357_);
v___y_1348_ = v_endExclusive_1358_;
goto v___jp_1347_;
}
v___jp_1347_:
{
lean_object* v_startInclusive_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_startInclusive_1349_ = lean_ctor_get(v_marker_1345_, 0);
lean_inc(v_startInclusive_1349_);
lean_dec_ref(v_marker_1345_);
v___x_1350_ = l_Lean_Markdown_subsliceClamped___redArg(v_startInclusive_1349_, v___y_1348_);
v___x_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
return v___x_1351_;
}
}
case 9:
{
lean_object* v_m_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1378_; 
v_m_1359_ = lean_ctor_get(v_x_1235_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_x_1235_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1361_ = v_x_1235_;
v_isShared_1362_ = v_isSharedCheck_1378_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_m_1359_);
lean_dec(v_x_1235_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1378_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v_openBracket_1363_; lean_object* v_destination_1364_; lean_object* v_title_x3f_1365_; lean_object* v___y_1367_; 
v_openBracket_1363_ = lean_ctor_get(v_m_1359_, 0);
lean_inc_ref(v_openBracket_1363_);
v_destination_1364_ = lean_ctor_get(v_m_1359_, 4);
lean_inc_ref(v_destination_1364_);
v_title_x3f_1365_ = lean_ctor_get(v_m_1359_, 5);
lean_inc(v_title_x3f_1365_);
lean_dec_ref(v_m_1359_);
if (lean_obj_tag(v_title_x3f_1365_) == 0)
{
lean_object* v___x_1373_; lean_object* v_endExclusive_1374_; 
v___x_1373_ = l_Lean_Markdown_LinkDestination_extent___redArg(v_destination_1364_);
v_endExclusive_1374_ = lean_ctor_get(v___x_1373_, 1);
lean_inc(v_endExclusive_1374_);
lean_dec_ref(v___x_1373_);
v___y_1367_ = v_endExclusive_1374_;
goto v___jp_1366_;
}
else
{
lean_object* v_val_1375_; lean_object* v_closer_1376_; lean_object* v_endExclusive_1377_; 
lean_dec_ref(v_destination_1364_);
v_val_1375_ = lean_ctor_get(v_title_x3f_1365_, 0);
lean_inc(v_val_1375_);
lean_dec_ref_known(v_title_x3f_1365_, 1);
v_closer_1376_ = lean_ctor_get(v_val_1375_, 2);
lean_inc_ref(v_closer_1376_);
lean_dec(v_val_1375_);
v_endExclusive_1377_ = lean_ctor_get(v_closer_1376_, 1);
lean_inc(v_endExclusive_1377_);
lean_dec_ref(v_closer_1376_);
v___y_1367_ = v_endExclusive_1377_;
goto v___jp_1366_;
}
v___jp_1366_:
{
lean_object* v_startInclusive_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v_startInclusive_1368_ = lean_ctor_get(v_openBracket_1363_, 0);
lean_inc(v_startInclusive_1368_);
lean_dec_ref(v_openBracket_1363_);
v___x_1369_ = l_Lean_Markdown_subsliceClamped___redArg(v_startInclusive_1368_, v___y_1367_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set_tag(v___x_1361_, 1);
lean_ctor_set(v___x_1361_, 0, v___x_1369_);
v___x_1371_ = v___x_1361_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
case 10:
{
lean_object* v_line_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
v_line_1379_ = lean_ctor_get(v_x_1235_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_x_1235_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v_x_1235_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_line_1379_);
lean_dec(v_x_1235_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set_tag(v___x_1381_, 1);
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_line_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
default: 
{
lean_object* v_lines_1387_; lean_object* v___x_1388_; 
v_lines_1387_ = lean_ctor_get(v_x_1235_, 0);
lean_inc_ref(v_lines_1387_);
lean_dec_ref(v_x_1235_);
v___x_1388_ = l___private_Lean_Data_Markdown_Block_0__Lean_Markdown_VerbatimLine_span_x3f___redArg(v_lines_1387_);
lean_dec_ref(v_lines_1387_);
return v___x_1388_;
}
}
v___jp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = l_Lean_Markdown_subsliceClamped___redArg(v___y_1237_, v___y_1238_);
v___x_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
v___jp_1241_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = l_Lean_Markdown_subsliceClamped___redArg(v___y_1242_, v___y_1243_);
v___x_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0_spec__0(lean_object* v_s_1389_, lean_object* v_as_1390_, size_t v_i_1391_, size_t v_stop_1392_, lean_object* v_b_1393_){
_start:
{
lean_object* v___y_1395_; uint8_t v___x_1399_; 
v___x_1399_ = lean_usize_dec_eq(v_i_1391_, v_stop_1392_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_array_uget_borrowed(v_as_1390_, v_i_1391_);
lean_inc(v___x_1400_);
v___x_1401_ = l_Lean_Markdown_Block_extent_x3f(v_s_1389_, v___x_1400_);
if (lean_obj_tag(v___x_1401_) == 0)
{
v___y_1395_ = v_b_1393_;
goto v___jp_1394_;
}
else
{
lean_object* v_val_1402_; lean_object* v___x_1403_; 
v_val_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_val_1402_);
lean_dec_ref_known(v___x_1401_, 1);
v___x_1403_ = lean_array_push(v_b_1393_, v_val_1402_);
v___y_1395_ = v___x_1403_;
goto v___jp_1394_;
}
}
else
{
return v_b_1393_;
}
v___jp_1394_:
{
size_t v___x_1396_; size_t v___x_1397_; 
v___x_1396_ = ((size_t)1ULL);
v___x_1397_ = lean_usize_add(v_i_1391_, v___x_1396_);
v_i_1391_ = v___x_1397_;
v_b_1393_ = v___y_1395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0_spec__0___boxed(lean_object* v_s_1404_, lean_object* v_as_1405_, lean_object* v_i_1406_, lean_object* v_stop_1407_, lean_object* v_b_1408_){
_start:
{
size_t v_i_boxed_1409_; size_t v_stop_boxed_1410_; lean_object* v_res_1411_; 
v_i_boxed_1409_ = lean_unbox_usize(v_i_1406_);
lean_dec(v_i_1406_);
v_stop_boxed_1410_ = lean_unbox_usize(v_stop_1407_);
lean_dec(v_stop_1407_);
v_res_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0_spec__0(v_s_1404_, v_as_1405_, v_i_boxed_1409_, v_stop_boxed_1410_, v_b_1408_);
lean_dec_ref(v_as_1405_);
lean_dec_ref(v_s_1404_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0___boxed(lean_object* v_s_1412_, lean_object* v_as_1413_, lean_object* v_start_1414_, lean_object* v_stop_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Array_filterMapM___at___00Lean_Markdown_Block_extent_x3f_spec__0(v_s_1412_, v_as_1413_, v_start_1414_, v_stop_1415_);
lean_dec(v_stop_1415_);
lean_dec(v_start_1414_);
lean_dec_ref(v_as_1413_);
lean_dec_ref(v_s_1412_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Block_extent_x3f___boxed(lean_object* v_s_1417_, lean_object* v_x_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_Markdown_Block_extent_x3f(v_s_1417_, v_x_1418_);
lean_dec_ref(v_s_1417_);
return v_res_1419_;
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Inline(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_InlineSource(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_Block(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_InlineSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Markdown_instInhabitedColumns_default = _init_l_Lean_Markdown_instInhabitedColumns_default();
lean_mark_persistent(l_Lean_Markdown_instInhabitedColumns_default);
l_Lean_Markdown_instInhabitedColumns = _init_l_Lean_Markdown_instInhabitedColumns();
lean_mark_persistent(l_Lean_Markdown_instInhabitedColumns);
l_Lean_Markdown_Columns_instLE = _init_l_Lean_Markdown_Columns_instLE();
lean_mark_persistent(l_Lean_Markdown_Columns_instLE);
l_Lean_Markdown_Columns_instLT = _init_l_Lean_Markdown_Columns_instLT();
lean_mark_persistent(l_Lean_Markdown_Columns_instLT);
l_Lean_Markdown_instInhabitedFenceChar_default = _init_l_Lean_Markdown_instInhabitedFenceChar_default();
l_Lean_Markdown_instInhabitedFenceChar = _init_l_Lean_Markdown_instInhabitedFenceChar();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_Block(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Inline(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_InlineSource(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_Block(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_InlineSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_Block(builtin);
}
#ifdef __cplusplus
}
#endif
