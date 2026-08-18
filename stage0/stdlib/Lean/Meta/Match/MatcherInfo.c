// Lean compiler output
// Module: Lean.Meta.Match.MatcherInfo
// Imports: public import Lean.Meta.Basic
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedDiscrInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedDiscrInfo;
static const lean_string_object l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hName\?"};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10;
static const lean_ctor_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Match_instReprDiscrInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_instReprDiscrInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instReprDiscrInfo = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedOverlaps_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedOverlaps;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3_spec__4___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3_spec__4_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3_spec__4(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__2_value;
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__3 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__3_value;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__3_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__4 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__4_value;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__5_value;
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__6 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__6_value;
static lean_once_cell_t l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__7;
static lean_once_cell_t l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__8;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__9 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__9_value;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__6_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__10 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg(lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.TreeSet.ofList "};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__2 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__2_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__3 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__3_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__4;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__5;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__6 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__6_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__3_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__7 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__2_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1___redArg(lean_object*);
static const lean_string_object l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "map"};
static const lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4;
static const lean_string_object l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.HashMap.ofList "};
static const lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Match_instReprOverlaps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_instReprOverlaps_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Match_instReprOverlaps___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instReprOverlaps = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Overlaps_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_isEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_insert___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Match_Overlaps_overlapping___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Match_Overlaps_overlapping___closed__0 = (const lean_object*)&l_Lean_Meta_Match_Overlaps_overlapping___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_overlapping(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_overlapping___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default = (const lean_object*)&l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo = (const lean_object*)&l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value;
static const lean_string_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numFields"};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4;
static const lean_string_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "numOverlaps"};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "hasUnitThunk"};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Match_instReprAltParamInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_instReprAltParamInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instReprAltParamInfo = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Match_instBEqAltParamInfo_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instBEqAltParamInfo_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Match_instBEqAltParamInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_instBEqAltParamInfo_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Match_instBEqAltParamInfo___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instBEqAltParamInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instBEqAltParamInfo = (const lean_object*)&l_Lean_Meta_Match_instBEqAltParamInfo___closed__0_value;
static const lean_array_object l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedMatcherInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedMatcherInfo;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(lean_object*);
static const lean_string_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numParams"};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numDiscrs"};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "altInfos"};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8;
static const lean_string_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "uElimPos\?"};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10_value;
static const lean_string_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "discrInfos"};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13;
static const lean_string_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "overlaps"};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Match_instReprMatcherInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_instReprMatcherInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instReprMatcherInfo = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_arity___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getDiscrRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getDiscrRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getAltRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getAltRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getNumEqsFromDiscrInfos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getNumEqsFromDiscrInfos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_altNumParams(lean_object*);
static lean_once_cell_t l_Lean_Meta_Match_Extension_instInhabitedState___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Extension_instInhabitedState___closed__0;
static lean_once_cell_t l_Lean_Meta_Match_Extension_instInhabitedState___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Extension_instInhabitedState___closed__1;
static lean_once_cell_t l_Lean_Meta_Match_Extension_instInhabitedState___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Extension_instInhabitedState___closed__2;
static lean_once_cell_t l_Lean_Meta_Match_Extension_instInhabitedState___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Extension_instInhabitedState___closed__3;
static lean_once_cell_t l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Extension_instInhabitedState___closed__4;
static lean_once_cell_t l_Lean_Meta_Match_Extension_instInhabitedState___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Extension_instInhabitedState___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_instInhabitedState;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_State_addEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_State_switch(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Match"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Extension"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "extension"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 134, 186, 123, 61, 240, 95, 75)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 199, 90, 164, 66, 112, 193, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 71, 76, 183, 128, 212, 252, 252)}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_Extension_State_addEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_extension;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_addMatcherInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "match_"};
static const lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfoCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "matcherLikeExt"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 239, 16, 207, 7, 86, 101, 26)}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matcherLikeExt;
LEAN_EXPORT lean_object* l_Lean_Meta_markMatcherLike(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherLikeCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLikeCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Match_instInhabitedDiscrInfo_default(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedDiscrInfo(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
lean_object* v___x_11_; 
v___x_11_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1));
return v___x_11_;
}
else
{
lean_object* v_val_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_val_12_ = lean_ctor_get(v_x_9_, 0);
lean_inc(v_val_12_);
lean_dec_ref_known(v_x_9_, 1);
v___x_13_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3));
v___x_14_ = lean_unsigned_to_nat(1024u);
v___x_15_ = l_Lean_Name_reprPrec(v_val_12_, v___x_14_);
v___x_16_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_13_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
v___x_17_ = l_Repr_addAppParen(v___x_16_, v_x_10_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___boxed(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(v_x_18_, v_x_19_);
lean_dec(v_x_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__1(lean_object* v_a_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_nat_to_int(v_a_21_);
return v___x_22_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(10u);
v___x_37_ = lean_nat_to_int(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0));
v___x_40_ = lean_string_length(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(lean_object* v_x_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_48_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6));
v___x_49_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7);
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(v_x_47_, v___x_50_);
v___x_52_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_49_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = 0;
v___x_54_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set_uint8(v___x_54_, sizeof(void*)*1, v___x_53_);
v___x_55_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_48_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_57_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_58_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v___x_55_);
v___x_59_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_60_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_56_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*1, v___x_53_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr(lean_object* v_x_63_, lean_object* v_prec_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_x_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___boxed(lean_object* v_x_66_, lean_object* v_prec_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Meta_Match_instReprDiscrInfo_repr(v_x_66_, v_prec_67_);
lean_dec(v_prec_67_);
return v_res_68_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0(void){
_start:
{
lean_object* v_cellCount_71_; lean_object* v___x_72_; 
v_cellCount_71_ = lean_unsigned_to_nat(16u);
v___x_72_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1(void){
_start:
{
lean_object* v_cellCount_73_; lean_object* v___x_74_; 
v_cellCount_73_ = lean_unsigned_to_nat(16u);
v___x_74_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__2(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1, &l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1);
v___x_76_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0, &l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0_once, _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_76_);
lean_ctor_set(v___x_78_, 2, v___x_75_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedOverlaps_default(void){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__2, &l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__2_once, _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__2);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedOverlaps(void){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Meta_Match_instInhabitedOverlaps_default;
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(lean_object* v_b_81_, lean_object* v_acc_82_, lean_object* v_i_83_){
_start:
{
lean_object* v_keyArray_88_; lean_object* v_valueArray_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v_keyArray_88_ = lean_ctor_get(v_b_81_, 1);
v_valueArray_89_ = lean_ctor_get(v_b_81_, 2);
v___x_90_ = lean_array_get_size(v_keyArray_88_);
v___x_91_ = lean_nat_dec_lt(v_i_83_, v___x_90_);
if (v___x_91_ == 0)
{
lean_dec(v_i_83_);
lean_inc(v_acc_82_);
return v_acc_82_;
}
else
{
lean_object* v___x_92_; uint8_t v_isSome_93_; 
v___x_92_ = lean_array_fget_borrowed(v_keyArray_88_, v_i_83_);
v_isSome_93_ = lean_noption_is_some(v___x_92_);
if (v_isSome_93_ == 0)
{
goto v___jp_84_;
}
else
{
lean_object* v___x_94_; uint8_t v_isSome_95_; 
v___x_94_ = lean_array_fget_borrowed(v_valueArray_89_, v_i_83_);
v_isSome_95_ = lean_noption_is_some(v___x_94_);
if (v_isSome_95_ == 0)
{
goto v___jp_84_;
}
else
{
lean_object* v_val_96_; lean_object* v_val_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_inc(v___x_92_);
v_val_96_ = lean_noption_get(v___x_92_);
lean_inc(v___x_94_);
v_val_97_ = lean_noption_get(v___x_94_);
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = lean_nat_add(v_i_83_, v___x_98_);
lean_dec(v_i_83_);
v___x_100_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(v_b_81_, v_acc_82_, v___x_99_);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v_val_96_);
lean_ctor_set(v___x_101_, 1, v_val_97_);
v___x_102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
return v___x_102_;
}
}
}
v___jp_84_:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v_i_83_, v___x_85_);
lean_dec(v_i_83_);
v_i_83_ = v___x_86_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___boxed(lean_object* v_b_103_, lean_object* v_acc_104_, lean_object* v_i_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(v_b_103_, v_acc_104_, v_i_105_);
lean_dec(v_acc_104_);
lean_dec_ref(v_b_103_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__4_spec__6(lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
lean_dec(v_x_107_);
return v_x_108_;
}
else
{
lean_object* v_head_110_; lean_object* v_tail_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_120_; 
v_head_110_ = lean_ctor_get(v_x_109_, 0);
v_tail_111_ = lean_ctor_get(v_x_109_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_109_);
if (v_isSharedCheck_120_ == 0)
{
v___x_113_ = v_x_109_;
v_isShared_114_ = v_isSharedCheck_120_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_tail_111_);
lean_inc(v_head_110_);
lean_dec(v_x_109_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_120_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
lean_inc(v_x_107_);
if (v_isShared_114_ == 0)
{
lean_ctor_set_tag(v___x_113_, 5);
lean_ctor_set(v___x_113_, 1, v_x_107_);
lean_ctor_set(v___x_113_, 0, v_x_108_);
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_x_108_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_x_107_);
v___x_116_ = v_reuseFailAlloc_119_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; 
v___x_117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_head_110_);
v_x_108_ = v___x_117_;
v_x_109_ = v_tail_111_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__4(lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
lean_object* v___x_123_; 
lean_dec(v_x_122_);
v___x_123_ = lean_box(0);
return v___x_123_;
}
else
{
lean_object* v_tail_124_; 
v_tail_124_ = lean_ctor_get(v_x_121_, 1);
if (lean_obj_tag(v_tail_124_) == 0)
{
lean_object* v_head_125_; 
lean_dec(v_x_122_);
v_head_125_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_head_125_);
lean_dec_ref_known(v_x_121_, 2);
return v_head_125_;
}
else
{
lean_object* v_head_126_; lean_object* v___x_127_; 
lean_inc(v_tail_124_);
v_head_126_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_head_126_);
lean_dec_ref_known(v_x_121_, 2);
v___x_127_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__4_spec__6(v_x_122_, v_head_126_, v_tail_124_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__2(lean_object* v_init_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
lean_object* v_k_130_; lean_object* v_l_131_; lean_object* v_r_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_k_130_ = lean_ctor_get(v_x_129_, 1);
v_l_131_ = lean_ctor_get(v_x_129_, 3);
v_r_132_ = lean_ctor_get(v_x_129_, 4);
v___x_133_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__2(v_init_128_, v_r_132_);
lean_inc(v_k_130_);
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v_k_130_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v_init_128_ = v___x_134_;
v_x_129_ = v_l_131_;
goto _start;
}
else
{
return v_init_128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__2___boxed(lean_object* v_init_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__2(v_init_136_, v_x_137_);
lean_dec(v_x_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3_spec__4___lam__0(lean_object* v___y_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = l_Nat_reprFast(v___y_139_);
v___x_141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3_spec__4_spec__6_spec__9(lean_object* v_x_142_, lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
lean_dec(v_x_142_);
return v_x_143_;
}
else
{
lean_object* v_head_145_; lean_object* v_tail_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_157_; 
v_head_145_ = lean_ctor_get(v_x_144_, 0);
v_tail_146_ = lean_ctor_get(v_x_144_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_144_);
if (v_isSharedCheck_157_ == 0)
{
v___x_148_ = v_x_144_;
v_isShared_149_ = v_isSharedCheck_157_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_tail_146_);
lean_inc(v_head_145_);
lean_dec(v_x_144_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_157_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
lean_inc(v_x_142_);
if (v_isShared_149_ == 0)
{
lean_ctor_set_tag(v___x_148_, 5);
lean_ctor_set(v___x_148_, 1, v_x_142_);
lean_ctor_set(v___x_148_, 0, v_x_143_);
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_x_143_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_x_142_);
v___x_151_ = v_reuseFailAlloc_156_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = l_Nat_reprFast(v_head_145_);
v___x_153_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
v___x_154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_151_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v_x_143_ = v___x_154_;
v_x_144_ = v_tail_146_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3_spec__4_spec__6(lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
if (lean_obj_tag(v_x_160_) == 0)
{
lean_dec(v_x_158_);
return v_x_159_;
}
else
{
lean_object* v_head_161_; lean_object* v_tail_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_173_; 
v_head_161_ = lean_ctor_get(v_x_160_, 0);
v_tail_162_ = lean_ctor_get(v_x_160_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v_x_160_);
if (v_isSharedCheck_173_ == 0)
{
v___x_164_ = v_x_160_;
v_isShared_165_ = v_isSharedCheck_173_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_tail_162_);
lean_inc(v_head_161_);
lean_dec(v_x_160_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_173_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
lean_inc(v_x_158_);
if (v_isShared_165_ == 0)
{
lean_ctor_set_tag(v___x_164_, 5);
lean_ctor_set(v___x_164_, 1, v_x_158_);
lean_ctor_set(v___x_164_, 0, v_x_159_);
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_x_159_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_x_158_);
v___x_167_ = v_reuseFailAlloc_172_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = l_Nat_reprFast(v_head_161_);
v___x_169_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_167_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3_spec__4_spec__6_spec__9(v_x_158_, v___x_170_, v_tail_162_);
return v___x_171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3_spec__4(lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_object* v___x_176_; 
lean_dec(v_x_175_);
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v_tail_177_; 
v_tail_177_ = lean_ctor_get(v_x_174_, 1);
if (lean_obj_tag(v_tail_177_) == 0)
{
lean_object* v_head_178_; lean_object* v___x_179_; 
lean_dec(v_x_175_);
v_head_178_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_head_178_);
lean_dec_ref_known(v_x_174_, 2);
v___x_179_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3_spec__4___lam__0(v_head_178_);
return v___x_179_;
}
else
{
lean_object* v_head_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_inc(v_tail_177_);
v_head_180_ = lean_ctor_get(v_x_174_, 0);
lean_inc(v_head_180_);
lean_dec_ref_known(v_x_174_, 2);
v___x_181_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3_spec__4___lam__0(v_head_180_);
v___x_182_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3_spec__4_spec__6(v_x_175_, v___x_181_, v_tail_177_);
return v___x_182_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__7(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__2));
v___x_195_ = lean_string_length(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__7, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__7_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__7);
v___x_197_ = lean_nat_to_int(v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg(lean_object* v_a_202_){
_start:
{
if (lean_obj_tag(v_a_202_) == 0)
{
lean_object* v___x_203_; 
v___x_203_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__1));
return v___x_203_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; lean_object* v___x_213_; 
v___x_204_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__5));
v___x_205_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3_spec__4(v_a_202_, v___x_204_);
v___x_206_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__8, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__8_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__8);
v___x_207_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__9));
v___x_208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_205_);
v___x_209_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__10));
v___x_210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_206_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = 0;
v___x_213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*1, v___x_212_);
return v___x_213_;
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__0));
v___x_220_ = lean_string_length(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__4, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__4_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__4);
v___x_222_ = lean_nat_to_int(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg(lean_object* v_x_227_){
_start:
{
lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_257_; 
v_fst_228_ = lean_ctor_get(v_x_227_, 0);
v_snd_229_ = lean_ctor_get(v_x_227_, 1);
v_isSharedCheck_257_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_257_ == 0)
{
v___x_231_ = v_x_227_;
v_isShared_232_ = v_isSharedCheck_257_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_snd_229_);
lean_inc(v_fst_228_);
lean_dec(v_x_227_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_257_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_233_ = l_Nat_reprFast(v_fst_228_);
v___x_234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___x_235_ = lean_box(0);
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 1);
lean_ctor_set(v___x_231_, 1, v___x_235_);
lean_ctor_set(v___x_231_, 0, v___x_234_);
v___x_237_ = v___x_231_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v___x_235_);
v___x_237_ = v_reuseFailAlloc_256_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; 
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__2));
v___x_240_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__2(v___x_235_, v_snd_229_);
lean_dec(v_snd_229_);
v___x_241_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg(v___x_240_);
v___x_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_239_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = l_Repr_addAppParen(v___x_242_, v___x_238_);
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_237_);
v___x_245_ = l_List_reverse___redArg(v___x_244_);
v___x_246_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__5));
v___x_247_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__4(v___x_245_, v___x_246_);
v___x_248_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__5, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__5_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__5);
v___x_249_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__6));
v___x_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_247_);
v___x_251_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg___closed__7));
v___x_252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_248_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = 0;
v___x_255_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*1, v___x_254_);
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__2_spec__6_spec__9(lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_dec(v_x_258_);
return v_x_259_;
}
else
{
lean_object* v_head_261_; lean_object* v_tail_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_272_; 
v_head_261_ = lean_ctor_get(v_x_260_, 0);
v_tail_262_ = lean_ctor_get(v_x_260_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_272_ == 0)
{
v___x_264_ = v_x_260_;
v_isShared_265_ = v_isSharedCheck_272_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_tail_262_);
lean_inc(v_head_261_);
lean_dec(v_x_260_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_272_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
lean_inc(v_x_258_);
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 5);
lean_ctor_set(v___x_264_, 1, v_x_258_);
lean_ctor_set(v___x_264_, 0, v_x_259_);
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_x_259_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_x_258_);
v___x_267_ = v_reuseFailAlloc_271_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg(v_head_261_);
v___x_269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v_x_259_ = v___x_269_;
v_x_260_ = v_tail_262_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__2_spec__6(lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
lean_dec(v_x_273_);
return v_x_274_;
}
else
{
lean_object* v_head_276_; lean_object* v_tail_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_287_; 
v_head_276_ = lean_ctor_get(v_x_275_, 0);
v_tail_277_ = lean_ctor_get(v_x_275_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_287_ == 0)
{
v___x_279_ = v_x_275_;
v_isShared_280_ = v_isSharedCheck_287_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_tail_277_);
lean_inc(v_head_276_);
lean_dec(v_x_275_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_287_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
lean_inc(v_x_273_);
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 5);
lean_ctor_set(v___x_279_, 1, v_x_273_);
lean_ctor_set(v___x_279_, 0, v_x_274_);
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_x_274_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_x_273_);
v___x_282_ = v_reuseFailAlloc_286_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg(v_head_276_);
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__2_spec__6_spec__9(v_x_273_, v___x_284_, v_tail_277_);
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__2(lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
if (lean_obj_tag(v_x_288_) == 0)
{
lean_object* v___x_290_; 
lean_dec(v_x_289_);
v___x_290_ = lean_box(0);
return v___x_290_;
}
else
{
lean_object* v_tail_291_; 
v_tail_291_ = lean_ctor_get(v_x_288_, 1);
if (lean_obj_tag(v_tail_291_) == 0)
{
lean_object* v_head_292_; lean_object* v___x_293_; 
lean_dec(v_x_289_);
v_head_292_ = lean_ctor_get(v_x_288_, 0);
lean_inc(v_head_292_);
lean_dec_ref_known(v_x_288_, 2);
v___x_293_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg(v_head_292_);
return v___x_293_;
}
else
{
lean_object* v_head_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
lean_inc(v_tail_291_);
v_head_294_ = lean_ctor_get(v_x_288_, 0);
lean_inc(v_head_294_);
lean_dec_ref_known(v_x_288_, 2);
v___x_295_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg(v_head_294_);
v___x_296_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__2_spec__6(v_x_289_, v___x_295_, v_tail_291_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1___redArg(lean_object* v_a_297_){
_start:
{
if (lean_obj_tag(v_a_297_) == 0)
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__1));
return v___x_298_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; lean_object* v___x_308_; 
v___x_299_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__5));
v___x_300_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__2(v_a_297_, v___x_299_);
v___x_301_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__8, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__8_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__8);
v___x_302_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__9));
v___x_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_300_);
v___x_304_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__10));
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_301_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = 0;
v___x_308_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*1, v___x_307_);
return v___x_308_;
}
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(7u);
v___x_319_ = lean_nat_to_int(v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg(lean_object* v_x_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_324_ = ((lean_object*)(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3));
v___x_325_ = lean_obj_once(&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4, &l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4_once, _init_l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4);
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = ((lean_object*)(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6));
v___x_328_ = lean_box(0);
v___x_329_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(v_x_323_, v___x_328_, v___x_326_);
v___x_330_ = l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1___redArg(v___x_329_);
v___x_331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_327_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = l_Repr_addAppParen(v___x_331_, v___x_326_);
v___x_333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_325_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = 0;
v___x_335_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*1, v___x_334_);
v___x_336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_324_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_338_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_336_);
v___x_340_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_337_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*1, v___x_334_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___boxed(lean_object* v_x_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg(v_x_344_);
lean_dec_ref(v_x_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr(lean_object* v_x_346_, lean_object* v_prec_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg(v_x_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___boxed(lean_object* v_x_349_, lean_object* v_prec_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Meta_Match_instReprOverlaps_repr(v_x_349_, v_prec_350_);
lean_dec(v_prec_350_);
lean_dec_ref(v_x_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(lean_object* v_a_352_, lean_object* v_n_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1___redArg(v_a_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1___boxed(lean_object* v_a_355_, lean_object* v_n_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(v_a_355_, v_n_356_);
lean_dec(v_n_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1(lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___redArg(v_x_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1___boxed(lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1(v_x_361_, v_x_362_);
lean_dec(v_x_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3(lean_object* v_a_364_, lean_object* v_n_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg(v_a_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___boxed(lean_object* v_a_367_, lean_object* v_n_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3(v_a_367_, v_n_368_);
lean_dec(v_n_368_);
return v_res_369_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Overlaps_isEmpty(lean_object* v_o_372_){
_start:
{
lean_object* v_size_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_size_373_ = lean_ctor_get(v_o_372_, 0);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_nat_dec_eq(v_size_373_, v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_isEmpty___boxed(lean_object* v_o_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_o_376_);
lean_dec_ref(v_o_376_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(lean_object* v_k_379_, lean_object* v_t_380_){
_start:
{
if (lean_obj_tag(v_t_380_) == 0)
{
lean_object* v_k_381_; lean_object* v_l_382_; lean_object* v_r_383_; uint8_t v___x_384_; 
v_k_381_ = lean_ctor_get(v_t_380_, 1);
v_l_382_ = lean_ctor_get(v_t_380_, 3);
v_r_383_ = lean_ctor_get(v_t_380_, 4);
v___x_384_ = lean_nat_dec_lt(v_k_379_, v_k_381_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; 
v___x_385_ = lean_nat_dec_eq(v_k_379_, v_k_381_);
if (v___x_385_ == 0)
{
v_t_380_ = v_r_383_;
goto _start;
}
else
{
return v___x_385_;
}
}
else
{
v_t_380_ = v_l_382_;
goto _start;
}
}
else
{
uint8_t v___x_388_; 
v___x_388_ = 0;
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg___boxed(lean_object* v_k_389_, lean_object* v_t_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_k_389_, v_t_390_);
lean_dec(v_t_390_);
lean_dec(v_k_389_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(lean_object* v_k_393_, lean_object* v_v_394_, lean_object* v_t_395_){
_start:
{
if (lean_obj_tag(v_t_395_) == 0)
{
lean_object* v_size_396_; lean_object* v_k_397_; lean_object* v_v_398_; lean_object* v_l_399_; lean_object* v_r_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_681_; 
v_size_396_ = lean_ctor_get(v_t_395_, 0);
v_k_397_ = lean_ctor_get(v_t_395_, 1);
v_v_398_ = lean_ctor_get(v_t_395_, 2);
v_l_399_ = lean_ctor_get(v_t_395_, 3);
v_r_400_ = lean_ctor_get(v_t_395_, 4);
v_isSharedCheck_681_ = !lean_is_exclusive(v_t_395_);
if (v_isSharedCheck_681_ == 0)
{
v___x_402_ = v_t_395_;
v_isShared_403_ = v_isSharedCheck_681_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_r_400_);
lean_inc(v_l_399_);
lean_inc(v_v_398_);
lean_inc(v_k_397_);
lean_inc(v_size_396_);
lean_dec(v_t_395_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_681_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
uint8_t v___x_404_; 
v___x_404_ = lean_nat_dec_lt(v_k_393_, v_k_397_);
if (v___x_404_ == 0)
{
uint8_t v___x_405_; 
v___x_405_ = lean_nat_dec_eq(v_k_393_, v_k_397_);
if (v___x_405_ == 0)
{
lean_object* v_impl_406_; lean_object* v___x_407_; 
lean_dec(v_size_396_);
v_impl_406_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_393_, v_v_394_, v_r_400_);
v___x_407_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_399_) == 0)
{
lean_object* v_size_408_; lean_object* v_size_409_; lean_object* v_k_410_; lean_object* v_v_411_; lean_object* v_l_412_; lean_object* v_r_413_; lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_size_408_ = lean_ctor_get(v_l_399_, 0);
v_size_409_ = lean_ctor_get(v_impl_406_, 0);
lean_inc(v_size_409_);
v_k_410_ = lean_ctor_get(v_impl_406_, 1);
lean_inc(v_k_410_);
v_v_411_ = lean_ctor_get(v_impl_406_, 2);
lean_inc(v_v_411_);
v_l_412_ = lean_ctor_get(v_impl_406_, 3);
lean_inc(v_l_412_);
v_r_413_ = lean_ctor_get(v_impl_406_, 4);
lean_inc(v_r_413_);
v___x_414_ = lean_unsigned_to_nat(3u);
v___x_415_ = lean_nat_mul(v___x_414_, v_size_408_);
v___x_416_ = lean_nat_dec_lt(v___x_415_, v_size_409_);
lean_dec(v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
lean_dec(v_r_413_);
lean_dec(v_l_412_);
lean_dec(v_v_411_);
lean_dec(v_k_410_);
v___x_417_ = lean_nat_add(v___x_407_, v_size_408_);
v___x_418_ = lean_nat_add(v___x_417_, v_size_409_);
lean_dec(v_size_409_);
lean_dec(v___x_417_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 4, v_impl_406_);
lean_ctor_set(v___x_402_, 0, v___x_418_);
v___x_420_ = v___x_402_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_k_397_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v_v_398_);
lean_ctor_set(v_reuseFailAlloc_421_, 3, v_l_399_);
lean_ctor_set(v_reuseFailAlloc_421_, 4, v_impl_406_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
else
{
lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_485_; 
v_isSharedCheck_485_ = !lean_is_exclusive(v_impl_406_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; lean_object* v_unused_487_; lean_object* v_unused_488_; lean_object* v_unused_489_; lean_object* v_unused_490_; 
v_unused_486_ = lean_ctor_get(v_impl_406_, 4);
lean_dec(v_unused_486_);
v_unused_487_ = lean_ctor_get(v_impl_406_, 3);
lean_dec(v_unused_487_);
v_unused_488_ = lean_ctor_get(v_impl_406_, 2);
lean_dec(v_unused_488_);
v_unused_489_ = lean_ctor_get(v_impl_406_, 1);
lean_dec(v_unused_489_);
v_unused_490_ = lean_ctor_get(v_impl_406_, 0);
lean_dec(v_unused_490_);
v___x_423_ = v_impl_406_;
v_isShared_424_ = v_isSharedCheck_485_;
goto v_resetjp_422_;
}
else
{
lean_dec(v_impl_406_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_485_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_size_425_; lean_object* v_k_426_; lean_object* v_v_427_; lean_object* v_l_428_; lean_object* v_r_429_; lean_object* v_size_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_size_425_ = lean_ctor_get(v_l_412_, 0);
v_k_426_ = lean_ctor_get(v_l_412_, 1);
v_v_427_ = lean_ctor_get(v_l_412_, 2);
v_l_428_ = lean_ctor_get(v_l_412_, 3);
v_r_429_ = lean_ctor_get(v_l_412_, 4);
v_size_430_ = lean_ctor_get(v_r_413_, 0);
v___x_431_ = lean_unsigned_to_nat(2u);
v___x_432_ = lean_nat_mul(v___x_431_, v_size_430_);
v___x_433_ = lean_nat_dec_lt(v_size_425_, v___x_432_);
lean_dec(v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_461_; 
lean_inc(v_r_429_);
lean_inc(v_l_428_);
lean_inc(v_v_427_);
lean_inc(v_k_426_);
v_isSharedCheck_461_ = !lean_is_exclusive(v_l_412_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; lean_object* v_unused_463_; lean_object* v_unused_464_; lean_object* v_unused_465_; lean_object* v_unused_466_; 
v_unused_462_ = lean_ctor_get(v_l_412_, 4);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v_l_412_, 3);
lean_dec(v_unused_463_);
v_unused_464_ = lean_ctor_get(v_l_412_, 2);
lean_dec(v_unused_464_);
v_unused_465_ = lean_ctor_get(v_l_412_, 1);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_l_412_, 0);
lean_dec(v_unused_466_);
v___x_435_ = v_l_412_;
v_isShared_436_ = v_isSharedCheck_461_;
goto v_resetjp_434_;
}
else
{
lean_dec(v_l_412_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_461_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_451_; 
v___x_437_ = lean_nat_add(v___x_407_, v_size_408_);
v___x_438_ = lean_nat_add(v___x_437_, v_size_409_);
lean_dec(v_size_409_);
if (lean_obj_tag(v_l_428_) == 0)
{
lean_object* v_size_459_; 
v_size_459_ = lean_ctor_get(v_l_428_, 0);
lean_inc(v_size_459_);
v___y_451_ = v_size_459_;
goto v___jp_450_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = lean_unsigned_to_nat(0u);
v___y_451_ = v___x_460_;
goto v___jp_450_;
}
v___jp_439_:
{
lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_443_ = lean_nat_add(v___y_440_, v___y_442_);
lean_dec(v___y_442_);
lean_dec(v___y_440_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 4, v_r_413_);
lean_ctor_set(v___x_435_, 3, v_r_429_);
lean_ctor_set(v___x_435_, 2, v_v_411_);
lean_ctor_set(v___x_435_, 1, v_k_410_);
lean_ctor_set(v___x_435_, 0, v___x_443_);
v___x_445_ = v___x_435_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_k_410_);
lean_ctor_set(v_reuseFailAlloc_449_, 2, v_v_411_);
lean_ctor_set(v_reuseFailAlloc_449_, 3, v_r_429_);
lean_ctor_set(v_reuseFailAlloc_449_, 4, v_r_413_);
v___x_445_ = v_reuseFailAlloc_449_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_447_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 4, v___x_445_);
lean_ctor_set(v___x_423_, 3, v___y_441_);
lean_ctor_set(v___x_423_, 2, v_v_427_);
lean_ctor_set(v___x_423_, 1, v_k_426_);
lean_ctor_set(v___x_423_, 0, v___x_438_);
v___x_447_ = v___x_423_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_k_426_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_v_427_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v___y_441_);
lean_ctor_set(v_reuseFailAlloc_448_, 4, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
v___jp_450_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = lean_nat_add(v___x_437_, v___y_451_);
lean_dec(v___y_451_);
lean_dec(v___x_437_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 4, v_l_428_);
lean_ctor_set(v___x_402_, 0, v___x_452_);
v___x_454_ = v___x_402_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_k_397_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v_v_398_);
lean_ctor_set(v_reuseFailAlloc_458_, 3, v_l_399_);
lean_ctor_set(v_reuseFailAlloc_458_, 4, v_l_428_);
v___x_454_ = v_reuseFailAlloc_458_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; 
v___x_455_ = lean_nat_add(v___x_407_, v_size_430_);
if (lean_obj_tag(v_r_429_) == 0)
{
lean_object* v_size_456_; 
v_size_456_ = lean_ctor_get(v_r_429_, 0);
lean_inc(v_size_456_);
v___y_440_ = v___x_455_;
v___y_441_ = v___x_454_;
v___y_442_ = v_size_456_;
goto v___jp_439_;
}
else
{
lean_object* v___x_457_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___y_440_ = v___x_455_;
v___y_441_ = v___x_454_;
v___y_442_ = v___x_457_;
goto v___jp_439_;
}
}
}
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
lean_del_object(v___x_402_);
v___x_467_ = lean_nat_add(v___x_407_, v_size_408_);
v___x_468_ = lean_nat_add(v___x_467_, v_size_409_);
lean_dec(v_size_409_);
v___x_469_ = lean_nat_add(v___x_467_, v_size_425_);
lean_dec(v___x_467_);
lean_inc_ref(v_l_399_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 4, v_l_412_);
lean_ctor_set(v___x_423_, 3, v_l_399_);
lean_ctor_set(v___x_423_, 2, v_v_398_);
lean_ctor_set(v___x_423_, 1, v_k_397_);
lean_ctor_set(v___x_423_, 0, v___x_469_);
v___x_471_ = v___x_423_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_k_397_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_v_398_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v_l_399_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v_l_412_);
v___x_471_ = v_reuseFailAlloc_484_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_isSharedCheck_478_ = !lean_is_exclusive(v_l_399_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; lean_object* v_unused_480_; lean_object* v_unused_481_; lean_object* v_unused_482_; lean_object* v_unused_483_; 
v_unused_479_ = lean_ctor_get(v_l_399_, 4);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_l_399_, 3);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_l_399_, 2);
lean_dec(v_unused_481_);
v_unused_482_ = lean_ctor_get(v_l_399_, 1);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v_l_399_, 0);
lean_dec(v_unused_483_);
v___x_473_ = v_l_399_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_dec(v_l_399_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 4, v_r_413_);
lean_ctor_set(v___x_473_, 3, v___x_471_);
lean_ctor_set(v___x_473_, 2, v_v_411_);
lean_ctor_set(v___x_473_, 1, v_k_410_);
lean_ctor_set(v___x_473_, 0, v___x_468_);
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_k_410_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_v_411_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_477_, 4, v_r_413_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_491_; 
v_l_491_ = lean_ctor_get(v_impl_406_, 3);
lean_inc(v_l_491_);
if (lean_obj_tag(v_l_491_) == 0)
{
lean_object* v_r_492_; lean_object* v_k_493_; lean_object* v_v_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_517_; 
v_r_492_ = lean_ctor_get(v_impl_406_, 4);
v_k_493_ = lean_ctor_get(v_impl_406_, 1);
v_v_494_ = lean_ctor_get(v_impl_406_, 2);
v_isSharedCheck_517_ = !lean_is_exclusive(v_impl_406_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; lean_object* v_unused_519_; 
v_unused_518_ = lean_ctor_get(v_impl_406_, 3);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v_impl_406_, 0);
lean_dec(v_unused_519_);
v___x_496_ = v_impl_406_;
v_isShared_497_ = v_isSharedCheck_517_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_r_492_);
lean_inc(v_v_494_);
lean_inc(v_k_493_);
lean_dec(v_impl_406_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_517_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_k_498_; lean_object* v_v_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_513_; 
v_k_498_ = lean_ctor_get(v_l_491_, 1);
v_v_499_ = lean_ctor_get(v_l_491_, 2);
v_isSharedCheck_513_ = !lean_is_exclusive(v_l_491_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; lean_object* v_unused_515_; lean_object* v_unused_516_; 
v_unused_514_ = lean_ctor_get(v_l_491_, 4);
lean_dec(v_unused_514_);
v_unused_515_ = lean_ctor_get(v_l_491_, 3);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_l_491_, 0);
lean_dec(v_unused_516_);
v___x_501_ = v_l_491_;
v_isShared_502_ = v_isSharedCheck_513_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_v_499_);
lean_inc(v_k_498_);
lean_dec(v_l_491_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_513_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_492_, 2);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 4, v_r_492_);
lean_ctor_set(v___x_501_, 3, v_r_492_);
lean_ctor_set(v___x_501_, 2, v_v_398_);
lean_ctor_set(v___x_501_, 1, v_k_397_);
lean_ctor_set(v___x_501_, 0, v___x_407_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_k_397_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_v_398_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_r_492_);
lean_ctor_set(v_reuseFailAlloc_512_, 4, v_r_492_);
v___x_505_ = v_reuseFailAlloc_512_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; 
lean_inc(v_r_492_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 3, v_r_492_);
lean_ctor_set(v___x_496_, 0, v___x_407_);
v___x_507_ = v___x_496_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_r_492_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_r_492_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_509_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 4, v___x_507_);
lean_ctor_set(v___x_402_, 3, v___x_505_);
lean_ctor_set(v___x_402_, 2, v_v_499_);
lean_ctor_set(v___x_402_, 1, v_k_498_);
lean_ctor_set(v___x_402_, 0, v___x_503_);
v___x_509_ = v___x_402_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
}
else
{
lean_object* v_r_520_; 
v_r_520_ = lean_ctor_get(v_impl_406_, 4);
lean_inc(v_r_520_);
if (lean_obj_tag(v_r_520_) == 0)
{
lean_object* v_k_521_; lean_object* v_v_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_533_; 
v_k_521_ = lean_ctor_get(v_impl_406_, 1);
v_v_522_ = lean_ctor_get(v_impl_406_, 2);
v_isSharedCheck_533_ = !lean_is_exclusive(v_impl_406_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; lean_object* v_unused_535_; lean_object* v_unused_536_; 
v_unused_534_ = lean_ctor_get(v_impl_406_, 4);
lean_dec(v_unused_534_);
v_unused_535_ = lean_ctor_get(v_impl_406_, 3);
lean_dec(v_unused_535_);
v_unused_536_ = lean_ctor_get(v_impl_406_, 0);
lean_dec(v_unused_536_);
v___x_524_ = v_impl_406_;
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_v_522_);
lean_inc(v_k_521_);
lean_dec(v_impl_406_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_unsigned_to_nat(3u);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 4, v_l_491_);
lean_ctor_set(v___x_524_, 2, v_v_398_);
lean_ctor_set(v___x_524_, 1, v_k_397_);
lean_ctor_set(v___x_524_, 0, v___x_407_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_k_397_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_v_398_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_l_491_);
lean_ctor_set(v_reuseFailAlloc_532_, 4, v_l_491_);
v___x_528_ = v_reuseFailAlloc_532_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 4, v_r_520_);
lean_ctor_set(v___x_402_, 3, v___x_528_);
lean_ctor_set(v___x_402_, 2, v_v_522_);
lean_ctor_set(v___x_402_, 1, v_k_521_);
lean_ctor_set(v___x_402_, 0, v___x_526_);
v___x_530_ = v___x_402_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_k_521_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_v_522_);
lean_ctor_set(v_reuseFailAlloc_531_, 3, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_531_, 4, v_r_520_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = lean_unsigned_to_nat(2u);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 4, v_impl_406_);
lean_ctor_set(v___x_402_, 3, v_r_520_);
lean_ctor_set(v___x_402_, 0, v___x_537_);
v___x_539_ = v___x_402_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_k_397_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v_v_398_);
lean_ctor_set(v_reuseFailAlloc_540_, 3, v_r_520_);
lean_ctor_set(v_reuseFailAlloc_540_, 4, v_impl_406_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
else
{
lean_object* v___x_542_; 
lean_dec(v_v_398_);
lean_dec(v_k_397_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 2, v_v_394_);
lean_ctor_set(v___x_402_, 1, v_k_393_);
v___x_542_ = v___x_402_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_size_396_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_k_393_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_v_394_);
lean_ctor_set(v_reuseFailAlloc_543_, 3, v_l_399_);
lean_ctor_set(v_reuseFailAlloc_543_, 4, v_r_400_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
else
{
lean_object* v_impl_544_; lean_object* v___x_545_; 
lean_dec(v_size_396_);
v_impl_544_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_393_, v_v_394_, v_l_399_);
v___x_545_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_400_) == 0)
{
lean_object* v_size_546_; lean_object* v_size_547_; lean_object* v_k_548_; lean_object* v_v_549_; lean_object* v_l_550_; lean_object* v_r_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_size_546_ = lean_ctor_get(v_r_400_, 0);
v_size_547_ = lean_ctor_get(v_impl_544_, 0);
lean_inc(v_size_547_);
v_k_548_ = lean_ctor_get(v_impl_544_, 1);
lean_inc(v_k_548_);
v_v_549_ = lean_ctor_get(v_impl_544_, 2);
lean_inc(v_v_549_);
v_l_550_ = lean_ctor_get(v_impl_544_, 3);
lean_inc(v_l_550_);
v_r_551_ = lean_ctor_get(v_impl_544_, 4);
lean_inc(v_r_551_);
v___x_552_ = lean_unsigned_to_nat(3u);
v___x_553_ = lean_nat_mul(v___x_552_, v_size_546_);
v___x_554_ = lean_nat_dec_lt(v___x_553_, v_size_547_);
lean_dec(v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
lean_dec(v_r_551_);
lean_dec(v_l_550_);
lean_dec(v_v_549_);
lean_dec(v_k_548_);
v___x_555_ = lean_nat_add(v___x_545_, v_size_547_);
lean_dec(v_size_547_);
v___x_556_ = lean_nat_add(v___x_555_, v_size_546_);
lean_dec(v___x_555_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 3, v_impl_544_);
lean_ctor_set(v___x_402_, 0, v___x_556_);
v___x_558_ = v___x_402_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_k_397_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_v_398_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_impl_544_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v_r_400_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
else
{
lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_625_; 
v_isSharedCheck_625_ = !lean_is_exclusive(v_impl_544_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; lean_object* v_unused_627_; lean_object* v_unused_628_; lean_object* v_unused_629_; lean_object* v_unused_630_; 
v_unused_626_ = lean_ctor_get(v_impl_544_, 4);
lean_dec(v_unused_626_);
v_unused_627_ = lean_ctor_get(v_impl_544_, 3);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v_impl_544_, 2);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_impl_544_, 1);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_impl_544_, 0);
lean_dec(v_unused_630_);
v___x_561_ = v_impl_544_;
v_isShared_562_ = v_isSharedCheck_625_;
goto v_resetjp_560_;
}
else
{
lean_dec(v_impl_544_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_625_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_size_563_; lean_object* v_size_564_; lean_object* v_k_565_; lean_object* v_v_566_; lean_object* v_l_567_; lean_object* v_r_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v_size_563_ = lean_ctor_get(v_l_550_, 0);
v_size_564_ = lean_ctor_get(v_r_551_, 0);
v_k_565_ = lean_ctor_get(v_r_551_, 1);
v_v_566_ = lean_ctor_get(v_r_551_, 2);
v_l_567_ = lean_ctor_get(v_r_551_, 3);
v_r_568_ = lean_ctor_get(v_r_551_, 4);
v___x_569_ = lean_unsigned_to_nat(2u);
v___x_570_ = lean_nat_mul(v___x_569_, v_size_563_);
v___x_571_ = lean_nat_dec_lt(v_size_564_, v___x_570_);
lean_dec(v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_600_; 
lean_inc(v_r_568_);
lean_inc(v_l_567_);
lean_inc(v_v_566_);
lean_inc(v_k_565_);
v_isSharedCheck_600_ = !lean_is_exclusive(v_r_551_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; lean_object* v_unused_602_; lean_object* v_unused_603_; lean_object* v_unused_604_; lean_object* v_unused_605_; 
v_unused_601_ = lean_ctor_get(v_r_551_, 4);
lean_dec(v_unused_601_);
v_unused_602_ = lean_ctor_get(v_r_551_, 3);
lean_dec(v_unused_602_);
v_unused_603_ = lean_ctor_get(v_r_551_, 2);
lean_dec(v_unused_603_);
v_unused_604_ = lean_ctor_get(v_r_551_, 1);
lean_dec(v_unused_604_);
v_unused_605_ = lean_ctor_get(v_r_551_, 0);
lean_dec(v_unused_605_);
v___x_573_ = v_r_551_;
v_isShared_574_ = v_isSharedCheck_600_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_r_551_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_600_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___x_588_; lean_object* v___y_590_; 
v___x_575_ = lean_nat_add(v___x_545_, v_size_547_);
lean_dec(v_size_547_);
v___x_576_ = lean_nat_add(v___x_575_, v_size_546_);
lean_dec(v___x_575_);
v___x_588_ = lean_nat_add(v___x_545_, v_size_563_);
if (lean_obj_tag(v_l_567_) == 0)
{
lean_object* v_size_598_; 
v_size_598_ = lean_ctor_get(v_l_567_, 0);
lean_inc(v_size_598_);
v___y_590_ = v_size_598_;
goto v___jp_589_;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___y_590_ = v___x_599_;
goto v___jp_589_;
}
v___jp_577_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = lean_nat_add(v___y_578_, v___y_580_);
lean_dec(v___y_580_);
lean_dec(v___y_578_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 4, v_r_400_);
lean_ctor_set(v___x_573_, 3, v_r_568_);
lean_ctor_set(v___x_573_, 2, v_v_398_);
lean_ctor_set(v___x_573_, 1, v_k_397_);
lean_ctor_set(v___x_573_, 0, v___x_581_);
v___x_583_ = v___x_573_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_k_397_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_v_398_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v_r_568_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v_r_400_);
v___x_583_ = v_reuseFailAlloc_587_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_585_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 4, v___x_583_);
lean_ctor_set(v___x_561_, 3, v___y_579_);
lean_ctor_set(v___x_561_, 2, v_v_566_);
lean_ctor_set(v___x_561_, 1, v_k_565_);
lean_ctor_set(v___x_561_, 0, v___x_576_);
v___x_585_ = v___x_561_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_k_565_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_v_566_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v___y_579_);
lean_ctor_set(v_reuseFailAlloc_586_, 4, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
v___jp_589_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = lean_nat_add(v___x_588_, v___y_590_);
lean_dec(v___y_590_);
lean_dec(v___x_588_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 4, v_l_567_);
lean_ctor_set(v___x_402_, 3, v_l_550_);
lean_ctor_set(v___x_402_, 2, v_v_549_);
lean_ctor_set(v___x_402_, 1, v_k_548_);
lean_ctor_set(v___x_402_, 0, v___x_591_);
v___x_593_ = v___x_402_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_k_548_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_v_549_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_l_550_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v_l_567_);
v___x_593_ = v_reuseFailAlloc_597_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; 
v___x_594_ = lean_nat_add(v___x_545_, v_size_546_);
if (lean_obj_tag(v_r_568_) == 0)
{
lean_object* v_size_595_; 
v_size_595_ = lean_ctor_get(v_r_568_, 0);
lean_inc(v_size_595_);
v___y_578_ = v___x_594_;
v___y_579_ = v___x_593_;
v___y_580_ = v_size_595_;
goto v___jp_577_;
}
else
{
lean_object* v___x_596_; 
v___x_596_ = lean_unsigned_to_nat(0u);
v___y_578_ = v___x_594_;
v___y_579_ = v___x_593_;
v___y_580_ = v___x_596_;
goto v___jp_577_;
}
}
}
}
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
lean_del_object(v___x_402_);
v___x_606_ = lean_nat_add(v___x_545_, v_size_547_);
lean_dec(v_size_547_);
v___x_607_ = lean_nat_add(v___x_606_, v_size_546_);
lean_dec(v___x_606_);
v___x_608_ = lean_nat_add(v___x_545_, v_size_546_);
v___x_609_ = lean_nat_add(v___x_608_, v_size_564_);
lean_dec(v___x_608_);
lean_inc_ref(v_r_400_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 4, v_r_400_);
lean_ctor_set(v___x_561_, 3, v_r_551_);
lean_ctor_set(v___x_561_, 2, v_v_398_);
lean_ctor_set(v___x_561_, 1, v_k_397_);
lean_ctor_set(v___x_561_, 0, v___x_609_);
v___x_611_ = v___x_561_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_k_397_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_v_398_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v_r_551_);
lean_ctor_set(v_reuseFailAlloc_624_, 4, v_r_400_);
v___x_611_ = v_reuseFailAlloc_624_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
v_isSharedCheck_618_ = !lean_is_exclusive(v_r_400_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; lean_object* v_unused_620_; lean_object* v_unused_621_; lean_object* v_unused_622_; lean_object* v_unused_623_; 
v_unused_619_ = lean_ctor_get(v_r_400_, 4);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_r_400_, 3);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_r_400_, 2);
lean_dec(v_unused_621_);
v_unused_622_ = lean_ctor_get(v_r_400_, 1);
lean_dec(v_unused_622_);
v_unused_623_ = lean_ctor_get(v_r_400_, 0);
lean_dec(v_unused_623_);
v___x_613_ = v_r_400_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_dec(v_r_400_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 4, v___x_611_);
lean_ctor_set(v___x_613_, 3, v_l_550_);
lean_ctor_set(v___x_613_, 2, v_v_549_);
lean_ctor_set(v___x_613_, 1, v_k_548_);
lean_ctor_set(v___x_613_, 0, v___x_607_);
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_k_548_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_v_549_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_l_550_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v___x_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_631_; 
v_l_631_ = lean_ctor_get(v_impl_544_, 3);
lean_inc(v_l_631_);
if (lean_obj_tag(v_l_631_) == 0)
{
lean_object* v_r_632_; lean_object* v_k_633_; lean_object* v_v_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_645_; 
v_r_632_ = lean_ctor_get(v_impl_544_, 4);
v_k_633_ = lean_ctor_get(v_impl_544_, 1);
v_v_634_ = lean_ctor_get(v_impl_544_, 2);
v_isSharedCheck_645_ = !lean_is_exclusive(v_impl_544_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; lean_object* v_unused_647_; 
v_unused_646_ = lean_ctor_get(v_impl_544_, 3);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_impl_544_, 0);
lean_dec(v_unused_647_);
v___x_636_ = v_impl_544_;
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_r_632_);
lean_inc(v_v_634_);
lean_inc(v_k_633_);
lean_dec(v_impl_544_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_632_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 3, v_r_632_);
lean_ctor_set(v___x_636_, 2, v_v_398_);
lean_ctor_set(v___x_636_, 1, v_k_397_);
lean_ctor_set(v___x_636_, 0, v___x_545_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_k_397_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_v_398_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_r_632_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v_r_632_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 4, v___x_640_);
lean_ctor_set(v___x_402_, 3, v_l_631_);
lean_ctor_set(v___x_402_, 2, v_v_634_);
lean_ctor_set(v___x_402_, 1, v_k_633_);
lean_ctor_set(v___x_402_, 0, v___x_638_);
v___x_642_ = v___x_402_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_k_633_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_v_634_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v_l_631_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v_r_648_; 
v_r_648_ = lean_ctor_get(v_impl_544_, 4);
lean_inc(v_r_648_);
if (lean_obj_tag(v_r_648_) == 0)
{
lean_object* v_k_649_; lean_object* v_v_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_673_; 
v_k_649_ = lean_ctor_get(v_impl_544_, 1);
v_v_650_ = lean_ctor_get(v_impl_544_, 2);
v_isSharedCheck_673_ = !lean_is_exclusive(v_impl_544_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; lean_object* v_unused_675_; lean_object* v_unused_676_; 
v_unused_674_ = lean_ctor_get(v_impl_544_, 4);
lean_dec(v_unused_674_);
v_unused_675_ = lean_ctor_get(v_impl_544_, 3);
lean_dec(v_unused_675_);
v_unused_676_ = lean_ctor_get(v_impl_544_, 0);
lean_dec(v_unused_676_);
v___x_652_ = v_impl_544_;
v_isShared_653_ = v_isSharedCheck_673_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_v_650_);
lean_inc(v_k_649_);
lean_dec(v_impl_544_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_673_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_k_654_; lean_object* v_v_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_669_; 
v_k_654_ = lean_ctor_get(v_r_648_, 1);
v_v_655_ = lean_ctor_get(v_r_648_, 2);
v_isSharedCheck_669_ = !lean_is_exclusive(v_r_648_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; lean_object* v_unused_671_; lean_object* v_unused_672_; 
v_unused_670_ = lean_ctor_get(v_r_648_, 4);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_r_648_, 3);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_r_648_, 0);
lean_dec(v_unused_672_);
v___x_657_ = v_r_648_;
v_isShared_658_ = v_isSharedCheck_669_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_v_655_);
lean_inc(v_k_654_);
lean_dec(v_r_648_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_669_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_unsigned_to_nat(3u);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 4, v_l_631_);
lean_ctor_set(v___x_657_, 3, v_l_631_);
lean_ctor_set(v___x_657_, 2, v_v_650_);
lean_ctor_set(v___x_657_, 1, v_k_649_);
lean_ctor_set(v___x_657_, 0, v___x_545_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_k_649_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_v_650_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_l_631_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v_l_631_);
v___x_661_ = v_reuseFailAlloc_668_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 4, v_l_631_);
lean_ctor_set(v___x_652_, 2, v_v_398_);
lean_ctor_set(v___x_652_, 1, v_k_397_);
lean_ctor_set(v___x_652_, 0, v___x_545_);
v___x_663_ = v___x_652_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_k_397_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_v_398_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v_l_631_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v_l_631_);
v___x_663_ = v_reuseFailAlloc_667_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_665_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 4, v___x_663_);
lean_ctor_set(v___x_402_, 3, v___x_661_);
lean_ctor_set(v___x_402_, 2, v_v_655_);
lean_ctor_set(v___x_402_, 1, v_k_654_);
lean_ctor_set(v___x_402_, 0, v___x_659_);
v___x_665_ = v___x_402_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_k_654_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_v_655_);
lean_ctor_set(v_reuseFailAlloc_666_, 3, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_666_, 4, v___x_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_unsigned_to_nat(2u);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 4, v_r_648_);
lean_ctor_set(v___x_402_, 3, v_impl_544_);
lean_ctor_set(v___x_402_, 0, v___x_677_);
v___x_679_ = v___x_402_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_k_397_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_v_398_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_impl_544_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_r_648_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v_k_393_);
lean_ctor_set(v___x_683_, 2, v_v_394_);
lean_ctor_set(v___x_683_, 3, v_t_395_);
lean_ctor_set(v___x_683_, 4, v_t_395_);
return v___x_683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_insert___lam__0(lean_object* v_overlapping_684_, lean_object* v_s_x3f_685_){
_start:
{
lean_object* v___y_687_; 
if (lean_obj_tag(v_s_x3f_685_) == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_box(1);
v___y_687_ = v___x_693_;
goto v___jp_686_;
}
else
{
lean_object* v_val_694_; 
v_val_694_ = lean_ctor_get(v_s_x3f_685_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v_s_x3f_685_, 1);
v___y_687_ = v_val_694_;
goto v___jp_686_;
}
v___jp_686_:
{
uint8_t v___x_688_; 
v___x_688_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_overlapping_684_, v___y_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_box(0);
v___x_690_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_overlapping_684_, v___x_689_, v___y_687_);
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
else
{
lean_object* v___x_692_; 
lean_dec(v_overlapping_684_);
v___x_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_692_, 0, v___y_687_);
return v___x_692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(lean_object* v_m_695_, lean_object* v_query_696_, lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
lean_object* v_zero_700_; uint8_t v_isZero_701_; 
v_zero_700_ = lean_unsigned_to_nat(0u);
v_isZero_701_ = lean_nat_dec_eq(v_x_698_, v_zero_700_);
if (v_isZero_701_ == 1)
{
lean_dec(v_x_699_);
lean_dec(v_x_698_);
if (lean_obj_tag(v_x_697_) == 0)
{
lean_object* v___x_702_; 
v___x_702_ = lean_box(2);
return v___x_702_;
}
else
{
lean_object* v_val_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_val_703_ = lean_ctor_get(v_x_697_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v_x_697_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v_x_697_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_val_703_);
lean_dec(v_x_697_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_val_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v_keyArray_711_; lean_object* v_valueArray_712_; lean_object* v___x_713_; uint8_t v_isSome_714_; 
v_keyArray_711_ = lean_ctor_get(v_m_695_, 1);
v_valueArray_712_ = lean_ctor_get(v_m_695_, 2);
v___x_713_ = lean_array_fget_borrowed(v_keyArray_711_, v_x_699_);
v_isSome_714_ = lean_noption_is_some(v___x_713_);
if (v_isSome_714_ == 0)
{
lean_dec(v_x_698_);
if (lean_obj_tag(v_x_697_) == 0)
{
lean_object* v___x_715_; 
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v_x_699_);
return v___x_715_;
}
else
{
lean_object* v_val_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_x_699_);
v_val_716_ = lean_ctor_get(v_x_697_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_x_697_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v_x_697_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_val_716_);
lean_dec(v_x_697_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_val_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_one_724_; lean_object* v_n_725_; lean_object* v___y_727_; 
v_one_724_ = lean_unsigned_to_nat(1u);
v_n_725_ = lean_nat_sub(v_x_698_, v_one_724_);
lean_dec(v_x_698_);
if (v_isSome_714_ == 0)
{
goto v___jp_733_;
}
else
{
lean_object* v___x_735_; uint8_t v_isSome_736_; 
v___x_735_ = lean_array_fget_borrowed(v_valueArray_712_, v_x_699_);
v_isSome_736_ = lean_noption_is_some(v___x_735_);
if (v_isSome_736_ == 0)
{
goto v___jp_733_;
}
else
{
lean_object* v_val_737_; uint8_t v___x_738_; 
lean_inc(v___x_713_);
v_val_737_ = lean_noption_get(v___x_713_);
v___x_738_ = lean_nat_dec_eq(v_val_737_, v_query_696_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
lean_dec(v_val_737_);
v___x_739_ = lean_array_get_size(v_keyArray_711_);
v___x_740_ = lean_nat_add(v_x_699_, v_one_724_);
lean_dec(v_x_699_);
v___x_741_ = lean_nat_dec_lt(v___x_740_, v___x_739_);
if (v___x_741_ == 0)
{
lean_dec(v___x_740_);
v_x_698_ = v_n_725_;
v_x_699_ = v_zero_700_;
goto _start;
}
else
{
v_x_698_ = v_n_725_;
v_x_699_ = v___x_740_;
goto _start;
}
}
else
{
lean_object* v_val_744_; lean_object* v___x_745_; 
lean_dec(v_n_725_);
lean_dec(v_x_697_);
lean_inc(v___x_735_);
v_val_744_ = lean_noption_get(v___x_735_);
v___x_745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_745_, 0, v_x_699_);
lean_ctor_set(v___x_745_, 1, v_val_737_);
lean_ctor_set(v___x_745_, 2, v_val_744_);
return v___x_745_;
}
}
}
v___jp_726_:
{
lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_728_ = lean_array_get_size(v_keyArray_711_);
v___x_729_ = lean_nat_add(v_x_699_, v_one_724_);
lean_dec(v_x_699_);
v___x_730_ = lean_nat_dec_lt(v___x_729_, v___x_728_);
if (v___x_730_ == 0)
{
lean_dec(v___x_729_);
v_x_697_ = v___y_727_;
v_x_698_ = v_n_725_;
v_x_699_ = v_zero_700_;
goto _start;
}
else
{
v_x_697_ = v___y_727_;
v_x_698_ = v_n_725_;
v_x_699_ = v___x_729_;
goto _start;
}
}
v___jp_733_:
{
if (lean_obj_tag(v_x_697_) == 0)
{
lean_object* v___x_734_; 
lean_inc(v_x_699_);
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v_x_699_);
v___y_727_ = v___x_734_;
goto v___jp_726_;
}
else
{
v___y_727_ = v_x_697_;
goto v___jp_726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg___boxed(lean_object* v_m_746_, lean_object* v_query_747_, lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_m_746_, v_query_747_, v_x_748_, v_x_749_, v_x_750_);
lean_dec(v_query_747_);
lean_dec_ref(v_m_746_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2___redArg(lean_object* v_m_752_, lean_object* v_query_753_){
_start:
{
lean_object* v_keyArray_754_; lean_object* v___x_755_; uint64_t v___x_756_; uint64_t v___x_757_; uint64_t v___x_758_; uint64_t v_fold_759_; uint64_t v___x_760_; uint64_t v___x_761_; uint64_t v___x_762_; size_t v___x_763_; size_t v___x_764_; size_t v___x_765_; size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_keyArray_754_ = lean_ctor_get(v_m_752_, 1);
v___x_755_ = lean_array_get_size(v_keyArray_754_);
v___x_756_ = lean_uint64_of_nat(v_query_753_);
v___x_757_ = 32ULL;
v___x_758_ = lean_uint64_shift_right(v___x_756_, v___x_757_);
v_fold_759_ = lean_uint64_xor(v___x_756_, v___x_758_);
v___x_760_ = 16ULL;
v___x_761_ = lean_uint64_shift_right(v_fold_759_, v___x_760_);
v___x_762_ = lean_uint64_xor(v_fold_759_, v___x_761_);
v___x_763_ = lean_uint64_to_usize(v___x_762_);
v___x_764_ = lean_usize_of_nat(v___x_755_);
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_sub(v___x_764_, v___x_765_);
v___x_767_ = lean_usize_land(v___x_763_, v___x_766_);
v___x_768_ = lean_usize_to_nat(v___x_767_);
v___x_769_ = lean_box(0);
v___x_770_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_m_752_, v_query_753_, v___x_769_, v___x_755_, v___x_768_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2___redArg___boxed(lean_object* v_m_771_, lean_object* v_query_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2___redArg(v_m_771_, v_query_772_);
lean_dec(v_query_772_);
lean_dec_ref(v_m_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4_spec__5___redArg(lean_object* v_b_774_, lean_object* v_acc_775_, lean_object* v_i_776_){
_start:
{
lean_object* v___y_778_; lean_object* v_keyArray_786_; lean_object* v_valueArray_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_keyArray_786_ = lean_ctor_get(v_b_774_, 1);
v_valueArray_787_ = lean_ctor_get(v_b_774_, 2);
v___x_788_ = lean_array_get_size(v_keyArray_786_);
v___x_789_ = lean_nat_dec_lt(v_i_776_, v___x_788_);
if (v___x_789_ == 0)
{
lean_dec(v_i_776_);
return v_acc_775_;
}
else
{
lean_object* v___x_790_; uint8_t v_isSome_791_; 
v___x_790_ = lean_array_fget_borrowed(v_keyArray_786_, v_i_776_);
v_isSome_791_ = lean_noption_is_some(v___x_790_);
if (v_isSome_791_ == 0)
{
goto v___jp_782_;
}
else
{
lean_object* v___x_792_; uint8_t v_isSome_793_; 
v___x_792_ = lean_array_fget_borrowed(v_valueArray_787_, v_i_776_);
v_isSome_793_ = lean_noption_is_some(v___x_792_);
if (v_isSome_793_ == 0)
{
goto v___jp_782_;
}
else
{
lean_object* v_val_794_; lean_object* v_val_795_; lean_object* v_i_797_; lean_object* v___x_802_; 
lean_inc(v___x_790_);
v_val_794_ = lean_noption_get(v___x_790_);
lean_inc(v___x_792_);
v_val_795_ = lean_noption_get(v___x_792_);
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2___redArg(v_acc_775_, v_val_794_);
switch(lean_obj_tag(v___x_802_))
{
case 0:
{
lean_object* v_index_803_; lean_object* v_size_804_; lean_object* v___x_805_; 
v_index_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_index_803_);
lean_dec_ref_known(v___x_802_, 3);
v_size_804_ = lean_ctor_get(v_acc_775_, 0);
lean_inc(v_size_804_);
v___x_805_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_775_, v_size_804_, v_index_803_, v_val_794_, v_val_795_);
lean_dec(v_index_803_);
v___y_778_ = v___x_805_;
goto v___jp_777_;
}
case 1:
{
lean_object* v_index_806_; 
v_index_806_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_index_806_);
lean_dec_ref_known(v___x_802_, 1);
v_i_797_ = v_index_806_;
goto v___jp_796_;
}
default: 
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_775_, v___x_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_index_809_; 
v_index_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_index_809_);
lean_dec_ref_known(v___x_808_, 1);
v_i_797_ = v_index_809_;
goto v___jp_796_;
}
else
{
lean_dec(v_val_795_);
lean_dec(v_val_794_);
v___y_778_ = v_acc_775_;
goto v___jp_777_;
}
}
}
v___jp_796_:
{
lean_object* v_size_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_size_798_ = lean_ctor_get(v_acc_775_, 0);
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_add(v_size_798_, v___x_799_);
v___x_801_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_775_, v___x_800_, v_i_797_, v_val_794_, v_val_795_);
lean_dec(v_i_797_);
v___y_778_ = v___x_801_;
goto v___jp_777_;
}
}
}
}
v___jp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_add(v_i_776_, v___x_779_);
lean_dec(v_i_776_);
v_acc_775_ = v___y_778_;
v_i_776_ = v___x_780_;
goto _start;
}
v___jp_782_:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = lean_nat_add(v_i_776_, v___x_783_);
lean_dec(v_i_776_);
v_i_776_ = v___x_784_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_b_810_, lean_object* v_acc_811_, lean_object* v_i_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4_spec__5___redArg(v_b_810_, v_acc_811_, v_i_812_);
lean_dec_ref(v_b_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4___redArg(lean_object* v_init_814_, lean_object* v_b_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4_spec__5___redArg(v_b_815_, v_init_814_, v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4___redArg___boxed(lean_object* v_init_818_, lean_object* v_b_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4___redArg(v_init_818_, v_b_819_);
lean_dec_ref(v_b_819_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3___redArg(lean_object* v_m_821_){
_start:
{
lean_object* v_keyArray_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_cellCount_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v_target_829_; lean_object* v___x_830_; 
v_keyArray_822_ = lean_ctor_get(v_m_821_, 1);
v___x_823_ = lean_array_get_size(v_keyArray_822_);
v___x_824_ = lean_unsigned_to_nat(2u);
v_cellCount_825_ = lean_nat_mul(v___x_823_, v___x_824_);
v___x_826_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_825_);
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_825_);
v___x_828_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_825_);
v_target_829_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_829_, 0, v___x_826_);
lean_ctor_set(v_target_829_, 1, v___x_827_);
lean_ctor_set(v_target_829_, 2, v___x_828_);
v___x_830_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4___redArg(v_target_829_, v_m_821_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3___redArg___boxed(lean_object* v_m_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3___redArg(v_m_831_);
lean_dec_ref(v_m_831_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_insert(lean_object* v_o_833_, lean_object* v_overlapping_834_, lean_object* v_overlapped_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2___redArg(v_o_833_, v_overlapped_835_);
switch(lean_obj_tag(v___x_836_))
{
case 0:
{
lean_object* v_index_837_; lean_object* v_value_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v_val_841_; lean_object* v_size_842_; lean_object* v___x_843_; 
v_index_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_index_837_);
v_value_838_ = lean_ctor_get(v___x_836_, 2);
lean_inc(v_value_838_);
lean_dec_ref_known(v___x_836_, 3);
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v_value_838_);
v___x_840_ = l_Lean_Meta_Match_Overlaps_insert___lam__0(v_overlapping_834_, v___x_839_);
v_val_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_val_841_);
lean_dec(v___x_840_);
v_size_842_ = lean_ctor_get(v_o_833_, 0);
lean_inc(v_size_842_);
v___x_843_ = l_Std_DHashMap_Raw_setEntry___redArg(v_o_833_, v_size_842_, v_index_837_, v_overlapped_835_, v_val_841_);
lean_dec(v_index_837_);
return v___x_843_;
}
case 1:
{
lean_object* v_index_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v_val_847_; lean_object* v___y_849_; lean_object* v_i_850_; lean_object* v_size_865_; lean_object* v_keyArray_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_index_844_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_index_844_);
lean_dec_ref_known(v___x_836_, 1);
v___x_845_ = lean_box(0);
v___x_846_ = l_Lean_Meta_Match_Overlaps_insert___lam__0(v_overlapping_834_, v___x_845_);
v_val_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_val_847_);
lean_dec(v___x_846_);
v_size_865_ = lean_ctor_get(v_o_833_, 0);
v_keyArray_866_ = lean_ctor_get(v_o_833_, 1);
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_add(v_size_865_, v___x_867_);
v___x_869_ = lean_array_get_size(v_keyArray_866_);
v___x_870_ = lean_nat_dec_lt(v___x_868_, v___x_869_);
if (v___x_870_ == 0)
{
lean_dec(v___x_868_);
lean_dec(v_index_844_);
goto v___jp_855_;
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_871_ = lean_unsigned_to_nat(4u);
v___x_872_ = lean_nat_mul(v___x_868_, v___x_871_);
v___x_873_ = lean_unsigned_to_nat(3u);
v___x_874_ = lean_nat_mul(v___x_869_, v___x_873_);
v___x_875_ = lean_nat_dec_le(v___x_872_, v___x_874_);
lean_dec(v___x_874_);
lean_dec(v___x_872_);
if (v___x_875_ == 0)
{
lean_dec(v___x_868_);
lean_dec(v_index_844_);
goto v___jp_855_;
}
else
{
lean_object* v___x_876_; 
v___x_876_ = l_Std_DHashMap_Raw_setEntry___redArg(v_o_833_, v___x_868_, v_index_844_, v_overlapped_835_, v_val_847_);
lean_dec(v_index_844_);
return v___x_876_;
}
}
v___jp_848_:
{
lean_object* v_size_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_size_851_ = lean_ctor_get(v___y_849_, 0);
v___x_852_ = lean_unsigned_to_nat(1u);
v___x_853_ = lean_nat_add(v_size_851_, v___x_852_);
v___x_854_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_849_, v___x_853_, v_i_850_, v_overlapped_835_, v_val_847_);
lean_dec(v_i_850_);
return v___x_854_;
}
v___jp_855_:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3___redArg(v_o_833_);
lean_dec_ref(v_o_833_);
v___x_857_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2___redArg(v___x_856_, v_overlapped_835_);
switch(lean_obj_tag(v___x_857_))
{
case 0:
{
lean_object* v_index_858_; lean_object* v_size_859_; lean_object* v___x_860_; 
v_index_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_index_858_);
lean_dec_ref_known(v___x_857_, 3);
v_size_859_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_size_859_);
v___x_860_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_856_, v_size_859_, v_index_858_, v_overlapped_835_, v_val_847_);
lean_dec(v_index_858_);
return v___x_860_;
}
case 1:
{
lean_object* v_index_861_; 
v_index_861_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_index_861_);
lean_dec_ref_known(v___x_857_, 1);
v___y_849_ = v___x_856_;
v_i_850_ = v_index_861_;
goto v___jp_848_;
}
default: 
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_856_, v___x_862_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_index_864_; 
v_index_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_index_864_);
lean_dec_ref_known(v___x_863_, 1);
v___y_849_ = v___x_856_;
v_i_850_ = v_index_864_;
goto v___jp_848_;
}
else
{
lean_dec(v_val_847_);
lean_dec(v_overlapped_835_);
return v___x_856_;
}
}
}
}
}
default: 
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v_val_879_; lean_object* v___y_881_; lean_object* v_i_882_; lean_object* v___y_888_; lean_object* v_size_897_; lean_object* v_keyArray_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_877_ = lean_box(0);
v___x_878_ = l_Lean_Meta_Match_Overlaps_insert___lam__0(v_overlapping_834_, v___x_877_);
v_val_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_val_879_);
lean_dec(v___x_878_);
v_size_897_ = lean_ctor_get(v_o_833_, 0);
v_keyArray_898_ = lean_ctor_get(v_o_833_, 1);
v___x_899_ = lean_unsigned_to_nat(1u);
v___x_900_ = lean_nat_add(v_size_897_, v___x_899_);
v___x_901_ = lean_array_get_size(v_keyArray_898_);
v___x_902_ = lean_nat_dec_lt(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_dec(v___x_900_);
v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3___redArg(v_o_833_);
lean_dec_ref(v_o_833_);
v___y_888_ = v___x_903_;
goto v___jp_887_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_904_ = lean_unsigned_to_nat(4u);
v___x_905_ = lean_nat_mul(v___x_900_, v___x_904_);
lean_dec(v___x_900_);
v___x_906_ = lean_unsigned_to_nat(3u);
v___x_907_ = lean_nat_mul(v___x_901_, v___x_906_);
v___x_908_ = lean_nat_dec_le(v___x_905_, v___x_907_);
lean_dec(v___x_907_);
lean_dec(v___x_905_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3___redArg(v_o_833_);
lean_dec_ref(v_o_833_);
v___y_888_ = v___x_909_;
goto v___jp_887_;
}
else
{
v___y_888_ = v_o_833_;
goto v___jp_887_;
}
}
v___jp_880_:
{
lean_object* v_size_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_size_883_ = lean_ctor_get(v___y_881_, 0);
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_nat_add(v_size_883_, v___x_884_);
v___x_886_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_881_, v___x_885_, v_i_882_, v_overlapped_835_, v_val_879_);
lean_dec(v_i_882_);
return v___x_886_;
}
v___jp_887_:
{
lean_object* v___x_889_; 
v___x_889_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2___redArg(v___y_888_, v_overlapped_835_);
switch(lean_obj_tag(v___x_889_))
{
case 0:
{
lean_object* v_index_890_; lean_object* v_size_891_; lean_object* v___x_892_; 
v_index_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_index_890_);
lean_dec_ref_known(v___x_889_, 3);
v_size_891_ = lean_ctor_get(v___y_888_, 0);
lean_inc(v_size_891_);
v___x_892_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_888_, v_size_891_, v_index_890_, v_overlapped_835_, v_val_879_);
lean_dec(v_index_890_);
return v___x_892_;
}
case 1:
{
lean_object* v_index_893_; 
v_index_893_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_index_893_);
lean_dec_ref_known(v___x_889_, 1);
v___y_881_ = v___y_888_;
v_i_882_ = v_index_893_;
goto v___jp_880_;
}
default: 
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_888_, v___x_894_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_index_896_; 
v_index_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_index_896_);
lean_dec_ref_known(v___x_895_, 1);
v___y_881_ = v___y_888_;
v_i_882_ = v_index_896_;
goto v___jp_880_;
}
else
{
lean_dec(v_val_879_);
lean_dec(v_overlapped_835_);
return v___y_888_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(lean_object* v_00_u03b2_910_, lean_object* v_k_911_, lean_object* v_t_912_){
_start:
{
uint8_t v___x_913_; 
v___x_913_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_k_911_, v_t_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___boxed(lean_object* v_00_u03b2_914_, lean_object* v_k_915_, lean_object* v_t_916_){
_start:
{
uint8_t v_res_917_; lean_object* v_r_918_; 
v_res_917_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(v_00_u03b2_914_, v_k_915_, v_t_916_);
lean_dec(v_t_916_);
lean_dec(v_k_915_);
v_r_918_ = lean_box(v_res_917_);
return v_r_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1(lean_object* v_00_u03b2_919_, lean_object* v_k_920_, lean_object* v_v_921_, lean_object* v_t_922_, lean_object* v_hl_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_920_, v_v_921_, v_t_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2(lean_object* v_00_u03b2_925_, lean_object* v_m_926_, lean_object* v_query_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2___redArg(v_m_926_, v_query_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2___boxed(lean_object* v_00_u03b2_929_, lean_object* v_m_930_, lean_object* v_query_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2(v_00_u03b2_929_, v_m_930_, v_query_931_);
lean_dec(v_query_931_);
lean_dec_ref(v_m_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3(lean_object* v_00_u03b2_933_, lean_object* v_m_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3___redArg(v_m_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3___boxed(lean_object* v_00_u03b2_936_, lean_object* v_m_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3(v_00_u03b2_936_, v_m_937_);
lean_dec_ref(v_m_937_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(lean_object* v_00_u03b2_939_, lean_object* v_m_940_, lean_object* v_query_941_, lean_object* v_x_942_, lean_object* v_x_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_m_940_, v_query_941_, v_x_942_, v_x_943_, v_x_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___boxed(lean_object* v_00_u03b2_947_, lean_object* v_m_948_, lean_object* v_query_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(v_00_u03b2_947_, v_m_948_, v_query_949_, v_x_950_, v_x_951_, v_x_952_, v_x_953_);
lean_dec(v_query_949_);
lean_dec_ref(v_m_948_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4(lean_object* v_00_u03b2_955_, lean_object* v_init_956_, lean_object* v_b_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4___redArg(v_init_956_, v_b_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4___boxed(lean_object* v_00_u03b2_959_, lean_object* v_init_960_, lean_object* v_b_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4(v_00_u03b2_959_, v_init_960_, v_b_961_);
lean_dec_ref(v_b_961_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_963_, lean_object* v_b_964_, lean_object* v_acc_965_, lean_object* v_i_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4_spec__5___redArg(v_b_964_, v_acc_965_, v_i_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_968_, lean_object* v_b_969_, lean_object* v_acc_970_, lean_object* v_i_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Match_Overlaps_insert_spec__3_spec__4_spec__5(v_00_u03b2_968_, v_b_969_, v_acc_970_, v_i_971_);
lean_dec_ref(v_b_969_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(lean_object* v_m_973_, lean_object* v_query_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Match_Overlaps_insert_spec__2___redArg(v_m_973_, v_query_974_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_index_976_; lean_object* v_key_977_; lean_object* v_value_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
v_index_976_ = lean_ctor_get(v___x_975_, 0);
v_key_977_ = lean_ctor_get(v___x_975_, 1);
v_value_978_ = lean_ctor_get(v___x_975_, 2);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_975_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_value_978_);
lean_inc(v_key_977_);
lean_inc(v_index_976_);
lean_dec(v___x_975_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_index_976_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_key_977_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_value_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
else
{
lean_object* v___x_986_; 
lean_dec(v___x_975_);
v___x_986_ = lean_box(1);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg___boxed(lean_object* v_m_987_, lean_object* v_query_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_m_987_, v_query_988_);
lean_dec(v_query_988_);
lean_dec_ref(v_m_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(lean_object* v_m_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_m_990_, v_a_991_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_value_993_; lean_object* v___x_994_; 
v_value_993_ = lean_ctor_get(v___x_992_, 2);
lean_inc(v_value_993_);
lean_dec_ref_known(v___x_992_, 3);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v_value_993_);
return v___x_994_;
}
else
{
lean_object* v___x_995_; 
v___x_995_ = lean_box(0);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg___boxed(lean_object* v_m_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_m_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_m_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(lean_object* v_init_999_, lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
lean_object* v_k_1001_; lean_object* v_l_1002_; lean_object* v_r_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_k_1001_ = lean_ctor_get(v_x_1000_, 1);
lean_inc(v_k_1001_);
v_l_1002_ = lean_ctor_get(v_x_1000_, 3);
lean_inc(v_l_1002_);
v_r_1003_ = lean_ctor_get(v_x_1000_, 4);
lean_inc(v_r_1003_);
lean_dec_ref_known(v_x_1000_, 5);
v___x_1004_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v_init_999_, v_l_1002_);
v___x_1005_ = lean_array_push(v___x_1004_, v_k_1001_);
v_init_999_ = v___x_1005_;
v_x_1000_ = v_r_1003_;
goto _start;
}
else
{
return v_init_999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_overlapping(lean_object* v_o_1009_, lean_object* v_overlapped_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_o_1009_, v_overlapped_1010_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v___x_1012_; 
v___x_1012_ = ((lean_object*)(l_Lean_Meta_Match_Overlaps_overlapping___closed__0));
return v___x_1012_;
}
else
{
lean_object* v_val_1013_; lean_object* v___y_1015_; 
v_val_1013_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v___x_1011_, 1);
if (lean_obj_tag(v_val_1013_) == 0)
{
lean_object* v_size_1018_; 
v_size_1018_ = lean_ctor_get(v_val_1013_, 0);
lean_inc(v_size_1018_);
v___y_1015_ = v_size_1018_;
goto v___jp_1014_;
}
else
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_unsigned_to_nat(0u);
v___y_1015_ = v___x_1019_;
goto v___jp_1014_;
}
v___jp_1014_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_mk_empty_array_with_capacity(v___y_1015_);
lean_dec(v___y_1015_);
v___x_1017_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v___x_1016_, v_val_1013_);
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_overlapping___boxed(lean_object* v_o_1020_, lean_object* v_overlapped_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Meta_Match_Overlaps_overlapping(v_o_1020_, v_overlapped_1021_);
lean_dec(v_overlapped_1021_);
lean_dec_ref(v_o_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(lean_object* v_00_u03b2_1023_, lean_object* v_m_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_m_1024_, v_a_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___boxed(lean_object* v_00_u03b2_1027_, lean_object* v_m_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(v_00_u03b2_1027_, v_m_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_m_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1(lean_object* v_init_1031_, lean_object* v_t_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v_init_1031_, v_t_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(lean_object* v_00_u03b2_1034_, lean_object* v_m_1035_, lean_object* v_query_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_m_1035_, v_query_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1038_, lean_object* v_m_1039_, lean_object* v_query_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(v_00_u03b2_1038_, v_m_1039_, v_query_1040_);
lean_dec(v_query_1040_);
lean_dec_ref(v_m_1039_);
return v_res_1041_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_unsigned_to_nat(13u);
v___x_1057_ = lean_nat_to_int(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_unsigned_to_nat(15u);
v___x_1062_ = lean_nat_to_int(v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_unsigned_to_nat(16u);
v___x_1067_ = lean_nat_to_int(v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(lean_object* v_x_1068_){
_start:
{
lean_object* v_numFields_1069_; lean_object* v_numOverlaps_1070_; uint8_t v_hasUnitThunk_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_numFields_1069_ = lean_ctor_get(v_x_1068_, 0);
lean_inc(v_numFields_1069_);
v_numOverlaps_1070_ = lean_ctor_get(v_x_1068_, 1);
lean_inc(v_numOverlaps_1070_);
v_hasUnitThunk_1071_ = lean_ctor_get_uint8(v_x_1068_, sizeof(void*)*2);
lean_dec_ref(v_x_1068_);
v___x_1072_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5));
v___x_1073_ = ((lean_object*)(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3));
v___x_1074_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4);
v___x_1075_ = l_Nat_reprFast(v_numFields_1069_);
v___x_1076_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1074_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = 0;
v___x_1079_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set_uint8(v___x_1079_, sizeof(void*)*1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1073_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__4));
v___x_1082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_box(1);
v___x_1084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = ((lean_object*)(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6));
v___x_1086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v___x_1072_);
v___x_1088_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7);
v___x_1089_ = l_Nat_reprFast(v_numOverlaps_1070_);
v___x_1090_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1088_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*1, v___x_1078_);
v___x_1093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1087_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v___x_1081_);
v___x_1095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v___x_1083_);
v___x_1096_ = ((lean_object*)(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9));
v___x_1097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v___x_1072_);
v___x_1099_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10);
v___x_1100_ = l_Bool_repr___redArg(v_hasUnitThunk_1071_);
v___x_1101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set_uint8(v___x_1102_, sizeof(void*)*1, v___x_1078_);
v___x_1103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1098_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_1105_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_1106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v___x_1103_);
v___x_1107_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_1108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1104_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set_uint8(v___x_1110_, sizeof(void*)*1, v___x_1078_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr(lean_object* v_x_1111_, lean_object* v_prec_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_x_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___boxed(lean_object* v_x_1114_, lean_object* v_prec_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_Meta_Match_instReprAltParamInfo_repr(v_x_1114_, v_prec_1115_);
lean_dec(v_prec_1115_);
return v_res_1116_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_instBEqAltParamInfo_beq(lean_object* v_x_1119_, lean_object* v_x_1120_){
_start:
{
lean_object* v_numFields_1121_; lean_object* v_numOverlaps_1122_; uint8_t v_hasUnitThunk_1123_; lean_object* v_numFields_1124_; lean_object* v_numOverlaps_1125_; uint8_t v_hasUnitThunk_1126_; uint8_t v___x_1127_; 
v_numFields_1121_ = lean_ctor_get(v_x_1119_, 0);
v_numOverlaps_1122_ = lean_ctor_get(v_x_1119_, 1);
v_hasUnitThunk_1123_ = lean_ctor_get_uint8(v_x_1119_, sizeof(void*)*2);
v_numFields_1124_ = lean_ctor_get(v_x_1120_, 0);
v_numOverlaps_1125_ = lean_ctor_get(v_x_1120_, 1);
v_hasUnitThunk_1126_ = lean_ctor_get_uint8(v_x_1120_, sizeof(void*)*2);
v___x_1127_ = lean_nat_dec_eq(v_numFields_1121_, v_numFields_1124_);
if (v___x_1127_ == 0)
{
return v___x_1127_;
}
else
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_nat_dec_eq(v_numOverlaps_1122_, v_numOverlaps_1125_);
if (v___x_1128_ == 0)
{
return v___x_1128_;
}
else
{
if (v_hasUnitThunk_1123_ == 0)
{
if (v_hasUnitThunk_1126_ == 0)
{
return v___x_1128_;
}
else
{
return v_hasUnitThunk_1123_;
}
}
else
{
return v_hasUnitThunk_1126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instBEqAltParamInfo_beq___boxed(lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v_x_1129_, v_x_1130_);
lean_dec_ref(v_x_1130_);
lean_dec_ref(v_x_1129_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1137_ = l_Lean_Meta_Match_instInhabitedOverlaps_default;
v___x_1138_ = lean_box(0);
v___x_1139_ = ((lean_object*)(l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0));
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
lean_ctor_set(v___x_1141_, 2, v___x_1139_);
lean_ctor_set(v___x_1141_, 3, v___x_1138_);
lean_ctor_set(v___x_1141_, 4, v___x_1139_);
lean_ctor_set(v___x_1141_, 5, v___x_1137_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default(void){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1, &l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatcherInfo(void){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Meta_Match_instInhabitedMatcherInfo_default;
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
if (lean_obj_tag(v_x_1144_) == 0)
{
lean_object* v___x_1146_; 
v___x_1146_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1));
return v___x_1146_;
}
else
{
lean_object* v_val_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1158_; 
v_val_1147_ = lean_ctor_get(v_x_1144_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1149_ = v_x_1144_;
v_isShared_1150_ = v_isSharedCheck_1158_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_val_1147_);
lean_dec(v_x_1144_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1158_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1151_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3));
v___x_1152_ = l_Nat_reprFast(v_val_1147_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 3);
lean_ctor_set(v___x_1149_, 0, v___x_1152_);
v___x_1154_ = v___x_1149_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1151_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Repr_addAppParen(v___x_1155_, v_x_1145_);
return v___x_1156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1___boxed(lean_object* v_x_1159_, lean_object* v_x_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(v_x_1159_, v_x_1160_);
lean_dec(v_x_1160_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_){
_start:
{
if (lean_obj_tag(v_x_1164_) == 0)
{
lean_dec(v_x_1162_);
return v_x_1163_;
}
else
{
lean_object* v_head_1165_; lean_object* v_tail_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1176_; 
v_head_1165_ = lean_ctor_get(v_x_1164_, 0);
v_tail_1166_ = lean_ctor_get(v_x_1164_, 1);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_x_1164_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1168_ = v_x_1164_;
v_isShared_1169_ = v_isSharedCheck_1176_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_tail_1166_);
lean_inc(v_head_1165_);
lean_dec(v_x_1164_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1176_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
lean_inc(v_x_1162_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 5);
lean_ctor_set(v___x_1168_, 1, v_x_1162_);
lean_ctor_set(v___x_1168_, 0, v_x_1163_);
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_x_1163_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_x_1162_);
v___x_1171_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1165_);
v___x_1173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v_x_1163_ = v___x_1173_;
v_x_1164_ = v_tail_1166_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2(lean_object* v_x_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_){
_start:
{
if (lean_obj_tag(v_x_1179_) == 0)
{
lean_dec(v_x_1177_);
return v_x_1178_;
}
else
{
lean_object* v_head_1180_; lean_object* v_tail_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1191_; 
v_head_1180_ = lean_ctor_get(v_x_1179_, 0);
v_tail_1181_ = lean_ctor_get(v_x_1179_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_x_1179_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1183_ = v_x_1179_;
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_tail_1181_);
lean_inc(v_head_1180_);
lean_dec(v_x_1179_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
lean_inc(v_x_1177_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set_tag(v___x_1183_, 5);
lean_ctor_set(v___x_1183_, 1, v_x_1177_);
lean_ctor_set(v___x_1183_, 0, v_x_1178_);
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_x_1178_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_x_1177_);
v___x_1186_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1187_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1180_);
v___x_1188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(v_x_1177_, v___x_1188_, v_tail_1181_);
return v___x_1189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(lean_object* v_x_1192_, lean_object* v_x_1193_){
_start:
{
if (lean_obj_tag(v_x_1192_) == 0)
{
lean_object* v___x_1194_; 
lean_dec(v_x_1193_);
v___x_1194_ = lean_box(0);
return v___x_1194_;
}
else
{
lean_object* v_tail_1195_; 
v_tail_1195_ = lean_ctor_get(v_x_1192_, 1);
if (lean_obj_tag(v_tail_1195_) == 0)
{
lean_object* v_head_1196_; lean_object* v___x_1197_; 
lean_dec(v_x_1193_);
v_head_1196_ = lean_ctor_get(v_x_1192_, 0);
lean_inc(v_head_1196_);
lean_dec_ref_known(v_x_1192_, 2);
v___x_1197_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1196_);
return v___x_1197_;
}
else
{
lean_object* v_head_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_inc(v_tail_1195_);
v_head_1198_ = lean_ctor_get(v_x_1192_, 0);
lean_inc(v_head_1198_);
lean_dec_ref_known(v_x_1192_, 2);
v___x_1199_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1198_);
v___x_1200_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2(v_x_1193_, v___x_1199_, v_tail_1195_);
return v___x_1200_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0));
v___x_1203_ = lean_string_length(v___x_1202_);
return v___x_1203_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1);
v___x_1205_ = lean_nat_to_int(v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0(lean_object* v_xs_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1212_ = lean_array_get_size(v_xs_1211_);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = lean_nat_dec_eq(v___x_1212_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1215_ = lean_array_to_list(v_xs_1211_);
v___x_1216_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__5));
v___x_1217_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(v___x_1215_, v___x_1216_);
v___x_1218_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2);
v___x_1219_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3));
v___x_1220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v___x_1217_);
v___x_1221_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__10));
v___x_1222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1218_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = l_Std_Format_fill(v___x_1223_);
return v___x_1224_;
}
else
{
lean_object* v___x_1225_; 
lean_dec_ref(v_xs_1211_);
v___x_1225_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5));
return v___x_1225_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(lean_object* v_x_1226_, lean_object* v_x_1227_, lean_object* v_x_1228_){
_start:
{
if (lean_obj_tag(v_x_1228_) == 0)
{
lean_dec(v_x_1226_);
return v_x_1227_;
}
else
{
lean_object* v_head_1229_; lean_object* v_tail_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1240_; 
v_head_1229_ = lean_ctor_get(v_x_1228_, 0);
v_tail_1230_ = lean_ctor_get(v_x_1228_, 1);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_x_1228_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1232_ = v_x_1228_;
v_isShared_1233_ = v_isSharedCheck_1240_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_tail_1230_);
lean_inc(v_head_1229_);
lean_dec(v_x_1228_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1240_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
lean_inc(v_x_1226_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set_tag(v___x_1232_, 5);
lean_ctor_set(v___x_1232_, 1, v_x_1226_);
lean_ctor_set(v___x_1232_, 0, v_x_1227_);
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_x_1227_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_x_1226_);
v___x_1235_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1229_);
v___x_1237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v_x_1227_ = v___x_1237_;
v_x_1228_ = v_tail_1230_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5(lean_object* v_x_1241_, lean_object* v_x_1242_, lean_object* v_x_1243_){
_start:
{
if (lean_obj_tag(v_x_1243_) == 0)
{
lean_dec(v_x_1241_);
return v_x_1242_;
}
else
{
lean_object* v_head_1244_; lean_object* v_tail_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1255_; 
v_head_1244_ = lean_ctor_get(v_x_1243_, 0);
v_tail_1245_ = lean_ctor_get(v_x_1243_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_x_1243_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1247_ = v_x_1243_;
v_isShared_1248_ = v_isSharedCheck_1255_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_tail_1245_);
lean_inc(v_head_1244_);
lean_dec(v_x_1243_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1255_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
lean_inc(v_x_1241_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set_tag(v___x_1247_, 5);
lean_ctor_set(v___x_1247_, 1, v_x_1241_);
lean_ctor_set(v___x_1247_, 0, v_x_1242_);
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_x_1242_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_x_1241_);
v___x_1250_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1244_);
v___x_1252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(v_x_1241_, v___x_1252_, v_tail_1245_);
return v___x_1253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
if (lean_obj_tag(v_x_1256_) == 0)
{
lean_object* v___x_1258_; 
lean_dec(v_x_1257_);
v___x_1258_ = lean_box(0);
return v___x_1258_;
}
else
{
lean_object* v_tail_1259_; 
v_tail_1259_ = lean_ctor_get(v_x_1256_, 1);
if (lean_obj_tag(v_tail_1259_) == 0)
{
lean_object* v_head_1260_; lean_object* v___x_1261_; 
lean_dec(v_x_1257_);
v_head_1260_ = lean_ctor_get(v_x_1256_, 0);
lean_inc(v_head_1260_);
lean_dec_ref_known(v_x_1256_, 2);
v___x_1261_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1260_);
return v___x_1261_;
}
else
{
lean_object* v_head_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_inc(v_tail_1259_);
v_head_1262_ = lean_ctor_get(v_x_1256_, 0);
lean_inc(v_head_1262_);
lean_dec_ref_known(v_x_1256_, 2);
v___x_1263_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1262_);
v___x_1264_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5(v_x_1257_, v___x_1263_, v_tail_1259_);
return v___x_1264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(lean_object* v_xs_1265_){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1266_ = lean_array_get_size(v_xs_1265_);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_nat_dec_eq(v___x_1266_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1269_ = lean_array_to_list(v_xs_1265_);
v___x_1270_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__5));
v___x_1271_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(v___x_1269_, v___x_1270_);
v___x_1272_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2);
v___x_1273_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3));
v___x_1274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v___x_1271_);
v___x_1275_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__10));
v___x_1276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1272_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = l_Std_Format_fill(v___x_1277_);
return v___x_1278_;
}
else
{
lean_object* v___x_1279_; 
lean_dec_ref(v_xs_1265_);
v___x_1279_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5));
return v___x_1279_;
}
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_unsigned_to_nat(12u);
v___x_1296_ = lean_nat_to_int(v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_unsigned_to_nat(14u);
v___x_1304_ = lean_nat_to_int(v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(lean_object* v_x_1308_){
_start:
{
lean_object* v_numParams_1309_; lean_object* v_numDiscrs_1310_; lean_object* v_altInfos_1311_; lean_object* v_uElimPos_x3f_1312_; lean_object* v_discrInfos_1313_; lean_object* v_overlaps_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_numParams_1309_ = lean_ctor_get(v_x_1308_, 0);
lean_inc(v_numParams_1309_);
v_numDiscrs_1310_ = lean_ctor_get(v_x_1308_, 1);
lean_inc(v_numDiscrs_1310_);
v_altInfos_1311_ = lean_ctor_get(v_x_1308_, 2);
lean_inc_ref(v_altInfos_1311_);
v_uElimPos_x3f_1312_ = lean_ctor_get(v_x_1308_, 3);
lean_inc(v_uElimPos_x3f_1312_);
v_discrInfos_1313_ = lean_ctor_get(v_x_1308_, 4);
lean_inc_ref(v_discrInfos_1313_);
v_overlaps_1314_ = lean_ctor_get(v_x_1308_, 5);
lean_inc_ref(v_overlaps_1314_);
lean_dec_ref(v_x_1308_);
v___x_1315_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5));
v___x_1316_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3));
v___x_1317_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4);
v___x_1318_ = l_Nat_reprFast(v_numParams_1309_);
v___x_1319_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1317_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = 0;
v___x_1322_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*1, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1316_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1_spec__1_spec__3___redArg___closed__4));
v___x_1325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1323_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = lean_box(1);
v___x_1327_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1325_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5));
v___x_1329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v___x_1315_);
v___x_1331_ = l_Nat_reprFast(v_numDiscrs_1310_);
v___x_1332_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
v___x_1333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1317_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set_uint8(v___x_1334_, sizeof(void*)*1, v___x_1321_);
v___x_1335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1330_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
lean_ctor_set(v___x_1336_, 1, v___x_1324_);
v___x_1337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v___x_1326_);
v___x_1338_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7));
v___x_1339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set(v___x_1340_, 1, v___x_1315_);
v___x_1341_ = lean_obj_once(&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8, &l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8_once, _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8);
v___x_1342_ = l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0(v_altInfos_1311_);
v___x_1343_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v___x_1344_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*1, v___x_1321_);
v___x_1345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1340_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v___x_1324_);
v___x_1347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v___x_1326_);
v___x_1348_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10));
v___x_1349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v___x_1315_);
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(v_uElimPos_x3f_1312_, v___x_1351_);
v___x_1353_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1317_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*1, v___x_1321_);
v___x_1355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1350_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
lean_ctor_set(v___x_1356_, 1, v___x_1324_);
v___x_1357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v___x_1326_);
v___x_1358_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12));
v___x_1359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v___x_1315_);
v___x_1361_ = lean_obj_once(&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13, &l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13_once, _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13);
v___x_1362_ = l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(v_discrInfos_1313_);
v___x_1363_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*1, v___x_1321_);
v___x_1365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1360_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v___x_1324_);
v___x_1367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
lean_ctor_set(v___x_1367_, 1, v___x_1326_);
v___x_1368_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15));
v___x_1369_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1367_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
lean_ctor_set(v___x_1370_, 1, v___x_1315_);
v___x_1371_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg(v_overlaps_1314_);
lean_dec_ref(v_overlaps_1314_);
v___x_1372_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1341_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*1, v___x_1321_);
v___x_1374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1370_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_1376_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_1377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
lean_ctor_set(v___x_1377_, 1, v___x_1374_);
v___x_1378_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_1379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1375_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1381_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
lean_ctor_set_uint8(v___x_1381_, sizeof(void*)*1, v___x_1321_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr(lean_object* v_x_1382_, lean_object* v_prec_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(v_x_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___boxed(lean_object* v_x_1385_, lean_object* v_prec_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Meta_Match_instReprMatcherInfo_repr(v_x_1385_, v_prec_1386_);
lean_dec(v_prec_1386_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object* v_info_1390_){
_start:
{
lean_object* v_altInfos_1391_; lean_object* v___x_1392_; 
v_altInfos_1391_ = lean_ctor_get(v_info_1390_, 2);
v___x_1392_ = lean_array_get_size(v_altInfos_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts___boxed(lean_object* v_info_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_1393_);
lean_dec_ref(v_info_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object* v_info_1395_){
_start:
{
lean_object* v_numParams_1396_; lean_object* v_numDiscrs_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v_numParams_1396_ = lean_ctor_get(v_info_1395_, 0);
v_numDiscrs_1397_ = lean_ctor_get(v_info_1395_, 1);
v___x_1398_ = lean_unsigned_to_nat(1u);
v___x_1399_ = lean_nat_add(v_numParams_1396_, v___x_1398_);
v___x_1400_ = lean_nat_add(v___x_1399_, v_numDiscrs_1397_);
lean_dec(v___x_1399_);
v___x_1401_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_1395_);
v___x_1402_ = lean_nat_add(v___x_1400_, v___x_1401_);
lean_dec(v___x_1401_);
lean_dec(v___x_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_arity___boxed(lean_object* v_info_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Meta_Match_MatcherInfo_arity(v_info_1403_);
lean_dec_ref(v_info_1403_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object* v_info_1405_){
_start:
{
lean_object* v_numParams_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_numParams_1406_ = lean_ctor_get(v_info_1405_, 0);
v___x_1407_ = lean_unsigned_to_nat(1u);
v___x_1408_ = lean_nat_add(v_numParams_1406_, v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos___boxed(lean_object* v_info_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_info_1409_);
lean_dec_ref(v_info_1409_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getDiscrRange(lean_object* v_info_1411_){
_start:
{
lean_object* v_numDiscrs_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_numDiscrs_1412_ = lean_ctor_get(v_info_1411_, 1);
v___x_1413_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_info_1411_);
v___x_1414_ = lean_nat_add(v___x_1413_, v_numDiscrs_1412_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getDiscrRange___boxed(lean_object* v_info_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Meta_Match_MatcherInfo_getDiscrRange(v_info_1416_);
lean_dec_ref(v_info_1416_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(lean_object* v_info_1418_){
_start:
{
lean_object* v_numParams_1419_; lean_object* v_numDiscrs_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v_numParams_1419_ = lean_ctor_get(v_info_1418_, 0);
v_numDiscrs_1420_ = lean_ctor_get(v_info_1418_, 1);
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = lean_nat_add(v_numParams_1419_, v___x_1421_);
v___x_1423_ = lean_nat_add(v___x_1422_, v_numDiscrs_1420_);
lean_dec(v___x_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos___boxed(lean_object* v_info_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_info_1424_);
lean_dec_ref(v_info_1424_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getAltRange(lean_object* v_info_1426_){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1427_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_info_1426_);
v___x_1428_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_1426_);
v___x_1429_ = lean_nat_add(v___x_1427_, v___x_1428_);
lean_dec(v___x_1428_);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1427_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getAltRange___boxed(lean_object* v_info_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Meta_Match_MatcherInfo_getAltRange(v_info_1431_);
lean_dec_ref(v_info_1431_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object* v_info_1433_){
_start:
{
lean_object* v_numParams_1434_; 
v_numParams_1434_ = lean_ctor_get(v_info_1433_, 0);
lean_inc(v_numParams_1434_);
return v_numParams_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos___boxed(lean_object* v_info_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_info_1435_);
lean_dec_ref(v_info_1435_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(lean_object* v_as_1437_, size_t v_sz_1438_, size_t v_i_1439_, lean_object* v_b_1440_){
_start:
{
lean_object* v_a_1442_; uint8_t v___x_1446_; 
v___x_1446_ = lean_usize_dec_lt(v_i_1439_, v_sz_1438_);
if (v___x_1446_ == 0)
{
return v_b_1440_;
}
else
{
lean_object* v_a_1447_; 
v_a_1447_ = lean_array_uget_borrowed(v_as_1437_, v_i_1439_);
if (lean_obj_tag(v_a_1447_) == 0)
{
v_a_1442_ = v_b_1440_;
goto v___jp_1441_;
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_nat_add(v_b_1440_, v___x_1448_);
lean_dec(v_b_1440_);
v_a_1442_ = v___x_1449_;
goto v___jp_1441_;
}
}
v___jp_1441_:
{
size_t v___x_1443_; size_t v___x_1444_; 
v___x_1443_ = ((size_t)1ULL);
v___x_1444_ = lean_usize_add(v_i_1439_, v___x_1443_);
v_i_1439_ = v___x_1444_;
v_b_1440_ = v_a_1442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0___boxed(lean_object* v_as_1450_, lean_object* v_sz_1451_, lean_object* v_i_1452_, lean_object* v_b_1453_){
_start:
{
size_t v_sz_boxed_1454_; size_t v_i_boxed_1455_; lean_object* v_res_1456_; 
v_sz_boxed_1454_ = lean_unbox_usize(v_sz_1451_);
lean_dec(v_sz_1451_);
v_i_boxed_1455_ = lean_unbox_usize(v_i_1452_);
lean_dec(v_i_1452_);
v_res_1456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(v_as_1450_, v_sz_boxed_1454_, v_i_boxed_1455_, v_b_1453_);
lean_dec_ref(v_as_1450_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getNumEqsFromDiscrInfos(lean_object* v_infos_1457_){
_start:
{
lean_object* v_r_1458_; size_t v_sz_1459_; size_t v___x_1460_; lean_object* v___x_1461_; 
v_r_1458_ = lean_unsigned_to_nat(0u);
v_sz_1459_ = lean_array_size(v_infos_1457_);
v___x_1460_ = ((size_t)0ULL);
v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(v_infos_1457_, v_sz_1459_, v___x_1460_, v_r_1458_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getNumEqsFromDiscrInfos___boxed(lean_object* v_infos_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_infos_1462_);
lean_dec_ref(v_infos_1462_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object* v_info_1464_){
_start:
{
lean_object* v_discrInfos_1465_; lean_object* v___x_1466_; 
v_discrInfos_1465_ = lean_ctor_get(v_info_1464_, 4);
v___x_1466_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs___boxed(lean_object* v_info_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_info_1467_);
lean_dec_ref(v_info_1467_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(lean_object* v_info_1469_, size_t v_sz_1470_, size_t v_i_1471_, lean_object* v_bs_1472_){
_start:
{
uint8_t v___x_1473_; 
v___x_1473_ = lean_usize_dec_lt(v_i_1471_, v_sz_1470_);
if (v___x_1473_ == 0)
{
return v_bs_1472_;
}
else
{
lean_object* v_v_1474_; lean_object* v_numFields_1475_; lean_object* v_numOverlaps_1476_; uint8_t v_hasUnitThunk_1477_; lean_object* v___x_1478_; lean_object* v_bs_x27_1479_; lean_object* v___x_1480_; lean_object* v___y_1482_; 
v_v_1474_ = lean_array_uget_borrowed(v_bs_1472_, v_i_1471_);
v_numFields_1475_ = lean_ctor_get(v_v_1474_, 0);
lean_inc(v_numFields_1475_);
v_numOverlaps_1476_ = lean_ctor_get(v_v_1474_, 1);
lean_inc(v_numOverlaps_1476_);
v_hasUnitThunk_1477_ = lean_ctor_get_uint8(v_v_1474_, sizeof(void*)*2);
v___x_1478_ = lean_unsigned_to_nat(0u);
v_bs_x27_1479_ = lean_array_uset(v_bs_1472_, v_i_1471_, v___x_1478_);
v___x_1480_ = lean_nat_add(v_numFields_1475_, v_numOverlaps_1476_);
lean_dec(v_numOverlaps_1476_);
lean_dec(v_numFields_1475_);
if (v_hasUnitThunk_1477_ == 0)
{
v___y_1482_ = v___x_1478_;
goto v___jp_1481_;
}
else
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_unsigned_to_nat(1u);
v___y_1482_ = v___x_1490_;
goto v___jp_1481_;
}
v___jp_1481_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; size_t v___x_1486_; size_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1483_ = lean_nat_add(v___x_1480_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec(v___x_1480_);
v___x_1484_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_info_1469_);
v___x_1485_ = lean_nat_add(v___x_1483_, v___x_1484_);
lean_dec(v___x_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = ((size_t)1ULL);
v___x_1487_ = lean_usize_add(v_i_1471_, v___x_1486_);
v___x_1488_ = lean_array_uset(v_bs_x27_1479_, v_i_1471_, v___x_1485_);
v_i_1471_ = v___x_1487_;
v_bs_1472_ = v___x_1488_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0___boxed(lean_object* v_info_1491_, lean_object* v_sz_1492_, lean_object* v_i_1493_, lean_object* v_bs_1494_){
_start:
{
size_t v_sz_boxed_1495_; size_t v_i_boxed_1496_; lean_object* v_res_1497_; 
v_sz_boxed_1495_ = lean_unbox_usize(v_sz_1492_);
lean_dec(v_sz_1492_);
v_i_boxed_1496_ = lean_unbox_usize(v_i_1493_);
lean_dec(v_i_1493_);
v_res_1497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(v_info_1491_, v_sz_boxed_1495_, v_i_boxed_1496_, v_bs_1494_);
lean_dec_ref(v_info_1491_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_altNumParams(lean_object* v_info_1498_){
_start:
{
lean_object* v_altInfos_1499_; size_t v_sz_1500_; size_t v___x_1501_; lean_object* v___x_1502_; 
v_altInfos_1499_ = lean_ctor_get(v_info_1498_, 2);
lean_inc_ref(v_altInfos_1499_);
v_sz_1500_ = lean_array_size(v_altInfos_1499_);
v___x_1501_ = ((size_t)0ULL);
v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(v_info_1498_, v_sz_1500_, v___x_1501_, v_altInfos_1499_);
lean_dec_ref(v_info_1498_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__0(void){
_start:
{
lean_object* v_cellCount_1503_; lean_object* v___x_1504_; 
v_cellCount_1503_ = lean_unsigned_to_nat(16u);
v___x_1504_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__1(void){
_start:
{
lean_object* v_cellCount_1505_; lean_object* v___x_1506_; 
v_cellCount_1505_ = lean_unsigned_to_nat(16u);
v___x_1506_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1505_);
return v___x_1506_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__2(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1507_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__1, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__1_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__1);
v___x_1508_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__0, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__0_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__0);
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v___x_1508_);
lean_ctor_set(v___x_1510_, 2, v___x_1507_);
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__3(void){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1511_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__3, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__3_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__3);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__5(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; 
v___x_1514_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__4, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4);
v___x_1515_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__2, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__2_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__2);
v___x_1516_ = 1;
v___x_1517_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1517_, 0, v___x_1515_);
lean_ctor_set(v___x_1517_, 1, v___x_1514_);
lean_ctor_set_uint8(v___x_1517_, sizeof(void*)*2, v___x_1516_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState(void){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__5, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__5_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__5);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_m_1519_, lean_object* v_query_1520_, lean_object* v_x_1521_, lean_object* v_x_1522_, lean_object* v_x_1523_){
_start:
{
lean_object* v_zero_1524_; uint8_t v_isZero_1525_; 
v_zero_1524_ = lean_unsigned_to_nat(0u);
v_isZero_1525_ = lean_nat_dec_eq(v_x_1522_, v_zero_1524_);
if (v_isZero_1525_ == 1)
{
lean_dec(v_x_1523_);
lean_dec(v_x_1522_);
if (lean_obj_tag(v_x_1521_) == 0)
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_box(2);
return v___x_1526_;
}
else
{
lean_object* v_val_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
v_val_1527_ = lean_ctor_get(v_x_1521_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_x_1521_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v_x_1521_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_val_1527_);
lean_dec(v_x_1521_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_val_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_object* v_keyArray_1535_; lean_object* v_valueArray_1536_; lean_object* v___x_1537_; uint8_t v_isSome_1538_; 
v_keyArray_1535_ = lean_ctor_get(v_m_1519_, 1);
v_valueArray_1536_ = lean_ctor_get(v_m_1519_, 2);
v___x_1537_ = lean_array_fget_borrowed(v_keyArray_1535_, v_x_1523_);
v_isSome_1538_ = lean_noption_is_some(v___x_1537_);
if (v_isSome_1538_ == 0)
{
lean_dec(v_x_1522_);
if (lean_obj_tag(v_x_1521_) == 0)
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1539_, 0, v_x_1523_);
return v___x_1539_;
}
else
{
lean_object* v_val_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec(v_x_1523_);
v_val_1540_ = lean_ctor_get(v_x_1521_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_x_1521_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v_x_1521_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_val_1540_);
lean_dec(v_x_1521_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_val_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
lean_object* v_one_1548_; lean_object* v_n_1549_; lean_object* v___y_1551_; 
v_one_1548_ = lean_unsigned_to_nat(1u);
v_n_1549_ = lean_nat_sub(v_x_1522_, v_one_1548_);
lean_dec(v_x_1522_);
if (v_isSome_1538_ == 0)
{
goto v___jp_1557_;
}
else
{
lean_object* v___x_1559_; uint8_t v_isSome_1560_; 
v___x_1559_ = lean_array_fget_borrowed(v_valueArray_1536_, v_x_1523_);
v_isSome_1560_ = lean_noption_is_some(v___x_1559_);
if (v_isSome_1560_ == 0)
{
goto v___jp_1557_;
}
else
{
lean_object* v_val_1561_; uint8_t v___x_1562_; 
lean_inc(v___x_1537_);
v_val_1561_ = lean_noption_get(v___x_1537_);
v___x_1562_ = lean_name_eq(v_val_1561_, v_query_1520_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
lean_dec(v_val_1561_);
v___x_1563_ = lean_array_get_size(v_keyArray_1535_);
v___x_1564_ = lean_nat_add(v_x_1523_, v_one_1548_);
lean_dec(v_x_1523_);
v___x_1565_ = lean_nat_dec_lt(v___x_1564_, v___x_1563_);
if (v___x_1565_ == 0)
{
lean_dec(v___x_1564_);
v_x_1522_ = v_n_1549_;
v_x_1523_ = v_zero_1524_;
goto _start;
}
else
{
v_x_1522_ = v_n_1549_;
v_x_1523_ = v___x_1564_;
goto _start;
}
}
else
{
lean_object* v_val_1568_; lean_object* v___x_1569_; 
lean_dec(v_n_1549_);
lean_dec(v_x_1521_);
lean_inc(v___x_1559_);
v_val_1568_ = lean_noption_get(v___x_1559_);
v___x_1569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1569_, 0, v_x_1523_);
lean_ctor_set(v___x_1569_, 1, v_val_1561_);
lean_ctor_set(v___x_1569_, 2, v_val_1568_);
return v___x_1569_;
}
}
}
v___jp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1552_ = lean_array_get_size(v_keyArray_1535_);
v___x_1553_ = lean_nat_add(v_x_1523_, v_one_1548_);
lean_dec(v_x_1523_);
v___x_1554_ = lean_nat_dec_lt(v___x_1553_, v___x_1552_);
if (v___x_1554_ == 0)
{
lean_dec(v___x_1553_);
v_x_1521_ = v___y_1551_;
v_x_1522_ = v_n_1549_;
v_x_1523_ = v_zero_1524_;
goto _start;
}
else
{
v_x_1521_ = v___y_1551_;
v_x_1522_ = v_n_1549_;
v_x_1523_ = v___x_1553_;
goto _start;
}
}
v___jp_1557_:
{
if (lean_obj_tag(v_x_1521_) == 0)
{
lean_object* v___x_1558_; 
lean_inc(v_x_1523_);
v___x_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_x_1523_);
v___y_1551_ = v___x_1558_;
goto v___jp_1550_;
}
else
{
v___y_1551_ = v_x_1521_;
goto v___jp_1550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_1570_, lean_object* v_query_1571_, lean_object* v_x_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_m_1570_, v_query_1571_, v_x_1572_, v_x_1573_, v_x_1574_);
lean_dec(v_query_1571_);
lean_dec_ref(v_m_1570_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(lean_object* v_m_1576_, lean_object* v_query_1577_){
_start:
{
lean_object* v_keyArray_1578_; lean_object* v___x_1579_; uint64_t v___y_1581_; 
v_keyArray_1578_ = lean_ctor_get(v_m_1576_, 1);
v___x_1579_ = lean_array_get_size(v_keyArray_1578_);
if (lean_obj_tag(v_query_1577_) == 0)
{
uint64_t v___x_1596_; 
v___x_1596_ = 1723ULL;
v___y_1581_ = v___x_1596_;
goto v___jp_1580_;
}
else
{
uint64_t v_hash_1597_; 
v_hash_1597_ = lean_ctor_get_uint64(v_query_1577_, sizeof(void*)*2);
v___y_1581_ = v_hash_1597_;
goto v___jp_1580_;
}
v___jp_1580_:
{
uint64_t v___x_1582_; uint64_t v___x_1583_; uint64_t v_fold_1584_; uint64_t v___x_1585_; uint64_t v___x_1586_; uint64_t v___x_1587_; size_t v___x_1588_; size_t v___x_1589_; size_t v___x_1590_; size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1582_ = 32ULL;
v___x_1583_ = lean_uint64_shift_right(v___y_1581_, v___x_1582_);
v_fold_1584_ = lean_uint64_xor(v___y_1581_, v___x_1583_);
v___x_1585_ = 16ULL;
v___x_1586_ = lean_uint64_shift_right(v_fold_1584_, v___x_1585_);
v___x_1587_ = lean_uint64_xor(v_fold_1584_, v___x_1586_);
v___x_1588_ = lean_uint64_to_usize(v___x_1587_);
v___x_1589_ = lean_usize_of_nat(v___x_1579_);
v___x_1590_ = ((size_t)1ULL);
v___x_1591_ = lean_usize_sub(v___x_1589_, v___x_1590_);
v___x_1592_ = lean_usize_land(v___x_1588_, v___x_1591_);
v___x_1593_ = lean_usize_to_nat(v___x_1592_);
v___x_1594_ = lean_box(0);
v___x_1595_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_m_1576_, v_query_1577_, v___x_1594_, v___x_1579_, v___x_1593_);
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg___boxed(lean_object* v_m_1598_, lean_object* v_query_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_m_1598_, v_query_1599_);
lean_dec(v_query_1599_);
lean_dec_ref(v_m_1598_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5_spec__8___redArg(lean_object* v_b_1601_, lean_object* v_acc_1602_, lean_object* v_i_1603_){
_start:
{
lean_object* v___y_1605_; lean_object* v_keyArray_1613_; lean_object* v_valueArray_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v_keyArray_1613_ = lean_ctor_get(v_b_1601_, 1);
v_valueArray_1614_ = lean_ctor_get(v_b_1601_, 2);
v___x_1615_ = lean_array_get_size(v_keyArray_1613_);
v___x_1616_ = lean_nat_dec_lt(v_i_1603_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_dec(v_i_1603_);
return v_acc_1602_;
}
else
{
lean_object* v___x_1617_; uint8_t v_isSome_1618_; 
v___x_1617_ = lean_array_fget_borrowed(v_keyArray_1613_, v_i_1603_);
v_isSome_1618_ = lean_noption_is_some(v___x_1617_);
if (v_isSome_1618_ == 0)
{
goto v___jp_1609_;
}
else
{
lean_object* v___x_1619_; uint8_t v_isSome_1620_; 
v___x_1619_ = lean_array_fget_borrowed(v_valueArray_1614_, v_i_1603_);
v_isSome_1620_ = lean_noption_is_some(v___x_1619_);
if (v_isSome_1620_ == 0)
{
goto v___jp_1609_;
}
else
{
lean_object* v_val_1621_; lean_object* v_val_1622_; lean_object* v_i_1624_; lean_object* v___x_1629_; 
lean_inc(v___x_1617_);
v_val_1621_ = lean_noption_get(v___x_1617_);
lean_inc(v___x_1619_);
v_val_1622_ = lean_noption_get(v___x_1619_);
v___x_1629_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_acc_1602_, v_val_1621_);
switch(lean_obj_tag(v___x_1629_))
{
case 0:
{
lean_object* v_index_1630_; lean_object* v_size_1631_; lean_object* v___x_1632_; 
v_index_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_index_1630_);
lean_dec_ref_known(v___x_1629_, 3);
v_size_1631_ = lean_ctor_get(v_acc_1602_, 0);
lean_inc(v_size_1631_);
v___x_1632_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1602_, v_size_1631_, v_index_1630_, v_val_1621_, v_val_1622_);
lean_dec(v_index_1630_);
v___y_1605_ = v___x_1632_;
goto v___jp_1604_;
}
case 1:
{
lean_object* v_index_1633_; 
v_index_1633_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_index_1633_);
lean_dec_ref_known(v___x_1629_, 1);
v_i_1624_ = v_index_1633_;
goto v___jp_1623_;
}
default: 
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1602_, v___x_1634_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_index_1636_; 
v_index_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_index_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v_i_1624_ = v_index_1636_;
goto v___jp_1623_;
}
else
{
lean_dec(v_val_1622_);
lean_dec(v_val_1621_);
v___y_1605_ = v_acc_1602_;
goto v___jp_1604_;
}
}
}
v___jp_1623_:
{
lean_object* v_size_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_size_1625_ = lean_ctor_get(v_acc_1602_, 0);
v___x_1626_ = lean_unsigned_to_nat(1u);
v___x_1627_ = lean_nat_add(v_size_1625_, v___x_1626_);
v___x_1628_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1602_, v___x_1627_, v_i_1624_, v_val_1621_, v_val_1622_);
lean_dec(v_i_1624_);
v___y_1605_ = v___x_1628_;
goto v___jp_1604_;
}
}
}
}
v___jp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = lean_unsigned_to_nat(1u);
v___x_1607_ = lean_nat_add(v_i_1603_, v___x_1606_);
lean_dec(v_i_1603_);
v_acc_1602_ = v___y_1605_;
v_i_1603_ = v___x_1607_;
goto _start;
}
v___jp_1609_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_unsigned_to_nat(1u);
v___x_1611_ = lean_nat_add(v_i_1603_, v___x_1610_);
lean_dec(v_i_1603_);
v_i_1603_ = v___x_1611_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_b_1637_, lean_object* v_acc_1638_, lean_object* v_i_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5_spec__8___redArg(v_b_1637_, v_acc_1638_, v_i_1639_);
lean_dec_ref(v_b_1637_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5___redArg(lean_object* v_init_1641_, lean_object* v_b_1642_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_unsigned_to_nat(0u);
v___x_1644_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5_spec__8___redArg(v_b_1642_, v_init_1641_, v___x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_init_1645_, lean_object* v_b_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5___redArg(v_init_1645_, v_b_1646_);
lean_dec_ref(v_b_1646_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2___redArg(lean_object* v_m_1648_){
_start:
{
lean_object* v_keyArray_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v_cellCount_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v_target_1656_; lean_object* v___x_1657_; 
v_keyArray_1649_ = lean_ctor_get(v_m_1648_, 1);
v___x_1650_ = lean_array_get_size(v_keyArray_1649_);
v___x_1651_ = lean_unsigned_to_nat(2u);
v_cellCount_1652_ = lean_nat_mul(v___x_1650_, v___x_1651_);
v___x_1653_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1652_);
v___x_1654_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1652_);
v___x_1655_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1652_);
v_target_1656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1656_, 0, v___x_1653_);
lean_ctor_set(v_target_1656_, 1, v___x_1654_);
lean_ctor_set(v_target_1656_, 2, v___x_1655_);
v___x_1657_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5___redArg(v_target_1656_, v_m_1648_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2___redArg___boxed(lean_object* v_m_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2___redArg(v_m_1658_);
lean_dec_ref(v_m_1658_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_){
_start:
{
lean_object* v_ks_1664_; lean_object* v_vs_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1689_; 
v_ks_1664_ = lean_ctor_get(v_x_1660_, 0);
v_vs_1665_ = lean_ctor_get(v_x_1660_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_x_1660_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1667_ = v_x_1660_;
v_isShared_1668_ = v_isSharedCheck_1689_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_vs_1665_);
lean_inc(v_ks_1664_);
lean_dec(v_x_1660_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1689_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = lean_array_get_size(v_ks_1664_);
v___x_1670_ = lean_nat_dec_lt(v_x_1661_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
lean_dec(v_x_1661_);
v___x_1671_ = lean_array_push(v_ks_1664_, v_x_1662_);
v___x_1672_ = lean_array_push(v_vs_1665_, v_x_1663_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 1, v___x_1672_);
lean_ctor_set(v___x_1667_, 0, v___x_1671_);
v___x_1674_ = v___x_1667_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
else
{
lean_object* v_k_x27_1676_; uint8_t v___x_1677_; 
v_k_x27_1676_ = lean_array_fget_borrowed(v_ks_1664_, v_x_1661_);
v___x_1677_ = lean_name_eq(v_x_1662_, v_k_x27_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1679_; 
if (v_isShared_1668_ == 0)
{
v___x_1679_ = v___x_1667_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_ks_1664_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_vs_1665_);
v___x_1679_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_unsigned_to_nat(1u);
v___x_1681_ = lean_nat_add(v_x_1661_, v___x_1680_);
lean_dec(v_x_1661_);
v_x_1660_ = v___x_1679_;
v_x_1661_ = v___x_1681_;
goto _start;
}
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1684_ = lean_array_fset(v_ks_1664_, v_x_1661_, v_x_1662_);
v___x_1685_ = lean_array_fset(v_vs_1665_, v_x_1661_, v_x_1663_);
lean_dec(v_x_1661_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 1, v___x_1685_);
lean_ctor_set(v___x_1667_, 0, v___x_1684_);
v___x_1687_ = v___x_1667_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_n_1690_, lean_object* v_k_1691_, lean_object* v_v_1692_){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_unsigned_to_nat(0u);
v___x_1694_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(v_n_1690_, v___x_1693_, v_k_1691_, v_v_1692_);
return v___x_1694_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1696_, size_t v_x_1697_, size_t v_x_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
lean_object* v_es_1701_; size_t v___x_1702_; size_t v___x_1703_; lean_object* v_j_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v_es_1701_ = lean_ctor_get(v_x_1696_, 0);
v___x_1702_ = ((size_t)31ULL);
v___x_1703_ = lean_usize_land(v_x_1697_, v___x_1702_);
v_j_1704_ = lean_usize_to_nat(v___x_1703_);
v___x_1705_ = lean_array_get_size(v_es_1701_);
v___x_1706_ = lean_nat_dec_lt(v_j_1704_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_dec(v_j_1704_);
lean_dec(v_x_1700_);
lean_dec(v_x_1699_);
return v_x_1696_;
}
else
{
lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1745_; 
lean_inc_ref(v_es_1701_);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_x_1696_);
if (v_isSharedCheck_1745_ == 0)
{
lean_object* v_unused_1746_; 
v_unused_1746_ = lean_ctor_get(v_x_1696_, 0);
lean_dec(v_unused_1746_);
v___x_1708_ = v_x_1696_;
v_isShared_1709_ = v_isSharedCheck_1745_;
goto v_resetjp_1707_;
}
else
{
lean_dec(v_x_1696_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1745_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v_v_1710_; lean_object* v___x_1711_; lean_object* v_xs_x27_1712_; lean_object* v___y_1714_; 
v_v_1710_ = lean_array_fget(v_es_1701_, v_j_1704_);
v___x_1711_ = lean_box(0);
v_xs_x27_1712_ = lean_array_fset(v_es_1701_, v_j_1704_, v___x_1711_);
switch(lean_obj_tag(v_v_1710_))
{
case 0:
{
lean_object* v_key_1719_; lean_object* v_val_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1730_; 
v_key_1719_ = lean_ctor_get(v_v_1710_, 0);
v_val_1720_ = lean_ctor_get(v_v_1710_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_v_1710_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1722_ = v_v_1710_;
v_isShared_1723_ = v_isSharedCheck_1730_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_val_1720_);
lean_inc(v_key_1719_);
lean_dec(v_v_1710_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1730_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_name_eq(v_x_1699_, v_key_1719_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
lean_del_object(v___x_1722_);
v___x_1725_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1719_, v_val_1720_, v_x_1699_, v_x_1700_);
v___x_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
v___y_1714_ = v___x_1726_;
goto v___jp_1713_;
}
else
{
lean_object* v___x_1728_; 
lean_dec(v_val_1720_);
lean_dec(v_key_1719_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 1, v_x_1700_);
lean_ctor_set(v___x_1722_, 0, v_x_1699_);
v___x_1728_ = v___x_1722_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_x_1700_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
v___y_1714_ = v___x_1728_;
goto v___jp_1713_;
}
}
}
}
case 1:
{
lean_object* v_node_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1743_; 
v_node_1731_ = lean_ctor_get(v_v_1710_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_v_1710_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1733_ = v_v_1710_;
v_isShared_1734_ = v_isSharedCheck_1743_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_node_1731_);
lean_dec(v_v_1710_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1743_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
size_t v___x_1735_; size_t v___x_1736_; size_t v___x_1737_; size_t v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1735_ = ((size_t)5ULL);
v___x_1736_ = lean_usize_shift_right(v_x_1697_, v___x_1735_);
v___x_1737_ = ((size_t)1ULL);
v___x_1738_ = lean_usize_add(v_x_1698_, v___x_1737_);
v___x_1739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_node_1731_, v___x_1736_, v___x_1738_, v_x_1699_, v_x_1700_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1739_);
v___x_1741_ = v___x_1733_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
v___y_1714_ = v___x_1741_;
goto v___jp_1713_;
}
}
}
default: 
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v_x_1699_);
lean_ctor_set(v___x_1744_, 1, v_x_1700_);
v___y_1714_ = v___x_1744_;
goto v___jp_1713_;
}
}
v___jp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1715_ = lean_array_fset(v_xs_x27_1712_, v_j_1704_, v___y_1714_);
lean_dec(v_j_1704_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1715_);
v___x_1717_ = v___x_1708_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
else
{
lean_object* v_ks_1747_; lean_object* v_vs_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1768_; 
v_ks_1747_ = lean_ctor_get(v_x_1696_, 0);
v_vs_1748_ = lean_ctor_get(v_x_1696_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_x_1696_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1750_ = v_x_1696_;
v_isShared_1751_ = v_isSharedCheck_1768_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_vs_1748_);
lean_inc(v_ks_1747_);
lean_dec(v_x_1696_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1768_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_ks_1747_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_vs_1748_);
v___x_1753_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v_newNode_1754_; uint8_t v___y_1756_; size_t v___x_1762_; uint8_t v___x_1763_; 
v_newNode_1754_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__4___redArg(v___x_1753_, v_x_1699_, v_x_1700_);
v___x_1762_ = ((size_t)7ULL);
v___x_1763_ = lean_usize_dec_le(v___x_1762_, v_x_1698_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1764_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1754_);
v___x_1765_ = lean_unsigned_to_nat(4u);
v___x_1766_ = lean_nat_dec_lt(v___x_1764_, v___x_1765_);
lean_dec(v___x_1764_);
v___y_1756_ = v___x_1766_;
goto v___jp_1755_;
}
else
{
v___y_1756_ = v___x_1763_;
goto v___jp_1755_;
}
v___jp_1755_:
{
if (v___y_1756_ == 0)
{
lean_object* v_ks_1757_; lean_object* v_vs_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_ks_1757_ = lean_ctor_get(v_newNode_1754_, 0);
lean_inc_ref(v_ks_1757_);
v_vs_1758_ = lean_ctor_get(v_newNode_1754_, 1);
lean_inc_ref(v_vs_1758_);
lean_dec_ref(v_newNode_1754_);
v___x_1759_ = lean_unsigned_to_nat(0u);
v___x_1760_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1761_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__5___redArg(v_x_1698_, v_ks_1757_, v_vs_1758_, v___x_1759_, v___x_1760_);
lean_dec_ref(v_vs_1758_);
lean_dec_ref(v_ks_1757_);
return v___x_1761_;
}
else
{
return v_newNode_1754_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__5___redArg(size_t v_depth_1769_, lean_object* v_keys_1770_, lean_object* v_vals_1771_, lean_object* v_i_1772_, lean_object* v_entries_1773_){
_start:
{
lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = lean_array_get_size(v_keys_1770_);
v___x_1775_ = lean_nat_dec_lt(v_i_1772_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_dec(v_i_1772_);
return v_entries_1773_;
}
else
{
lean_object* v_k_1776_; lean_object* v_v_1777_; uint64_t v___y_1779_; 
v_k_1776_ = lean_array_fget_borrowed(v_keys_1770_, v_i_1772_);
v_v_1777_ = lean_array_fget_borrowed(v_vals_1771_, v_i_1772_);
if (lean_obj_tag(v_k_1776_) == 0)
{
uint64_t v___x_1790_; 
v___x_1790_ = 1723ULL;
v___y_1779_ = v___x_1790_;
goto v___jp_1778_;
}
else
{
uint64_t v_hash_1791_; 
v_hash_1791_ = lean_ctor_get_uint64(v_k_1776_, sizeof(void*)*2);
v___y_1779_ = v_hash_1791_;
goto v___jp_1778_;
}
v___jp_1778_:
{
size_t v_h_1780_; size_t v___x_1781_; lean_object* v___x_1782_; size_t v___x_1783_; size_t v___x_1784_; size_t v___x_1785_; size_t v_h_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_h_1780_ = lean_uint64_to_usize(v___y_1779_);
v___x_1781_ = ((size_t)5ULL);
v___x_1782_ = lean_unsigned_to_nat(1u);
v___x_1783_ = ((size_t)1ULL);
v___x_1784_ = lean_usize_sub(v_depth_1769_, v___x_1783_);
v___x_1785_ = lean_usize_mul(v___x_1781_, v___x_1784_);
v_h_1786_ = lean_usize_shift_right(v_h_1780_, v___x_1785_);
v___x_1787_ = lean_nat_add(v_i_1772_, v___x_1782_);
lean_dec(v_i_1772_);
lean_inc(v_v_1777_);
lean_inc(v_k_1776_);
v___x_1788_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_entries_1773_, v_h_1786_, v_depth_1769_, v_k_1776_, v_v_1777_);
v_i_1772_ = v___x_1787_;
v_entries_1773_ = v___x_1788_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_1792_, lean_object* v_keys_1793_, lean_object* v_vals_1794_, lean_object* v_i_1795_, lean_object* v_entries_1796_){
_start:
{
size_t v_depth_boxed_1797_; lean_object* v_res_1798_; 
v_depth_boxed_1797_ = lean_unbox_usize(v_depth_1792_);
lean_dec(v_depth_1792_);
v_res_1798_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__5___redArg(v_depth_boxed_1797_, v_keys_1793_, v_vals_1794_, v_i_1795_, v_entries_1796_);
lean_dec_ref(v_vals_1794_);
lean_dec_ref(v_keys_1793_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1799_, lean_object* v_x_1800_, lean_object* v_x_1801_, lean_object* v_x_1802_, lean_object* v_x_1803_){
_start:
{
size_t v_x_1281__boxed_1804_; size_t v_x_1282__boxed_1805_; lean_object* v_res_1806_; 
v_x_1281__boxed_1804_ = lean_unbox_usize(v_x_1800_);
lean_dec(v_x_1800_);
v_x_1282__boxed_1805_ = lean_unbox_usize(v_x_1801_);
lean_dec(v_x_1801_);
v_res_1806_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_x_1799_, v_x_1281__boxed_1804_, v_x_1282__boxed_1805_, v_x_1802_, v_x_1803_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(lean_object* v_x_1807_, lean_object* v_x_1808_, lean_object* v_x_1809_){
_start:
{
uint64_t v___y_1811_; 
if (lean_obj_tag(v_x_1808_) == 0)
{
uint64_t v___x_1815_; 
v___x_1815_ = 1723ULL;
v___y_1811_ = v___x_1815_;
goto v___jp_1810_;
}
else
{
uint64_t v_hash_1816_; 
v_hash_1816_ = lean_ctor_get_uint64(v_x_1808_, sizeof(void*)*2);
v___y_1811_ = v_hash_1816_;
goto v___jp_1810_;
}
v___jp_1810_:
{
size_t v___x_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = lean_uint64_to_usize(v___y_1811_);
v___x_1813_ = ((size_t)1ULL);
v___x_1814_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_x_1807_, v___x_1812_, v___x_1813_, v_x_1808_, v_x_1809_);
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(lean_object* v_x_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
uint8_t v_stage_u2081_1820_; lean_object* v_map_u2081_1821_; lean_object* v_map_u2082_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1902_; 
v_stage_u2081_1820_ = lean_ctor_get_uint8(v_x_1817_, sizeof(void*)*2);
v_map_u2081_1821_ = lean_ctor_get(v_x_1817_, 0);
v_map_u2082_1822_ = lean_ctor_get(v_x_1817_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_x_1817_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1824_ = v_x_1817_;
v_isShared_1825_ = v_isSharedCheck_1902_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_map_u2082_1822_);
lean_inc(v_map_u2081_1821_);
lean_dec(v_x_1817_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1902_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___y_1827_; lean_object* v_i_1828_; lean_object* v___y_1837_; lean_object* v___y_1849_; lean_object* v_i_1850_; 
if (v_stage_u2081_1820_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_del_object(v___x_1824_);
v___x_1868_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(v_map_u2082_1822_, v_x_1818_, v_x_1819_);
v___x_1869_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1869_, 0, v_map_u2081_1821_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
lean_ctor_set_uint8(v___x_1869_, sizeof(void*)*2, v_stage_u2081_1820_);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_map_u2081_1821_, v_x_1818_);
switch(lean_obj_tag(v___x_1870_))
{
case 0:
{
lean_object* v_index_1871_; lean_object* v_size_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_del_object(v___x_1824_);
v_index_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_index_1871_);
lean_dec_ref_known(v___x_1870_, 3);
v_size_1872_ = lean_ctor_get(v_map_u2081_1821_, 0);
lean_inc(v_size_1872_);
v___x_1873_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_1821_, v_size_1872_, v_index_1871_, v_x_1818_, v_x_1819_);
lean_dec(v_index_1871_);
v___x_1874_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v_map_u2082_1822_);
lean_ctor_set_uint8(v___x_1874_, sizeof(void*)*2, v_stage_u2081_1820_);
return v___x_1874_;
}
case 1:
{
lean_object* v_index_1875_; lean_object* v_size_1876_; lean_object* v_keyArray_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
lean_del_object(v___x_1824_);
v_index_1875_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_index_1875_);
lean_dec_ref_known(v___x_1870_, 1);
v_size_1876_ = lean_ctor_get(v_map_u2081_1821_, 0);
v_keyArray_1877_ = lean_ctor_get(v_map_u2081_1821_, 1);
v___x_1878_ = lean_unsigned_to_nat(1u);
v___x_1879_ = lean_nat_add(v_size_1876_, v___x_1878_);
v___x_1880_ = lean_array_get_size(v_keyArray_1877_);
v___x_1881_ = lean_nat_dec_lt(v___x_1879_, v___x_1880_);
if (v___x_1881_ == 0)
{
lean_dec(v___x_1879_);
lean_dec(v_index_1875_);
goto v___jp_1856_;
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1882_ = lean_unsigned_to_nat(4u);
v___x_1883_ = lean_nat_mul(v___x_1879_, v___x_1882_);
v___x_1884_ = lean_unsigned_to_nat(3u);
v___x_1885_ = lean_nat_mul(v___x_1880_, v___x_1884_);
v___x_1886_ = lean_nat_dec_le(v___x_1883_, v___x_1885_);
lean_dec(v___x_1885_);
lean_dec(v___x_1883_);
if (v___x_1886_ == 0)
{
lean_dec(v___x_1879_);
lean_dec(v_index_1875_);
goto v___jp_1856_;
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_1821_, v___x_1879_, v_index_1875_, v_x_1818_, v_x_1819_);
lean_dec(v_index_1875_);
v___x_1888_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v_map_u2082_1822_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*2, v_stage_u2081_1820_);
return v___x_1888_;
}
}
}
default: 
{
lean_object* v_size_1889_; lean_object* v_keyArray_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v_size_1889_ = lean_ctor_get(v_map_u2081_1821_, 0);
v_keyArray_1890_ = lean_ctor_get(v_map_u2081_1821_, 1);
v___x_1891_ = lean_unsigned_to_nat(1u);
v___x_1892_ = lean_nat_add(v_size_1889_, v___x_1891_);
v___x_1893_ = lean_array_get_size(v_keyArray_1890_);
v___x_1894_ = lean_nat_dec_lt(v___x_1892_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; 
lean_dec(v___x_1892_);
v___x_1895_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2___redArg(v_map_u2081_1821_);
lean_dec_ref(v_map_u2081_1821_);
v___y_1837_ = v___x_1895_;
goto v___jp_1836_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1896_ = lean_unsigned_to_nat(4u);
v___x_1897_ = lean_nat_mul(v___x_1892_, v___x_1896_);
lean_dec(v___x_1892_);
v___x_1898_ = lean_unsigned_to_nat(3u);
v___x_1899_ = lean_nat_mul(v___x_1893_, v___x_1898_);
v___x_1900_ = lean_nat_dec_le(v___x_1897_, v___x_1899_);
lean_dec(v___x_1899_);
lean_dec(v___x_1897_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2___redArg(v_map_u2081_1821_);
lean_dec_ref(v_map_u2081_1821_);
v___y_1837_ = v___x_1901_;
goto v___jp_1836_;
}
else
{
v___y_1837_ = v_map_u2081_1821_;
goto v___jp_1836_;
}
}
}
}
}
v___jp_1826_:
{
lean_object* v_size_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v_size_1829_ = lean_ctor_get(v___y_1827_, 0);
v___x_1830_ = lean_unsigned_to_nat(1u);
v___x_1831_ = lean_nat_add(v_size_1829_, v___x_1830_);
v___x_1832_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1827_, v___x_1831_, v_i_1828_, v_x_1818_, v_x_1819_);
lean_dec(v_i_1828_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1832_);
v___x_1834_ = v___x_1824_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_map_u2082_1822_);
lean_ctor_set_uint8(v_reuseFailAlloc_1835_, sizeof(void*)*2, v_stage_u2081_1820_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
v___jp_1836_:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v___y_1837_, v_x_1818_);
switch(lean_obj_tag(v___x_1838_))
{
case 0:
{
lean_object* v_index_1839_; lean_object* v_size_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_del_object(v___x_1824_);
v_index_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_index_1839_);
lean_dec_ref_known(v___x_1838_, 3);
v_size_1840_ = lean_ctor_get(v___y_1837_, 0);
lean_inc(v_size_1840_);
v___x_1841_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1837_, v_size_1840_, v_index_1839_, v_x_1818_, v_x_1819_);
lean_dec(v_index_1839_);
v___x_1842_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v_map_u2082_1822_);
lean_ctor_set_uint8(v___x_1842_, sizeof(void*)*2, v_stage_u2081_1820_);
return v___x_1842_;
}
case 1:
{
lean_object* v_index_1843_; 
v_index_1843_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_index_1843_);
lean_dec_ref_known(v___x_1838_, 1);
v___y_1827_ = v___y_1837_;
v_i_1828_ = v_index_1843_;
goto v___jp_1826_;
}
default: 
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1837_, v___x_1844_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_index_1846_; 
v_index_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_index_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v___y_1827_ = v___y_1837_;
v_i_1828_ = v_index_1846_;
goto v___jp_1826_;
}
else
{
lean_object* v___x_1847_; 
lean_del_object(v___x_1824_);
lean_dec(v_x_1819_);
lean_dec(v_x_1818_);
v___x_1847_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1847_, 0, v___y_1837_);
lean_ctor_set(v___x_1847_, 1, v_map_u2082_1822_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*2, v_stage_u2081_1820_);
return v___x_1847_;
}
}
}
}
v___jp_1848_:
{
lean_object* v_size_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v_size_1851_ = lean_ctor_get(v___y_1849_, 0);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_nat_add(v_size_1851_, v___x_1852_);
v___x_1854_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1849_, v___x_1853_, v_i_1850_, v_x_1818_, v_x_1819_);
lean_dec(v_i_1850_);
v___x_1855_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v_map_u2082_1822_);
lean_ctor_set_uint8(v___x_1855_, sizeof(void*)*2, v_stage_u2081_1820_);
return v___x_1855_;
}
v___jp_1856_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2___redArg(v_map_u2081_1821_);
lean_dec_ref(v_map_u2081_1821_);
v___x_1858_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v___x_1857_, v_x_1818_);
switch(lean_obj_tag(v___x_1858_))
{
case 0:
{
lean_object* v_index_1859_; lean_object* v_size_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v_index_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_index_1859_);
lean_dec_ref_known(v___x_1858_, 3);
v_size_1860_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_size_1860_);
v___x_1861_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1857_, v_size_1860_, v_index_1859_, v_x_1818_, v_x_1819_);
lean_dec(v_index_1859_);
v___x_1862_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v_map_u2082_1822_);
lean_ctor_set_uint8(v___x_1862_, sizeof(void*)*2, v_stage_u2081_1820_);
return v___x_1862_;
}
case 1:
{
lean_object* v_index_1863_; 
v_index_1863_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_index_1863_);
lean_dec_ref_known(v___x_1858_, 1);
v___y_1849_ = v___x_1857_;
v_i_1850_ = v_index_1863_;
goto v___jp_1848_;
}
default: 
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1857_, v___x_1864_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_index_1866_; 
v_index_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_index_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v___y_1849_ = v___x_1857_;
v_i_1850_ = v_index_1866_;
goto v___jp_1848_;
}
else
{
lean_object* v___x_1867_; 
lean_dec(v_x_1819_);
lean_dec(v_x_1818_);
v___x_1867_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1867_, 0, v___x_1857_);
lean_ctor_set(v___x_1867_, 1, v_map_u2082_1822_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*2, v_stage_u2081_1820_);
return v___x_1867_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_State_addEntry(lean_object* v_s_1903_, lean_object* v_e_1904_){
_start:
{
lean_object* v_name_1905_; lean_object* v_info_1906_; lean_object* v___x_1907_; 
v_name_1905_ = lean_ctor_get(v_e_1904_, 0);
lean_inc(v_name_1905_);
v_info_1906_ = lean_ctor_get(v_e_1904_, 1);
lean_inc_ref(v_info_1906_);
lean_dec_ref(v_e_1904_);
v___x_1907_ = l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(v_s_1903_, v_name_1905_, v_info_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0(lean_object* v_00_u03b2_1908_, lean_object* v_x_1909_, lean_object* v_x_1910_, lean_object* v_x_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(v_x_1909_, v_x_1910_, v_x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0(lean_object* v_00_u03b2_1913_, lean_object* v_m_1914_, lean_object* v_query_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_m_1914_, v_query_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1917_, lean_object* v_m_1918_, lean_object* v_query_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0(v_00_u03b2_1917_, v_m_1918_, v_query_1919_);
lean_dec(v_query_1919_);
lean_dec_ref(v_m_1918_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1(lean_object* v_00_u03b2_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(v_x_1922_, v_x_1923_, v_x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2(lean_object* v_00_u03b2_1926_, lean_object* v_m_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2___redArg(v_m_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1929_, lean_object* v_m_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2(v_00_u03b2_1929_, v_m_1930_);
lean_dec_ref(v_m_1930_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1932_, lean_object* v_m_1933_, lean_object* v_query_1934_, lean_object* v_x_1935_, lean_object* v_x_1936_, lean_object* v_x_1937_, lean_object* v_x_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_m_1933_, v_query_1934_, v_x_1935_, v_x_1936_, v_x_1937_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1940_, lean_object* v_m_1941_, lean_object* v_query_1942_, lean_object* v_x_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_, lean_object* v_x_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(v_00_u03b2_1940_, v_m_1941_, v_query_1942_, v_x_1943_, v_x_1944_, v_x_1945_, v_x_1946_);
lean_dec(v_query_1942_);
lean_dec_ref(v_m_1941_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1948_, lean_object* v_x_1949_, size_t v_x_1950_, size_t v_x_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_x_1949_, v_x_1950_, v_x_1951_, v_x_1952_, v_x_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1955_, lean_object* v_x_1956_, lean_object* v_x_1957_, lean_object* v_x_1958_, lean_object* v_x_1959_, lean_object* v_x_1960_){
_start:
{
size_t v_x_1643__boxed_1961_; size_t v_x_1644__boxed_1962_; lean_object* v_res_1963_; 
v_x_1643__boxed_1961_ = lean_unbox_usize(v_x_1957_);
lean_dec(v_x_1957_);
v_x_1644__boxed_1962_ = lean_unbox_usize(v_x_1958_);
lean_dec(v_x_1958_);
v_res_1963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(v_00_u03b2_1955_, v_x_1956_, v_x_1643__boxed_1961_, v_x_1644__boxed_1962_, v_x_1959_, v_x_1960_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1964_, lean_object* v_init_1965_, lean_object* v_b_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5___redArg(v_init_1965_, v_b_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1968_, lean_object* v_init_1969_, lean_object* v_b_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5(v_00_u03b2_1968_, v_init_1969_, v_b_1970_);
lean_dec_ref(v_b_1970_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1972_, lean_object* v_n_1973_, lean_object* v_k_1974_, lean_object* v_v_1975_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__4___redArg(v_n_1973_, v_k_1974_, v_v_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1977_, size_t v_depth_1978_, lean_object* v_keys_1979_, lean_object* v_vals_1980_, lean_object* v_heq_1981_, lean_object* v_i_1982_, lean_object* v_entries_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__5___redArg(v_depth_1978_, v_keys_1979_, v_vals_1980_, v_i_1982_, v_entries_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1985_, lean_object* v_depth_1986_, lean_object* v_keys_1987_, lean_object* v_vals_1988_, lean_object* v_heq_1989_, lean_object* v_i_1990_, lean_object* v_entries_1991_){
_start:
{
size_t v_depth_boxed_1992_; lean_object* v_res_1993_; 
v_depth_boxed_1992_ = lean_unbox_usize(v_depth_1986_);
lean_dec(v_depth_1986_);
v_res_1993_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__5(v_00_u03b2_1985_, v_depth_boxed_1992_, v_keys_1987_, v_vals_1988_, v_heq_1989_, v_i_1990_, v_entries_1991_);
lean_dec_ref(v_vals_1988_);
lean_dec_ref(v_keys_1987_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1994_, lean_object* v_b_1995_, lean_object* v_acc_1996_, lean_object* v_i_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5_spec__8___redArg(v_b_1995_, v_acc_1996_, v_i_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1999_, lean_object* v_b_2000_, lean_object* v_acc_2001_, lean_object* v_i_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__2_spec__5_spec__8(v_00_u03b2_1999_, v_b_2000_, v_acc_2001_, v_i_2002_);
lean_dec_ref(v_b_2000_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_2004_, lean_object* v_x_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(v_x_2005_, v_x_2006_, v_x_2007_, v_x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(lean_object* v_m_2010_){
_start:
{
uint8_t v_stage_u2081_2011_; 
v_stage_u2081_2011_ = lean_ctor_get_uint8(v_m_2010_, sizeof(void*)*2);
if (v_stage_u2081_2011_ == 0)
{
return v_m_2010_;
}
else
{
lean_object* v_map_u2081_2012_; lean_object* v_map_u2082_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2021_; 
v_map_u2081_2012_ = lean_ctor_get(v_m_2010_, 0);
v_map_u2082_2013_ = lean_ctor_get(v_m_2010_, 1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_m_2010_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2015_ = v_m_2010_;
v_isShared_2016_ = v_isSharedCheck_2021_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_map_u2082_2013_);
lean_inc(v_map_u2081_2012_);
lean_dec(v_m_2010_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2021_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
uint8_t v___x_2017_; lean_object* v___x_2019_; 
v___x_2017_ = 0;
if (v_isShared_2016_ == 0)
{
v___x_2019_ = v___x_2015_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_map_u2081_2012_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_map_u2082_2013_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_ctor_set_uint8(v___x_2019_, sizeof(void*)*2, v___x_2017_);
return v___x_2019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0(lean_object* v_00_u03b2_2022_, lean_object* v_m_2023_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(v_m_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_State_switch(lean_object* v_s_2025_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(v_s_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(lean_object* v_env_2027_, lean_object* v_as_2028_, size_t v_i_2029_, size_t v_stop_2030_, lean_object* v_b_2031_){
_start:
{
lean_object* v___y_2033_; uint8_t v___x_2037_; 
v___x_2037_ = lean_usize_dec_eq(v_i_2029_, v_stop_2030_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v_name_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2038_ = lean_array_uget_borrowed(v_as_2028_, v_i_2029_);
v_name_2039_ = lean_ctor_get(v___x_2038_, 0);
v___x_2040_ = 1;
lean_inc_ref(v_env_2027_);
v___x_2041_ = l_Lean_Environment_setExporting(v_env_2027_, v___x_2040_);
lean_inc(v_name_2039_);
v___x_2042_ = l_Lean_Environment_contains(v___x_2041_, v_name_2039_, v___x_2037_);
if (v___x_2042_ == 0)
{
v___y_2033_ = v_b_2031_;
goto v___jp_2032_;
}
else
{
lean_object* v___x_2043_; 
lean_inc(v___x_2038_);
v___x_2043_ = lean_array_push(v_b_2031_, v___x_2038_);
v___y_2033_ = v___x_2043_;
goto v___jp_2032_;
}
}
else
{
lean_dec_ref(v_env_2027_);
return v_b_2031_;
}
v___jp_2032_:
{
size_t v___x_2034_; size_t v___x_2035_; 
v___x_2034_ = ((size_t)1ULL);
v___x_2035_ = lean_usize_add(v_i_2029_, v___x_2034_);
v_i_2029_ = v___x_2035_;
v_b_2031_ = v___y_2033_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_2044_, lean_object* v_as_2045_, lean_object* v_i_2046_, lean_object* v_stop_2047_, lean_object* v_b_2048_){
_start:
{
size_t v_i_boxed_2049_; size_t v_stop_boxed_2050_; lean_object* v_res_2051_; 
v_i_boxed_2049_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_stop_boxed_2050_ = lean_unbox_usize(v_stop_2047_);
lean_dec(v_stop_2047_);
v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_2044_, v_as_2045_, v_i_boxed_2049_, v_stop_boxed_2050_, v_b_2048_);
lean_dec_ref(v_as_2045_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object* v_env_2054_, lean_object* v_x_2055_, lean_object* v_entries_2056_){
_start:
{
lean_object* v_all_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v_all_2057_ = lean_array_mk(v_entries_2056_);
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = lean_array_get_size(v_all_2057_);
v___x_2060_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_));
v___x_2061_ = lean_nat_dec_lt(v___x_2058_, v___x_2059_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; 
lean_dec_ref(v_env_2054_);
v___x_2062_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2060_);
lean_ctor_set(v___x_2062_, 1, v___x_2060_);
lean_ctor_set(v___x_2062_, 2, v_all_2057_);
return v___x_2062_;
}
else
{
uint8_t v___x_2063_; 
v___x_2063_ = lean_nat_dec_le(v___x_2059_, v___x_2059_);
if (v___x_2063_ == 0)
{
if (v___x_2061_ == 0)
{
lean_object* v___x_2064_; 
lean_dec_ref(v_env_2054_);
v___x_2064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2060_);
lean_ctor_set(v___x_2064_, 1, v___x_2060_);
lean_ctor_set(v___x_2064_, 2, v_all_2057_);
return v___x_2064_;
}
else
{
size_t v___x_2065_; size_t v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2065_ = ((size_t)0ULL);
v___x_2066_ = lean_usize_of_nat(v___x_2059_);
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_2054_, v_all_2057_, v___x_2065_, v___x_2066_, v___x_2060_);
lean_inc_ref(v___x_2067_);
v___x_2068_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
lean_ctor_set(v___x_2068_, 2, v_all_2057_);
return v___x_2068_;
}
}
else
{
size_t v___x_2069_; size_t v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2069_ = ((size_t)0ULL);
v___x_2070_ = lean_usize_of_nat(v___x_2059_);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_2054_, v_all_2057_, v___x_2069_, v___x_2070_, v___x_2060_);
lean_inc_ref(v___x_2071_);
v___x_2072_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
lean_ctor_set(v___x_2072_, 2, v_all_2057_);
return v___x_2072_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object* v_env_2073_, lean_object* v_x_2074_, lean_object* v_entries_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(v_env_2073_, v_x_2074_, v_entries_2075_);
lean_dec_ref(v_x_2074_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object* v_es_2077_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_array_mk(v_es_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_2079_, size_t v_i_2080_, size_t v_stop_2081_, lean_object* v_b_2082_){
_start:
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_usize_dec_eq(v_i_2080_, v_stop_2081_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; size_t v___x_2086_; size_t v___x_2087_; 
v___x_2084_ = lean_array_uget_borrowed(v_as_2079_, v_i_2080_);
lean_inc(v___x_2084_);
v___x_2085_ = l_Lean_Meta_Match_Extension_State_addEntry(v_b_2082_, v___x_2084_);
v___x_2086_ = ((size_t)1ULL);
v___x_2087_ = lean_usize_add(v_i_2080_, v___x_2086_);
v_i_2080_ = v___x_2087_;
v_b_2082_ = v___x_2085_;
goto _start;
}
else
{
return v_b_2082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_2089_, lean_object* v_i_2090_, lean_object* v_stop_2091_, lean_object* v_b_2092_){
_start:
{
size_t v_i_boxed_2093_; size_t v_stop_boxed_2094_; lean_object* v_res_2095_; 
v_i_boxed_2093_ = lean_unbox_usize(v_i_2090_);
lean_dec(v_i_2090_);
v_stop_boxed_2094_ = lean_unbox_usize(v_stop_2091_);
lean_dec(v_stop_2091_);
v_res_2095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(v_as_2089_, v_i_boxed_2093_, v_stop_boxed_2094_, v_b_2092_);
lean_dec_ref(v_as_2089_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_2096_, size_t v_i_2097_, size_t v_stop_2098_, lean_object* v_b_2099_){
_start:
{
lean_object* v___y_2101_; uint8_t v___x_2105_; 
v___x_2105_ = lean_usize_dec_eq(v_i_2097_, v_stop_2098_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2106_ = lean_array_uget_borrowed(v_as_2096_, v_i_2097_);
v___x_2107_ = lean_unsigned_to_nat(0u);
v___x_2108_ = lean_array_get_size(v___x_2106_);
v___x_2109_ = lean_nat_dec_lt(v___x_2107_, v___x_2108_);
if (v___x_2109_ == 0)
{
v___y_2101_ = v_b_2099_;
goto v___jp_2100_;
}
else
{
uint8_t v___x_2110_; 
v___x_2110_ = lean_nat_dec_le(v___x_2108_, v___x_2108_);
if (v___x_2110_ == 0)
{
if (v___x_2109_ == 0)
{
v___y_2101_ = v_b_2099_;
goto v___jp_2100_;
}
else
{
size_t v___x_2111_; size_t v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = ((size_t)0ULL);
v___x_2112_ = lean_usize_of_nat(v___x_2108_);
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(v___x_2106_, v___x_2111_, v___x_2112_, v_b_2099_);
v___y_2101_ = v___x_2113_;
goto v___jp_2100_;
}
}
else
{
size_t v___x_2114_; size_t v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = ((size_t)0ULL);
v___x_2115_ = lean_usize_of_nat(v___x_2108_);
v___x_2116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(v___x_2106_, v___x_2114_, v___x_2115_, v_b_2099_);
v___y_2101_ = v___x_2116_;
goto v___jp_2100_;
}
}
}
else
{
return v_b_2099_;
}
v___jp_2100_:
{
size_t v___x_2102_; size_t v___x_2103_; 
v___x_2102_ = ((size_t)1ULL);
v___x_2103_ = lean_usize_add(v_i_2097_, v___x_2102_);
v_i_2097_ = v___x_2103_;
v_b_2099_ = v___y_2101_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_2117_, lean_object* v_i_2118_, lean_object* v_stop_2119_, lean_object* v_b_2120_){
_start:
{
size_t v_i_boxed_2121_; size_t v_stop_boxed_2122_; lean_object* v_res_2123_; 
v_i_boxed_2121_ = lean_unbox_usize(v_i_2118_);
lean_dec(v_i_2118_);
v_stop_boxed_2122_ = lean_unbox_usize(v_stop_2119_);
lean_dec(v_stop_2119_);
v_res_2123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_2117_, v_i_boxed_2121_, v_stop_boxed_2122_, v_b_2120_);
lean_dec_ref(v_as_2117_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(lean_object* v_initState_2124_, lean_object* v_as_2125_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = lean_array_get_size(v_as_2125_);
v___x_2128_ = lean_nat_dec_lt(v___x_2126_, v___x_2127_);
if (v___x_2128_ == 0)
{
return v_initState_2124_;
}
else
{
uint8_t v___x_2129_; 
v___x_2129_ = lean_nat_dec_le(v___x_2127_, v___x_2127_);
if (v___x_2129_ == 0)
{
if (v___x_2128_ == 0)
{
return v_initState_2124_;
}
else
{
size_t v___x_2130_; size_t v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = ((size_t)0ULL);
v___x_2131_ = lean_usize_of_nat(v___x_2127_);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_2125_, v___x_2130_, v___x_2131_, v_initState_2124_);
return v___x_2132_;
}
}
else
{
size_t v___x_2133_; size_t v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = ((size_t)0ULL);
v___x_2134_ = lean_usize_of_nat(v___x_2127_);
v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_2125_, v___x_2133_, v___x_2134_, v_initState_2124_);
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_2136_, lean_object* v_as_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(v_initState_2136_, v_as_2137_);
lean_dec_ref(v_as_2137_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object* v_es_2139_){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__5, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__5_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__5);
v___x_2141_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(v___x_2140_, v_es_2139_);
v___x_2142_ = l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object* v_es_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(v_es_2143_);
lean_dec_ref(v_es_2143_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_));
v___x_2174_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_();
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_addMatcherInfo(lean_object* v_env_2177_, lean_object* v_matcherName_2178_, lean_object* v_info_2179_){
_start:
{
lean_object* v___x_2180_; lean_object* v_toEnvExtension_2181_; lean_object* v_asyncMode_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2180_ = l_Lean_Meta_Match_Extension_extension;
v_toEnvExtension_2181_ = lean_ctor_get(v___x_2180_, 0);
v_asyncMode_2182_ = lean_ctor_get(v_toEnvExtension_2181_, 2);
lean_inc(v_matcherName_2178_);
v___x_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2183_, 0, v_matcherName_2178_);
lean_ctor_set(v___x_2183_, 1, v_info_2179_);
v___x_2184_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2180_, v_env_2177_, v___x_2183_, v_asyncMode_2182_, v_matcherName_2178_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_2185_, lean_object* v_vals_2186_, lean_object* v_i_2187_, lean_object* v_k_2188_){
_start:
{
lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2189_ = lean_array_get_size(v_keys_2185_);
v___x_2190_ = lean_nat_dec_lt(v_i_2187_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
lean_dec(v_i_2187_);
v___x_2191_ = lean_box(0);
return v___x_2191_;
}
else
{
lean_object* v_k_x27_2192_; uint8_t v___x_2193_; 
v_k_x27_2192_ = lean_array_fget_borrowed(v_keys_2185_, v_i_2187_);
v___x_2193_ = lean_name_eq(v_k_2188_, v_k_x27_2192_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_nat_add(v_i_2187_, v___x_2194_);
lean_dec(v_i_2187_);
v_i_2187_ = v___x_2195_;
goto _start;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = lean_array_fget_borrowed(v_vals_2186_, v_i_2187_);
lean_dec(v_i_2187_);
lean_inc(v___x_2197_);
v___x_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
return v___x_2198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2199_, lean_object* v_vals_2200_, lean_object* v_i_2201_, lean_object* v_k_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2199_, v_vals_2200_, v_i_2201_, v_k_2202_);
lean_dec(v_k_2202_);
lean_dec_ref(v_vals_2200_);
lean_dec_ref(v_keys_2199_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2204_, size_t v_x_2205_, lean_object* v_x_2206_){
_start:
{
if (lean_obj_tag(v_x_2204_) == 0)
{
lean_object* v_es_2207_; lean_object* v___x_2208_; size_t v___x_2209_; size_t v___x_2210_; lean_object* v_j_2211_; lean_object* v___x_2212_; 
v_es_2207_ = lean_ctor_get(v_x_2204_, 0);
v___x_2208_ = lean_box(2);
v___x_2209_ = ((size_t)31ULL);
v___x_2210_ = lean_usize_land(v_x_2205_, v___x_2209_);
v_j_2211_ = lean_usize_to_nat(v___x_2210_);
v___x_2212_ = lean_array_get_borrowed(v___x_2208_, v_es_2207_, v_j_2211_);
lean_dec(v_j_2211_);
switch(lean_obj_tag(v___x_2212_))
{
case 0:
{
lean_object* v_key_2213_; lean_object* v_val_2214_; uint8_t v___x_2215_; 
v_key_2213_ = lean_ctor_get(v___x_2212_, 0);
v_val_2214_ = lean_ctor_get(v___x_2212_, 1);
v___x_2215_ = lean_name_eq(v_x_2206_, v_key_2213_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; 
v___x_2216_ = lean_box(0);
return v___x_2216_;
}
else
{
lean_object* v___x_2217_; 
lean_inc(v_val_2214_);
v___x_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2217_, 0, v_val_2214_);
return v___x_2217_;
}
}
case 1:
{
lean_object* v_node_2218_; size_t v___x_2219_; size_t v___x_2220_; 
v_node_2218_ = lean_ctor_get(v___x_2212_, 0);
v___x_2219_ = ((size_t)5ULL);
v___x_2220_ = lean_usize_shift_right(v_x_2205_, v___x_2219_);
v_x_2204_ = v_node_2218_;
v_x_2205_ = v___x_2220_;
goto _start;
}
default: 
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_box(0);
return v___x_2222_;
}
}
}
else
{
lean_object* v_ks_2223_; lean_object* v_vs_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v_ks_2223_ = lean_ctor_get(v_x_2204_, 0);
v_vs_2224_ = lean_ctor_get(v_x_2204_, 1);
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_2223_, v_vs_2224_, v___x_2225_, v_x_2206_);
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_){
_start:
{
size_t v_x_540__boxed_2230_; lean_object* v_res_2231_; 
v_x_540__boxed_2230_ = lean_unbox_usize(v_x_2228_);
lean_dec(v_x_2228_);
v_res_2231_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_2227_, v_x_540__boxed_2230_, v_x_2229_);
lean_dec(v_x_2229_);
lean_dec_ref(v_x_2227_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_2232_, lean_object* v_x_2233_){
_start:
{
uint64_t v___y_2235_; 
if (lean_obj_tag(v_x_2233_) == 0)
{
uint64_t v___x_2238_; 
v___x_2238_ = 1723ULL;
v___y_2235_ = v___x_2238_;
goto v___jp_2234_;
}
else
{
uint64_t v_hash_2239_; 
v_hash_2239_ = lean_ctor_get_uint64(v_x_2233_, sizeof(void*)*2);
v___y_2235_ = v_hash_2239_;
goto v___jp_2234_;
}
v___jp_2234_:
{
size_t v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = lean_uint64_to_usize(v___y_2235_);
v___x_2237_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_2232_, v___x_2236_, v_x_2233_);
return v___x_2237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2240_, lean_object* v_x_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_x_2240_, v_x_2241_);
lean_dec(v_x_2241_);
lean_dec_ref(v_x_2240_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(lean_object* v_m_2243_, lean_object* v_query_2244_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_m_2243_, v_query_2244_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_index_2246_; lean_object* v_key_2247_; lean_object* v_value_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
v_index_2246_ = lean_ctor_get(v___x_2245_, 0);
v_key_2247_ = lean_ctor_get(v___x_2245_, 1);
v_value_2248_ = lean_ctor_get(v___x_2245_, 2);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2245_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_value_2248_);
lean_inc(v_key_2247_);
lean_inc(v_index_2246_);
lean_dec(v___x_2245_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_index_2246_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_key_2247_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_value_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
else
{
lean_object* v___x_2256_; 
lean_dec(v___x_2245_);
v___x_2256_ = lean_box(1);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_m_2257_, lean_object* v_query_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_m_2257_, v_query_2258_);
lean_dec(v_query_2258_);
lean_dec_ref(v_m_2257_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(lean_object* v_m_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_m_2260_, v_a_2261_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_value_2263_; lean_object* v___x_2264_; 
v_value_2263_ = lean_ctor_get(v___x_2262_, 2);
lean_inc(v_value_2263_);
lean_dec_ref_known(v___x_2262_, 3);
v___x_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2264_, 0, v_value_2263_);
return v___x_2264_;
}
else
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_box(0);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_m_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_m_2266_, v_a_2267_);
lean_dec(v_a_2267_);
lean_dec_ref(v_m_2266_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(lean_object* v_x_2269_, lean_object* v_x_2270_){
_start:
{
uint8_t v_stage_u2081_2271_; 
v_stage_u2081_2271_ = lean_ctor_get_uint8(v_x_2269_, sizeof(void*)*2);
if (v_stage_u2081_2271_ == 0)
{
lean_object* v_map_u2081_2272_; lean_object* v_map_u2082_2273_; lean_object* v___x_2274_; 
v_map_u2081_2272_ = lean_ctor_get(v_x_2269_, 0);
v_map_u2082_2273_ = lean_ctor_get(v_x_2269_, 1);
v___x_2274_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_map_u2082_2273_, v_x_2270_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_map_u2081_2272_, v_x_2270_);
return v___x_2275_;
}
else
{
return v___x_2274_;
}
}
else
{
lean_object* v_map_u2081_2276_; lean_object* v___x_2277_; 
v_map_u2081_2276_ = lean_ctor_get(v_x_2269_, 0);
v___x_2277_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_map_u2081_2276_, v_x_2270_);
return v___x_2277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_2278_, lean_object* v_x_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v_x_2278_, v_x_2279_);
lean_dec(v_x_2279_);
lean_dec_ref(v_x_2278_);
return v_res_2280_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = ((lean_object*)(l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0));
v___x_2283_ = lean_string_utf8_byte_size(v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object* v_env_2284_, lean_object* v_declName_2285_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Name_eraseMacroScopes(v_declName_2285_);
if (lean_obj_tag(v___x_2286_) == 1)
{
lean_object* v_str_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v_str_2287_ = lean_ctor_get(v___x_2286_, 1);
lean_inc_ref(v_str_2287_);
lean_dec_ref_known(v___x_2286_, 2);
v___x_2288_ = ((lean_object*)(l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0));
v___x_2289_ = lean_string_utf8_byte_size(v_str_2287_);
v___x_2290_ = lean_obj_once(&l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1, &l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1_once, _init_l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1);
v___x_2291_ = lean_nat_dec_le(v___x_2290_, v___x_2289_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; 
lean_dec_ref(v_str_2287_);
lean_dec(v_declName_2285_);
lean_dec_ref(v_env_2284_);
v___x_2292_ = lean_box(0);
return v___x_2292_;
}
else
{
lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2293_ = lean_unsigned_to_nat(0u);
v___x_2294_ = lean_string_memcmp(v_str_2287_, v___x_2288_, v___x_2293_, v___x_2293_, v___x_2290_);
lean_dec_ref(v_str_2287_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; 
lean_dec(v_declName_2285_);
lean_dec_ref(v_env_2284_);
v___x_2295_ = lean_box(0);
return v___x_2295_;
}
else
{
lean_object* v___x_2296_; lean_object* v_toEnvExtension_2297_; lean_object* v_asyncMode_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2296_ = l_Lean_Meta_Match_Extension_extension;
v_toEnvExtension_2297_ = lean_ctor_get(v___x_2296_, 0);
v_asyncMode_2298_ = lean_ctor_get(v_toEnvExtension_2297_, 2);
v___x_2299_ = l_Lean_Meta_Match_Extension_instInhabitedState;
lean_inc(v_declName_2285_);
v___x_2300_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2299_, v___x_2296_, v_env_2284_, v_asyncMode_2298_, v_declName_2285_);
v___x_2301_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v___x_2300_, v_declName_2285_);
lean_dec(v_declName_2285_);
lean_dec(v___x_2300_);
return v___x_2301_;
}
}
}
else
{
lean_object* v___x_2302_; 
lean_dec(v___x_2286_);
lean_dec(v_declName_2285_);
lean_dec_ref(v_env_2284_);
v___x_2302_ = lean_box(0);
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(lean_object* v_00_u03b2_2303_, lean_object* v_x_2304_, lean_object* v_x_2305_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v_x_2304_, v_x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_2307_, lean_object* v_x_2308_, lean_object* v_x_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(v_00_u03b2_2307_, v_x_2308_, v_x_2309_);
lean_dec(v_x_2309_);
lean_dec_ref(v_x_2308_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_x_2312_, v_x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2315_, lean_object* v_x_2316_, lean_object* v_x_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(v_00_u03b2_2315_, v_x_2316_, v_x_2317_);
lean_dec(v_x_2317_);
lean_dec_ref(v_x_2316_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(lean_object* v_00_u03b2_2319_, lean_object* v_m_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_m_2320_, v_a_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2323_, lean_object* v_m_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(v_00_u03b2_2323_, v_m_2324_, v_a_2325_);
lean_dec(v_a_2325_);
lean_dec_ref(v_m_2324_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2327_, lean_object* v_x_2328_, size_t v_x_2329_, lean_object* v_x_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_2328_, v_x_2329_, v_x_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_, lean_object* v_x_2335_){
_start:
{
size_t v_x_716__boxed_2336_; lean_object* v_res_2337_; 
v_x_716__boxed_2336_ = lean_unbox_usize(v_x_2334_);
lean_dec(v_x_2334_);
v_res_2337_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2332_, v_x_2333_, v_x_716__boxed_2336_, v_x_2335_);
lean_dec(v_x_2335_);
lean_dec_ref(v_x_2333_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2338_, lean_object* v_m_2339_, lean_object* v_query_2340_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_m_2339_, v_query_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2342_, lean_object* v_m_2343_, lean_object* v_query_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(v_00_u03b2_2342_, v_m_2343_, v_query_2344_);
lean_dec(v_query_2344_);
lean_dec_ref(v_m_2343_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2346_, lean_object* v_keys_2347_, lean_object* v_vals_2348_, lean_object* v_heq_2349_, lean_object* v_i_2350_, lean_object* v_k_2351_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2347_, v_vals_2348_, v_i_2350_, v_k_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2353_, lean_object* v_keys_2354_, lean_object* v_vals_2355_, lean_object* v_heq_2356_, lean_object* v_i_2357_, lean_object* v_k_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2353_, v_keys_2354_, v_vals_2355_, v_heq_2356_, v_i_2357_, v_k_2358_);
lean_dec(v_k_2358_);
lean_dec_ref(v_vals_2355_);
lean_dec_ref(v_keys_2354_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0(lean_object* v_matcherName_2360_, lean_object* v_info_2361_, lean_object* v_env_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2362_, v_matcherName_2360_, v_info_2361_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___redArg(lean_object* v_inst_2364_, lean_object* v_matcherName_2365_, lean_object* v_info_2366_){
_start:
{
lean_object* v_modifyEnv_2367_; lean_object* v___f_2368_; lean_object* v___x_2369_; 
v_modifyEnv_2367_ = lean_ctor_get(v_inst_2364_, 1);
lean_inc(v_modifyEnv_2367_);
lean_dec_ref(v_inst_2364_);
v___f_2368_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2368_, 0, v_matcherName_2365_);
lean_closure_set(v___f_2368_, 1, v_info_2366_);
v___x_2369_ = lean_apply_1(v_modifyEnv_2367_, v___f_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo(lean_object* v_m_2370_, lean_object* v_inst_2371_, lean_object* v_inst_2372_, lean_object* v_matcherName_2373_, lean_object* v_info_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_Meta_Match_addMatcherInfo___redArg(v_inst_2372_, v_matcherName_2373_, v_info_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___boxed(lean_object* v_m_2376_, lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_matcherName_2379_, lean_object* v_info_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_Meta_Match_addMatcherInfo(v_m_2376_, v_inst_2377_, v_inst_2378_, v_matcherName_2379_, v_info_2380_);
lean_dec_ref(v_inst_2377_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfoCore_x3f(lean_object* v_env_2382_, lean_object* v_declName_2383_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2382_, v_declName_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0(lean_object* v_declName_2385_, lean_object* v_toPure_2386_, lean_object* v_____do__lift_2387_){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_____do__lift_2387_, v_declName_2385_);
v___x_2389_ = lean_apply_2(v_toPure_2386_, lean_box(0), v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg(lean_object* v_inst_2390_, lean_object* v_inst_2391_, lean_object* v_declName_2392_){
_start:
{
lean_object* v_toApplicative_2393_; lean_object* v_toBind_2394_; lean_object* v_getEnv_2395_; lean_object* v_toPure_2396_; lean_object* v___f_2397_; lean_object* v___x_2398_; 
v_toApplicative_2393_ = lean_ctor_get(v_inst_2390_, 0);
lean_inc_ref(v_toApplicative_2393_);
v_toBind_2394_ = lean_ctor_get(v_inst_2390_, 1);
lean_inc(v_toBind_2394_);
lean_dec_ref(v_inst_2390_);
v_getEnv_2395_ = lean_ctor_get(v_inst_2391_, 0);
lean_inc(v_getEnv_2395_);
lean_dec_ref(v_inst_2391_);
v_toPure_2396_ = lean_ctor_get(v_toApplicative_2393_, 1);
lean_inc(v_toPure_2396_);
lean_dec_ref(v_toApplicative_2393_);
v___f_2397_ = lean_alloc_closure((void*)(l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2397_, 0, v_declName_2392_);
lean_closure_set(v___f_2397_, 1, v_toPure_2396_);
v___x_2398_ = lean_apply_4(v_toBind_2394_, lean_box(0), lean_box(0), v_getEnv_2395_, v___f_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f(lean_object* v_m_2399_, lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_declName_2402_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_2400_, v_inst_2401_, v_declName_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherCore(lean_object* v_env_2404_, lean_object* v_declName_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2404_, v_declName_2405_);
if (lean_obj_tag(v___x_2406_) == 0)
{
uint8_t v___x_2407_; 
v___x_2407_ = 0;
return v___x_2407_;
}
else
{
uint8_t v___x_2408_; 
lean_dec_ref_known(v___x_2406_, 1);
v___x_2408_ = 1;
return v___x_2408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherCore___boxed(lean_object* v_env_2409_, lean_object* v_declName_2410_){
_start:
{
uint8_t v_res_2411_; lean_object* v_r_2412_; 
v_res_2411_ = l_Lean_Meta_isMatcherCore(v_env_2409_, v_declName_2410_);
v_r_2412_ = lean_box(v_res_2411_);
return v_r_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___redArg___lam__0(lean_object* v_declName_2413_, lean_object* v_toPure_2414_, lean_object* v_____do__lift_2415_){
_start:
{
uint8_t v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = l_Lean_Meta_isMatcherCore(v_____do__lift_2415_, v_declName_2413_);
v___x_2417_ = lean_box(v___x_2416_);
v___x_2418_ = lean_apply_2(v_toPure_2414_, lean_box(0), v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___redArg(lean_object* v_inst_2419_, lean_object* v_inst_2420_, lean_object* v_declName_2421_){
_start:
{
lean_object* v_toApplicative_2422_; lean_object* v_toBind_2423_; lean_object* v_getEnv_2424_; lean_object* v_toPure_2425_; lean_object* v___f_2426_; lean_object* v___x_2427_; 
v_toApplicative_2422_ = lean_ctor_get(v_inst_2419_, 0);
lean_inc_ref(v_toApplicative_2422_);
v_toBind_2423_ = lean_ctor_get(v_inst_2419_, 1);
lean_inc(v_toBind_2423_);
lean_dec_ref(v_inst_2419_);
v_getEnv_2424_ = lean_ctor_get(v_inst_2420_, 0);
lean_inc(v_getEnv_2424_);
lean_dec_ref(v_inst_2420_);
v_toPure_2425_ = lean_ctor_get(v_toApplicative_2422_, 1);
lean_inc(v_toPure_2425_);
lean_dec_ref(v_toApplicative_2422_);
v___f_2426_ = lean_alloc_closure((void*)(l_Lean_Meta_isMatcher___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2426_, 0, v_declName_2421_);
lean_closure_set(v___f_2426_, 1, v_toPure_2425_);
v___x_2427_ = lean_apply_4(v_toBind_2423_, lean_box(0), lean_box(0), v_getEnv_2424_, v___f_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher(lean_object* v_m_2428_, lean_object* v_inst_2429_, lean_object* v_inst_2430_, lean_object* v_declName_2431_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_Meta_isMatcher___redArg(v_inst_2429_, v_inst_2430_, v_declName_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object* v_env_2433_, lean_object* v_e_2434_){
_start:
{
lean_object* v_fn_2435_; uint8_t v___x_2436_; 
v_fn_2435_ = l_Lean_Expr_getAppFn(v_e_2434_);
v___x_2436_ = l_Lean_Expr_isConst(v_fn_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; 
lean_dec_ref(v_fn_2435_);
lean_dec_ref(v_env_2433_);
v___x_2437_ = lean_box(0);
return v___x_2437_;
}
else
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = l_Lean_Expr_constName_x21(v_fn_2435_);
lean_dec_ref(v_fn_2435_);
v___x_2439_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2433_, v___x_2438_);
if (lean_obj_tag(v___x_2439_) == 1)
{
lean_object* v_val_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
v_val_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_val_2440_);
v___x_2441_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2440_);
lean_dec(v_val_2440_);
v___x_2442_ = l_Lean_Expr_getAppNumArgs(v_e_2434_);
v___x_2443_ = lean_nat_dec_le(v___x_2441_, v___x_2442_);
lean_dec(v___x_2442_);
lean_dec(v___x_2441_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; 
lean_dec_ref_known(v___x_2439_, 1);
v___x_2444_ = lean_box(0);
return v___x_2444_;
}
else
{
return v___x_2439_;
}
}
else
{
lean_object* v___x_2445_; 
lean_dec(v___x_2439_);
v___x_2445_ = lean_box(0);
return v___x_2445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore_x3f___boxed(lean_object* v_env_2446_, lean_object* v_e_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_2446_, v_e_2447_);
lean_dec_ref(v_e_2447_);
return v_res_2448_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherAppCore(lean_object* v_env_2449_, lean_object* v_e_2450_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_2449_, v_e_2450_);
if (lean_obj_tag(v___x_2451_) == 0)
{
uint8_t v___x_2452_; 
v___x_2452_ = 0;
return v___x_2452_;
}
else
{
uint8_t v___x_2453_; 
lean_dec_ref_known(v___x_2451_, 1);
v___x_2453_ = 1;
return v___x_2453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore___boxed(lean_object* v_env_2454_, lean_object* v_e_2455_){
_start:
{
uint8_t v_res_2456_; lean_object* v_r_2457_; 
v_res_2456_ = l_Lean_Meta_isMatcherAppCore(v_env_2454_, v_e_2455_);
lean_dec_ref(v_e_2455_);
v_r_2457_ = lean_box(v_res_2456_);
return v_r_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg___lam__0(lean_object* v_e_2458_, lean_object* v_toPure_2459_, lean_object* v_____do__lift_2460_){
_start:
{
uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2461_ = l_Lean_Meta_isMatcherAppCore(v_____do__lift_2460_, v_e_2458_);
v___x_2462_ = lean_box(v___x_2461_);
v___x_2463_ = lean_apply_2(v_toPure_2459_, lean_box(0), v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed(lean_object* v_e_2464_, lean_object* v_toPure_2465_, lean_object* v_____do__lift_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_Meta_isMatcherApp___redArg___lam__0(v_e_2464_, v_toPure_2465_, v_____do__lift_2466_);
lean_dec_ref(v_e_2464_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg(lean_object* v_inst_2468_, lean_object* v_inst_2469_, lean_object* v_e_2470_){
_start:
{
lean_object* v_toApplicative_2471_; lean_object* v_toBind_2472_; lean_object* v_getEnv_2473_; lean_object* v_toPure_2474_; lean_object* v___f_2475_; lean_object* v___x_2476_; 
v_toApplicative_2471_ = lean_ctor_get(v_inst_2468_, 0);
lean_inc_ref(v_toApplicative_2471_);
v_toBind_2472_ = lean_ctor_get(v_inst_2468_, 1);
lean_inc(v_toBind_2472_);
lean_dec_ref(v_inst_2468_);
v_getEnv_2473_ = lean_ctor_get(v_inst_2469_, 0);
lean_inc(v_getEnv_2473_);
lean_dec_ref(v_inst_2469_);
v_toPure_2474_ = lean_ctor_get(v_toApplicative_2471_, 1);
lean_inc(v_toPure_2474_);
lean_dec_ref(v_toApplicative_2471_);
v___f_2475_ = lean_alloc_closure((void*)(l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2475_, 0, v_e_2470_);
lean_closure_set(v___f_2475_, 1, v_toPure_2474_);
v___x_2476_ = lean_apply_4(v_toBind_2472_, lean_box(0), lean_box(0), v_getEnv_2473_, v___f_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp(lean_object* v_m_2477_, lean_object* v_inst_2478_, lean_object* v_inst_2479_, lean_object* v_e_2480_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Meta_isMatcherApp___redArg(v_inst_2478_, v_inst_2479_, v_e_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_));
v___x_2489_ = lean_box(0);
v___x_2490_ = l_Lean_mkTagDeclarationExtension(v___x_2488_, v___x_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2____boxed(lean_object* v_a_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_();
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markMatcherLike(lean_object* v_env_2493_, lean_object* v_declName_2494_){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = l_Lean_Meta_matcherLikeExt;
v___x_2496_ = l_Lean_TagDeclarationExtension_tag(v___x_2495_, v_env_2493_, v_declName_2494_);
return v___x_2496_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherLikeCore(lean_object* v_env_2497_, lean_object* v_declName_2498_){
_start:
{
lean_object* v___x_2499_; lean_object* v_toEnvExtension_2500_; lean_object* v_asyncMode_2501_; uint8_t v___x_2502_; 
v___x_2499_ = l_Lean_Meta_matcherLikeExt;
v_toEnvExtension_2500_ = lean_ctor_get(v___x_2499_, 0);
v_asyncMode_2501_ = lean_ctor_get(v_toEnvExtension_2500_, 2);
v___x_2502_ = l_Lean_TagDeclarationExtension_isTagged(v___x_2499_, v_env_2497_, v_declName_2498_, v_asyncMode_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLikeCore___boxed(lean_object* v_env_2503_, lean_object* v_declName_2504_){
_start:
{
uint8_t v_res_2505_; lean_object* v_r_2506_; 
v_res_2505_ = l_Lean_Meta_isMatcherLikeCore(v_env_2503_, v_declName_2504_);
v_r_2506_ = lean_box(v_res_2505_);
return v_r_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike___redArg___lam__0(lean_object* v_declName_2507_, lean_object* v_toPure_2508_, lean_object* v_____do__lift_2509_){
_start:
{
uint8_t v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = l_Lean_Meta_isMatcherLikeCore(v_____do__lift_2509_, v_declName_2507_);
v___x_2511_ = lean_box(v___x_2510_);
v___x_2512_ = lean_apply_2(v_toPure_2508_, lean_box(0), v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike___redArg(lean_object* v_inst_2513_, lean_object* v_inst_2514_, lean_object* v_declName_2515_){
_start:
{
lean_object* v_toApplicative_2516_; lean_object* v_toBind_2517_; lean_object* v_getEnv_2518_; lean_object* v_toPure_2519_; lean_object* v___f_2520_; lean_object* v___x_2521_; 
v_toApplicative_2516_ = lean_ctor_get(v_inst_2513_, 0);
lean_inc_ref(v_toApplicative_2516_);
v_toBind_2517_ = lean_ctor_get(v_inst_2513_, 1);
lean_inc(v_toBind_2517_);
lean_dec_ref(v_inst_2513_);
v_getEnv_2518_ = lean_ctor_get(v_inst_2514_, 0);
lean_inc(v_getEnv_2518_);
lean_dec_ref(v_inst_2514_);
v_toPure_2519_ = lean_ctor_get(v_toApplicative_2516_, 1);
lean_inc(v_toPure_2519_);
lean_dec_ref(v_toApplicative_2516_);
v___f_2520_ = lean_alloc_closure((void*)(l_Lean_Meta_isMatcherLike___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2520_, 0, v_declName_2515_);
lean_closure_set(v___f_2520_, 1, v_toPure_2519_);
v___x_2521_ = lean_apply_4(v_toBind_2517_, lean_box(0), lean_box(0), v_getEnv_2518_, v___f_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike(lean_object* v_m_2522_, lean_object* v_inst_2523_, lean_object* v_inst_2524_, lean_object* v_declName_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_Meta_isMatcherLike___redArg(v_inst_2523_, v_inst_2524_, v_declName_2525_);
return v___x_2526_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Match_instInhabitedDiscrInfo_default = _init_l_Lean_Meta_Match_instInhabitedDiscrInfo_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedDiscrInfo_default);
l_Lean_Meta_Match_instInhabitedDiscrInfo = _init_l_Lean_Meta_Match_instInhabitedDiscrInfo();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedDiscrInfo);
l_Lean_Meta_Match_instInhabitedOverlaps_default = _init_l_Lean_Meta_Match_instInhabitedOverlaps_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedOverlaps_default);
l_Lean_Meta_Match_instInhabitedOverlaps = _init_l_Lean_Meta_Match_instInhabitedOverlaps();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedOverlaps);
l_Lean_Meta_Match_instInhabitedMatcherInfo_default = _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatcherInfo_default);
l_Lean_Meta_Match_instInhabitedMatcherInfo = _init_l_Lean_Meta_Match_instInhabitedMatcherInfo();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatcherInfo);
l_Lean_Meta_Match_Extension_instInhabitedState = _init_l_Lean_Meta_Match_Extension_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Match_Extension_instInhabitedState);
res = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Match_Extension_extension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Match_Extension_extension);
lean_dec_ref(res);
res = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_matcherLikeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_matcherLikeExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_MatcherInfo(builtin);
}
#ifdef __cplusplus
}
#endif
