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
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedOverlaps_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedOverlaps;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2_value;
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3_value;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5_value;
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6_value;
static lean_once_cell_t l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7;
static lean_once_cell_t l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9_value;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.TreeSet.ofList "};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Match_instReprOverlaps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_instReprOverlaps_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Match_instReprOverlaps___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instReprOverlaps = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Overlaps_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_isEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_instInhabitedState;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_State_addEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t lean_is_matcher(lean_object*, lean_object*);
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
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_box(0);
v___x_72_ = lean_unsigned_to_nat(16u);
v___x_73_ = lean_mk_array(v___x_72_, v___x_71_);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0, &l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0_once, _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0);
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedOverlaps_default(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1, &l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedOverlaps(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_Match_instInhabitedOverlaps_default;
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_inc(v_x_79_);
return v_x_79_;
}
else
{
lean_object* v_key_81_; lean_object* v_value_82_; lean_object* v_tail_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_key_81_ = lean_ctor_get(v_x_80_, 0);
v_value_82_ = lean_ctor_get(v_x_80_, 1);
v_tail_83_ = lean_ctor_get(v_x_80_, 2);
v___x_84_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(v_x_79_, v_tail_83_);
lean_inc(v_value_82_);
lean_inc(v_key_81_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v_key_81_);
lean_ctor_set(v___x_85_, 1, v_value_82_);
v___x_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1___boxed(lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(v_x_87_, v_x_88_);
lean_dec(v_x_88_);
lean_dec(v_x_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(lean_object* v_as_90_, size_t v_i_91_, size_t v_stop_92_, lean_object* v_b_93_){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = lean_usize_dec_eq(v_i_91_, v_stop_92_);
if (v___x_94_ == 0)
{
size_t v___x_95_; size_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_sub(v_i_91_, v___x_95_);
v___x_97_ = lean_array_uget_borrowed(v_as_90_, v___x_96_);
v___x_98_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(v_b_93_, v___x_97_);
lean_dec(v_b_93_);
v_i_91_ = v___x_96_;
v_b_93_ = v___x_98_;
goto _start;
}
else
{
return v_b_93_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2___boxed(lean_object* v_as_100_, lean_object* v_i_101_, lean_object* v_stop_102_, lean_object* v_b_103_){
_start:
{
size_t v_i_boxed_104_; size_t v_stop_boxed_105_; lean_object* v_res_106_; 
v_i_boxed_104_ = lean_unbox_usize(v_i_101_);
lean_dec(v_i_101_);
v_stop_boxed_105_ = lean_unbox_usize(v_stop_102_);
lean_dec(v_stop_102_);
v_res_106_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(v_as_100_, v_i_boxed_104_, v_stop_boxed_105_, v_b_103_);
lean_dec_ref(v_as_100_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7_spec__10(lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
lean_dec(v_x_107_);
return v_x_108_;
}
else
{
lean_object* v_head_110_; lean_object* v_tail_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_122_; 
v_head_110_ = lean_ctor_get(v_x_109_, 0);
v_tail_111_ = lean_ctor_get(v_x_109_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_x_109_);
if (v_isSharedCheck_122_ == 0)
{
v___x_113_ = v_x_109_;
v_isShared_114_ = v_isSharedCheck_122_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_tail_111_);
lean_inc(v_head_110_);
lean_dec(v_x_109_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_122_;
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
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_x_108_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_x_107_);
v___x_116_ = v_reuseFailAlloc_121_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = l_Nat_reprFast(v_head_110_);
v___x_118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
v___x_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_116_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v_x_108_ = v___x_119_;
v_x_109_ = v_tail_111_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_dec(v_x_123_);
return v_x_124_;
}
else
{
lean_object* v_head_126_; lean_object* v_tail_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_138_; 
v_head_126_ = lean_ctor_get(v_x_125_, 0);
v_tail_127_ = lean_ctor_get(v_x_125_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_138_ == 0)
{
v___x_129_ = v_x_125_;
v_isShared_130_ = v_isSharedCheck_138_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_tail_127_);
lean_inc(v_head_126_);
lean_dec(v_x_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_138_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
lean_inc(v_x_123_);
if (v_isShared_130_ == 0)
{
lean_ctor_set_tag(v___x_129_, 5);
lean_ctor_set(v___x_129_, 1, v_x_123_);
lean_ctor_set(v___x_129_, 0, v_x_124_);
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_x_124_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_x_123_);
v___x_132_ = v_reuseFailAlloc_137_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = l_Nat_reprFast(v_head_126_);
v___x_134_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_132_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7_spec__10(v_x_123_, v___x_135_, v_tail_127_);
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = l_Nat_reprFast(v___y_139_);
v___x_141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v___x_144_; 
lean_dec(v_x_143_);
v___x_144_ = lean_box(0);
return v___x_144_;
}
else
{
lean_object* v_tail_145_; 
v_tail_145_ = lean_ctor_get(v_x_142_, 1);
if (lean_obj_tag(v_tail_145_) == 0)
{
lean_object* v_head_146_; lean_object* v___x_147_; 
lean_dec(v_x_143_);
v_head_146_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_head_146_);
lean_dec_ref_known(v_x_142_, 2);
v___x_147_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_146_);
return v___x_147_;
}
else
{
lean_object* v_head_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_inc(v_tail_145_);
v_head_148_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_head_148_);
lean_dec_ref_known(v_x_142_, 2);
v___x_149_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_148_);
v___x_150_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7(v_x_143_, v___x_149_, v_tail_145_);
return v___x_150_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_163_ = lean_string_length(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7);
v___x_165_ = lean_nat_to_int(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(lean_object* v_a_170_){
_start:
{
if (lean_obj_tag(v_a_170_) == 0)
{
lean_object* v___x_171_; 
v___x_171_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1));
return v___x_171_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; lean_object* v___x_181_; 
v___x_172_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_173_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5(v_a_170_, v___x_172_);
v___x_174_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8);
v___x_175_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9));
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_173_);
v___x_177_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10));
v___x_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_174_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = 0;
v___x_181_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_180_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_dec(v_x_182_);
return v_x_183_;
}
else
{
lean_object* v_head_185_; lean_object* v_tail_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_195_; 
v_head_185_ = lean_ctor_get(v_x_184_, 0);
v_tail_186_ = lean_ctor_get(v_x_184_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_195_ == 0)
{
v___x_188_ = v_x_184_;
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_tail_186_);
lean_inc(v_head_185_);
lean_dec(v_x_184_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
lean_inc(v_x_182_);
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 5);
lean_ctor_set(v___x_188_, 1, v_x_182_);
lean_ctor_set(v___x_188_, 0, v_x_183_);
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_x_183_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_x_182_);
v___x_191_ = v_reuseFailAlloc_194_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_head_185_);
v_x_183_ = v___x_192_;
v_x_184_ = v_tail_186_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3(lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v___x_198_; 
lean_dec(v_x_197_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
lean_object* v_tail_199_; 
v_tail_199_ = lean_ctor_get(v_x_196_, 1);
if (lean_obj_tag(v_tail_199_) == 0)
{
lean_object* v_head_200_; 
lean_dec(v_x_197_);
v_head_200_ = lean_ctor_get(v_x_196_, 0);
lean_inc(v_head_200_);
lean_dec_ref_known(v_x_196_, 2);
return v_head_200_;
}
else
{
lean_object* v_head_201_; lean_object* v___x_202_; 
lean_inc(v_tail_199_);
v_head_201_ = lean_ctor_get(v_x_196_, 0);
lean_inc(v_head_201_);
lean_dec_ref_known(v_x_196_, 2);
v___x_202_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3_spec__7(v_x_197_, v_head_201_, v_tail_199_);
return v___x_202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(lean_object* v_init_203_, lean_object* v_x_204_){
_start:
{
if (lean_obj_tag(v_x_204_) == 0)
{
lean_object* v_k_205_; lean_object* v_l_206_; lean_object* v_r_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_k_205_ = lean_ctor_get(v_x_204_, 1);
v_l_206_ = lean_ctor_get(v_x_204_, 3);
v_r_207_ = lean_ctor_get(v_x_204_, 4);
v___x_208_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v_init_203_, v_r_207_);
lean_inc(v_k_205_);
v___x_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_209_, 0, v_k_205_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v_init_203_ = v___x_209_;
v_x_204_ = v_l_206_;
goto _start;
}
else
{
return v_init_203_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_init_211_, lean_object* v_x_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v_init_211_, v_x_212_);
lean_dec(v_x_212_);
return v_res_213_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0));
v___x_220_ = lean_string_length(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4);
v___x_222_ = lean_nat_to_int(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(lean_object* v_x_227_){
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
v___x_239_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2));
v___x_240_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v___x_235_, v_snd_229_);
lean_dec(v_snd_229_);
v___x_241_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(v___x_240_);
v___x_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_239_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = l_Repr_addAppParen(v___x_242_, v___x_238_);
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_237_);
v___x_245_ = l_List_reverse___redArg(v___x_244_);
v___x_246_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_247_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3(v___x_245_, v___x_246_);
v___x_248_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5);
v___x_249_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6));
v___x_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_247_);
v___x_251_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7));
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
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5_spec__10(lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_){
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
v___x_268_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_261_);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5(lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_){
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
v___x_283_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_276_);
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5_spec__10(v_x_273_, v___x_284_, v_tail_277_);
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1(lean_object* v_x_288_, lean_object* v_x_289_){
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
v___x_293_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_292_);
return v___x_293_;
}
else
{
lean_object* v_head_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
lean_inc(v_tail_291_);
v_head_294_ = lean_ctor_get(v_x_288_, 0);
lean_inc(v_head_294_);
lean_dec_ref_known(v_x_288_, 2);
v___x_295_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_294_);
v___x_296_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5(v_x_289_, v___x_295_, v_tail_291_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(lean_object* v_a_297_){
_start:
{
if (lean_obj_tag(v_a_297_) == 0)
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1));
return v___x_298_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; lean_object* v___x_308_; 
v___x_299_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_300_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1(v_a_297_, v___x_299_);
v___x_301_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8);
v___x_302_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9));
v___x_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_300_);
v___x_304_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10));
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
lean_object* v_buckets_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_356_; 
v_buckets_324_ = lean_ctor_get(v_x_323_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v_x_323_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; 
v_unused_357_ = lean_ctor_get(v_x_323_, 0);
lean_dec(v_unused_357_);
v___x_326_ = v_x_323_;
v_isShared_327_ = v_isSharedCheck_356_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_buckets_324_);
lean_dec(v_x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_356_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___y_333_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_328_ = ((lean_object*)(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3));
v___x_329_ = lean_obj_once(&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4, &l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4_once, _init_l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = ((lean_object*)(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6));
v___x_350_ = lean_box(0);
v___x_351_ = lean_array_get_size(v_buckets_324_);
v___x_352_ = lean_nat_dec_lt(v___x_330_, v___x_351_);
if (v___x_352_ == 0)
{
lean_dec_ref(v_buckets_324_);
v___y_333_ = v___x_350_;
goto v___jp_332_;
}
else
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_usize_of_nat(v___x_351_);
v___x_354_ = ((size_t)0ULL);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(v_buckets_324_, v___x_353_, v___x_354_, v___x_350_);
lean_dec_ref(v_buckets_324_);
v___y_333_ = v___x_355_;
goto v___jp_332_;
}
v___jp_332_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_334_ = l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(v___y_333_);
if (v_isShared_327_ == 0)
{
lean_ctor_set_tag(v___x_326_, 5);
lean_ctor_set(v___x_326_, 1, v___x_334_);
lean_ctor_set(v___x_326_, 0, v___x_331_);
v___x_336_ = v___x_326_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_334_);
v___x_336_ = v_reuseFailAlloc_349_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_337_ = l_Repr_addAppParen(v___x_336_, v___x_330_);
v___x_338_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_329_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = 0;
v___x_340_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*1, v___x_339_);
v___x_341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_328_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_343_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___x_341_);
v___x_345_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_342_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*1, v___x_339_);
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr(lean_object* v_x_358_, lean_object* v_prec_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg(v_x_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___boxed(lean_object* v_x_361_, lean_object* v_prec_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_Match_instReprOverlaps_repr(v_x_361_, v_prec_362_);
lean_dec(v_prec_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(lean_object* v_a_364_, lean_object* v_n_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(v_a_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___boxed(lean_object* v_a_367_, lean_object* v_n_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(v_a_367_, v_n_368_);
lean_dec(v_n_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0(lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_x_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___boxed(lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0(v_x_373_, v_x_374_);
lean_dec(v_x_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2(lean_object* v_a_376_, lean_object* v_n_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(v_a_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_a_379_, lean_object* v_n_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2(v_a_379_, v_n_380_);
lean_dec(v_n_380_);
return v_res_381_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Overlaps_isEmpty(lean_object* v_o_384_){
_start:
{
lean_object* v_size_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_size_385_ = lean_ctor_get(v_o_384_, 0);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_nat_dec_eq(v_size_385_, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_isEmpty___boxed(lean_object* v_o_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_o_388_);
lean_dec_ref(v_o_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(lean_object* v_k_391_, lean_object* v_t_392_){
_start:
{
if (lean_obj_tag(v_t_392_) == 0)
{
lean_object* v_k_393_; lean_object* v_l_394_; lean_object* v_r_395_; uint8_t v___x_396_; 
v_k_393_ = lean_ctor_get(v_t_392_, 1);
v_l_394_ = lean_ctor_get(v_t_392_, 3);
v_r_395_ = lean_ctor_get(v_t_392_, 4);
v___x_396_ = lean_nat_dec_lt(v_k_391_, v_k_393_);
if (v___x_396_ == 0)
{
uint8_t v___x_397_; 
v___x_397_ = lean_nat_dec_eq(v_k_391_, v_k_393_);
if (v___x_397_ == 0)
{
v_t_392_ = v_r_395_;
goto _start;
}
else
{
return v___x_397_;
}
}
else
{
v_t_392_ = v_l_394_;
goto _start;
}
}
else
{
uint8_t v___x_400_; 
v___x_400_ = 0;
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg___boxed(lean_object* v_k_401_, lean_object* v_t_402_){
_start:
{
uint8_t v_res_403_; lean_object* v_r_404_; 
v_res_403_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_k_401_, v_t_402_);
lean_dec(v_t_402_);
lean_dec(v_k_401_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(lean_object* v_k_405_, lean_object* v_v_406_, lean_object* v_t_407_){
_start:
{
if (lean_obj_tag(v_t_407_) == 0)
{
lean_object* v_size_408_; lean_object* v_k_409_; lean_object* v_v_410_; lean_object* v_l_411_; lean_object* v_r_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_693_; 
v_size_408_ = lean_ctor_get(v_t_407_, 0);
v_k_409_ = lean_ctor_get(v_t_407_, 1);
v_v_410_ = lean_ctor_get(v_t_407_, 2);
v_l_411_ = lean_ctor_get(v_t_407_, 3);
v_r_412_ = lean_ctor_get(v_t_407_, 4);
v_isSharedCheck_693_ = !lean_is_exclusive(v_t_407_);
if (v_isSharedCheck_693_ == 0)
{
v___x_414_ = v_t_407_;
v_isShared_415_ = v_isSharedCheck_693_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_r_412_);
lean_inc(v_l_411_);
lean_inc(v_v_410_);
lean_inc(v_k_409_);
lean_inc(v_size_408_);
lean_dec(v_t_407_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_693_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
uint8_t v___x_416_; 
v___x_416_ = lean_nat_dec_lt(v_k_405_, v_k_409_);
if (v___x_416_ == 0)
{
uint8_t v___x_417_; 
v___x_417_ = lean_nat_dec_eq(v_k_405_, v_k_409_);
if (v___x_417_ == 0)
{
lean_object* v_impl_418_; lean_object* v___x_419_; 
lean_dec(v_size_408_);
v_impl_418_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_405_, v_v_406_, v_r_412_);
v___x_419_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_411_) == 0)
{
lean_object* v_size_420_; lean_object* v_size_421_; lean_object* v_k_422_; lean_object* v_v_423_; lean_object* v_l_424_; lean_object* v_r_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_size_420_ = lean_ctor_get(v_l_411_, 0);
v_size_421_ = lean_ctor_get(v_impl_418_, 0);
lean_inc(v_size_421_);
v_k_422_ = lean_ctor_get(v_impl_418_, 1);
lean_inc(v_k_422_);
v_v_423_ = lean_ctor_get(v_impl_418_, 2);
lean_inc(v_v_423_);
v_l_424_ = lean_ctor_get(v_impl_418_, 3);
lean_inc(v_l_424_);
v_r_425_ = lean_ctor_get(v_impl_418_, 4);
lean_inc(v_r_425_);
v___x_426_ = lean_unsigned_to_nat(3u);
v___x_427_ = lean_nat_mul(v___x_426_, v_size_420_);
v___x_428_ = lean_nat_dec_lt(v___x_427_, v_size_421_);
lean_dec(v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
lean_dec(v_r_425_);
lean_dec(v_l_424_);
lean_dec(v_v_423_);
lean_dec(v_k_422_);
v___x_429_ = lean_nat_add(v___x_419_, v_size_420_);
v___x_430_ = lean_nat_add(v___x_429_, v_size_421_);
lean_dec(v_size_421_);
lean_dec(v___x_429_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v_impl_418_);
lean_ctor_set(v___x_414_, 0, v___x_430_);
v___x_432_ = v___x_414_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_l_411_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v_impl_418_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
else
{
lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_497_; 
v_isSharedCheck_497_ = !lean_is_exclusive(v_impl_418_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; lean_object* v_unused_499_; lean_object* v_unused_500_; lean_object* v_unused_501_; lean_object* v_unused_502_; 
v_unused_498_ = lean_ctor_get(v_impl_418_, 4);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_impl_418_, 3);
lean_dec(v_unused_499_);
v_unused_500_ = lean_ctor_get(v_impl_418_, 2);
lean_dec(v_unused_500_);
v_unused_501_ = lean_ctor_get(v_impl_418_, 1);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_impl_418_, 0);
lean_dec(v_unused_502_);
v___x_435_ = v_impl_418_;
v_isShared_436_ = v_isSharedCheck_497_;
goto v_resetjp_434_;
}
else
{
lean_dec(v_impl_418_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_497_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_size_437_; lean_object* v_k_438_; lean_object* v_v_439_; lean_object* v_l_440_; lean_object* v_r_441_; lean_object* v_size_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v_size_437_ = lean_ctor_get(v_l_424_, 0);
v_k_438_ = lean_ctor_get(v_l_424_, 1);
v_v_439_ = lean_ctor_get(v_l_424_, 2);
v_l_440_ = lean_ctor_get(v_l_424_, 3);
v_r_441_ = lean_ctor_get(v_l_424_, 4);
v_size_442_ = lean_ctor_get(v_r_425_, 0);
v___x_443_ = lean_unsigned_to_nat(2u);
v___x_444_ = lean_nat_mul(v___x_443_, v_size_442_);
v___x_445_ = lean_nat_dec_lt(v_size_437_, v___x_444_);
lean_dec(v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_473_; 
lean_inc(v_r_441_);
lean_inc(v_l_440_);
lean_inc(v_v_439_);
lean_inc(v_k_438_);
v_isSharedCheck_473_ = !lean_is_exclusive(v_l_424_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_474_ = lean_ctor_get(v_l_424_, 4);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_l_424_, 3);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_l_424_, 2);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_l_424_, 1);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_l_424_, 0);
lean_dec(v_unused_478_);
v___x_447_ = v_l_424_;
v_isShared_448_ = v_isSharedCheck_473_;
goto v_resetjp_446_;
}
else
{
lean_dec(v_l_424_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_473_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_463_; 
v___x_449_ = lean_nat_add(v___x_419_, v_size_420_);
v___x_450_ = lean_nat_add(v___x_449_, v_size_421_);
lean_dec(v_size_421_);
if (lean_obj_tag(v_l_440_) == 0)
{
lean_object* v_size_471_; 
v_size_471_ = lean_ctor_get(v_l_440_, 0);
lean_inc(v_size_471_);
v___y_463_ = v_size_471_;
goto v___jp_462_;
}
else
{
lean_object* v___x_472_; 
v___x_472_ = lean_unsigned_to_nat(0u);
v___y_463_ = v___x_472_;
goto v___jp_462_;
}
v___jp_451_:
{
lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_455_ = lean_nat_add(v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec(v___y_453_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 4, v_r_425_);
lean_ctor_set(v___x_447_, 3, v_r_441_);
lean_ctor_set(v___x_447_, 2, v_v_423_);
lean_ctor_set(v___x_447_, 1, v_k_422_);
lean_ctor_set(v___x_447_, 0, v___x_455_);
v___x_457_ = v___x_447_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_k_422_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v_v_423_);
lean_ctor_set(v_reuseFailAlloc_461_, 3, v_r_441_);
lean_ctor_set(v_reuseFailAlloc_461_, 4, v_r_425_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 4, v___x_457_);
lean_ctor_set(v___x_435_, 3, v___y_452_);
lean_ctor_set(v___x_435_, 2, v_v_439_);
lean_ctor_set(v___x_435_, 1, v_k_438_);
lean_ctor_set(v___x_435_, 0, v___x_450_);
v___x_459_ = v___x_435_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_k_438_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v_v_439_);
lean_ctor_set(v_reuseFailAlloc_460_, 3, v___y_452_);
lean_ctor_set(v_reuseFailAlloc_460_, 4, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
v___jp_462_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_nat_add(v___x_449_, v___y_463_);
lean_dec(v___y_463_);
lean_dec(v___x_449_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v_l_440_);
lean_ctor_set(v___x_414_, 0, v___x_464_);
v___x_466_ = v___x_414_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v_l_411_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v_l_440_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; 
v___x_467_ = lean_nat_add(v___x_419_, v_size_442_);
if (lean_obj_tag(v_r_441_) == 0)
{
lean_object* v_size_468_; 
v_size_468_ = lean_ctor_get(v_r_441_, 0);
lean_inc(v_size_468_);
v___y_452_ = v___x_466_;
v___y_453_ = v___x_467_;
v___y_454_ = v_size_468_;
goto v___jp_451_;
}
else
{
lean_object* v___x_469_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v___y_452_ = v___x_466_;
v___y_453_ = v___x_467_;
v___y_454_ = v___x_469_;
goto v___jp_451_;
}
}
}
}
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
lean_del_object(v___x_414_);
v___x_479_ = lean_nat_add(v___x_419_, v_size_420_);
v___x_480_ = lean_nat_add(v___x_479_, v_size_421_);
lean_dec(v_size_421_);
v___x_481_ = lean_nat_add(v___x_479_, v_size_437_);
lean_dec(v___x_479_);
lean_inc_ref(v_l_411_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 4, v_l_424_);
lean_ctor_set(v___x_435_, 3, v_l_411_);
lean_ctor_set(v___x_435_, 2, v_v_410_);
lean_ctor_set(v___x_435_, 1, v_k_409_);
lean_ctor_set(v___x_435_, 0, v___x_481_);
v___x_483_ = v___x_435_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_l_411_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_l_424_);
v___x_483_ = v_reuseFailAlloc_496_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_isSharedCheck_490_ = !lean_is_exclusive(v_l_411_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; lean_object* v_unused_492_; lean_object* v_unused_493_; lean_object* v_unused_494_; lean_object* v_unused_495_; 
v_unused_491_ = lean_ctor_get(v_l_411_, 4);
lean_dec(v_unused_491_);
v_unused_492_ = lean_ctor_get(v_l_411_, 3);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_l_411_, 2);
lean_dec(v_unused_493_);
v_unused_494_ = lean_ctor_get(v_l_411_, 1);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_l_411_, 0);
lean_dec(v_unused_495_);
v___x_485_ = v_l_411_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_dec(v_l_411_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 4, v_r_425_);
lean_ctor_set(v___x_485_, 3, v___x_483_);
lean_ctor_set(v___x_485_, 2, v_v_423_);
lean_ctor_set(v___x_485_, 1, v_k_422_);
lean_ctor_set(v___x_485_, 0, v___x_480_);
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_k_422_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v_v_423_);
lean_ctor_set(v_reuseFailAlloc_489_, 3, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_489_, 4, v_r_425_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_503_; 
v_l_503_ = lean_ctor_get(v_impl_418_, 3);
lean_inc(v_l_503_);
if (lean_obj_tag(v_l_503_) == 0)
{
lean_object* v_r_504_; lean_object* v_k_505_; lean_object* v_v_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_529_; 
v_r_504_ = lean_ctor_get(v_impl_418_, 4);
v_k_505_ = lean_ctor_get(v_impl_418_, 1);
v_v_506_ = lean_ctor_get(v_impl_418_, 2);
v_isSharedCheck_529_ = !lean_is_exclusive(v_impl_418_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; lean_object* v_unused_531_; 
v_unused_530_ = lean_ctor_get(v_impl_418_, 3);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_impl_418_, 0);
lean_dec(v_unused_531_);
v___x_508_ = v_impl_418_;
v_isShared_509_ = v_isSharedCheck_529_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_r_504_);
lean_inc(v_v_506_);
lean_inc(v_k_505_);
lean_dec(v_impl_418_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_529_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v_k_510_; lean_object* v_v_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_525_; 
v_k_510_ = lean_ctor_get(v_l_503_, 1);
v_v_511_ = lean_ctor_get(v_l_503_, 2);
v_isSharedCheck_525_ = !lean_is_exclusive(v_l_503_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; lean_object* v_unused_527_; lean_object* v_unused_528_; 
v_unused_526_ = lean_ctor_get(v_l_503_, 4);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_l_503_, 3);
lean_dec(v_unused_527_);
v_unused_528_ = lean_ctor_get(v_l_503_, 0);
lean_dec(v_unused_528_);
v___x_513_ = v_l_503_;
v_isShared_514_ = v_isSharedCheck_525_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_v_511_);
lean_inc(v_k_510_);
lean_dec(v_l_503_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_525_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_504_, 2);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 4, v_r_504_);
lean_ctor_set(v___x_513_, 3, v_r_504_);
lean_ctor_set(v___x_513_, 2, v_v_410_);
lean_ctor_set(v___x_513_, 1, v_k_409_);
lean_ctor_set(v___x_513_, 0, v___x_419_);
v___x_517_ = v___x_513_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_r_504_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_r_504_);
v___x_517_ = v_reuseFailAlloc_524_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_519_; 
lean_inc(v_r_504_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 3, v_r_504_);
lean_ctor_set(v___x_508_, 0, v___x_419_);
v___x_519_ = v___x_508_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_k_505_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_v_506_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_r_504_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v_r_504_);
v___x_519_ = v_reuseFailAlloc_523_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_521_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v___x_519_);
lean_ctor_set(v___x_414_, 3, v___x_517_);
lean_ctor_set(v___x_414_, 2, v_v_511_);
lean_ctor_set(v___x_414_, 1, v_k_510_);
lean_ctor_set(v___x_414_, 0, v___x_515_);
v___x_521_ = v___x_414_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_k_510_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_v_511_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
}
else
{
lean_object* v_r_532_; 
v_r_532_ = lean_ctor_get(v_impl_418_, 4);
lean_inc(v_r_532_);
if (lean_obj_tag(v_r_532_) == 0)
{
lean_object* v_k_533_; lean_object* v_v_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_545_; 
v_k_533_ = lean_ctor_get(v_impl_418_, 1);
v_v_534_ = lean_ctor_get(v_impl_418_, 2);
v_isSharedCheck_545_ = !lean_is_exclusive(v_impl_418_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; lean_object* v_unused_547_; lean_object* v_unused_548_; 
v_unused_546_ = lean_ctor_get(v_impl_418_, 4);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_impl_418_, 3);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_impl_418_, 0);
lean_dec(v_unused_548_);
v___x_536_ = v_impl_418_;
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_v_534_);
lean_inc(v_k_533_);
lean_dec(v_impl_418_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_unsigned_to_nat(3u);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 4, v_l_503_);
lean_ctor_set(v___x_536_, 2, v_v_410_);
lean_ctor_set(v___x_536_, 1, v_k_409_);
lean_ctor_set(v___x_536_, 0, v___x_419_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_544_, 3, v_l_503_);
lean_ctor_set(v_reuseFailAlloc_544_, 4, v_l_503_);
v___x_540_ = v_reuseFailAlloc_544_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v_r_532_);
lean_ctor_set(v___x_414_, 3, v___x_540_);
lean_ctor_set(v___x_414_, 2, v_v_534_);
lean_ctor_set(v___x_414_, 1, v_k_533_);
lean_ctor_set(v___x_414_, 0, v___x_538_);
v___x_542_ = v___x_414_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_543_, 3, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_543_, 4, v_r_532_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_unsigned_to_nat(2u);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v_impl_418_);
lean_ctor_set(v___x_414_, 3, v_r_532_);
lean_ctor_set(v___x_414_, 0, v___x_549_);
v___x_551_ = v___x_414_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_r_532_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_impl_418_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
else
{
lean_object* v___x_554_; 
lean_dec(v_v_410_);
lean_dec(v_k_409_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 2, v_v_406_);
lean_ctor_set(v___x_414_, 1, v_k_405_);
v___x_554_ = v___x_414_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_size_408_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_k_405_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_v_406_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_l_411_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_r_412_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
else
{
lean_object* v_impl_556_; lean_object* v___x_557_; 
lean_dec(v_size_408_);
v_impl_556_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_405_, v_v_406_, v_l_411_);
v___x_557_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_412_) == 0)
{
lean_object* v_size_558_; lean_object* v_size_559_; lean_object* v_k_560_; lean_object* v_v_561_; lean_object* v_l_562_; lean_object* v_r_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_size_558_ = lean_ctor_get(v_r_412_, 0);
v_size_559_ = lean_ctor_get(v_impl_556_, 0);
lean_inc(v_size_559_);
v_k_560_ = lean_ctor_get(v_impl_556_, 1);
lean_inc(v_k_560_);
v_v_561_ = lean_ctor_get(v_impl_556_, 2);
lean_inc(v_v_561_);
v_l_562_ = lean_ctor_get(v_impl_556_, 3);
lean_inc(v_l_562_);
v_r_563_ = lean_ctor_get(v_impl_556_, 4);
lean_inc(v_r_563_);
v___x_564_ = lean_unsigned_to_nat(3u);
v___x_565_ = lean_nat_mul(v___x_564_, v_size_558_);
v___x_566_ = lean_nat_dec_lt(v___x_565_, v_size_559_);
lean_dec(v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec(v_r_563_);
lean_dec(v_l_562_);
lean_dec(v_v_561_);
lean_dec(v_k_560_);
v___x_567_ = lean_nat_add(v___x_557_, v_size_559_);
lean_dec(v_size_559_);
v___x_568_ = lean_nat_add(v___x_567_, v_size_558_);
lean_dec(v___x_567_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 3, v_impl_556_);
lean_ctor_set(v___x_414_, 0, v___x_568_);
v___x_570_ = v___x_414_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_impl_556_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v_r_412_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
else
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_637_; 
v_isSharedCheck_637_ = !lean_is_exclusive(v_impl_556_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; lean_object* v_unused_639_; lean_object* v_unused_640_; lean_object* v_unused_641_; lean_object* v_unused_642_; 
v_unused_638_ = lean_ctor_get(v_impl_556_, 4);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_impl_556_, 3);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_impl_556_, 2);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_impl_556_, 1);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_impl_556_, 0);
lean_dec(v_unused_642_);
v___x_573_ = v_impl_556_;
v_isShared_574_ = v_isSharedCheck_637_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_impl_556_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_637_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_size_575_; lean_object* v_size_576_; lean_object* v_k_577_; lean_object* v_v_578_; lean_object* v_l_579_; lean_object* v_r_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_size_575_ = lean_ctor_get(v_l_562_, 0);
v_size_576_ = lean_ctor_get(v_r_563_, 0);
v_k_577_ = lean_ctor_get(v_r_563_, 1);
v_v_578_ = lean_ctor_get(v_r_563_, 2);
v_l_579_ = lean_ctor_get(v_r_563_, 3);
v_r_580_ = lean_ctor_get(v_r_563_, 4);
v___x_581_ = lean_unsigned_to_nat(2u);
v___x_582_ = lean_nat_mul(v___x_581_, v_size_575_);
v___x_583_ = lean_nat_dec_lt(v_size_576_, v___x_582_);
lean_dec(v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_612_; 
lean_inc(v_r_580_);
lean_inc(v_l_579_);
lean_inc(v_v_578_);
lean_inc(v_k_577_);
v_isSharedCheck_612_ = !lean_is_exclusive(v_r_563_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; lean_object* v_unused_614_; lean_object* v_unused_615_; lean_object* v_unused_616_; lean_object* v_unused_617_; 
v_unused_613_ = lean_ctor_get(v_r_563_, 4);
lean_dec(v_unused_613_);
v_unused_614_ = lean_ctor_get(v_r_563_, 3);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_r_563_, 2);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_r_563_, 1);
lean_dec(v_unused_616_);
v_unused_617_ = lean_ctor_get(v_r_563_, 0);
lean_dec(v_unused_617_);
v___x_585_ = v_r_563_;
v_isShared_586_ = v_isSharedCheck_612_;
goto v_resetjp_584_;
}
else
{
lean_dec(v_r_563_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_612_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___x_600_; lean_object* v___y_602_; 
v___x_587_ = lean_nat_add(v___x_557_, v_size_559_);
lean_dec(v_size_559_);
v___x_588_ = lean_nat_add(v___x_587_, v_size_558_);
lean_dec(v___x_587_);
v___x_600_ = lean_nat_add(v___x_557_, v_size_575_);
if (lean_obj_tag(v_l_579_) == 0)
{
lean_object* v_size_610_; 
v_size_610_ = lean_ctor_get(v_l_579_, 0);
lean_inc(v_size_610_);
v___y_602_ = v_size_610_;
goto v___jp_601_;
}
else
{
lean_object* v___x_611_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___y_602_ = v___x_611_;
goto v___jp_601_;
}
v___jp_589_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = lean_nat_add(v___y_590_, v___y_592_);
lean_dec(v___y_592_);
lean_dec(v___y_590_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 4, v_r_412_);
lean_ctor_set(v___x_585_, 3, v_r_580_);
lean_ctor_set(v___x_585_, 2, v_v_410_);
lean_ctor_set(v___x_585_, 1, v_k_409_);
lean_ctor_set(v___x_585_, 0, v___x_593_);
v___x_595_ = v___x_585_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_r_580_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v_r_412_);
v___x_595_ = v_reuseFailAlloc_599_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_597_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 4, v___x_595_);
lean_ctor_set(v___x_573_, 3, v___y_591_);
lean_ctor_set(v___x_573_, 2, v_v_578_);
lean_ctor_set(v___x_573_, 1, v_k_577_);
lean_ctor_set(v___x_573_, 0, v___x_588_);
v___x_597_ = v___x_573_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_k_577_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_v_578_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v___y_591_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
v___jp_601_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = lean_nat_add(v___x_600_, v___y_602_);
lean_dec(v___y_602_);
lean_dec(v___x_600_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v_l_579_);
lean_ctor_set(v___x_414_, 3, v_l_562_);
lean_ctor_set(v___x_414_, 2, v_v_561_);
lean_ctor_set(v___x_414_, 1, v_k_560_);
lean_ctor_set(v___x_414_, 0, v___x_603_);
v___x_605_ = v___x_414_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_l_562_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_l_579_);
v___x_605_ = v_reuseFailAlloc_609_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; 
v___x_606_ = lean_nat_add(v___x_557_, v_size_558_);
if (lean_obj_tag(v_r_580_) == 0)
{
lean_object* v_size_607_; 
v_size_607_ = lean_ctor_get(v_r_580_, 0);
lean_inc(v_size_607_);
v___y_590_ = v___x_606_;
v___y_591_ = v___x_605_;
v___y_592_ = v_size_607_;
goto v___jp_589_;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___y_590_ = v___x_606_;
v___y_591_ = v___x_605_;
v___y_592_ = v___x_608_;
goto v___jp_589_;
}
}
}
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
lean_del_object(v___x_414_);
v___x_618_ = lean_nat_add(v___x_557_, v_size_559_);
lean_dec(v_size_559_);
v___x_619_ = lean_nat_add(v___x_618_, v_size_558_);
lean_dec(v___x_618_);
v___x_620_ = lean_nat_add(v___x_557_, v_size_558_);
v___x_621_ = lean_nat_add(v___x_620_, v_size_576_);
lean_dec(v___x_620_);
lean_inc_ref(v_r_412_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 4, v_r_412_);
lean_ctor_set(v___x_573_, 3, v_r_563_);
lean_ctor_set(v___x_573_, 2, v_v_410_);
lean_ctor_set(v___x_573_, 1, v_k_409_);
lean_ctor_set(v___x_573_, 0, v___x_621_);
v___x_623_ = v___x_573_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_r_563_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_r_412_);
v___x_623_ = v_reuseFailAlloc_636_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_isSharedCheck_630_ = !lean_is_exclusive(v_r_412_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; lean_object* v_unused_632_; lean_object* v_unused_633_; lean_object* v_unused_634_; lean_object* v_unused_635_; 
v_unused_631_ = lean_ctor_get(v_r_412_, 4);
lean_dec(v_unused_631_);
v_unused_632_ = lean_ctor_get(v_r_412_, 3);
lean_dec(v_unused_632_);
v_unused_633_ = lean_ctor_get(v_r_412_, 2);
lean_dec(v_unused_633_);
v_unused_634_ = lean_ctor_get(v_r_412_, 1);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_r_412_, 0);
lean_dec(v_unused_635_);
v___x_625_ = v_r_412_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_dec(v_r_412_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v___x_623_);
lean_ctor_set(v___x_625_, 3, v_l_562_);
lean_ctor_set(v___x_625_, 2, v_v_561_);
lean_ctor_set(v___x_625_, 1, v_k_560_);
lean_ctor_set(v___x_625_, 0, v___x_619_);
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_629_, 3, v_l_562_);
lean_ctor_set(v_reuseFailAlloc_629_, 4, v___x_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_643_; 
v_l_643_ = lean_ctor_get(v_impl_556_, 3);
lean_inc(v_l_643_);
if (lean_obj_tag(v_l_643_) == 0)
{
lean_object* v_r_644_; lean_object* v_k_645_; lean_object* v_v_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_657_; 
v_r_644_ = lean_ctor_get(v_impl_556_, 4);
v_k_645_ = lean_ctor_get(v_impl_556_, 1);
v_v_646_ = lean_ctor_get(v_impl_556_, 2);
v_isSharedCheck_657_ = !lean_is_exclusive(v_impl_556_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; lean_object* v_unused_659_; 
v_unused_658_ = lean_ctor_get(v_impl_556_, 3);
lean_dec(v_unused_658_);
v_unused_659_ = lean_ctor_get(v_impl_556_, 0);
lean_dec(v_unused_659_);
v___x_648_ = v_impl_556_;
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_r_644_);
lean_inc(v_v_646_);
lean_inc(v_k_645_);
lean_dec(v_impl_556_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_644_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 3, v_r_644_);
lean_ctor_set(v___x_648_, 2, v_v_410_);
lean_ctor_set(v___x_648_, 1, v_k_409_);
lean_ctor_set(v___x_648_, 0, v___x_557_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_656_, 3, v_r_644_);
lean_ctor_set(v_reuseFailAlloc_656_, 4, v_r_644_);
v___x_652_ = v_reuseFailAlloc_656_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_654_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v___x_652_);
lean_ctor_set(v___x_414_, 3, v_l_643_);
lean_ctor_set(v___x_414_, 2, v_v_646_);
lean_ctor_set(v___x_414_, 1, v_k_645_);
lean_ctor_set(v___x_414_, 0, v___x_650_);
v___x_654_ = v___x_414_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_k_645_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_v_646_);
lean_ctor_set(v_reuseFailAlloc_655_, 3, v_l_643_);
lean_ctor_set(v_reuseFailAlloc_655_, 4, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v_r_660_; 
v_r_660_ = lean_ctor_get(v_impl_556_, 4);
lean_inc(v_r_660_);
if (lean_obj_tag(v_r_660_) == 0)
{
lean_object* v_k_661_; lean_object* v_v_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_685_; 
v_k_661_ = lean_ctor_get(v_impl_556_, 1);
v_v_662_ = lean_ctor_get(v_impl_556_, 2);
v_isSharedCheck_685_ = !lean_is_exclusive(v_impl_556_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; lean_object* v_unused_687_; lean_object* v_unused_688_; 
v_unused_686_ = lean_ctor_get(v_impl_556_, 4);
lean_dec(v_unused_686_);
v_unused_687_ = lean_ctor_get(v_impl_556_, 3);
lean_dec(v_unused_687_);
v_unused_688_ = lean_ctor_get(v_impl_556_, 0);
lean_dec(v_unused_688_);
v___x_664_ = v_impl_556_;
v_isShared_665_ = v_isSharedCheck_685_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_v_662_);
lean_inc(v_k_661_);
lean_dec(v_impl_556_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_685_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v_k_666_; lean_object* v_v_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_681_; 
v_k_666_ = lean_ctor_get(v_r_660_, 1);
v_v_667_ = lean_ctor_get(v_r_660_, 2);
v_isSharedCheck_681_ = !lean_is_exclusive(v_r_660_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; lean_object* v_unused_683_; lean_object* v_unused_684_; 
v_unused_682_ = lean_ctor_get(v_r_660_, 4);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_r_660_, 3);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_r_660_, 0);
lean_dec(v_unused_684_);
v___x_669_ = v_r_660_;
v_isShared_670_ = v_isSharedCheck_681_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_v_667_);
lean_inc(v_k_666_);
lean_dec(v_r_660_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_681_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = lean_unsigned_to_nat(3u);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v_l_643_);
lean_ctor_set(v___x_669_, 3, v_l_643_);
lean_ctor_set(v___x_669_, 2, v_v_662_);
lean_ctor_set(v___x_669_, 1, v_k_661_);
lean_ctor_set(v___x_669_, 0, v___x_557_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_k_661_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_v_662_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_l_643_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_l_643_);
v___x_673_ = v_reuseFailAlloc_680_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_675_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v_l_643_);
lean_ctor_set(v___x_664_, 2, v_v_410_);
lean_ctor_set(v___x_664_, 1, v_k_409_);
lean_ctor_set(v___x_664_, 0, v___x_557_);
v___x_675_ = v___x_664_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_l_643_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_l_643_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v___x_675_);
lean_ctor_set(v___x_414_, 3, v___x_673_);
lean_ctor_set(v___x_414_, 2, v_v_667_);
lean_ctor_set(v___x_414_, 1, v_k_666_);
lean_ctor_set(v___x_414_, 0, v___x_671_);
v___x_677_ = v___x_414_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_k_666_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_v_667_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
else
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_unsigned_to_nat(2u);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v_r_660_);
lean_ctor_set(v___x_414_, 3, v_impl_556_);
lean_ctor_set(v___x_414_, 0, v___x_689_);
v___x_691_ = v___x_414_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_impl_556_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_r_660_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_k_405_);
lean_ctor_set(v___x_695_, 2, v_v_406_);
lean_ctor_set(v___x_695_, 3, v_t_407_);
lean_ctor_set(v___x_695_, 4, v_t_407_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(lean_object* v_overlapping_696_, lean_object* v_s_x3f_697_){
_start:
{
lean_object* v___y_699_; 
if (lean_obj_tag(v_s_x3f_697_) == 0)
{
lean_object* v___x_705_; 
v___x_705_ = lean_box(1);
v___y_699_ = v___x_705_;
goto v___jp_698_;
}
else
{
lean_object* v_val_706_; 
v_val_706_ = lean_ctor_get(v_s_x3f_697_, 0);
lean_inc(v_val_706_);
lean_dec_ref_known(v_s_x3f_697_, 1);
v___y_699_ = v_val_706_;
goto v___jp_698_;
}
v___jp_698_:
{
uint8_t v___x_700_; 
v___x_700_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_overlapping_696_, v___y_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_box(0);
v___x_702_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_overlapping_696_, v___x_701_, v___y_699_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; 
lean_dec(v_overlapping_696_);
v___x_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_704_, 0, v___y_699_);
return v___x_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(lean_object* v_overlapping_707_, lean_object* v_a_708_, lean_object* v_x_709_){
_start:
{
if (lean_obj_tag(v_x_709_) == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_val_712_; lean_object* v___x_713_; 
v___x_710_ = lean_box(0);
v___x_711_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(v_overlapping_707_, v___x_710_);
v_val_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_val_712_);
lean_dec(v___x_711_);
v___x_713_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_713_, 0, v_a_708_);
lean_ctor_set(v___x_713_, 1, v_val_712_);
lean_ctor_set(v___x_713_, 2, v_x_709_);
return v___x_713_;
}
else
{
lean_object* v_key_714_; lean_object* v_value_715_; lean_object* v_tail_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_731_; 
v_key_714_ = lean_ctor_get(v_x_709_, 0);
v_value_715_ = lean_ctor_get(v_x_709_, 1);
v_tail_716_ = lean_ctor_get(v_x_709_, 2);
v_isSharedCheck_731_ = !lean_is_exclusive(v_x_709_);
if (v_isSharedCheck_731_ == 0)
{
v___x_718_ = v_x_709_;
v_isShared_719_ = v_isSharedCheck_731_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_tail_716_);
lean_inc(v_value_715_);
lean_inc(v_key_714_);
lean_dec(v_x_709_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_731_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
uint8_t v___x_720_; 
v___x_720_ = lean_nat_dec_eq(v_key_714_, v_a_708_);
if (v___x_720_ == 0)
{
lean_object* v_tail_721_; lean_object* v___x_723_; 
v_tail_721_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(v_overlapping_707_, v_a_708_, v_tail_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 2, v_tail_721_);
v___x_723_ = v___x_718_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_key_714_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_value_715_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_tail_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_val_727_; lean_object* v___x_729_; 
lean_dec(v_key_714_);
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v_value_715_);
v___x_726_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(v_overlapping_707_, v___x_725_);
v_val_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_val_727_);
lean_dec(v___x_726_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v_val_727_);
lean_ctor_set(v___x_718_, 0, v_a_708_);
v___x_729_ = v___x_718_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_708_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_val_727_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_tail_716_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(lean_object* v_a_732_, lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_733_) == 0)
{
uint8_t v___x_734_; 
v___x_734_ = 0;
return v___x_734_;
}
else
{
lean_object* v_key_735_; lean_object* v_tail_736_; uint8_t v___x_737_; 
v_key_735_ = lean_ctor_get(v_x_733_, 0);
v_tail_736_ = lean_ctor_get(v_x_733_, 2);
v___x_737_ = lean_nat_dec_eq(v_key_735_, v_a_732_);
if (v___x_737_ == 0)
{
v_x_733_ = v_tail_736_;
goto _start;
}
else
{
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg___boxed(lean_object* v_a_739_, lean_object* v_x_740_){
_start:
{
uint8_t v_res_741_; lean_object* v_r_742_; 
v_res_741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_739_, v_x_740_);
lean_dec(v_x_740_);
lean_dec(v_a_739_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
return v_x_743_;
}
else
{
lean_object* v_key_745_; lean_object* v_value_746_; lean_object* v_tail_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_770_; 
v_key_745_ = lean_ctor_get(v_x_744_, 0);
v_value_746_ = lean_ctor_get(v_x_744_, 1);
v_tail_747_ = lean_ctor_get(v_x_744_, 2);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_744_);
if (v_isSharedCheck_770_ == 0)
{
v___x_749_ = v_x_744_;
v_isShared_750_ = v_isSharedCheck_770_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_tail_747_);
lean_inc(v_value_746_);
lean_inc(v_key_745_);
lean_dec(v_x_744_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_770_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; uint64_t v___x_752_; uint64_t v___x_753_; uint64_t v___x_754_; uint64_t v_fold_755_; uint64_t v___x_756_; uint64_t v___x_757_; uint64_t v___x_758_; size_t v___x_759_; size_t v___x_760_; size_t v___x_761_; size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_751_ = lean_array_get_size(v_x_743_);
v___x_752_ = lean_uint64_of_nat(v_key_745_);
v___x_753_ = 32ULL;
v___x_754_ = lean_uint64_shift_right(v___x_752_, v___x_753_);
v_fold_755_ = lean_uint64_xor(v___x_752_, v___x_754_);
v___x_756_ = 16ULL;
v___x_757_ = lean_uint64_shift_right(v_fold_755_, v___x_756_);
v___x_758_ = lean_uint64_xor(v_fold_755_, v___x_757_);
v___x_759_ = lean_uint64_to_usize(v___x_758_);
v___x_760_ = lean_usize_of_nat(v___x_751_);
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_sub(v___x_760_, v___x_761_);
v___x_763_ = lean_usize_land(v___x_759_, v___x_762_);
v___x_764_ = lean_array_uget_borrowed(v_x_743_, v___x_763_);
lean_inc(v___x_764_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 2, v___x_764_);
v___x_766_ = v___x_749_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_key_745_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_value_746_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v___x_764_);
v___x_766_ = v_reuseFailAlloc_769_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; 
v___x_767_ = lean_array_uset(v_x_743_, v___x_763_, v___x_766_);
v_x_743_ = v___x_767_;
v_x_744_ = v_tail_747_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(lean_object* v_i_771_, lean_object* v_source_772_, lean_object* v_target_773_){
_start:
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_array_get_size(v_source_772_);
v___x_775_ = lean_nat_dec_lt(v_i_771_, v___x_774_);
if (v___x_775_ == 0)
{
lean_dec_ref(v_source_772_);
lean_dec(v_i_771_);
return v_target_773_;
}
else
{
lean_object* v_es_776_; lean_object* v___x_777_; lean_object* v_source_778_; lean_object* v_target_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_es_776_ = lean_array_fget(v_source_772_, v_i_771_);
v___x_777_ = lean_box(0);
v_source_778_ = lean_array_fset(v_source_772_, v_i_771_, v___x_777_);
v_target_779_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(v_target_773_, v_es_776_);
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_add(v_i_771_, v___x_780_);
lean_dec(v_i_771_);
v_i_771_ = v___x_781_;
v_source_772_ = v_source_778_;
v_target_773_ = v_target_779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(lean_object* v_data_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v_nbuckets_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_784_ = lean_array_get_size(v_data_783_);
v___x_785_ = lean_unsigned_to_nat(2u);
v_nbuckets_786_ = lean_nat_mul(v___x_784_, v___x_785_);
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = lean_box(0);
v___x_789_ = lean_mk_array(v_nbuckets_786_, v___x_788_);
v___x_790_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(v___x_787_, v_data_783_, v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2(lean_object* v_overlapping_791_, lean_object* v_m_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_size_794_; lean_object* v_buckets_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_847_; 
v_size_794_ = lean_ctor_get(v_m_792_, 0);
v_buckets_795_ = lean_ctor_get(v_m_792_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v_m_792_);
if (v_isSharedCheck_847_ == 0)
{
v___x_797_ = v_m_792_;
v_isShared_798_ = v_isSharedCheck_847_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_buckets_795_);
lean_inc(v_size_794_);
lean_dec(v_m_792_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_847_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; uint64_t v___x_800_; uint64_t v___x_801_; uint64_t v___x_802_; uint64_t v_fold_803_; uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; size_t v___x_811_; lean_object* v_bkt_812_; lean_object* v___y_814_; uint8_t v___x_832_; 
v___x_799_ = lean_array_get_size(v_buckets_795_);
v___x_800_ = lean_uint64_of_nat(v_a_793_);
v___x_801_ = 32ULL;
v___x_802_ = lean_uint64_shift_right(v___x_800_, v___x_801_);
v_fold_803_ = lean_uint64_xor(v___x_800_, v___x_802_);
v___x_804_ = 16ULL;
v___x_805_ = lean_uint64_shift_right(v_fold_803_, v___x_804_);
v___x_806_ = lean_uint64_xor(v_fold_803_, v___x_805_);
v___x_807_ = lean_uint64_to_usize(v___x_806_);
v___x_808_ = lean_usize_of_nat(v___x_799_);
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_sub(v___x_808_, v___x_809_);
v___x_811_ = lean_usize_land(v___x_807_, v___x_810_);
v_bkt_812_ = lean_array_uget_borrowed(v_buckets_795_, v___x_811_);
v___x_832_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_793_, v_bkt_812_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = lean_box(1);
v___x_834_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_overlapping_791_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_box(0);
v___x_836_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_overlapping_791_, v___x_835_, v___x_833_);
v___y_814_ = v___x_836_;
goto v___jp_813_;
}
else
{
lean_dec(v_overlapping_791_);
v___y_814_ = v___x_833_;
goto v___jp_813_;
}
}
else
{
lean_object* v___x_837_; lean_object* v_buckets_x27_838_; lean_object* v_bkt_x27_839_; lean_object* v___y_841_; uint8_t v___x_844_; 
lean_inc(v_bkt_812_);
lean_del_object(v___x_797_);
v___x_837_ = lean_box(0);
v_buckets_x27_838_ = lean_array_uset(v_buckets_795_, v___x_811_, v___x_837_);
lean_inc(v_a_793_);
v_bkt_x27_839_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(v_overlapping_791_, v_a_793_, v_bkt_812_);
v___x_844_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_793_, v_bkt_x27_839_);
lean_dec(v_a_793_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_unsigned_to_nat(1u);
v___x_846_ = lean_nat_sub(v_size_794_, v___x_845_);
lean_dec(v_size_794_);
v___y_841_ = v___x_846_;
goto v___jp_840_;
}
else
{
v___y_841_ = v_size_794_;
goto v___jp_840_;
}
v___jp_840_:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_array_uset(v_buckets_x27_838_, v___x_811_, v_bkt_x27_839_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v___y_841_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
return v___x_843_;
}
}
v___jp_813_:
{
lean_object* v___x_815_; lean_object* v_size_x27_816_; lean_object* v___x_817_; lean_object* v_buckets_x27_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_815_ = lean_unsigned_to_nat(1u);
v_size_x27_816_ = lean_nat_add(v_size_794_, v___x_815_);
lean_dec(v_size_794_);
lean_inc(v_bkt_812_);
v___x_817_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_817_, 0, v_a_793_);
lean_ctor_set(v___x_817_, 1, v___y_814_);
lean_ctor_set(v___x_817_, 2, v_bkt_812_);
v_buckets_x27_818_ = lean_array_uset(v_buckets_795_, v___x_811_, v___x_817_);
v___x_819_ = lean_unsigned_to_nat(4u);
v___x_820_ = lean_nat_mul(v_size_x27_816_, v___x_819_);
v___x_821_ = lean_unsigned_to_nat(3u);
v___x_822_ = lean_nat_div(v___x_820_, v___x_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_array_get_size(v_buckets_x27_818_);
v___x_824_ = lean_nat_dec_le(v___x_822_, v___x_823_);
lean_dec(v___x_822_);
if (v___x_824_ == 0)
{
lean_object* v_val_825_; lean_object* v___x_827_; 
v_val_825_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(v_buckets_x27_818_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v_val_825_);
lean_ctor_set(v___x_797_, 0, v_size_x27_816_);
v___x_827_ = v___x_797_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_size_x27_816_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_val_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
else
{
lean_object* v___x_830_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v_buckets_x27_818_);
lean_ctor_set(v___x_797_, 0, v_size_x27_816_);
v___x_830_ = v___x_797_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_size_x27_816_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_buckets_x27_818_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_insert(lean_object* v_o_848_, lean_object* v_overlapping_849_, lean_object* v_overlapped_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2(v_overlapping_849_, v_o_848_, v_overlapped_850_);
return v___x_851_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(lean_object* v_00_u03b2_852_, lean_object* v_k_853_, lean_object* v_t_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_k_853_, v_t_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___boxed(lean_object* v_00_u03b2_856_, lean_object* v_k_857_, lean_object* v_t_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(v_00_u03b2_856_, v_k_857_, v_t_858_);
lean_dec(v_t_858_);
lean_dec(v_k_857_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1(lean_object* v_00_u03b2_861_, lean_object* v_k_862_, lean_object* v_v_863_, lean_object* v_t_864_, lean_object* v_hl_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_862_, v_v_863_, v_t_864_);
return v___x_866_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(lean_object* v_00_u03b2_867_, lean_object* v_a_868_, lean_object* v_x_869_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_868_, v_x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___boxed(lean_object* v_00_u03b2_871_, lean_object* v_a_872_, lean_object* v_x_873_){
_start:
{
uint8_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(v_00_u03b2_871_, v_a_872_, v_x_873_);
lean_dec(v_x_873_);
lean_dec(v_a_872_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3(lean_object* v_00_u03b2_876_, lean_object* v_data_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(v_data_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_879_, lean_object* v_i_880_, lean_object* v_source_881_, lean_object* v_target_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(v_i_880_, v_source_881_, v_target_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_884_, lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(v_x_885_, v_x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(lean_object* v_a_888_, lean_object* v_x_889_){
_start:
{
if (lean_obj_tag(v_x_889_) == 0)
{
lean_object* v___x_890_; 
v___x_890_ = lean_box(0);
return v___x_890_;
}
else
{
lean_object* v_key_891_; lean_object* v_value_892_; lean_object* v_tail_893_; uint8_t v___x_894_; 
v_key_891_ = lean_ctor_get(v_x_889_, 0);
v_value_892_ = lean_ctor_get(v_x_889_, 1);
v_tail_893_ = lean_ctor_get(v_x_889_, 2);
v___x_894_ = lean_nat_dec_eq(v_key_891_, v_a_888_);
if (v___x_894_ == 0)
{
v_x_889_ = v_tail_893_;
goto _start;
}
else
{
lean_object* v___x_896_; 
lean_inc(v_value_892_);
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v_value_892_);
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg___boxed(lean_object* v_a_897_, lean_object* v_x_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_897_, v_x_898_);
lean_dec(v_x_898_);
lean_dec(v_a_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(lean_object* v_m_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_buckets_902_; lean_object* v___x_903_; uint64_t v___x_904_; uint64_t v___x_905_; uint64_t v___x_906_; uint64_t v_fold_907_; uint64_t v___x_908_; uint64_t v___x_909_; uint64_t v___x_910_; size_t v___x_911_; size_t v___x_912_; size_t v___x_913_; size_t v___x_914_; size_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_buckets_902_ = lean_ctor_get(v_m_900_, 1);
v___x_903_ = lean_array_get_size(v_buckets_902_);
v___x_904_ = lean_uint64_of_nat(v_a_901_);
v___x_905_ = 32ULL;
v___x_906_ = lean_uint64_shift_right(v___x_904_, v___x_905_);
v_fold_907_ = lean_uint64_xor(v___x_904_, v___x_906_);
v___x_908_ = 16ULL;
v___x_909_ = lean_uint64_shift_right(v_fold_907_, v___x_908_);
v___x_910_ = lean_uint64_xor(v_fold_907_, v___x_909_);
v___x_911_ = lean_uint64_to_usize(v___x_910_);
v___x_912_ = lean_usize_of_nat(v___x_903_);
v___x_913_ = ((size_t)1ULL);
v___x_914_ = lean_usize_sub(v___x_912_, v___x_913_);
v___x_915_ = lean_usize_land(v___x_911_, v___x_914_);
v___x_916_ = lean_array_uget_borrowed(v_buckets_902_, v___x_915_);
v___x_917_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_901_, v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg___boxed(lean_object* v_m_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_m_918_, v_a_919_);
lean_dec(v_a_919_);
lean_dec_ref(v_m_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(lean_object* v_init_921_, lean_object* v_x_922_){
_start:
{
if (lean_obj_tag(v_x_922_) == 0)
{
lean_object* v_k_923_; lean_object* v_l_924_; lean_object* v_r_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_k_923_ = lean_ctor_get(v_x_922_, 1);
lean_inc(v_k_923_);
v_l_924_ = lean_ctor_get(v_x_922_, 3);
lean_inc(v_l_924_);
v_r_925_ = lean_ctor_get(v_x_922_, 4);
lean_inc(v_r_925_);
lean_dec_ref_known(v_x_922_, 5);
v___x_926_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v_init_921_, v_l_924_);
v___x_927_ = lean_array_push(v___x_926_, v_k_923_);
v_init_921_ = v___x_927_;
v_x_922_ = v_r_925_;
goto _start;
}
else
{
return v_init_921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_overlapping(lean_object* v_o_931_, lean_object* v_overlapped_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_o_931_, v_overlapped_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v___x_934_; 
v___x_934_ = ((lean_object*)(l_Lean_Meta_Match_Overlaps_overlapping___closed__0));
return v___x_934_;
}
else
{
lean_object* v_val_935_; lean_object* v___y_937_; 
v_val_935_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v___x_933_, 1);
if (lean_obj_tag(v_val_935_) == 0)
{
lean_object* v_size_940_; 
v_size_940_ = lean_ctor_get(v_val_935_, 0);
lean_inc(v_size_940_);
v___y_937_ = v_size_940_;
goto v___jp_936_;
}
else
{
lean_object* v___x_941_; 
v___x_941_ = lean_unsigned_to_nat(0u);
v___y_937_ = v___x_941_;
goto v___jp_936_;
}
v___jp_936_:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_mk_empty_array_with_capacity(v___y_937_);
lean_dec(v___y_937_);
v___x_939_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v___x_938_, v_val_935_);
return v___x_939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_overlapping___boxed(lean_object* v_o_942_, lean_object* v_overlapped_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_Match_Overlaps_overlapping(v_o_942_, v_overlapped_943_);
lean_dec(v_overlapped_943_);
lean_dec_ref(v_o_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(lean_object* v_00_u03b2_945_, lean_object* v_m_946_, lean_object* v_a_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_m_946_, v_a_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___boxed(lean_object* v_00_u03b2_949_, lean_object* v_m_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(v_00_u03b2_949_, v_m_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_m_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1(lean_object* v_init_953_, lean_object* v_t_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v_init_953_, v_t_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(lean_object* v_00_u03b2_956_, lean_object* v_a_957_, lean_object* v_x_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_957_, v_x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___boxed(lean_object* v_00_u03b2_960_, lean_object* v_a_961_, lean_object* v_x_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(v_00_u03b2_960_, v_a_961_, v_x_962_);
lean_dec(v_x_962_);
lean_dec(v_a_961_);
return v_res_963_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_unsigned_to_nat(13u);
v___x_979_ = lean_nat_to_int(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_unsigned_to_nat(15u);
v___x_984_ = lean_nat_to_int(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_unsigned_to_nat(16u);
v___x_989_ = lean_nat_to_int(v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(lean_object* v_x_990_){
_start:
{
lean_object* v_numFields_991_; lean_object* v_numOverlaps_992_; uint8_t v_hasUnitThunk_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_numFields_991_ = lean_ctor_get(v_x_990_, 0);
lean_inc(v_numFields_991_);
v_numOverlaps_992_ = lean_ctor_get(v_x_990_, 1);
lean_inc(v_numOverlaps_992_);
v_hasUnitThunk_993_ = lean_ctor_get_uint8(v_x_990_, sizeof(void*)*2);
lean_dec_ref(v_x_990_);
v___x_994_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5));
v___x_995_ = ((lean_object*)(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3));
v___x_996_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4);
v___x_997_ = l_Nat_reprFast(v_numFields_991_);
v___x_998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
v___x_999_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_996_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = 0;
v___x_1001_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_995_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_box(1);
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = ((lean_object*)(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6));
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_994_);
v___x_1010_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7);
v___x_1011_ = l_Nat_reprFast(v_numOverlaps_992_);
v___x_1012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1010_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*1, v___x_1000_);
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1009_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_1003_);
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_1005_);
v___x_1018_ = ((lean_object*)(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9));
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_994_);
v___x_1021_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10);
v___x_1022_ = l_Bool_repr___redArg(v_hasUnitThunk_993_);
v___x_1023_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set_uint8(v___x_1024_, sizeof(void*)*1, v___x_1000_);
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1020_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_1027_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___x_1025_);
v___x_1029_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1026_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*1, v___x_1000_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr(lean_object* v_x_1033_, lean_object* v_prec_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_x_1033_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___boxed(lean_object* v_x_1036_, lean_object* v_prec_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Meta_Match_instReprAltParamInfo_repr(v_x_1036_, v_prec_1037_);
lean_dec(v_prec_1037_);
return v_res_1038_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_instBEqAltParamInfo_beq(lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
lean_object* v_numFields_1043_; lean_object* v_numOverlaps_1044_; uint8_t v_hasUnitThunk_1045_; lean_object* v_numFields_1046_; lean_object* v_numOverlaps_1047_; uint8_t v_hasUnitThunk_1048_; uint8_t v___x_1049_; 
v_numFields_1043_ = lean_ctor_get(v_x_1041_, 0);
v_numOverlaps_1044_ = lean_ctor_get(v_x_1041_, 1);
v_hasUnitThunk_1045_ = lean_ctor_get_uint8(v_x_1041_, sizeof(void*)*2);
v_numFields_1046_ = lean_ctor_get(v_x_1042_, 0);
v_numOverlaps_1047_ = lean_ctor_get(v_x_1042_, 1);
v_hasUnitThunk_1048_ = lean_ctor_get_uint8(v_x_1042_, sizeof(void*)*2);
v___x_1049_ = lean_nat_dec_eq(v_numFields_1043_, v_numFields_1046_);
if (v___x_1049_ == 0)
{
return v___x_1049_;
}
else
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_nat_dec_eq(v_numOverlaps_1044_, v_numOverlaps_1047_);
if (v___x_1050_ == 0)
{
return v___x_1050_;
}
else
{
if (v_hasUnitThunk_1045_ == 0)
{
if (v_hasUnitThunk_1048_ == 0)
{
return v___x_1050_;
}
else
{
return v_hasUnitThunk_1045_;
}
}
else
{
return v_hasUnitThunk_1048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instBEqAltParamInfo_beq___boxed(lean_object* v_x_1051_, lean_object* v_x_1052_){
_start:
{
uint8_t v_res_1053_; lean_object* v_r_1054_; 
v_res_1053_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v_x_1051_, v_x_1052_);
lean_dec_ref(v_x_1052_);
lean_dec_ref(v_x_1051_);
v_r_1054_ = lean_box(v_res_1053_);
return v_r_1054_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1059_ = l_Lean_Meta_Match_instInhabitedOverlaps_default;
v___x_1060_ = lean_box(0);
v___x_1061_ = ((lean_object*)(l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0));
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
lean_ctor_set(v___x_1063_, 2, v___x_1061_);
lean_ctor_set(v___x_1063_, 3, v___x_1060_);
lean_ctor_set(v___x_1063_, 4, v___x_1061_);
lean_ctor_set(v___x_1063_, 5, v___x_1059_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default(void){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1, &l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatcherInfo(void){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_Meta_Match_instInhabitedMatcherInfo_default;
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(lean_object* v_x_1066_, lean_object* v_x_1067_){
_start:
{
if (lean_obj_tag(v_x_1066_) == 0)
{
lean_object* v___x_1068_; 
v___x_1068_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1));
return v___x_1068_;
}
else
{
lean_object* v_val_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1080_; 
v_val_1069_ = lean_ctor_get(v_x_1066_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_x_1066_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1071_ = v_x_1066_;
v_isShared_1072_ = v_isSharedCheck_1080_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_val_1069_);
lean_dec(v_x_1066_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1080_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1073_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3));
v___x_1074_ = l_Nat_reprFast(v_val_1069_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set_tag(v___x_1071_, 3);
lean_ctor_set(v___x_1071_, 0, v___x_1074_);
v___x_1076_ = v___x_1071_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1073_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l_Repr_addAppParen(v___x_1077_, v_x_1067_);
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1___boxed(lean_object* v_x_1081_, lean_object* v_x_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(v_x_1081_, v_x_1082_);
lean_dec(v_x_1082_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
if (lean_obj_tag(v_x_1086_) == 0)
{
lean_dec(v_x_1084_);
return v_x_1085_;
}
else
{
lean_object* v_head_1087_; lean_object* v_tail_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1098_; 
v_head_1087_ = lean_ctor_get(v_x_1086_, 0);
v_tail_1088_ = lean_ctor_get(v_x_1086_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_x_1086_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1090_ = v_x_1086_;
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_tail_1088_);
lean_inc(v_head_1087_);
lean_dec(v_x_1086_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
lean_inc(v_x_1084_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set_tag(v___x_1090_, 5);
lean_ctor_set(v___x_1090_, 1, v_x_1084_);
lean_ctor_set(v___x_1090_, 0, v_x_1085_);
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_x_1085_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_x_1084_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1087_);
v___x_1095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v_x_1085_ = v___x_1095_;
v_x_1086_ = v_tail_1088_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2(lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
if (lean_obj_tag(v_x_1101_) == 0)
{
lean_dec(v_x_1099_);
return v_x_1100_;
}
else
{
lean_object* v_head_1102_; lean_object* v_tail_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1113_; 
v_head_1102_ = lean_ctor_get(v_x_1101_, 0);
v_tail_1103_ = lean_ctor_get(v_x_1101_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_x_1101_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1105_ = v_x_1101_;
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_tail_1103_);
lean_inc(v_head_1102_);
lean_dec(v_x_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
lean_inc(v_x_1099_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 5);
lean_ctor_set(v___x_1105_, 1, v_x_1099_);
lean_ctor_set(v___x_1105_, 0, v_x_1100_);
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_x_1100_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_x_1099_);
v___x_1108_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1102_);
v___x_1110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(v_x_1099_, v___x_1110_, v_tail_1103_);
return v___x_1111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
if (lean_obj_tag(v_x_1114_) == 0)
{
lean_object* v___x_1116_; 
lean_dec(v_x_1115_);
v___x_1116_ = lean_box(0);
return v___x_1116_;
}
else
{
lean_object* v_tail_1117_; 
v_tail_1117_ = lean_ctor_get(v_x_1114_, 1);
if (lean_obj_tag(v_tail_1117_) == 0)
{
lean_object* v_head_1118_; lean_object* v___x_1119_; 
lean_dec(v_x_1115_);
v_head_1118_ = lean_ctor_get(v_x_1114_, 0);
lean_inc(v_head_1118_);
lean_dec_ref_known(v_x_1114_, 2);
v___x_1119_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1118_);
return v___x_1119_;
}
else
{
lean_object* v_head_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_inc(v_tail_1117_);
v_head_1120_ = lean_ctor_get(v_x_1114_, 0);
lean_inc(v_head_1120_);
lean_dec_ref_known(v_x_1114_, 2);
v___x_1121_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1120_);
v___x_1122_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2(v_x_1115_, v___x_1121_, v_tail_1117_);
return v___x_1122_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0));
v___x_1125_ = lean_string_length(v___x_1124_);
return v___x_1125_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1);
v___x_1127_ = lean_nat_to_int(v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0(lean_object* v_xs_1133_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1134_ = lean_array_get_size(v_xs_1133_);
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = lean_nat_dec_eq(v___x_1134_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1137_ = lean_array_to_list(v_xs_1133_);
v___x_1138_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_1139_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(v___x_1137_, v___x_1138_);
v___x_1140_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2);
v___x_1141_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3));
v___x_1142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v___x_1139_);
v___x_1143_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10));
v___x_1144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1140_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = l_Std_Format_fill(v___x_1145_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; 
lean_dec_ref(v_xs_1133_);
v___x_1147_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5));
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(lean_object* v_x_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
if (lean_obj_tag(v_x_1150_) == 0)
{
lean_dec(v_x_1148_);
return v_x_1149_;
}
else
{
lean_object* v_head_1151_; lean_object* v_tail_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1162_; 
v_head_1151_ = lean_ctor_get(v_x_1150_, 0);
v_tail_1152_ = lean_ctor_get(v_x_1150_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1154_ = v_x_1150_;
v_isShared_1155_ = v_isSharedCheck_1162_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_tail_1152_);
lean_inc(v_head_1151_);
lean_dec(v_x_1150_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1162_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
lean_inc(v_x_1148_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 5);
lean_ctor_set(v___x_1154_, 1, v_x_1148_);
lean_ctor_set(v___x_1154_, 0, v_x_1149_);
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_x_1149_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_x_1148_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1151_);
v___x_1159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v_x_1149_ = v___x_1159_;
v_x_1150_ = v_tail_1152_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5(lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_){
_start:
{
if (lean_obj_tag(v_x_1165_) == 0)
{
lean_dec(v_x_1163_);
return v_x_1164_;
}
else
{
lean_object* v_head_1166_; lean_object* v_tail_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1177_; 
v_head_1166_ = lean_ctor_get(v_x_1165_, 0);
v_tail_1167_ = lean_ctor_get(v_x_1165_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_x_1165_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1169_ = v_x_1165_;
v_isShared_1170_ = v_isSharedCheck_1177_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_tail_1167_);
lean_inc(v_head_1166_);
lean_dec(v_x_1165_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1177_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
lean_inc(v_x_1163_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 5);
lean_ctor_set(v___x_1169_, 1, v_x_1163_);
lean_ctor_set(v___x_1169_, 0, v_x_1164_);
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_x_1164_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_x_1163_);
v___x_1172_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1166_);
v___x_1174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(v_x_1163_, v___x_1174_, v_tail_1167_);
return v___x_1175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(lean_object* v_x_1178_, lean_object* v_x_1179_){
_start:
{
if (lean_obj_tag(v_x_1178_) == 0)
{
lean_object* v___x_1180_; 
lean_dec(v_x_1179_);
v___x_1180_ = lean_box(0);
return v___x_1180_;
}
else
{
lean_object* v_tail_1181_; 
v_tail_1181_ = lean_ctor_get(v_x_1178_, 1);
if (lean_obj_tag(v_tail_1181_) == 0)
{
lean_object* v_head_1182_; lean_object* v___x_1183_; 
lean_dec(v_x_1179_);
v_head_1182_ = lean_ctor_get(v_x_1178_, 0);
lean_inc(v_head_1182_);
lean_dec_ref_known(v_x_1178_, 2);
v___x_1183_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1182_);
return v___x_1183_;
}
else
{
lean_object* v_head_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_inc(v_tail_1181_);
v_head_1184_ = lean_ctor_get(v_x_1178_, 0);
lean_inc(v_head_1184_);
lean_dec_ref_known(v_x_1178_, 2);
v___x_1185_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1184_);
v___x_1186_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5(v_x_1179_, v___x_1185_, v_tail_1181_);
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(lean_object* v_xs_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1188_ = lean_array_get_size(v_xs_1187_);
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = lean_nat_dec_eq(v___x_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1191_ = lean_array_to_list(v_xs_1187_);
v___x_1192_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_1193_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(v___x_1191_, v___x_1192_);
v___x_1194_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2);
v___x_1195_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3));
v___x_1196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___x_1193_);
v___x_1197_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10));
v___x_1198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1194_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Std_Format_fill(v___x_1199_);
return v___x_1200_;
}
else
{
lean_object* v___x_1201_; 
lean_dec_ref(v_xs_1187_);
v___x_1201_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5));
return v___x_1201_;
}
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_unsigned_to_nat(12u);
v___x_1218_ = lean_nat_to_int(v___x_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_unsigned_to_nat(14u);
v___x_1226_ = lean_nat_to_int(v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(lean_object* v_x_1230_){
_start:
{
lean_object* v_numParams_1231_; lean_object* v_numDiscrs_1232_; lean_object* v_altInfos_1233_; lean_object* v_uElimPos_x3f_1234_; lean_object* v_discrInfos_1235_; lean_object* v_overlaps_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_numParams_1231_ = lean_ctor_get(v_x_1230_, 0);
lean_inc(v_numParams_1231_);
v_numDiscrs_1232_ = lean_ctor_get(v_x_1230_, 1);
lean_inc(v_numDiscrs_1232_);
v_altInfos_1233_ = lean_ctor_get(v_x_1230_, 2);
lean_inc_ref(v_altInfos_1233_);
v_uElimPos_x3f_1234_ = lean_ctor_get(v_x_1230_, 3);
lean_inc(v_uElimPos_x3f_1234_);
v_discrInfos_1235_ = lean_ctor_get(v_x_1230_, 4);
lean_inc_ref(v_discrInfos_1235_);
v_overlaps_1236_ = lean_ctor_get(v_x_1230_, 5);
lean_inc_ref(v_overlaps_1236_);
lean_dec_ref(v_x_1230_);
v___x_1237_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5));
v___x_1238_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3));
v___x_1239_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4);
v___x_1240_ = l_Nat_reprFast(v_numParams_1231_);
v___x_1241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
v___x_1242_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1239_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = 0;
v___x_1244_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set_uint8(v___x_1244_, sizeof(void*)*1, v___x_1243_);
v___x_1245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1238_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_1247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = lean_box(1);
v___x_1249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5));
v___x_1251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v___x_1237_);
v___x_1253_ = l_Nat_reprFast(v_numDiscrs_1232_);
v___x_1254_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
v___x_1255_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1239_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set_uint8(v___x_1256_, sizeof(void*)*1, v___x_1243_);
v___x_1257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1252_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v___x_1246_);
v___x_1259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v___x_1248_);
v___x_1260_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7));
v___x_1261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v___x_1237_);
v___x_1263_ = lean_obj_once(&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8, &l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8_once, _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8);
v___x_1264_ = l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0(v_altInfos_1233_);
v___x_1265_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*1, v___x_1243_);
v___x_1267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1262_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
lean_ctor_set(v___x_1268_, 1, v___x_1246_);
v___x_1269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v___x_1248_);
v___x_1270_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10));
v___x_1271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v___x_1237_);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(v_uElimPos_x3f_1234_, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1239_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set_uint8(v___x_1276_, sizeof(void*)*1, v___x_1243_);
v___x_1277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1272_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v___x_1246_);
v___x_1279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v___x_1248_);
v___x_1280_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12));
v___x_1281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v___x_1237_);
v___x_1283_ = lean_obj_once(&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13, &l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13_once, _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13);
v___x_1284_ = l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(v_discrInfos_1235_);
v___x_1285_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*1, v___x_1243_);
v___x_1287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1282_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v___x_1246_);
v___x_1289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v___x_1248_);
v___x_1290_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15));
v___x_1291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1289_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v___x_1237_);
v___x_1293_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg(v_overlaps_1236_);
v___x_1294_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1263_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*1, v___x_1243_);
v___x_1296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1292_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_1298_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_1299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v___x_1296_);
v___x_1300_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_1301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1297_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___x_1303_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set_uint8(v___x_1303_, sizeof(void*)*1, v___x_1243_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr(lean_object* v_x_1304_, lean_object* v_prec_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(v_x_1304_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___boxed(lean_object* v_x_1307_, lean_object* v_prec_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Meta_Match_instReprMatcherInfo_repr(v_x_1307_, v_prec_1308_);
lean_dec(v_prec_1308_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object* v_info_1312_){
_start:
{
lean_object* v_altInfos_1313_; lean_object* v___x_1314_; 
v_altInfos_1313_ = lean_ctor_get(v_info_1312_, 2);
v___x_1314_ = lean_array_get_size(v_altInfos_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts___boxed(lean_object* v_info_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_1315_);
lean_dec_ref(v_info_1315_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object* v_info_1317_){
_start:
{
lean_object* v_numParams_1318_; lean_object* v_numDiscrs_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_numParams_1318_ = lean_ctor_get(v_info_1317_, 0);
v_numDiscrs_1319_ = lean_ctor_get(v_info_1317_, 1);
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_add(v_numParams_1318_, v___x_1320_);
v___x_1322_ = lean_nat_add(v___x_1321_, v_numDiscrs_1319_);
lean_dec(v___x_1321_);
v___x_1323_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_1317_);
v___x_1324_ = lean_nat_add(v___x_1322_, v___x_1323_);
lean_dec(v___x_1323_);
lean_dec(v___x_1322_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_arity___boxed(lean_object* v_info_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Meta_Match_MatcherInfo_arity(v_info_1325_);
lean_dec_ref(v_info_1325_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object* v_info_1327_){
_start:
{
lean_object* v_numParams_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_numParams_1328_ = lean_ctor_get(v_info_1327_, 0);
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = lean_nat_add(v_numParams_1328_, v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos___boxed(lean_object* v_info_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_info_1331_);
lean_dec_ref(v_info_1331_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getDiscrRange(lean_object* v_info_1333_){
_start:
{
lean_object* v_numDiscrs_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_numDiscrs_1334_ = lean_ctor_get(v_info_1333_, 1);
v___x_1335_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_info_1333_);
v___x_1336_ = lean_nat_add(v___x_1335_, v_numDiscrs_1334_);
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getDiscrRange___boxed(lean_object* v_info_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_Meta_Match_MatcherInfo_getDiscrRange(v_info_1338_);
lean_dec_ref(v_info_1338_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(lean_object* v_info_1340_){
_start:
{
lean_object* v_numParams_1341_; lean_object* v_numDiscrs_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_numParams_1341_ = lean_ctor_get(v_info_1340_, 0);
v_numDiscrs_1342_ = lean_ctor_get(v_info_1340_, 1);
v___x_1343_ = lean_unsigned_to_nat(1u);
v___x_1344_ = lean_nat_add(v_numParams_1341_, v___x_1343_);
v___x_1345_ = lean_nat_add(v___x_1344_, v_numDiscrs_1342_);
lean_dec(v___x_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos___boxed(lean_object* v_info_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_info_1346_);
lean_dec_ref(v_info_1346_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getAltRange(lean_object* v_info_1348_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1349_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_info_1348_);
v___x_1350_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_1348_);
v___x_1351_ = lean_nat_add(v___x_1349_, v___x_1350_);
lean_dec(v___x_1350_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1349_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getAltRange___boxed(lean_object* v_info_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_Meta_Match_MatcherInfo_getAltRange(v_info_1353_);
lean_dec_ref(v_info_1353_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object* v_info_1355_){
_start:
{
lean_object* v_numParams_1356_; 
v_numParams_1356_ = lean_ctor_get(v_info_1355_, 0);
lean_inc(v_numParams_1356_);
return v_numParams_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos___boxed(lean_object* v_info_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_info_1357_);
lean_dec_ref(v_info_1357_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(lean_object* v_as_1359_, size_t v_sz_1360_, size_t v_i_1361_, lean_object* v_b_1362_){
_start:
{
lean_object* v_a_1364_; uint8_t v___x_1368_; 
v___x_1368_ = lean_usize_dec_lt(v_i_1361_, v_sz_1360_);
if (v___x_1368_ == 0)
{
return v_b_1362_;
}
else
{
lean_object* v_a_1369_; 
v_a_1369_ = lean_array_uget_borrowed(v_as_1359_, v_i_1361_);
if (lean_obj_tag(v_a_1369_) == 0)
{
v_a_1364_ = v_b_1362_;
goto v___jp_1363_;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = lean_nat_add(v_b_1362_, v___x_1370_);
lean_dec(v_b_1362_);
v_a_1364_ = v___x_1371_;
goto v___jp_1363_;
}
}
v___jp_1363_:
{
size_t v___x_1365_; size_t v___x_1366_; 
v___x_1365_ = ((size_t)1ULL);
v___x_1366_ = lean_usize_add(v_i_1361_, v___x_1365_);
v_i_1361_ = v___x_1366_;
v_b_1362_ = v_a_1364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0___boxed(lean_object* v_as_1372_, lean_object* v_sz_1373_, lean_object* v_i_1374_, lean_object* v_b_1375_){
_start:
{
size_t v_sz_boxed_1376_; size_t v_i_boxed_1377_; lean_object* v_res_1378_; 
v_sz_boxed_1376_ = lean_unbox_usize(v_sz_1373_);
lean_dec(v_sz_1373_);
v_i_boxed_1377_ = lean_unbox_usize(v_i_1374_);
lean_dec(v_i_1374_);
v_res_1378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(v_as_1372_, v_sz_boxed_1376_, v_i_boxed_1377_, v_b_1375_);
lean_dec_ref(v_as_1372_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getNumEqsFromDiscrInfos(lean_object* v_infos_1379_){
_start:
{
lean_object* v_r_1380_; size_t v_sz_1381_; size_t v___x_1382_; lean_object* v___x_1383_; 
v_r_1380_ = lean_unsigned_to_nat(0u);
v_sz_1381_ = lean_array_size(v_infos_1379_);
v___x_1382_ = ((size_t)0ULL);
v___x_1383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(v_infos_1379_, v_sz_1381_, v___x_1382_, v_r_1380_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getNumEqsFromDiscrInfos___boxed(lean_object* v_infos_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_infos_1384_);
lean_dec_ref(v_infos_1384_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object* v_info_1386_){
_start:
{
lean_object* v_discrInfos_1387_; lean_object* v___x_1388_; 
v_discrInfos_1387_ = lean_ctor_get(v_info_1386_, 4);
v___x_1388_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs___boxed(lean_object* v_info_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_info_1389_);
lean_dec_ref(v_info_1389_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(lean_object* v_info_1391_, size_t v_sz_1392_, size_t v_i_1393_, lean_object* v_bs_1394_){
_start:
{
uint8_t v___x_1395_; 
v___x_1395_ = lean_usize_dec_lt(v_i_1393_, v_sz_1392_);
if (v___x_1395_ == 0)
{
return v_bs_1394_;
}
else
{
lean_object* v_v_1396_; lean_object* v_numFields_1397_; lean_object* v_numOverlaps_1398_; uint8_t v_hasUnitThunk_1399_; lean_object* v___x_1400_; lean_object* v_bs_x27_1401_; lean_object* v___x_1402_; lean_object* v___y_1404_; 
v_v_1396_ = lean_array_uget_borrowed(v_bs_1394_, v_i_1393_);
v_numFields_1397_ = lean_ctor_get(v_v_1396_, 0);
lean_inc(v_numFields_1397_);
v_numOverlaps_1398_ = lean_ctor_get(v_v_1396_, 1);
lean_inc(v_numOverlaps_1398_);
v_hasUnitThunk_1399_ = lean_ctor_get_uint8(v_v_1396_, sizeof(void*)*2);
v___x_1400_ = lean_unsigned_to_nat(0u);
v_bs_x27_1401_ = lean_array_uset(v_bs_1394_, v_i_1393_, v___x_1400_);
v___x_1402_ = lean_nat_add(v_numFields_1397_, v_numOverlaps_1398_);
lean_dec(v_numOverlaps_1398_);
lean_dec(v_numFields_1397_);
if (v_hasUnitThunk_1399_ == 0)
{
v___y_1404_ = v___x_1400_;
goto v___jp_1403_;
}
else
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_unsigned_to_nat(1u);
v___y_1404_ = v___x_1412_;
goto v___jp_1403_;
}
v___jp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; size_t v___x_1408_; size_t v___x_1409_; lean_object* v___x_1410_; 
v___x_1405_ = lean_nat_add(v___x_1402_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec(v___x_1402_);
v___x_1406_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_info_1391_);
v___x_1407_ = lean_nat_add(v___x_1405_, v___x_1406_);
lean_dec(v___x_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_add(v_i_1393_, v___x_1408_);
v___x_1410_ = lean_array_uset(v_bs_x27_1401_, v_i_1393_, v___x_1407_);
v_i_1393_ = v___x_1409_;
v_bs_1394_ = v___x_1410_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0___boxed(lean_object* v_info_1413_, lean_object* v_sz_1414_, lean_object* v_i_1415_, lean_object* v_bs_1416_){
_start:
{
size_t v_sz_boxed_1417_; size_t v_i_boxed_1418_; lean_object* v_res_1419_; 
v_sz_boxed_1417_ = lean_unbox_usize(v_sz_1414_);
lean_dec(v_sz_1414_);
v_i_boxed_1418_ = lean_unbox_usize(v_i_1415_);
lean_dec(v_i_1415_);
v_res_1419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(v_info_1413_, v_sz_boxed_1417_, v_i_boxed_1418_, v_bs_1416_);
lean_dec_ref(v_info_1413_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_altNumParams(lean_object* v_info_1420_){
_start:
{
lean_object* v_altInfos_1421_; size_t v_sz_1422_; size_t v___x_1423_; lean_object* v___x_1424_; 
v_altInfos_1421_ = lean_ctor_get(v_info_1420_, 2);
lean_inc_ref(v_altInfos_1421_);
v_sz_1422_ = lean_array_size(v_altInfos_1421_);
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(v_info_1420_, v_sz_1422_, v___x_1423_, v_altInfos_1421_);
lean_dec_ref(v_info_1420_);
return v___x_1424_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__0(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_unsigned_to_nat(16u);
v___x_1427_ = lean_mk_array(v___x_1426_, v___x_1425_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__1(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__0, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__0_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__0);
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1428_);
return v___x_1430_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__2(void){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1431_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__3(void){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__2, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__2_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__2);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; 
v___x_1434_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__3, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__3_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__3);
v___x_1435_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__1, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__1_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__1);
v___x_1436_ = 1;
v___x_1437_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1434_);
lean_ctor_set_uint8(v___x_1437_, sizeof(void*)*2, v___x_1436_);
return v___x_1437_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState(void){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__4, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4);
return v___x_1438_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_1439_, lean_object* v_x_1440_){
_start:
{
if (lean_obj_tag(v_x_1440_) == 0)
{
uint8_t v___x_1441_; 
v___x_1441_ = 0;
return v___x_1441_;
}
else
{
lean_object* v_key_1442_; lean_object* v_tail_1443_; uint8_t v___x_1444_; 
v_key_1442_ = lean_ctor_get(v_x_1440_, 0);
v_tail_1443_ = lean_ctor_get(v_x_1440_, 2);
v___x_1444_ = lean_name_eq(v_key_1442_, v_a_1439_);
if (v___x_1444_ == 0)
{
v_x_1440_ = v_tail_1443_;
goto _start;
}
else
{
return v___x_1444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_1446_, lean_object* v_x_1447_){
_start:
{
uint8_t v_res_1448_; lean_object* v_r_1449_; 
v_res_1448_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_1446_, v_x_1447_);
lean_dec(v_x_1447_);
lean_dec(v_a_1446_);
v_r_1449_ = lean_box(v_res_1448_);
return v_r_1449_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1450_; uint64_t v___x_1451_; 
v___x_1450_ = lean_unsigned_to_nat(1723u);
v___x_1451_ = lean_uint64_of_nat(v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(lean_object* v_x_1452_, lean_object* v_x_1453_){
_start:
{
if (lean_obj_tag(v_x_1453_) == 0)
{
return v_x_1452_;
}
else
{
lean_object* v_key_1454_; lean_object* v_value_1455_; lean_object* v_tail_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1482_; 
v_key_1454_ = lean_ctor_get(v_x_1453_, 0);
v_value_1455_ = lean_ctor_get(v_x_1453_, 1);
v_tail_1456_ = lean_ctor_get(v_x_1453_, 2);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_x_1453_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1458_ = v_x_1453_;
v_isShared_1459_ = v_isSharedCheck_1482_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_tail_1456_);
lean_inc(v_value_1455_);
lean_inc(v_key_1454_);
lean_dec(v_x_1453_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1482_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; uint64_t v___y_1462_; 
v___x_1460_ = lean_array_get_size(v_x_1452_);
if (lean_obj_tag(v_key_1454_) == 0)
{
uint64_t v___x_1480_; 
v___x_1480_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
v___y_1462_ = v___x_1480_;
goto v___jp_1461_;
}
else
{
uint64_t v_hash_1481_; 
v_hash_1481_ = lean_ctor_get_uint64(v_key_1454_, sizeof(void*)*2);
v___y_1462_ = v_hash_1481_;
goto v___jp_1461_;
}
v___jp_1461_:
{
uint64_t v___x_1463_; uint64_t v___x_1464_; uint64_t v_fold_1465_; uint64_t v___x_1466_; uint64_t v___x_1467_; uint64_t v___x_1468_; size_t v___x_1469_; size_t v___x_1470_; size_t v___x_1471_; size_t v___x_1472_; size_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1463_ = 32ULL;
v___x_1464_ = lean_uint64_shift_right(v___y_1462_, v___x_1463_);
v_fold_1465_ = lean_uint64_xor(v___y_1462_, v___x_1464_);
v___x_1466_ = 16ULL;
v___x_1467_ = lean_uint64_shift_right(v_fold_1465_, v___x_1466_);
v___x_1468_ = lean_uint64_xor(v_fold_1465_, v___x_1467_);
v___x_1469_ = lean_uint64_to_usize(v___x_1468_);
v___x_1470_ = lean_usize_of_nat(v___x_1460_);
v___x_1471_ = ((size_t)1ULL);
v___x_1472_ = lean_usize_sub(v___x_1470_, v___x_1471_);
v___x_1473_ = lean_usize_land(v___x_1469_, v___x_1472_);
v___x_1474_ = lean_array_uget_borrowed(v_x_1452_, v___x_1473_);
lean_inc(v___x_1474_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 2, v___x_1474_);
v___x_1476_ = v___x_1458_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_key_1454_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_value_1455_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_array_uset(v_x_1452_, v___x_1473_, v___x_1476_);
v_x_1452_ = v___x_1477_;
v_x_1453_ = v_tail_1456_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_i_1483_, lean_object* v_source_1484_, lean_object* v_target_1485_){
_start:
{
lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = lean_array_get_size(v_source_1484_);
v___x_1487_ = lean_nat_dec_lt(v_i_1483_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_dec_ref(v_source_1484_);
lean_dec(v_i_1483_);
return v_target_1485_;
}
else
{
lean_object* v_es_1488_; lean_object* v___x_1489_; lean_object* v_source_1490_; lean_object* v_target_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v_es_1488_ = lean_array_fget(v_source_1484_, v_i_1483_);
v___x_1489_ = lean_box(0);
v_source_1490_ = lean_array_fset(v_source_1484_, v_i_1483_, v___x_1489_);
v_target_1491_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_target_1485_, v_es_1488_);
v___x_1492_ = lean_unsigned_to_nat(1u);
v___x_1493_ = lean_nat_add(v_i_1483_, v___x_1492_);
lean_dec(v_i_1483_);
v_i_1483_ = v___x_1493_;
v_source_1484_ = v_source_1490_;
v_target_1485_ = v_target_1491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(lean_object* v_data_1495_){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v_nbuckets_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1496_ = lean_array_get_size(v_data_1495_);
v___x_1497_ = lean_unsigned_to_nat(2u);
v_nbuckets_1498_ = lean_nat_mul(v___x_1496_, v___x_1497_);
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_mk_array(v_nbuckets_1498_, v___x_1500_);
v___x_1502_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(v___x_1499_, v_data_1495_, v___x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(lean_object* v_a_1503_, lean_object* v_b_1504_, lean_object* v_x_1505_){
_start:
{
if (lean_obj_tag(v_x_1505_) == 0)
{
lean_dec(v_b_1504_);
lean_dec(v_a_1503_);
return v_x_1505_;
}
else
{
lean_object* v_key_1506_; lean_object* v_value_1507_; lean_object* v_tail_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1520_; 
v_key_1506_ = lean_ctor_get(v_x_1505_, 0);
v_value_1507_ = lean_ctor_get(v_x_1505_, 1);
v_tail_1508_ = lean_ctor_get(v_x_1505_, 2);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_x_1505_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1510_ = v_x_1505_;
v_isShared_1511_ = v_isSharedCheck_1520_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_tail_1508_);
lean_inc(v_value_1507_);
lean_inc(v_key_1506_);
lean_dec(v_x_1505_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1520_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
uint8_t v___x_1512_; 
v___x_1512_ = lean_name_eq(v_key_1506_, v_a_1503_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1513_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_1503_, v_b_1504_, v_tail_1508_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 2, v___x_1513_);
v___x_1515_ = v___x_1510_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_key_1506_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_value_1507_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
else
{
lean_object* v___x_1518_; 
lean_dec(v_value_1507_);
lean_dec(v_key_1506_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 1, v_b_1504_);
lean_ctor_set(v___x_1510_, 0, v_a_1503_);
v___x_1518_ = v___x_1510_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1503_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_b_1504_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_tail_1508_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(lean_object* v_m_1521_, lean_object* v_a_1522_, lean_object* v_b_1523_){
_start:
{
lean_object* v_size_1524_; lean_object* v_buckets_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1571_; 
v_size_1524_ = lean_ctor_get(v_m_1521_, 0);
v_buckets_1525_ = lean_ctor_get(v_m_1521_, 1);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_m_1521_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1527_ = v_m_1521_;
v_isShared_1528_ = v_isSharedCheck_1571_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_buckets_1525_);
lean_inc(v_size_1524_);
lean_dec(v_m_1521_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1571_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; uint64_t v___y_1531_; 
v___x_1529_ = lean_array_get_size(v_buckets_1525_);
if (lean_obj_tag(v_a_1522_) == 0)
{
uint64_t v___x_1569_; 
v___x_1569_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
v___y_1531_ = v___x_1569_;
goto v___jp_1530_;
}
else
{
uint64_t v_hash_1570_; 
v_hash_1570_ = lean_ctor_get_uint64(v_a_1522_, sizeof(void*)*2);
v___y_1531_ = v_hash_1570_;
goto v___jp_1530_;
}
v___jp_1530_:
{
uint64_t v___x_1532_; uint64_t v___x_1533_; uint64_t v_fold_1534_; uint64_t v___x_1535_; uint64_t v___x_1536_; uint64_t v___x_1537_; size_t v___x_1538_; size_t v___x_1539_; size_t v___x_1540_; size_t v___x_1541_; size_t v___x_1542_; lean_object* v_bkt_1543_; uint8_t v___x_1544_; 
v___x_1532_ = 32ULL;
v___x_1533_ = lean_uint64_shift_right(v___y_1531_, v___x_1532_);
v_fold_1534_ = lean_uint64_xor(v___y_1531_, v___x_1533_);
v___x_1535_ = 16ULL;
v___x_1536_ = lean_uint64_shift_right(v_fold_1534_, v___x_1535_);
v___x_1537_ = lean_uint64_xor(v_fold_1534_, v___x_1536_);
v___x_1538_ = lean_uint64_to_usize(v___x_1537_);
v___x_1539_ = lean_usize_of_nat(v___x_1529_);
v___x_1540_ = ((size_t)1ULL);
v___x_1541_ = lean_usize_sub(v___x_1539_, v___x_1540_);
v___x_1542_ = lean_usize_land(v___x_1538_, v___x_1541_);
v_bkt_1543_ = lean_array_uget_borrowed(v_buckets_1525_, v___x_1542_);
v___x_1544_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_1522_, v_bkt_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v_size_x27_1546_; lean_object* v___x_1547_; lean_object* v_buckets_x27_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1545_ = lean_unsigned_to_nat(1u);
v_size_x27_1546_ = lean_nat_add(v_size_1524_, v___x_1545_);
lean_dec(v_size_1524_);
lean_inc(v_bkt_1543_);
v___x_1547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1547_, 0, v_a_1522_);
lean_ctor_set(v___x_1547_, 1, v_b_1523_);
lean_ctor_set(v___x_1547_, 2, v_bkt_1543_);
v_buckets_x27_1548_ = lean_array_uset(v_buckets_1525_, v___x_1542_, v___x_1547_);
v___x_1549_ = lean_unsigned_to_nat(4u);
v___x_1550_ = lean_nat_mul(v_size_x27_1546_, v___x_1549_);
v___x_1551_ = lean_unsigned_to_nat(3u);
v___x_1552_ = lean_nat_div(v___x_1550_, v___x_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_array_get_size(v_buckets_x27_1548_);
v___x_1554_ = lean_nat_dec_le(v___x_1552_, v___x_1553_);
lean_dec(v___x_1552_);
if (v___x_1554_ == 0)
{
lean_object* v_val_1555_; lean_object* v___x_1557_; 
v_val_1555_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(v_buckets_x27_1548_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v_val_1555_);
lean_ctor_set(v___x_1527_, 0, v_size_x27_1546_);
v___x_1557_ = v___x_1527_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_size_x27_1546_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_val_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
else
{
lean_object* v___x_1560_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v_buckets_x27_1548_);
lean_ctor_set(v___x_1527_, 0, v_size_x27_1546_);
v___x_1560_ = v___x_1527_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_size_x27_1546_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_buckets_x27_1548_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
else
{
lean_object* v___x_1562_; lean_object* v_buckets_x27_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
lean_inc(v_bkt_1543_);
v___x_1562_ = lean_box(0);
v_buckets_x27_1563_ = lean_array_uset(v_buckets_1525_, v___x_1542_, v___x_1562_);
v___x_1564_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_1522_, v_b_1523_, v_bkt_1543_);
v___x_1565_ = lean_array_uset(v_buckets_x27_1563_, v___x_1542_, v___x_1564_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v___x_1565_);
v___x_1567_ = v___x_1527_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_size_1524_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_){
_start:
{
lean_object* v_ks_1576_; lean_object* v_vs_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1601_; 
v_ks_1576_ = lean_ctor_get(v_x_1572_, 0);
v_vs_1577_ = lean_ctor_get(v_x_1572_, 1);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_x_1572_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1579_ = v_x_1572_;
v_isShared_1580_ = v_isSharedCheck_1601_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_vs_1577_);
lean_inc(v_ks_1576_);
lean_dec(v_x_1572_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1601_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = lean_array_get_size(v_ks_1576_);
v___x_1582_ = lean_nat_dec_lt(v_x_1573_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
lean_dec(v_x_1573_);
v___x_1583_ = lean_array_push(v_ks_1576_, v_x_1574_);
v___x_1584_ = lean_array_push(v_vs_1577_, v_x_1575_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v___x_1584_);
lean_ctor_set(v___x_1579_, 0, v___x_1583_);
v___x_1586_ = v___x_1579_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
else
{
lean_object* v_k_x27_1588_; uint8_t v___x_1589_; 
v_k_x27_1588_ = lean_array_fget_borrowed(v_ks_1576_, v_x_1573_);
v___x_1589_ = lean_name_eq(v_x_1574_, v_k_x27_1588_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1591_; 
if (v_isShared_1580_ == 0)
{
v___x_1591_ = v___x_1579_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_ks_1576_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_vs_1577_);
v___x_1591_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_unsigned_to_nat(1u);
v___x_1593_ = lean_nat_add(v_x_1573_, v___x_1592_);
lean_dec(v_x_1573_);
v_x_1572_ = v___x_1591_;
v_x_1573_ = v___x_1593_;
goto _start;
}
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1596_ = lean_array_fset(v_ks_1576_, v_x_1573_, v_x_1574_);
v___x_1597_ = lean_array_fset(v_vs_1577_, v_x_1573_, v_x_1575_);
lean_dec(v_x_1573_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v___x_1597_);
lean_ctor_set(v___x_1579_, 0, v___x_1596_);
v___x_1599_ = v___x_1579_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1602_, lean_object* v_k_1603_, lean_object* v_v_1604_){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_unsigned_to_nat(0u);
v___x_1606_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_n_1602_, v___x_1605_, v_k_1603_, v_v_1604_);
return v___x_1606_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1608_, size_t v_x_1609_, size_t v_x_1610_, lean_object* v_x_1611_, lean_object* v_x_1612_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 0)
{
lean_object* v_es_1613_; size_t v___x_1614_; size_t v___x_1615_; lean_object* v_j_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v_es_1613_ = lean_ctor_get(v_x_1608_, 0);
v___x_1614_ = ((size_t)31ULL);
v___x_1615_ = lean_usize_land(v_x_1609_, v___x_1614_);
v_j_1616_ = lean_usize_to_nat(v___x_1615_);
v___x_1617_ = lean_array_get_size(v_es_1613_);
v___x_1618_ = lean_nat_dec_lt(v_j_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_dec(v_j_1616_);
lean_dec(v_x_1612_);
lean_dec(v_x_1611_);
return v_x_1608_;
}
else
{
lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1657_; 
lean_inc_ref(v_es_1613_);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v_x_1608_, 0);
lean_dec(v_unused_1658_);
v___x_1620_ = v_x_1608_;
v_isShared_1621_ = v_isSharedCheck_1657_;
goto v_resetjp_1619_;
}
else
{
lean_dec(v_x_1608_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1657_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_v_1622_; lean_object* v___x_1623_; lean_object* v_xs_x27_1624_; lean_object* v___y_1626_; 
v_v_1622_ = lean_array_fget(v_es_1613_, v_j_1616_);
v___x_1623_ = lean_box(0);
v_xs_x27_1624_ = lean_array_fset(v_es_1613_, v_j_1616_, v___x_1623_);
switch(lean_obj_tag(v_v_1622_))
{
case 0:
{
lean_object* v_key_1631_; lean_object* v_val_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1642_; 
v_key_1631_ = lean_ctor_get(v_v_1622_, 0);
v_val_1632_ = lean_ctor_get(v_v_1622_, 1);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_v_1622_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1634_ = v_v_1622_;
v_isShared_1635_ = v_isSharedCheck_1642_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_val_1632_);
lean_inc(v_key_1631_);
lean_dec(v_v_1622_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1642_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_name_eq(v_x_1611_, v_key_1631_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_del_object(v___x_1634_);
v___x_1637_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1631_, v_val_1632_, v_x_1611_, v_x_1612_);
v___x_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
v___y_1626_ = v___x_1638_;
goto v___jp_1625_;
}
else
{
lean_object* v___x_1640_; 
lean_dec(v_val_1632_);
lean_dec(v_key_1631_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 1, v_x_1612_);
lean_ctor_set(v___x_1634_, 0, v_x_1611_);
v___x_1640_ = v___x_1634_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_x_1611_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_x_1612_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
v___y_1626_ = v___x_1640_;
goto v___jp_1625_;
}
}
}
}
case 1:
{
lean_object* v_node_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1655_; 
v_node_1643_ = lean_ctor_get(v_v_1622_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_v_1622_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1645_ = v_v_1622_;
v_isShared_1646_ = v_isSharedCheck_1655_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_node_1643_);
lean_dec(v_v_1622_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1655_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
size_t v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; size_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1647_ = ((size_t)5ULL);
v___x_1648_ = lean_usize_shift_right(v_x_1609_, v___x_1647_);
v___x_1649_ = ((size_t)1ULL);
v___x_1650_ = lean_usize_add(v_x_1610_, v___x_1649_);
v___x_1651_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_node_1643_, v___x_1648_, v___x_1650_, v_x_1611_, v_x_1612_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1651_);
v___x_1653_ = v___x_1645_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
v___y_1626_ = v___x_1653_;
goto v___jp_1625_;
}
}
}
default: 
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v_x_1611_);
lean_ctor_set(v___x_1656_, 1, v_x_1612_);
v___y_1626_ = v___x_1656_;
goto v___jp_1625_;
}
}
v___jp_1625_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = lean_array_fset(v_xs_x27_1624_, v_j_1616_, v___y_1626_);
lean_dec(v_j_1616_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1627_);
v___x_1629_ = v___x_1620_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
else
{
lean_object* v_ks_1659_; lean_object* v_vs_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1680_; 
v_ks_1659_ = lean_ctor_get(v_x_1608_, 0);
v_vs_1660_ = lean_ctor_get(v_x_1608_, 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1662_ = v_x_1608_;
v_isShared_1663_ = v_isSharedCheck_1680_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_vs_1660_);
lean_inc(v_ks_1659_);
lean_dec(v_x_1608_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1680_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_ks_1659_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_vs_1660_);
v___x_1665_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v_newNode_1666_; uint8_t v___y_1668_; size_t v___x_1674_; uint8_t v___x_1675_; 
v_newNode_1666_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1665_, v_x_1611_, v_x_1612_);
v___x_1674_ = ((size_t)7ULL);
v___x_1675_ = lean_usize_dec_le(v___x_1674_, v_x_1610_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1676_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1666_);
v___x_1677_ = lean_unsigned_to_nat(4u);
v___x_1678_ = lean_nat_dec_lt(v___x_1676_, v___x_1677_);
lean_dec(v___x_1676_);
v___y_1668_ = v___x_1678_;
goto v___jp_1667_;
}
else
{
v___y_1668_ = v___x_1675_;
goto v___jp_1667_;
}
v___jp_1667_:
{
if (v___y_1668_ == 0)
{
lean_object* v_ks_1669_; lean_object* v_vs_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_ks_1669_ = lean_ctor_get(v_newNode_1666_, 0);
lean_inc_ref(v_ks_1669_);
v_vs_1670_ = lean_ctor_get(v_newNode_1666_, 1);
lean_inc_ref(v_vs_1670_);
lean_dec_ref(v_newNode_1666_);
v___x_1671_ = lean_unsigned_to_nat(0u);
v___x_1672_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1673_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1610_, v_ks_1669_, v_vs_1670_, v___x_1671_, v___x_1672_);
lean_dec_ref(v_vs_1670_);
lean_dec_ref(v_ks_1669_);
return v___x_1673_;
}
else
{
return v_newNode_1666_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1681_, lean_object* v_keys_1682_, lean_object* v_vals_1683_, lean_object* v_i_1684_, lean_object* v_entries_1685_){
_start:
{
lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = lean_array_get_size(v_keys_1682_);
v___x_1687_ = lean_nat_dec_lt(v_i_1684_, v___x_1686_);
if (v___x_1687_ == 0)
{
lean_dec(v_i_1684_);
return v_entries_1685_;
}
else
{
lean_object* v_k_1688_; lean_object* v_v_1689_; uint64_t v___y_1691_; 
v_k_1688_ = lean_array_fget_borrowed(v_keys_1682_, v_i_1684_);
v_v_1689_ = lean_array_fget_borrowed(v_vals_1683_, v_i_1684_);
if (lean_obj_tag(v_k_1688_) == 0)
{
uint64_t v___x_1702_; 
v___x_1702_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
v___y_1691_ = v___x_1702_;
goto v___jp_1690_;
}
else
{
uint64_t v_hash_1703_; 
v_hash_1703_ = lean_ctor_get_uint64(v_k_1688_, sizeof(void*)*2);
v___y_1691_ = v_hash_1703_;
goto v___jp_1690_;
}
v___jp_1690_:
{
size_t v_h_1692_; size_t v___x_1693_; lean_object* v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; size_t v_h_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_h_1692_ = lean_uint64_to_usize(v___y_1691_);
v___x_1693_ = ((size_t)5ULL);
v___x_1694_ = lean_unsigned_to_nat(1u);
v___x_1695_ = ((size_t)1ULL);
v___x_1696_ = lean_usize_sub(v_depth_1681_, v___x_1695_);
v___x_1697_ = lean_usize_mul(v___x_1693_, v___x_1696_);
v_h_1698_ = lean_usize_shift_right(v_h_1692_, v___x_1697_);
v___x_1699_ = lean_nat_add(v_i_1684_, v___x_1694_);
lean_dec(v_i_1684_);
lean_inc(v_v_1689_);
lean_inc(v_k_1688_);
v___x_1700_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_entries_1685_, v_h_1698_, v_depth_1681_, v_k_1688_, v_v_1689_);
v_i_1684_ = v___x_1699_;
v_entries_1685_ = v___x_1700_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1704_, lean_object* v_keys_1705_, lean_object* v_vals_1706_, lean_object* v_i_1707_, lean_object* v_entries_1708_){
_start:
{
size_t v_depth_boxed_1709_; lean_object* v_res_1710_; 
v_depth_boxed_1709_ = lean_unbox_usize(v_depth_1704_);
lean_dec(v_depth_1704_);
v_res_1710_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1709_, v_keys_1705_, v_vals_1706_, v_i_1707_, v_entries_1708_);
lean_dec_ref(v_vals_1706_);
lean_dec_ref(v_keys_1705_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_, lean_object* v_x_1715_){
_start:
{
size_t v_x_1008__boxed_1716_; size_t v_x_1009__boxed_1717_; lean_object* v_res_1718_; 
v_x_1008__boxed_1716_ = lean_unbox_usize(v_x_1712_);
lean_dec(v_x_1712_);
v_x_1009__boxed_1717_ = lean_unbox_usize(v_x_1713_);
lean_dec(v_x_1713_);
v_res_1718_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_1711_, v_x_1008__boxed_1716_, v_x_1009__boxed_1717_, v_x_1714_, v_x_1715_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(lean_object* v_x_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_){
_start:
{
uint64_t v___y_1723_; 
if (lean_obj_tag(v_x_1720_) == 0)
{
uint64_t v___x_1727_; 
v___x_1727_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
v___y_1723_ = v___x_1727_;
goto v___jp_1722_;
}
else
{
uint64_t v_hash_1728_; 
v_hash_1728_ = lean_ctor_get_uint64(v_x_1720_, sizeof(void*)*2);
v___y_1723_ = v_hash_1728_;
goto v___jp_1722_;
}
v___jp_1722_:
{
size_t v___x_1724_; size_t v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_uint64_to_usize(v___y_1723_);
v___x_1725_ = ((size_t)1ULL);
v___x_1726_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_1719_, v___x_1724_, v___x_1725_, v_x_1720_, v_x_1721_);
return v___x_1726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(lean_object* v_x_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_){
_start:
{
uint8_t v_stage_u2081_1732_; 
v_stage_u2081_1732_ = lean_ctor_get_uint8(v_x_1729_, sizeof(void*)*2);
if (v_stage_u2081_1732_ == 0)
{
lean_object* v_map_u2081_1733_; lean_object* v_map_u2082_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1742_; 
v_map_u2081_1733_ = lean_ctor_get(v_x_1729_, 0);
v_map_u2082_1734_ = lean_ctor_get(v_x_1729_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_x_1729_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1736_ = v_x_1729_;
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_map_u2082_1734_);
lean_inc(v_map_u2081_1733_);
lean_dec(v_x_1729_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_map_u2082_1734_, v_x_1730_, v_x_1731_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_map_u2081_1733_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v___x_1738_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, sizeof(void*)*2, v_stage_u2081_1732_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_object* v_map_u2081_1743_; lean_object* v_map_u2082_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1752_; 
v_map_u2081_1743_ = lean_ctor_get(v_x_1729_, 0);
v_map_u2082_1744_ = lean_ctor_get(v_x_1729_, 1);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_x_1729_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1746_ = v_x_1729_;
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_map_u2082_1744_);
lean_inc(v_map_u2081_1743_);
lean_dec(v_x_1729_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(v_map_u2081_1743_, v_x_1730_, v_x_1731_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1748_);
v___x_1750_ = v___x_1746_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_map_u2082_1744_);
lean_ctor_set_uint8(v_reuseFailAlloc_1751_, sizeof(void*)*2, v_stage_u2081_1732_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_State_addEntry(lean_object* v_s_1753_, lean_object* v_e_1754_){
_start:
{
lean_object* v_name_1755_; lean_object* v_info_1756_; lean_object* v___x_1757_; 
v_name_1755_ = lean_ctor_get(v_e_1754_, 0);
lean_inc(v_name_1755_);
v_info_1756_ = lean_ctor_get(v_e_1754_, 1);
lean_inc_ref(v_info_1756_);
lean_dec_ref(v_e_1754_);
v___x_1757_ = l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(v_s_1753_, v_name_1755_, v_info_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0(lean_object* v_00_u03b2_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(v_x_1759_, v_x_1760_, v_x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0(lean_object* v_00_u03b2_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_x_1764_, v_x_1765_, v_x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1(lean_object* v_00_u03b2_1768_, lean_object* v_m_1769_, lean_object* v_a_1770_, lean_object* v_b_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(v_m_1769_, v_a_1770_, v_b_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1773_, lean_object* v_x_1774_, size_t v_x_1775_, size_t v_x_1776_, lean_object* v_x_1777_, lean_object* v_x_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_1774_, v_x_1775_, v_x_1776_, v_x_1777_, v_x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_, lean_object* v_x_1783_, lean_object* v_x_1784_, lean_object* v_x_1785_){
_start:
{
size_t v_x_1255__boxed_1786_; size_t v_x_1256__boxed_1787_; lean_object* v_res_1788_; 
v_x_1255__boxed_1786_ = lean_unbox_usize(v_x_1782_);
lean_dec(v_x_1782_);
v_x_1256__boxed_1787_ = lean_unbox_usize(v_x_1783_);
lean_dec(v_x_1783_);
v_res_1788_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(v_00_u03b2_1780_, v_x_1781_, v_x_1255__boxed_1786_, v_x_1256__boxed_1787_, v_x_1784_, v_x_1785_);
return v_res_1788_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1789_, lean_object* v_a_1790_, lean_object* v_x_1791_){
_start:
{
uint8_t v___x_1792_; 
v___x_1792_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_1790_, v_x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1793_, lean_object* v_a_1794_, lean_object* v_x_1795_){
_start:
{
uint8_t v_res_1796_; lean_object* v_r_1797_; 
v_res_1796_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(v_00_u03b2_1793_, v_a_1794_, v_x_1795_);
lean_dec(v_x_1795_);
lean_dec(v_a_1794_);
v_r_1797_ = lean_box(v_res_1796_);
return v_r_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1798_, lean_object* v_data_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(v_data_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1801_, lean_object* v_a_1802_, lean_object* v_b_1803_, lean_object* v_x_1804_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_1802_, v_b_1803_, v_x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1806_, lean_object* v_n_1807_, lean_object* v_k_1808_, lean_object* v_v_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1807_, v_k_1808_, v_v_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1811_, size_t v_depth_1812_, lean_object* v_keys_1813_, lean_object* v_vals_1814_, lean_object* v_heq_1815_, lean_object* v_i_1816_, lean_object* v_entries_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1812_, v_keys_1813_, v_vals_1814_, v_i_1816_, v_entries_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1819_, lean_object* v_depth_1820_, lean_object* v_keys_1821_, lean_object* v_vals_1822_, lean_object* v_heq_1823_, lean_object* v_i_1824_, lean_object* v_entries_1825_){
_start:
{
size_t v_depth_boxed_1826_; lean_object* v_res_1827_; 
v_depth_boxed_1826_ = lean_unbox_usize(v_depth_1820_);
lean_dec(v_depth_1820_);
v_res_1827_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1819_, v_depth_boxed_1826_, v_keys_1821_, v_vals_1822_, v_heq_1823_, v_i_1824_, v_entries_1825_);
lean_dec_ref(v_vals_1822_);
lean_dec_ref(v_keys_1821_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_1828_, lean_object* v_i_1829_, lean_object* v_source_1830_, lean_object* v_target_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(v_i_1829_, v_source_1830_, v_target_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1833_, lean_object* v_x_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_, lean_object* v_x_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1834_, v_x_1835_, v_x_1836_, v_x_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_x_1840_, v_x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(lean_object* v_m_1843_){
_start:
{
uint8_t v_stage_u2081_1844_; 
v_stage_u2081_1844_ = lean_ctor_get_uint8(v_m_1843_, sizeof(void*)*2);
if (v_stage_u2081_1844_ == 0)
{
return v_m_1843_;
}
else
{
lean_object* v_map_u2081_1845_; lean_object* v_map_u2082_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1854_; 
v_map_u2081_1845_ = lean_ctor_get(v_m_1843_, 0);
v_map_u2082_1846_ = lean_ctor_get(v_m_1843_, 1);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_m_1843_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1848_ = v_m_1843_;
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_map_u2082_1846_);
lean_inc(v_map_u2081_1845_);
lean_dec(v_m_1843_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
uint8_t v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = 0;
if (v_isShared_1849_ == 0)
{
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_map_u2081_1845_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_map_u2082_1846_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_ctor_set_uint8(v___x_1852_, sizeof(void*)*2, v___x_1850_);
return v___x_1852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0(lean_object* v_00_u03b2_1855_, lean_object* v_m_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(v_m_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_State_switch(lean_object* v_s_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(v_s_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(lean_object* v_env_1860_, lean_object* v_as_1861_, size_t v_i_1862_, size_t v_stop_1863_, lean_object* v_b_1864_){
_start:
{
lean_object* v___y_1866_; uint8_t v___x_1870_; 
v___x_1870_ = lean_usize_dec_eq(v_i_1862_, v_stop_1863_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v_name_1872_; uint8_t v___x_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v___x_1871_ = lean_array_uget_borrowed(v_as_1861_, v_i_1862_);
v_name_1872_ = lean_ctor_get(v___x_1871_, 0);
v___x_1873_ = 1;
lean_inc_ref(v_env_1860_);
v___x_1874_ = l_Lean_Environment_setExporting(v_env_1860_, v___x_1873_);
lean_inc(v_name_1872_);
v___x_1875_ = l_Lean_Environment_contains(v___x_1874_, v_name_1872_, v___x_1870_);
if (v___x_1875_ == 0)
{
v___y_1866_ = v_b_1864_;
goto v___jp_1865_;
}
else
{
lean_object* v___x_1876_; 
lean_inc(v___x_1871_);
v___x_1876_ = lean_array_push(v_b_1864_, v___x_1871_);
v___y_1866_ = v___x_1876_;
goto v___jp_1865_;
}
}
else
{
lean_dec_ref(v_env_1860_);
return v_b_1864_;
}
v___jp_1865_:
{
size_t v___x_1867_; size_t v___x_1868_; 
v___x_1867_ = ((size_t)1ULL);
v___x_1868_ = lean_usize_add(v_i_1862_, v___x_1867_);
v_i_1862_ = v___x_1868_;
v_b_1864_ = v___y_1866_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_1877_, lean_object* v_as_1878_, lean_object* v_i_1879_, lean_object* v_stop_1880_, lean_object* v_b_1881_){
_start:
{
size_t v_i_boxed_1882_; size_t v_stop_boxed_1883_; lean_object* v_res_1884_; 
v_i_boxed_1882_ = lean_unbox_usize(v_i_1879_);
lean_dec(v_i_1879_);
v_stop_boxed_1883_ = lean_unbox_usize(v_stop_1880_);
lean_dec(v_stop_1880_);
v_res_1884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_1877_, v_as_1878_, v_i_boxed_1882_, v_stop_boxed_1883_, v_b_1881_);
lean_dec_ref(v_as_1878_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object* v_env_1887_, lean_object* v_x_1888_, lean_object* v_entries_1889_){
_start:
{
lean_object* v_all_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v_all_1890_ = lean_array_mk(v_entries_1889_);
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = lean_array_get_size(v_all_1890_);
v___x_1893_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_));
v___x_1894_ = lean_nat_dec_lt(v___x_1891_, v___x_1892_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; 
lean_dec_ref(v_env_1887_);
v___x_1895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1893_);
lean_ctor_set(v___x_1895_, 2, v_all_1890_);
return v___x_1895_;
}
else
{
uint8_t v___x_1896_; 
v___x_1896_ = lean_nat_dec_le(v___x_1892_, v___x_1892_);
if (v___x_1896_ == 0)
{
if (v___x_1894_ == 0)
{
lean_object* v___x_1897_; 
lean_dec_ref(v_env_1887_);
v___x_1897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1893_);
lean_ctor_set(v___x_1897_, 1, v___x_1893_);
lean_ctor_set(v___x_1897_, 2, v_all_1890_);
return v___x_1897_;
}
else
{
size_t v___x_1898_; size_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1898_ = ((size_t)0ULL);
v___x_1899_ = lean_usize_of_nat(v___x_1892_);
v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_1887_, v_all_1890_, v___x_1898_, v___x_1899_, v___x_1893_);
lean_inc_ref(v___x_1900_);
v___x_1901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
lean_ctor_set(v___x_1901_, 2, v_all_1890_);
return v___x_1901_;
}
}
else
{
size_t v___x_1902_; size_t v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1902_ = ((size_t)0ULL);
v___x_1903_ = lean_usize_of_nat(v___x_1892_);
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_1887_, v_all_1890_, v___x_1902_, v___x_1903_, v___x_1893_);
lean_inc_ref(v___x_1904_);
v___x_1905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
lean_ctor_set(v___x_1905_, 2, v_all_1890_);
return v___x_1905_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object* v_env_1906_, lean_object* v_x_1907_, lean_object* v_entries_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(v_env_1906_, v_x_1907_, v_entries_1908_);
lean_dec_ref(v_x_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object* v_es_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_array_mk(v_es_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_1912_, size_t v_i_1913_, size_t v_stop_1914_, lean_object* v_b_1915_){
_start:
{
uint8_t v___x_1916_; 
v___x_1916_ = lean_usize_dec_eq(v_i_1913_, v_stop_1914_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; lean_object* v___x_1918_; size_t v___x_1919_; size_t v___x_1920_; 
v___x_1917_ = lean_array_uget_borrowed(v_as_1912_, v_i_1913_);
lean_inc(v___x_1917_);
v___x_1918_ = l_Lean_Meta_Match_Extension_State_addEntry(v_b_1915_, v___x_1917_);
v___x_1919_ = ((size_t)1ULL);
v___x_1920_ = lean_usize_add(v_i_1913_, v___x_1919_);
v_i_1913_ = v___x_1920_;
v_b_1915_ = v___x_1918_;
goto _start;
}
else
{
return v_b_1915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_1922_, lean_object* v_i_1923_, lean_object* v_stop_1924_, lean_object* v_b_1925_){
_start:
{
size_t v_i_boxed_1926_; size_t v_stop_boxed_1927_; lean_object* v_res_1928_; 
v_i_boxed_1926_ = lean_unbox_usize(v_i_1923_);
lean_dec(v_i_1923_);
v_stop_boxed_1927_ = lean_unbox_usize(v_stop_1924_);
lean_dec(v_stop_1924_);
v_res_1928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(v_as_1922_, v_i_boxed_1926_, v_stop_boxed_1927_, v_b_1925_);
lean_dec_ref(v_as_1922_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_1929_, size_t v_i_1930_, size_t v_stop_1931_, lean_object* v_b_1932_){
_start:
{
lean_object* v___y_1934_; uint8_t v___x_1938_; 
v___x_1938_ = lean_usize_dec_eq(v_i_1930_, v_stop_1931_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1939_ = lean_array_uget_borrowed(v_as_1929_, v_i_1930_);
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1941_ = lean_array_get_size(v___x_1939_);
v___x_1942_ = lean_nat_dec_lt(v___x_1940_, v___x_1941_);
if (v___x_1942_ == 0)
{
v___y_1934_ = v_b_1932_;
goto v___jp_1933_;
}
else
{
uint8_t v___x_1943_; 
v___x_1943_ = lean_nat_dec_le(v___x_1941_, v___x_1941_);
if (v___x_1943_ == 0)
{
if (v___x_1942_ == 0)
{
v___y_1934_ = v_b_1932_;
goto v___jp_1933_;
}
else
{
size_t v___x_1944_; size_t v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = ((size_t)0ULL);
v___x_1945_ = lean_usize_of_nat(v___x_1941_);
v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(v___x_1939_, v___x_1944_, v___x_1945_, v_b_1932_);
v___y_1934_ = v___x_1946_;
goto v___jp_1933_;
}
}
else
{
size_t v___x_1947_; size_t v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = ((size_t)0ULL);
v___x_1948_ = lean_usize_of_nat(v___x_1941_);
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(v___x_1939_, v___x_1947_, v___x_1948_, v_b_1932_);
v___y_1934_ = v___x_1949_;
goto v___jp_1933_;
}
}
}
else
{
return v_b_1932_;
}
v___jp_1933_:
{
size_t v___x_1935_; size_t v___x_1936_; 
v___x_1935_ = ((size_t)1ULL);
v___x_1936_ = lean_usize_add(v_i_1930_, v___x_1935_);
v_i_1930_ = v___x_1936_;
v_b_1932_ = v___y_1934_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_1950_, lean_object* v_i_1951_, lean_object* v_stop_1952_, lean_object* v_b_1953_){
_start:
{
size_t v_i_boxed_1954_; size_t v_stop_boxed_1955_; lean_object* v_res_1956_; 
v_i_boxed_1954_ = lean_unbox_usize(v_i_1951_);
lean_dec(v_i_1951_);
v_stop_boxed_1955_ = lean_unbox_usize(v_stop_1952_);
lean_dec(v_stop_1952_);
v_res_1956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_1950_, v_i_boxed_1954_, v_stop_boxed_1955_, v_b_1953_);
lean_dec_ref(v_as_1950_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(lean_object* v_initState_1957_, lean_object* v_as_1958_){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = lean_array_get_size(v_as_1958_);
v___x_1961_ = lean_nat_dec_lt(v___x_1959_, v___x_1960_);
if (v___x_1961_ == 0)
{
return v_initState_1957_;
}
else
{
uint8_t v___x_1962_; 
v___x_1962_ = lean_nat_dec_le(v___x_1960_, v___x_1960_);
if (v___x_1962_ == 0)
{
if (v___x_1961_ == 0)
{
return v_initState_1957_;
}
else
{
size_t v___x_1963_; size_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = lean_usize_of_nat(v___x_1960_);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_1958_, v___x_1963_, v___x_1964_, v_initState_1957_);
return v___x_1965_;
}
}
else
{
size_t v___x_1966_; size_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = ((size_t)0ULL);
v___x_1967_ = lean_usize_of_nat(v___x_1960_);
v___x_1968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_1958_, v___x_1966_, v___x_1967_, v_initState_1957_);
return v___x_1968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_1969_, lean_object* v_as_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(v_initState_1969_, v_as_1970_);
lean_dec_ref(v_as_1970_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object* v_es_1972_){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1973_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__4, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4);
v___x_1974_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(v___x_1973_, v_es_1972_);
v___x_1975_ = l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(v___x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object* v_es_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(v_es_1976_);
lean_dec_ref(v_es_1976_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_));
v___x_2007_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_();
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_addMatcherInfo(lean_object* v_env_2010_, lean_object* v_matcherName_2011_, lean_object* v_info_2012_){
_start:
{
lean_object* v___x_2013_; lean_object* v_toEnvExtension_2014_; lean_object* v_asyncMode_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2013_ = l_Lean_Meta_Match_Extension_extension;
v_toEnvExtension_2014_ = lean_ctor_get(v___x_2013_, 0);
v_asyncMode_2015_ = lean_ctor_get(v_toEnvExtension_2014_, 2);
lean_inc(v_matcherName_2011_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v_matcherName_2011_);
lean_ctor_set(v___x_2016_, 1, v_info_2012_);
v___x_2017_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2013_, v_env_2010_, v___x_2016_, v_asyncMode_2015_, v_matcherName_2011_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_2018_, lean_object* v_vals_2019_, lean_object* v_i_2020_, lean_object* v_k_2021_){
_start:
{
lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = lean_array_get_size(v_keys_2018_);
v___x_2023_ = lean_nat_dec_lt(v_i_2020_, v___x_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; 
lean_dec(v_i_2020_);
v___x_2024_ = lean_box(0);
return v___x_2024_;
}
else
{
lean_object* v_k_x27_2025_; uint8_t v___x_2026_; 
v_k_x27_2025_ = lean_array_fget_borrowed(v_keys_2018_, v_i_2020_);
v___x_2026_ = lean_name_eq(v_k_2021_, v_k_x27_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_unsigned_to_nat(1u);
v___x_2028_ = lean_nat_add(v_i_2020_, v___x_2027_);
lean_dec(v_i_2020_);
v_i_2020_ = v___x_2028_;
goto _start;
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_array_fget_borrowed(v_vals_2019_, v_i_2020_);
lean_dec(v_i_2020_);
lean_inc(v___x_2030_);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
return v___x_2031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2032_, lean_object* v_vals_2033_, lean_object* v_i_2034_, lean_object* v_k_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2032_, v_vals_2033_, v_i_2034_, v_k_2035_);
lean_dec(v_k_2035_);
lean_dec_ref(v_vals_2033_);
lean_dec_ref(v_keys_2032_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2037_, size_t v_x_2038_, lean_object* v_x_2039_){
_start:
{
if (lean_obj_tag(v_x_2037_) == 0)
{
lean_object* v_es_2040_; lean_object* v___x_2041_; size_t v___x_2042_; size_t v___x_2043_; lean_object* v_j_2044_; lean_object* v___x_2045_; 
v_es_2040_ = lean_ctor_get(v_x_2037_, 0);
v___x_2041_ = lean_box(2);
v___x_2042_ = ((size_t)31ULL);
v___x_2043_ = lean_usize_land(v_x_2038_, v___x_2042_);
v_j_2044_ = lean_usize_to_nat(v___x_2043_);
v___x_2045_ = lean_array_get_borrowed(v___x_2041_, v_es_2040_, v_j_2044_);
lean_dec(v_j_2044_);
switch(lean_obj_tag(v___x_2045_))
{
case 0:
{
lean_object* v_key_2046_; lean_object* v_val_2047_; uint8_t v___x_2048_; 
v_key_2046_ = lean_ctor_get(v___x_2045_, 0);
v_val_2047_ = lean_ctor_get(v___x_2045_, 1);
v___x_2048_ = lean_name_eq(v_x_2039_, v_key_2046_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_box(0);
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; 
lean_inc(v_val_2047_);
v___x_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_val_2047_);
return v___x_2050_;
}
}
case 1:
{
lean_object* v_node_2051_; size_t v___x_2052_; size_t v___x_2053_; 
v_node_2051_ = lean_ctor_get(v___x_2045_, 0);
v___x_2052_ = ((size_t)5ULL);
v___x_2053_ = lean_usize_shift_right(v_x_2038_, v___x_2052_);
v_x_2037_ = v_node_2051_;
v_x_2038_ = v___x_2053_;
goto _start;
}
default: 
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_box(0);
return v___x_2055_;
}
}
}
else
{
lean_object* v_ks_2056_; lean_object* v_vs_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v_ks_2056_ = lean_ctor_get(v_x_2037_, 0);
v_vs_2057_ = lean_ctor_get(v_x_2037_, 1);
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_2056_, v_vs_2057_, v___x_2058_, v_x_2039_);
return v___x_2059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2060_, lean_object* v_x_2061_, lean_object* v_x_2062_){
_start:
{
size_t v_x_563__boxed_2063_; lean_object* v_res_2064_; 
v_x_563__boxed_2063_ = lean_unbox_usize(v_x_2061_);
lean_dec(v_x_2061_);
v_res_2064_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_2060_, v_x_563__boxed_2063_, v_x_2062_);
lean_dec(v_x_2062_);
lean_dec_ref(v_x_2060_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_2065_, lean_object* v_x_2066_){
_start:
{
uint64_t v___y_2068_; 
if (lean_obj_tag(v_x_2066_) == 0)
{
uint64_t v___x_2071_; 
v___x_2071_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
v___y_2068_ = v___x_2071_;
goto v___jp_2067_;
}
else
{
uint64_t v_hash_2072_; 
v_hash_2072_ = lean_ctor_get_uint64(v_x_2066_, sizeof(void*)*2);
v___y_2068_ = v_hash_2072_;
goto v___jp_2067_;
}
v___jp_2067_:
{
size_t v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_uint64_to_usize(v___y_2068_);
v___x_2070_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_2065_, v___x_2069_, v_x_2066_);
return v___x_2070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2073_, lean_object* v_x_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_x_2073_, v_x_2074_);
lean_dec(v_x_2074_);
lean_dec_ref(v_x_2073_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(lean_object* v_a_2076_, lean_object* v_x_2077_){
_start:
{
if (lean_obj_tag(v_x_2077_) == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_box(0);
return v___x_2078_;
}
else
{
lean_object* v_key_2079_; lean_object* v_value_2080_; lean_object* v_tail_2081_; uint8_t v___x_2082_; 
v_key_2079_ = lean_ctor_get(v_x_2077_, 0);
v_value_2080_ = lean_ctor_get(v_x_2077_, 1);
v_tail_2081_ = lean_ctor_get(v_x_2077_, 2);
v___x_2082_ = lean_name_eq(v_key_2079_, v_a_2076_);
if (v___x_2082_ == 0)
{
v_x_2077_ = v_tail_2081_;
goto _start;
}
else
{
lean_object* v___x_2084_; 
lean_inc(v_value_2080_);
v___x_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2084_, 0, v_value_2080_);
return v___x_2084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_2085_, lean_object* v_x_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_2085_, v_x_2086_);
lean_dec(v_x_2086_);
lean_dec(v_a_2085_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(lean_object* v_m_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_buckets_2090_; lean_object* v___x_2091_; uint64_t v___y_2093_; 
v_buckets_2090_ = lean_ctor_get(v_m_2088_, 1);
v___x_2091_ = lean_array_get_size(v_buckets_2090_);
if (lean_obj_tag(v_a_2089_) == 0)
{
uint64_t v___x_2107_; 
v___x_2107_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg___closed__0);
v___y_2093_ = v___x_2107_;
goto v___jp_2092_;
}
else
{
uint64_t v_hash_2108_; 
v_hash_2108_ = lean_ctor_get_uint64(v_a_2089_, sizeof(void*)*2);
v___y_2093_ = v_hash_2108_;
goto v___jp_2092_;
}
v___jp_2092_:
{
uint64_t v___x_2094_; uint64_t v___x_2095_; uint64_t v_fold_2096_; uint64_t v___x_2097_; uint64_t v___x_2098_; uint64_t v___x_2099_; size_t v___x_2100_; size_t v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; size_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2094_ = 32ULL;
v___x_2095_ = lean_uint64_shift_right(v___y_2093_, v___x_2094_);
v_fold_2096_ = lean_uint64_xor(v___y_2093_, v___x_2095_);
v___x_2097_ = 16ULL;
v___x_2098_ = lean_uint64_shift_right(v_fold_2096_, v___x_2097_);
v___x_2099_ = lean_uint64_xor(v_fold_2096_, v___x_2098_);
v___x_2100_ = lean_uint64_to_usize(v___x_2099_);
v___x_2101_ = lean_usize_of_nat(v___x_2091_);
v___x_2102_ = ((size_t)1ULL);
v___x_2103_ = lean_usize_sub(v___x_2101_, v___x_2102_);
v___x_2104_ = lean_usize_land(v___x_2100_, v___x_2103_);
v___x_2105_ = lean_array_uget_borrowed(v_buckets_2090_, v___x_2104_);
v___x_2106_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_2089_, v___x_2105_);
return v___x_2106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_m_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_m_2109_, v_a_2110_);
lean_dec(v_a_2110_);
lean_dec_ref(v_m_2109_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(lean_object* v_x_2112_, lean_object* v_x_2113_){
_start:
{
uint8_t v_stage_u2081_2114_; 
v_stage_u2081_2114_ = lean_ctor_get_uint8(v_x_2112_, sizeof(void*)*2);
if (v_stage_u2081_2114_ == 0)
{
lean_object* v_map_u2081_2115_; lean_object* v_map_u2082_2116_; lean_object* v___x_2117_; 
v_map_u2081_2115_ = lean_ctor_get(v_x_2112_, 0);
v_map_u2082_2116_ = lean_ctor_get(v_x_2112_, 1);
v___x_2117_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_map_u2082_2116_, v_x_2113_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_map_u2081_2115_, v_x_2113_);
return v___x_2118_;
}
else
{
return v___x_2117_;
}
}
else
{
lean_object* v_map_u2081_2119_; lean_object* v___x_2120_; 
v_map_u2081_2119_ = lean_ctor_get(v_x_2112_, 0);
v___x_2120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_map_u2081_2119_, v_x_2113_);
return v___x_2120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_2121_, lean_object* v_x_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v_x_2121_, v_x_2122_);
lean_dec(v_x_2122_);
lean_dec_ref(v_x_2121_);
return v_res_2123_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = ((lean_object*)(l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0));
v___x_2126_ = lean_string_utf8_byte_size(v___x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object* v_env_2127_, lean_object* v_declName_2128_){
_start:
{
lean_object* v___x_2129_; 
lean_inc(v_declName_2128_);
v___x_2129_ = lean_erase_macro_scopes(v_declName_2128_);
if (lean_obj_tag(v___x_2129_) == 1)
{
lean_object* v_str_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v_str_2130_ = lean_ctor_get(v___x_2129_, 1);
lean_inc_ref(v_str_2130_);
lean_dec_ref_known(v___x_2129_, 2);
v___x_2131_ = ((lean_object*)(l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0));
v___x_2132_ = lean_string_utf8_byte_size(v_str_2130_);
v___x_2133_ = lean_obj_once(&l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1, &l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1_once, _init_l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1);
v___x_2134_ = lean_nat_dec_le(v___x_2133_, v___x_2132_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; 
lean_dec_ref(v_str_2130_);
lean_dec(v_declName_2128_);
lean_dec_ref(v_env_2127_);
v___x_2135_ = lean_box(0);
return v___x_2135_;
}
else
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = lean_unsigned_to_nat(0u);
v___x_2137_ = lean_string_memcmp(v_str_2130_, v___x_2131_, v___x_2136_, v___x_2136_, v___x_2133_);
lean_dec_ref(v_str_2130_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; 
lean_dec(v_declName_2128_);
lean_dec_ref(v_env_2127_);
v___x_2138_ = lean_box(0);
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; lean_object* v_toEnvExtension_2140_; lean_object* v_asyncMode_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2139_ = l_Lean_Meta_Match_Extension_extension;
v_toEnvExtension_2140_ = lean_ctor_get(v___x_2139_, 0);
v_asyncMode_2141_ = lean_ctor_get(v_toEnvExtension_2140_, 2);
v___x_2142_ = l_Lean_Meta_Match_Extension_instInhabitedState;
lean_inc(v_declName_2128_);
v___x_2143_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2142_, v___x_2139_, v_env_2127_, v_asyncMode_2141_, v_declName_2128_);
v___x_2144_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v___x_2143_, v_declName_2128_);
lean_dec(v_declName_2128_);
lean_dec(v___x_2143_);
return v___x_2144_;
}
}
}
else
{
lean_object* v___x_2145_; 
lean_dec(v___x_2129_);
lean_dec(v_declName_2128_);
lean_dec_ref(v_env_2127_);
v___x_2145_ = lean_box(0);
return v___x_2145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(lean_object* v_00_u03b2_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v_x_2147_, v_x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(v_00_u03b2_2150_, v_x_2151_, v_x_2152_);
lean_dec(v_x_2152_);
lean_dec_ref(v_x_2151_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_x_2155_, v_x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2158_, lean_object* v_x_2159_, lean_object* v_x_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(v_00_u03b2_2158_, v_x_2159_, v_x_2160_);
lean_dec(v_x_2160_);
lean_dec_ref(v_x_2159_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(lean_object* v_00_u03b2_2162_, lean_object* v_m_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_m_2163_, v_a_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2166_, lean_object* v_m_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(v_00_u03b2_2166_, v_m_2167_, v_a_2168_);
lean_dec(v_a_2168_);
lean_dec_ref(v_m_2167_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2170_, lean_object* v_x_2171_, size_t v_x_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_2171_, v_x_2172_, v_x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_){
_start:
{
size_t v_x_763__boxed_2179_; lean_object* v_res_2180_; 
v_x_763__boxed_2179_ = lean_unbox_usize(v_x_2177_);
lean_dec(v_x_2177_);
v_res_2180_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2175_, v_x_2176_, v_x_763__boxed_2179_, v_x_2178_);
lean_dec(v_x_2178_);
lean_dec_ref(v_x_2176_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2181_, lean_object* v_a_2182_, lean_object* v_x_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_2182_, v_x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2185_, lean_object* v_a_2186_, lean_object* v_x_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(v_00_u03b2_2185_, v_a_2186_, v_x_2187_);
lean_dec(v_x_2187_);
lean_dec(v_a_2186_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2189_, lean_object* v_keys_2190_, lean_object* v_vals_2191_, lean_object* v_heq_2192_, lean_object* v_i_2193_, lean_object* v_k_2194_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2190_, v_vals_2191_, v_i_2193_, v_k_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2196_, lean_object* v_keys_2197_, lean_object* v_vals_2198_, lean_object* v_heq_2199_, lean_object* v_i_2200_, lean_object* v_k_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2196_, v_keys_2197_, v_vals_2198_, v_heq_2199_, v_i_2200_, v_k_2201_);
lean_dec(v_k_2201_);
lean_dec_ref(v_vals_2198_);
lean_dec_ref(v_keys_2197_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0(lean_object* v_matcherName_2203_, lean_object* v_info_2204_, lean_object* v_env_2205_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2205_, v_matcherName_2203_, v_info_2204_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___redArg(lean_object* v_inst_2207_, lean_object* v_matcherName_2208_, lean_object* v_info_2209_){
_start:
{
lean_object* v_modifyEnv_2210_; lean_object* v___f_2211_; lean_object* v___x_2212_; 
v_modifyEnv_2210_ = lean_ctor_get(v_inst_2207_, 1);
lean_inc(v_modifyEnv_2210_);
lean_dec_ref(v_inst_2207_);
v___f_2211_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2211_, 0, v_matcherName_2208_);
lean_closure_set(v___f_2211_, 1, v_info_2209_);
v___x_2212_ = lean_apply_1(v_modifyEnv_2210_, v___f_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo(lean_object* v_m_2213_, lean_object* v_inst_2214_, lean_object* v_inst_2215_, lean_object* v_matcherName_2216_, lean_object* v_info_2217_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_Meta_Match_addMatcherInfo___redArg(v_inst_2215_, v_matcherName_2216_, v_info_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___boxed(lean_object* v_m_2219_, lean_object* v_inst_2220_, lean_object* v_inst_2221_, lean_object* v_matcherName_2222_, lean_object* v_info_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_Meta_Match_addMatcherInfo(v_m_2219_, v_inst_2220_, v_inst_2221_, v_matcherName_2222_, v_info_2223_);
lean_dec_ref(v_inst_2220_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfoCore_x3f(lean_object* v_env_2225_, lean_object* v_declName_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2225_, v_declName_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0(lean_object* v_declName_2228_, lean_object* v_toPure_2229_, lean_object* v_____do__lift_2230_){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_____do__lift_2230_, v_declName_2228_);
v___x_2232_ = lean_apply_2(v_toPure_2229_, lean_box(0), v___x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg(lean_object* v_inst_2233_, lean_object* v_inst_2234_, lean_object* v_declName_2235_){
_start:
{
lean_object* v_toApplicative_2236_; lean_object* v_toBind_2237_; lean_object* v_getEnv_2238_; lean_object* v_toPure_2239_; lean_object* v___f_2240_; lean_object* v___x_2241_; 
v_toApplicative_2236_ = lean_ctor_get(v_inst_2233_, 0);
lean_inc_ref(v_toApplicative_2236_);
v_toBind_2237_ = lean_ctor_get(v_inst_2233_, 1);
lean_inc(v_toBind_2237_);
lean_dec_ref(v_inst_2233_);
v_getEnv_2238_ = lean_ctor_get(v_inst_2234_, 0);
lean_inc(v_getEnv_2238_);
lean_dec_ref(v_inst_2234_);
v_toPure_2239_ = lean_ctor_get(v_toApplicative_2236_, 1);
lean_inc(v_toPure_2239_);
lean_dec_ref(v_toApplicative_2236_);
v___f_2240_ = lean_alloc_closure((void*)(l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2240_, 0, v_declName_2235_);
lean_closure_set(v___f_2240_, 1, v_toPure_2239_);
v___x_2241_ = lean_apply_4(v_toBind_2237_, lean_box(0), lean_box(0), v_getEnv_2238_, v___f_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f(lean_object* v_m_2242_, lean_object* v_inst_2243_, lean_object* v_inst_2244_, lean_object* v_declName_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_2243_, v_inst_2244_, v_declName_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT uint8_t lean_is_matcher(lean_object* v_env_2247_, lean_object* v_declName_2248_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2247_, v_declName_2248_);
if (lean_obj_tag(v___x_2249_) == 0)
{
uint8_t v___x_2250_; 
v___x_2250_ = 0;
return v___x_2250_;
}
else
{
uint8_t v___x_2251_; 
lean_dec_ref_known(v___x_2249_, 1);
v___x_2251_ = 1;
return v___x_2251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherCore___boxed(lean_object* v_env_2252_, lean_object* v_declName_2253_){
_start:
{
uint8_t v_res_2254_; lean_object* v_r_2255_; 
v_res_2254_ = lean_is_matcher(v_env_2252_, v_declName_2253_);
v_r_2255_ = lean_box(v_res_2254_);
return v_r_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___redArg___lam__0(lean_object* v_declName_2256_, lean_object* v_toPure_2257_, lean_object* v_____do__lift_2258_){
_start:
{
uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2259_ = lean_is_matcher(v_____do__lift_2258_, v_declName_2256_);
v___x_2260_ = lean_box(v___x_2259_);
v___x_2261_ = lean_apply_2(v_toPure_2257_, lean_box(0), v___x_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___redArg(lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_declName_2264_){
_start:
{
lean_object* v_toApplicative_2265_; lean_object* v_toBind_2266_; lean_object* v_getEnv_2267_; lean_object* v_toPure_2268_; lean_object* v___f_2269_; lean_object* v___x_2270_; 
v_toApplicative_2265_ = lean_ctor_get(v_inst_2262_, 0);
lean_inc_ref(v_toApplicative_2265_);
v_toBind_2266_ = lean_ctor_get(v_inst_2262_, 1);
lean_inc(v_toBind_2266_);
lean_dec_ref(v_inst_2262_);
v_getEnv_2267_ = lean_ctor_get(v_inst_2263_, 0);
lean_inc(v_getEnv_2267_);
lean_dec_ref(v_inst_2263_);
v_toPure_2268_ = lean_ctor_get(v_toApplicative_2265_, 1);
lean_inc(v_toPure_2268_);
lean_dec_ref(v_toApplicative_2265_);
v___f_2269_ = lean_alloc_closure((void*)(l_Lean_Meta_isMatcher___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2269_, 0, v_declName_2264_);
lean_closure_set(v___f_2269_, 1, v_toPure_2268_);
v___x_2270_ = lean_apply_4(v_toBind_2266_, lean_box(0), lean_box(0), v_getEnv_2267_, v___f_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher(lean_object* v_m_2271_, lean_object* v_inst_2272_, lean_object* v_inst_2273_, lean_object* v_declName_2274_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Meta_isMatcher___redArg(v_inst_2272_, v_inst_2273_, v_declName_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object* v_env_2276_, lean_object* v_e_2277_){
_start:
{
lean_object* v_fn_2278_; uint8_t v___x_2279_; 
v_fn_2278_ = l_Lean_Expr_getAppFn(v_e_2277_);
v___x_2279_ = l_Lean_Expr_isConst(v_fn_2278_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2280_; 
lean_dec_ref(v_fn_2278_);
lean_dec_ref(v_env_2276_);
v___x_2280_ = lean_box(0);
return v___x_2280_;
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = l_Lean_Expr_constName_x21(v_fn_2278_);
lean_dec_ref(v_fn_2278_);
v___x_2282_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2276_, v___x_2281_);
if (lean_obj_tag(v___x_2282_) == 1)
{
lean_object* v_val_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v_val_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_val_2283_);
v___x_2284_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2283_);
lean_dec(v_val_2283_);
v___x_2285_ = l_Lean_Expr_getAppNumArgs(v_e_2277_);
v___x_2286_ = lean_nat_dec_le(v___x_2284_, v___x_2285_);
lean_dec(v___x_2285_);
lean_dec(v___x_2284_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; 
lean_dec_ref_known(v___x_2282_, 1);
v___x_2287_ = lean_box(0);
return v___x_2287_;
}
else
{
return v___x_2282_;
}
}
else
{
lean_object* v___x_2288_; 
lean_dec(v___x_2282_);
v___x_2288_ = lean_box(0);
return v___x_2288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore_x3f___boxed(lean_object* v_env_2289_, lean_object* v_e_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_2289_, v_e_2290_);
lean_dec_ref(v_e_2290_);
return v_res_2291_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherAppCore(lean_object* v_env_2292_, lean_object* v_e_2293_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_2292_, v_e_2293_);
if (lean_obj_tag(v___x_2294_) == 0)
{
uint8_t v___x_2295_; 
v___x_2295_ = 0;
return v___x_2295_;
}
else
{
uint8_t v___x_2296_; 
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = 1;
return v___x_2296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore___boxed(lean_object* v_env_2297_, lean_object* v_e_2298_){
_start:
{
uint8_t v_res_2299_; lean_object* v_r_2300_; 
v_res_2299_ = l_Lean_Meta_isMatcherAppCore(v_env_2297_, v_e_2298_);
lean_dec_ref(v_e_2298_);
v_r_2300_ = lean_box(v_res_2299_);
return v_r_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg___lam__0(lean_object* v_e_2301_, lean_object* v_toPure_2302_, lean_object* v_____do__lift_2303_){
_start:
{
uint8_t v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = l_Lean_Meta_isMatcherAppCore(v_____do__lift_2303_, v_e_2301_);
v___x_2305_ = lean_box(v___x_2304_);
v___x_2306_ = lean_apply_2(v_toPure_2302_, lean_box(0), v___x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed(lean_object* v_e_2307_, lean_object* v_toPure_2308_, lean_object* v_____do__lift_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Meta_isMatcherApp___redArg___lam__0(v_e_2307_, v_toPure_2308_, v_____do__lift_2309_);
lean_dec_ref(v_e_2307_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg(lean_object* v_inst_2311_, lean_object* v_inst_2312_, lean_object* v_e_2313_){
_start:
{
lean_object* v_toApplicative_2314_; lean_object* v_toBind_2315_; lean_object* v_getEnv_2316_; lean_object* v_toPure_2317_; lean_object* v___f_2318_; lean_object* v___x_2319_; 
v_toApplicative_2314_ = lean_ctor_get(v_inst_2311_, 0);
lean_inc_ref(v_toApplicative_2314_);
v_toBind_2315_ = lean_ctor_get(v_inst_2311_, 1);
lean_inc(v_toBind_2315_);
lean_dec_ref(v_inst_2311_);
v_getEnv_2316_ = lean_ctor_get(v_inst_2312_, 0);
lean_inc(v_getEnv_2316_);
lean_dec_ref(v_inst_2312_);
v_toPure_2317_ = lean_ctor_get(v_toApplicative_2314_, 1);
lean_inc(v_toPure_2317_);
lean_dec_ref(v_toApplicative_2314_);
v___f_2318_ = lean_alloc_closure((void*)(l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2318_, 0, v_e_2313_);
lean_closure_set(v___f_2318_, 1, v_toPure_2317_);
v___x_2319_ = lean_apply_4(v_toBind_2315_, lean_box(0), lean_box(0), v_getEnv_2316_, v___f_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp(lean_object* v_m_2320_, lean_object* v_inst_2321_, lean_object* v_inst_2322_, lean_object* v_e_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Meta_isMatcherApp___redArg(v_inst_2321_, v_inst_2322_, v_e_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_));
v___x_2332_ = lean_box(0);
v___x_2333_ = l_Lean_mkTagDeclarationExtension(v___x_2331_, v___x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2____boxed(lean_object* v_a_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_();
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markMatcherLike(lean_object* v_env_2336_, lean_object* v_declName_2337_){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = l_Lean_Meta_matcherLikeExt;
v___x_2339_ = l_Lean_TagDeclarationExtension_tag(v___x_2338_, v_env_2336_, v_declName_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherLikeCore(lean_object* v_env_2340_, lean_object* v_declName_2341_){
_start:
{
lean_object* v___x_2342_; lean_object* v_toEnvExtension_2343_; lean_object* v_asyncMode_2344_; uint8_t v___x_2345_; 
v___x_2342_ = l_Lean_Meta_matcherLikeExt;
v_toEnvExtension_2343_ = lean_ctor_get(v___x_2342_, 0);
v_asyncMode_2344_ = lean_ctor_get(v_toEnvExtension_2343_, 2);
v___x_2345_ = l_Lean_TagDeclarationExtension_isTagged(v___x_2342_, v_env_2340_, v_declName_2341_, v_asyncMode_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLikeCore___boxed(lean_object* v_env_2346_, lean_object* v_declName_2347_){
_start:
{
uint8_t v_res_2348_; lean_object* v_r_2349_; 
v_res_2348_ = l_Lean_Meta_isMatcherLikeCore(v_env_2346_, v_declName_2347_);
v_r_2349_ = lean_box(v_res_2348_);
return v_r_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike___redArg___lam__0(lean_object* v_declName_2350_, lean_object* v_toPure_2351_, lean_object* v_____do__lift_2352_){
_start:
{
uint8_t v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = l_Lean_Meta_isMatcherLikeCore(v_____do__lift_2352_, v_declName_2350_);
v___x_2354_ = lean_box(v___x_2353_);
v___x_2355_ = lean_apply_2(v_toPure_2351_, lean_box(0), v___x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike___redArg(lean_object* v_inst_2356_, lean_object* v_inst_2357_, lean_object* v_declName_2358_){
_start:
{
lean_object* v_toApplicative_2359_; lean_object* v_toBind_2360_; lean_object* v_getEnv_2361_; lean_object* v_toPure_2362_; lean_object* v___f_2363_; lean_object* v___x_2364_; 
v_toApplicative_2359_ = lean_ctor_get(v_inst_2356_, 0);
lean_inc_ref(v_toApplicative_2359_);
v_toBind_2360_ = lean_ctor_get(v_inst_2356_, 1);
lean_inc(v_toBind_2360_);
lean_dec_ref(v_inst_2356_);
v_getEnv_2361_ = lean_ctor_get(v_inst_2357_, 0);
lean_inc(v_getEnv_2361_);
lean_dec_ref(v_inst_2357_);
v_toPure_2362_ = lean_ctor_get(v_toApplicative_2359_, 1);
lean_inc(v_toPure_2362_);
lean_dec_ref(v_toApplicative_2359_);
v___f_2363_ = lean_alloc_closure((void*)(l_Lean_Meta_isMatcherLike___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2363_, 0, v_declName_2358_);
lean_closure_set(v___f_2363_, 1, v_toPure_2362_);
v___x_2364_ = lean_apply_4(v_toBind_2360_, lean_box(0), lean_box(0), v_getEnv_2361_, v___f_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike(lean_object* v_m_2365_, lean_object* v_inst_2366_, lean_object* v_inst_2367_, lean_object* v_declName_2368_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_Meta_isMatcherLike___redArg(v_inst_2366_, v_inst_2367_, v_declName_2368_);
return v___x_2369_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
