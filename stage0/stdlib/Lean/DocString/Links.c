// Lean compiler output
// Module: Lean.DocString.Links
// Imports: public import Lean.Syntax import Init.Data.String.TakeDrop import Init.Data.String.Search import Init.Data.ToString.Macro import Init.While import Init.Data.String.Length
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_manual_get_root(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_getManualRoot___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "https://lean-lang.org/doc/reference/latest/"};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "LEAN_MANUAL_ROOT"};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_manualRoot;
static const lean_string_object l_Lean_errorExplanationManualDomain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Manual.errorExplanation"};
static const lean_object* l_Lean_errorExplanationManualDomain___closed__0 = (const lean_object*)&l_Lean_errorExplanationManualDomain___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_errorExplanationManualDomain = (const lean_object*)&l_Lean_errorExplanationManualDomain___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_domainMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "section"};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_domainMap___closed__0 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_domainMap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Verso.Genre.Manual.section"};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_domainMap___closed__1 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Links_0__Lean_domainMap___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__0_value),((lean_object*)&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__1_value)}};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_domainMap___closed__2 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_domainMap___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "errorExplanation"};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_domainMap___closed__3 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__3_value;
static const lean_ctor_object l___private_Lean_DocString_Links_0__Lean_domainMap___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__3_value),((lean_object*)&l_Lean_errorExplanationManualDomain___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_domainMap___closed__4 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__4_value;
static const lean_ctor_object l___private_Lean_DocString_Links_0__Lean_domainMap___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_domainMap___closed__5 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__5_value;
static const lean_ctor_object l___private_Lean_DocString_Links_0__Lean_domainMap___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__2_value),((lean_object*)&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__5_value)}};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_domainMap___closed__6 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__6_value;
static lean_once_cell_t l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7;
static lean_once_cell_t l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8;
static lean_once_cell_t l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_domainMap;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_manualDomains;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_manualLink_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_List_mapTR_loop___at___00Lean_manualLink_spec__1___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_manualLink_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_manualLink_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_manualLink___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "find/\?domain="};
static const lean_object* l_Lean_manualLink___closed__0 = (const lean_object*)&l_Lean_manualLink___closed__0_value;
static const lean_string_object l_Lean_manualLink___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "&name="};
static const lean_object* l_Lean_manualLink___closed__1 = (const lean_object*)&l_Lean_manualLink___closed__1_value;
static const lean_string_object l_Lean_manualLink___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_manualLink___closed__2 = (const lean_object*)&l_Lean_manualLink___closed__2_value;
static const lean_string_object l_Lean_manualLink___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Unknown documentation type `"};
static const lean_object* l_Lean_manualLink___closed__3 = (const lean_object*)&l_Lean_manualLink___closed__3_value;
static const lean_string_object l_Lean_manualLink___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "`. Expected one of the following: "};
static const lean_object* l_Lean_manualLink___closed__4 = (const lean_object*)&l_Lean_manualLink___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_manualLink(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_manualLink___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1_value;
static const lean_string_object l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_rw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Expected one item after `"};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_rw___closed__0 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_rw___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_rw___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "`, but got "};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_rw___closed__1 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_rw___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_rw___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Missing documentation type"};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_rw___closed__2 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_rw___closed__2_value;
static const lean_ctor_object l___private_Lean_DocString_Links_0__Lean_rw___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Links_0__Lean_rw___closed__2_value)}};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_rw___closed__3 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_rw___closed__3_value;
static const lean_array_object l___private_Lean_DocString_Links_0__Lean_rw___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_rw___closed__4 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_rw___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_rw___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Empty "};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_rw___closed__5 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_rw___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_rw___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " ID"};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_rw___closed__6 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_rw___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_rw___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_rw___closed__7 = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_rw___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rw(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lean-manual://"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(lean_object*, lean_object*);
static const lean_array_object l_Lean_rewriteManualLinksCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_rewriteManualLinksCore___closed__0 = (const lean_object*)&l_Lean_rewriteManualLinksCore___closed__0_value;
static const lean_ctor_object l_Lean_rewriteManualLinksCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_rewriteManualLinksCore___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_rewriteManualLinksCore___closed__1 = (const lean_object*)&l_Lean_rewriteManualLinksCore___closed__1_value;
static const lean_ctor_object l_Lean_rewriteManualLinksCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Links_0__Lean_rw___closed__7_value),((lean_object*)&l_Lean_rewriteManualLinksCore___closed__1_value)}};
static const lean_object* l_Lean_rewriteManualLinksCore___closed__2 = (const lean_object*)&l_Lean_rewriteManualLinksCore___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " * ```"};
static const lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0_value;
static const lean_string_object l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "```: "};
static const lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1_value;
static const lean_string_object l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_rewriteManualLinks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 262, .m_capacity = 262, .m_length = 259, .m_data = "**❌ Syntax Errors in Lean Language Reference Links**\n\nThe `lean-manual` URL scheme is used to link to the version of the Lean reference manual that\ncorresponds to this version of Lean. Errors occurred while processing the links in this documentation\ncomment:\n"};
static const lean_object* l_Lean_rewriteManualLinks___closed__0 = (const lean_object*)&l_Lean_rewriteManualLinks___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks(lean_object*);
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " * "};
static const lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0_value;
static const lean_string_object l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ":\n    "};
static const lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1_value;
static const lean_string_object l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_validateBuiltinDocString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Errors in builtin documentation comment:\n"};
static const lean_object* l_Lean_validateBuiltinDocString___closed__0 = (const lean_object*)&l_Lean_validateBuiltinDocString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString___boxed(lean_object*, lean_object*);
LEAN_EXPORT void l___private_Lean_DocString_Links_0__Lean_getManualRoot_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_1_ = stack[0].m_obj;
lean_object* v_res_2_;
v_res_2_ = lean_manual_get_root(v_a_00___x40___internal___hyg_1_);
stack->m_obj
 = v_res_2_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_getManualRoot___boxed(lean_object* v_a_00___x40___internal___hyg_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lean_manual_get_root(v_a_00___x40___internal___hyg_3_);
return v_res_4_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_box(0);
v___x_10_ = lean_manual_get_root(v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
v___x_12_ = lean_string_utf8_byte_size(v___x_11_);
return v___x_12_;
}
}
static uint8_t _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
v___x_15_ = lean_nat_dec_eq(v___x_14_, v___x_13_);
return v___x_15_;
}
}
lean_object* l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_(){
_start:
{
lean_object* v___y_18_; lean_object* v___y_19_; lean_object* v_r_23_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_));
v___x_33_ = lean_io_getenv(v___x_32_);
if (lean_obj_tag(v___x_33_) == 1)
{
lean_object* v_val_34_; 
v_val_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_val_34_);
lean_dec_ref_known(v___x_33_, 1);
v_r_23_ = v_val_34_;
goto v___jp_22_;
}
else
{
lean_object* v___x_35_; uint8_t v___x_36_; 
lean_dec(v___x_33_);
v___x_35_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
v___x_36_ = lean_uint8_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
if (v___x_36_ == 0)
{
v_r_23_ = v___x_35_;
goto v___jp_22_;
}
else
{
lean_object* v___x_37_; 
v___x_37_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot___closed__0));
v_r_23_ = v___x_37_;
goto v___jp_22_;
}
}
v___jp_17_:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_string_append(v___y_19_, v___y_18_);
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
v___jp_22_:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_24_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_));
v___x_25_ = lean_string_utf8_byte_size(v_r_23_);
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_dec_le(v___x_26_, v___x_25_);
if (v___x_27_ == 0)
{
v___y_18_ = v___x_24_;
v___y_19_ = v_r_23_;
goto v___jp_17_;
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_nat_sub(v___x_25_, v___x_26_);
v___x_30_ = lean_string_memcmp(v_r_23_, v___x_24_, v___x_29_, v___x_28_, v___x_26_);
lean_dec(v___x_29_);
if (v___x_30_ == 0)
{
v___y_18_ = v___x_24_;
v___y_19_ = v_r_23_;
goto v___jp_17_;
}
else
{
lean_object* v___x_31_; 
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v_r_23_);
return v___x_31_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_38_;
v_res_38_ = l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_();
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2____boxed(lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_();
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
return v_x_43_;
}
else
{
lean_object* v_key_45_; lean_object* v_value_46_; lean_object* v_tail_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_70_; 
v_key_45_ = lean_ctor_get(v_x_44_, 0);
v_value_46_ = lean_ctor_get(v_x_44_, 1);
v_tail_47_ = lean_ctor_get(v_x_44_, 2);
v_isSharedCheck_70_ = !lean_is_exclusive(v_x_44_);
if (v_isSharedCheck_70_ == 0)
{
v___x_49_ = v_x_44_;
v_isShared_50_ = v_isSharedCheck_70_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_tail_47_);
lean_inc(v_value_46_);
lean_inc(v_key_45_);
lean_dec(v_x_44_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_70_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; uint64_t v___x_52_; uint64_t v___x_53_; uint64_t v___x_54_; uint64_t v_fold_55_; uint64_t v___x_56_; uint64_t v___x_57_; uint64_t v___x_58_; size_t v___x_59_; size_t v___x_60_; size_t v___x_61_; size_t v___x_62_; size_t v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_51_ = lean_array_get_size(v_x_43_);
v___x_52_ = lean_string_hash(v_key_45_);
v___x_53_ = 32ULL;
v___x_54_ = lean_uint64_shift_right(v___x_52_, v___x_53_);
v_fold_55_ = lean_uint64_xor(v___x_52_, v___x_54_);
v___x_56_ = 16ULL;
v___x_57_ = lean_uint64_shift_right(v_fold_55_, v___x_56_);
v___x_58_ = lean_uint64_xor(v_fold_55_, v___x_57_);
v___x_59_ = lean_uint64_to_usize(v___x_58_);
v___x_60_ = lean_usize_of_nat(v___x_51_);
v___x_61_ = ((size_t)1ULL);
v___x_62_ = lean_usize_sub(v___x_60_, v___x_61_);
v___x_63_ = lean_usize_land(v___x_59_, v___x_62_);
v___x_64_ = lean_array_uget_borrowed(v_x_43_, v___x_63_);
lean_inc(v___x_64_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 2, v___x_64_);
v___x_66_ = v___x_49_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_key_45_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_value_46_);
lean_ctor_set(v_reuseFailAlloc_69_, 2, v___x_64_);
v___x_66_ = v_reuseFailAlloc_69_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; 
v___x_67_ = lean_array_uset(v_x_43_, v___x_63_, v___x_66_);
v_x_43_ = v___x_67_;
v_x_44_ = v_tail_47_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_71_, lean_object* v_source_72_, lean_object* v_target_73_){
_start:
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = lean_array_get_size(v_source_72_);
v___x_75_ = lean_nat_dec_lt(v_i_71_, v___x_74_);
if (v___x_75_ == 0)
{
lean_dec_ref(v_source_72_);
lean_dec(v_i_71_);
return v_target_73_;
}
else
{
lean_object* v_es_76_; lean_object* v___x_77_; lean_object* v_source_78_; lean_object* v_target_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_es_76_ = lean_array_fget(v_source_72_, v_i_71_);
v___x_77_ = lean_box(0);
v_source_78_ = lean_array_fset(v_source_72_, v_i_71_, v___x_77_);
v_target_79_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_73_, v_es_76_);
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_add(v_i_71_, v___x_80_);
lean_dec(v_i_71_);
v_i_71_ = v___x_81_;
v_source_72_ = v_source_78_;
v_target_73_ = v_target_79_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(lean_object* v_data_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_nbuckets_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_84_ = lean_array_get_size(v_data_83_);
v___x_85_ = lean_unsigned_to_nat(2u);
v_nbuckets_86_ = lean_nat_mul(v___x_84_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_box(0);
v___x_89_ = lean_mk_array(v_nbuckets_86_, v___x_88_);
v___x_90_ = lean_array_propagate_mark(v_data_83_, v___x_89_);
v___x_91_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(v___x_87_, v_data_83_, v___x_90_);
return v___x_91_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(lean_object* v_a_92_, lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
else
{
lean_object* v_key_95_; lean_object* v_tail_96_; uint8_t v___x_97_; 
v_key_95_ = lean_ctor_get(v_x_93_, 0);
v_tail_96_ = lean_ctor_get(v_x_93_, 2);
v___x_97_ = lean_string_dec_eq(v_key_95_, v_a_92_);
if (v___x_97_ == 0)
{
v_x_93_ = v_tail_96_;
goto _start;
}
else
{
return v___x_97_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_92_ = stack[0].m_obj;
lean_object* v_x_93_ = stack[1].m_obj;
uint8_t v_res_99_;
v_res_99_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_92_, v_x_93_);
stack->m_num = v_res_99_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_100_, lean_object* v_x_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_100_, v_x_101_);
lean_dec(v_x_101_);
lean_dec_ref(v_a_100_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(lean_object* v_a_104_, lean_object* v_b_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_106_) == 0)
{
lean_dec(v_b_105_);
lean_dec_ref(v_a_104_);
return v_x_106_;
}
else
{
lean_object* v_key_107_; lean_object* v_value_108_; lean_object* v_tail_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_121_; 
v_key_107_ = lean_ctor_get(v_x_106_, 0);
v_value_108_ = lean_ctor_get(v_x_106_, 1);
v_tail_109_ = lean_ctor_get(v_x_106_, 2);
v_isSharedCheck_121_ = !lean_is_exclusive(v_x_106_);
if (v_isSharedCheck_121_ == 0)
{
v___x_111_ = v_x_106_;
v_isShared_112_ = v_isSharedCheck_121_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_tail_109_);
lean_inc(v_value_108_);
lean_inc(v_key_107_);
lean_dec(v_x_106_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_121_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
uint8_t v___x_113_; 
v___x_113_ = lean_string_dec_eq(v_key_107_, v_a_104_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_104_, v_b_105_, v_tail_109_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 2, v___x_114_);
v___x_116_ = v___x_111_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_key_107_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_value_108_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
else
{
lean_object* v___x_119_; 
lean_dec(v_value_108_);
lean_dec(v_key_107_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 1, v_b_105_);
lean_ctor_set(v___x_111_, 0, v_a_104_);
v___x_119_ = v___x_111_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_104_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_b_105_);
lean_ctor_set(v_reuseFailAlloc_120_, 2, v_tail_109_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(lean_object* v_m_122_, lean_object* v_a_123_, lean_object* v_b_124_){
_start:
{
lean_object* v_size_125_; lean_object* v_buckets_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_169_; 
v_size_125_ = lean_ctor_get(v_m_122_, 0);
v_buckets_126_ = lean_ctor_get(v_m_122_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v_m_122_);
if (v_isSharedCheck_169_ == 0)
{
v___x_128_ = v_m_122_;
v_isShared_129_ = v_isSharedCheck_169_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_buckets_126_);
lean_inc(v_size_125_);
lean_dec(v_m_122_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_169_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v_fold_134_; uint64_t v___x_135_; uint64_t v___x_136_; uint64_t v___x_137_; size_t v___x_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; size_t v___x_142_; lean_object* v_bkt_143_; uint8_t v___x_144_; 
v___x_130_ = lean_array_get_size(v_buckets_126_);
v___x_131_ = lean_string_hash(v_a_123_);
v___x_132_ = 32ULL;
v___x_133_ = lean_uint64_shift_right(v___x_131_, v___x_132_);
v_fold_134_ = lean_uint64_xor(v___x_131_, v___x_133_);
v___x_135_ = 16ULL;
v___x_136_ = lean_uint64_shift_right(v_fold_134_, v___x_135_);
v___x_137_ = lean_uint64_xor(v_fold_134_, v___x_136_);
v___x_138_ = lean_uint64_to_usize(v___x_137_);
v___x_139_ = lean_usize_of_nat(v___x_130_);
v___x_140_ = ((size_t)1ULL);
v___x_141_ = lean_usize_sub(v___x_139_, v___x_140_);
v___x_142_ = lean_usize_land(v___x_138_, v___x_141_);
v_bkt_143_ = lean_array_uget_borrowed(v_buckets_126_, v___x_142_);
v___x_144_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_123_, v_bkt_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; lean_object* v_size_x27_146_; lean_object* v___x_147_; lean_object* v_buckets_x27_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_145_ = lean_unsigned_to_nat(1u);
v_size_x27_146_ = lean_nat_add(v_size_125_, v___x_145_);
lean_dec(v_size_125_);
lean_inc(v_bkt_143_);
v___x_147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_147_, 0, v_a_123_);
lean_ctor_set(v___x_147_, 1, v_b_124_);
lean_ctor_set(v___x_147_, 2, v_bkt_143_);
v_buckets_x27_148_ = lean_array_uset(v_buckets_126_, v___x_142_, v___x_147_);
v___x_149_ = lean_unsigned_to_nat(4u);
v___x_150_ = lean_nat_mul(v_size_x27_146_, v___x_149_);
v___x_151_ = lean_unsigned_to_nat(3u);
v___x_152_ = lean_nat_div(v___x_150_, v___x_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_array_get_size(v_buckets_x27_148_);
v___x_154_ = lean_nat_dec_le(v___x_152_, v___x_153_);
lean_dec(v___x_152_);
if (v___x_154_ == 0)
{
lean_object* v_val_155_; lean_object* v___x_157_; 
v_val_155_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(v_buckets_x27_148_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v_val_155_);
lean_ctor_set(v___x_128_, 0, v_size_x27_146_);
v___x_157_ = v___x_128_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_size_x27_146_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_val_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
else
{
lean_object* v___x_160_; 
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v_buckets_x27_148_);
lean_ctor_set(v___x_128_, 0, v_size_x27_146_);
v___x_160_ = v___x_128_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_size_x27_146_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_buckets_x27_148_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
else
{
lean_object* v___x_162_; lean_object* v_buckets_x27_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
lean_inc(v_bkt_143_);
v___x_162_ = lean_box(0);
v_buckets_x27_163_ = lean_array_uset(v_buckets_126_, v___x_142_, v___x_162_);
v___x_164_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_123_, v_b_124_, v_bkt_143_);
v___x_165_ = lean_array_uset(v_buckets_x27_163_, v___x_142_, v___x_164_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v___x_165_);
v___x_167_ = v___x_128_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_size_125_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(lean_object* v_as_x27_170_, lean_object* v_b_171_){
_start:
{
if (lean_obj_tag(v_as_x27_170_) == 0)
{
return v_b_171_;
}
else
{
lean_object* v_head_172_; lean_object* v_tail_173_; lean_object* v_fst_174_; lean_object* v_snd_175_; lean_object* v_r_176_; 
v_head_172_ = lean_ctor_get(v_as_x27_170_, 0);
v_tail_173_ = lean_ctor_get(v_as_x27_170_, 1);
v_fst_174_ = lean_ctor_get(v_head_172_, 0);
v_snd_175_ = lean_ctor_get(v_head_172_, 1);
lean_inc(v_snd_175_);
lean_inc(v_fst_174_);
v_r_176_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_b_171_, v_fst_174_, v_snd_175_);
v_as_x27_170_ = v_tail_173_;
v_b_171_ = v_r_176_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_178_, lean_object* v_b_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_as_x27_178_, v_b_179_);
lean_dec(v_as_x27_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(lean_object* v_m_181_, lean_object* v_l_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_l_182_, v_m_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0___boxed(lean_object* v_m_184_, lean_object* v_l_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(v_m_184_, v_l_185_);
lean_dec(v_l_185_);
return v_res_186_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_box(0);
v___x_203_ = lean_unsigned_to_nat(16u);
v___x_204_ = lean_mk_array(v___x_203_, v___x_202_);
return v___x_204_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8);
v___x_209_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__6));
v___x_210_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v___x_209_, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0(lean_object* v_00_u03b2_212_, lean_object* v_m_213_, lean_object* v_a_214_, lean_object* v_b_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_m_213_, v_a_214_, v_b_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(lean_object* v_as_217_, lean_object* v_as_x27_218_, lean_object* v_b_219_, lean_object* v_a_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_as_x27_218_, v_b_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___boxed(lean_object* v_as_222_, lean_object* v_as_x27_223_, lean_object* v_b_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(v_as_222_, v_as_x27_223_, v_b_224_, v_a_225_);
lean_dec(v_as_x27_223_);
lean_dec(v_as_222_);
return v_res_226_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_227_, lean_object* v_a_228_, lean_object* v_x_229_){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_228_, v_x_229_);
return v___x_230_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_228_ = stack[1].m_obj;
lean_object* v_x_229_ = stack[2].m_obj;
uint8_t v_res_231_;
v_res_231_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(lean_box(0), v_a_228_, v_x_229_);
stack->m_num = v_res_231_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_232_, lean_object* v_a_233_, lean_object* v_x_234_){
_start:
{
uint8_t v_res_235_; lean_object* v_r_236_; 
v_res_235_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(v_00_u03b2_232_, v_a_233_, v_x_234_);
lean_dec(v_x_234_);
lean_dec_ref(v_a_233_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_237_, lean_object* v_data_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(v_data_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_240_, lean_object* v_a_241_, lean_object* v_b_242_, lean_object* v_x_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_241_, v_b_242_, v_x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_245_, lean_object* v_i_246_, lean_object* v_source_247_, lean_object* v_target_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_246_, v_source_247_, v_target_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_251_, v_x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
lean_inc(v_x_254_);
return v_x_254_;
}
else
{
lean_object* v_key_256_; lean_object* v_tail_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_key_256_ = lean_ctor_get(v_x_255_, 0);
v_tail_257_ = lean_ctor_get(v_x_255_, 2);
v___x_258_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_x_254_, v_tail_257_);
lean_inc(v_key_256_);
v___x_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_259_, 0, v_key_256_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0___boxed(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_x_260_, v_x_261_);
lean_dec(v_x_261_);
lean_dec(v_x_260_);
return v_res_262_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(lean_object* v_as_263_, size_t v_i_264_, size_t v_stop_265_, lean_object* v_b_266_){
_start:
{
uint8_t v___x_267_; 
v___x_267_ = lean_usize_dec_eq(v_i_264_, v_stop_265_);
if (v___x_267_ == 0)
{
size_t v___x_268_; size_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_268_ = ((size_t)1ULL);
v___x_269_ = lean_usize_sub(v_i_264_, v___x_268_);
v___x_270_ = lean_array_uget_borrowed(v_as_263_, v___x_269_);
v___x_271_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_b_266_, v___x_270_);
lean_dec(v_b_266_);
v_i_264_ = v___x_269_;
v_b_266_ = v___x_271_;
goto _start;
}
else
{
return v_b_266_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_263_ = stack[0].m_obj;
size_t v_i_264_ = stack[1].m_num;
size_t v_stop_265_ = stack[2].m_num;
lean_object* v_b_266_ = stack[3].m_obj;
lean_object* v_res_273_;
v_res_273_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(v_as_263_, v_i_264_, v_stop_265_, v_b_266_);
stack->m_obj
 = v_res_273_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1___boxed(lean_object* v_as_274_, lean_object* v_i_275_, lean_object* v_stop_276_, lean_object* v_b_277_){
_start:
{
size_t v_i_boxed_278_; size_t v_stop_boxed_279_; lean_object* v_res_280_; 
v_i_boxed_278_ = lean_unbox_usize(v_i_275_);
lean_dec(v_i_275_);
v_stop_boxed_279_ = lean_unbox_usize(v_stop_276_);
lean_dec(v_stop_276_);
v_res_280_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(v_as_274_, v_i_boxed_278_, v_stop_boxed_279_, v_b_277_);
lean_dec_ref(v_as_274_);
return v_res_280_;
}
}
static lean_object* _init_l_Lean_manualDomains(void){
_start:
{
lean_object* v___x_281_; lean_object* v_buckets_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_281_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v_buckets_282_ = lean_ctor_get(v___x_281_, 1);
v___x_283_ = lean_box(0);
v___x_284_ = lean_array_get_size(v_buckets_282_);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_nat_dec_lt(v___x_285_, v___x_284_);
if (v___x_286_ == 0)
{
return v___x_283_;
}
else
{
size_t v___x_287_; size_t v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_usize_of_nat(v___x_284_);
v___x_288_ = ((size_t)0ULL);
v___x_289_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(v_buckets_282_, v___x_287_, v___x_288_, v___x_283_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(lean_object* v_a_290_, lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
lean_object* v___x_292_; 
v___x_292_ = lean_box(0);
return v___x_292_;
}
else
{
lean_object* v_key_293_; lean_object* v_value_294_; lean_object* v_tail_295_; uint8_t v___x_296_; 
v_key_293_ = lean_ctor_get(v_x_291_, 0);
v_value_294_ = lean_ctor_get(v_x_291_, 1);
v_tail_295_ = lean_ctor_get(v_x_291_, 2);
v___x_296_ = lean_string_dec_eq(v_key_293_, v_a_290_);
if (v___x_296_ == 0)
{
v_x_291_ = v_tail_295_;
goto _start;
}
else
{
lean_object* v___x_298_; 
lean_inc(v_value_294_);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v_value_294_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg___boxed(lean_object* v_a_299_, lean_object* v_x_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_299_, v_x_300_);
lean_dec(v_x_300_);
lean_dec_ref(v_a_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(lean_object* v_m_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_buckets_304_; lean_object* v___x_305_; uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v___x_308_; uint64_t v_fold_309_; uint64_t v___x_310_; uint64_t v___x_311_; uint64_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_buckets_304_ = lean_ctor_get(v_m_302_, 1);
v___x_305_ = lean_array_get_size(v_buckets_304_);
v___x_306_ = lean_string_hash(v_a_303_);
v___x_307_ = 32ULL;
v___x_308_ = lean_uint64_shift_right(v___x_306_, v___x_307_);
v_fold_309_ = lean_uint64_xor(v___x_306_, v___x_308_);
v___x_310_ = 16ULL;
v___x_311_ = lean_uint64_shift_right(v_fold_309_, v___x_310_);
v___x_312_ = lean_uint64_xor(v_fold_309_, v___x_311_);
v___x_313_ = lean_uint64_to_usize(v___x_312_);
v___x_314_ = lean_usize_of_nat(v___x_305_);
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_sub(v___x_314_, v___x_315_);
v___x_317_ = lean_usize_land(v___x_313_, v___x_316_);
v___x_318_ = lean_array_uget_borrowed(v_buckets_304_, v___x_317_);
v___x_319_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_303_, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg___boxed(lean_object* v_m_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v_m_320_, v_a_321_);
lean_dec_ref(v_a_321_);
lean_dec_ref(v_m_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_inc(v_x_323_);
return v_x_323_;
}
else
{
lean_object* v_key_325_; lean_object* v_value_326_; lean_object* v_tail_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_key_325_ = lean_ctor_get(v_x_324_, 0);
v_value_326_ = lean_ctor_get(v_x_324_, 1);
v_tail_327_ = lean_ctor_get(v_x_324_, 2);
v___x_328_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_x_323_, v_tail_327_);
lean_inc(v_value_326_);
lean_inc(v_key_325_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v_key_325_);
lean_ctor_set(v___x_329_, 1, v_value_326_);
v___x_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2___boxed(lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_x_331_, v_x_332_);
lean_dec(v_x_332_);
lean_dec(v_x_331_);
return v_res_333_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(lean_object* v_as_334_, size_t v_i_335_, size_t v_stop_336_, lean_object* v_b_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_eq(v_i_335_, v_stop_336_);
if (v___x_338_ == 0)
{
size_t v___x_339_; size_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_sub(v_i_335_, v___x_339_);
v___x_341_ = lean_array_uget_borrowed(v_as_334_, v___x_340_);
v___x_342_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_b_337_, v___x_341_);
lean_dec(v_b_337_);
v_i_335_ = v___x_340_;
v_b_337_ = v___x_342_;
goto _start;
}
else
{
return v_b_337_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_334_ = stack[0].m_obj;
size_t v_i_335_ = stack[1].m_num;
size_t v_stop_336_ = stack[2].m_num;
lean_object* v_b_337_ = stack[3].m_obj;
lean_object* v_res_344_;
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_as_334_, v_i_335_, v_stop_336_, v_b_337_);
stack->m_obj
 = v_res_344_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3___boxed(lean_object* v_as_345_, lean_object* v_i_346_, lean_object* v_stop_347_, lean_object* v_b_348_){
_start:
{
size_t v_i_boxed_349_; size_t v_stop_boxed_350_; lean_object* v_res_351_; 
v_i_boxed_349_ = lean_unbox_usize(v_i_346_);
lean_dec(v_i_346_);
v_stop_boxed_350_ = lean_unbox_usize(v_stop_347_);
lean_dec(v_stop_347_);
v_res_351_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_as_345_, v_i_boxed_349_, v_stop_boxed_350_, v_b_348_);
lean_dec_ref(v_as_345_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_manualLink_spec__1(lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
if (lean_obj_tag(v_a_353_) == 0)
{
lean_object* v___x_355_; 
v___x_355_ = l_List_reverse___redArg(v_a_354_);
return v___x_355_;
}
else
{
lean_object* v_head_356_; lean_object* v_tail_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_369_; 
v_head_356_ = lean_ctor_get(v_a_353_, 0);
v_tail_357_ = lean_ctor_get(v_a_353_, 1);
v_isSharedCheck_369_ = !lean_is_exclusive(v_a_353_);
if (v_isSharedCheck_369_ == 0)
{
v___x_359_ = v_a_353_;
v_isShared_360_ = v_isSharedCheck_369_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_tail_357_);
lean_inc(v_head_356_);
lean_dec(v_a_353_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_369_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_fst_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v_fst_361_ = lean_ctor_get(v_head_356_, 0);
lean_inc(v_fst_361_);
lean_dec(v_head_356_);
v___x_362_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_manualLink_spec__1___closed__0));
v___x_363_ = lean_string_append(v___x_362_, v_fst_361_);
lean_dec(v_fst_361_);
v___x_364_ = lean_string_append(v___x_363_, v___x_362_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v_a_354_);
lean_ctor_set(v___x_359_, 0, v___x_364_);
v___x_366_ = v___x_359_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_a_354_);
v___x_366_ = v_reuseFailAlloc_368_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
v_a_353_ = v_tail_357_;
v_a_354_ = v___x_366_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_manualLink(lean_object* v_kind_375_, lean_object* v_name_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_378_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_377_, v_kind_375_);
if (lean_obj_tag(v___x_378_) == 1)
{
lean_object* v_val_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_393_; 
v_val_379_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_393_ == 0)
{
v___x_381_ = v___x_378_;
v_isShared_382_ = v_isSharedCheck_393_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_val_379_);
lean_dec(v___x_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_393_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_383_ = l_Lean_manualRoot;
v___x_384_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_385_ = lean_string_append(v___x_384_, v_val_379_);
lean_dec(v_val_379_);
v___x_386_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_387_ = lean_string_append(v___x_385_, v___x_386_);
v___x_388_ = lean_string_append(v___x_387_, v_name_376_);
v___x_389_ = lean_string_append(v___x_383_, v___x_388_);
lean_dec_ref(v___x_388_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_389_);
v___x_391_ = v___x_381_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
else
{
lean_object* v_buckets_394_; lean_object* v___x_395_; lean_object* v___y_397_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
lean_dec(v___x_378_);
v_buckets_394_ = lean_ctor_get(v___x_377_, 1);
v___x_395_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_407_ = lean_box(0);
v___x_408_ = lean_array_get_size(v_buckets_394_);
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = lean_nat_dec_lt(v___x_409_, v___x_408_);
if (v___x_410_ == 0)
{
v___y_397_ = v___x_407_;
goto v___jp_396_;
}
else
{
size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; 
v___x_411_ = lean_usize_of_nat(v___x_408_);
v___x_412_ = ((size_t)0ULL);
v___x_413_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_394_, v___x_411_, v___x_412_, v___x_407_);
v___y_397_ = v___x_413_;
goto v___jp_396_;
}
v___jp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_acceptableKinds_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_398_ = lean_box(0);
v___x_399_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_397_, v___x_398_);
v_acceptableKinds_400_ = l_String_intercalate(v___x_395_, v___x_399_);
v___x_401_ = ((lean_object*)(l_Lean_manualLink___closed__3));
v___x_402_ = lean_string_append(v___x_401_, v_kind_375_);
v___x_403_ = ((lean_object*)(l_Lean_manualLink___closed__4));
v___x_404_ = lean_string_append(v___x_402_, v___x_403_);
v___x_405_ = lean_string_append(v___x_404_, v_acceptableKinds_400_);
lean_dec_ref(v_acceptableKinds_400_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_manualLink___boxed(lean_object* v_kind_414_, lean_object* v_name_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_manualLink(v_kind_414_, v_name_415_);
lean_dec_ref(v_name_415_);
lean_dec_ref(v_kind_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(lean_object* v_00_u03b2_417_, lean_object* v_m_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v_m_418_, v_a_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___boxed(lean_object* v_00_u03b2_421_, lean_object* v_m_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(v_00_u03b2_421_, v_m_422_, v_a_423_);
lean_dec_ref(v_a_423_);
lean_dec_ref(v_m_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(lean_object* v_00_u03b2_425_, lean_object* v_a_426_, lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_426_, v_x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___boxed(lean_object* v_00_u03b2_429_, lean_object* v_a_430_, lean_object* v_x_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(v_00_u03b2_429_, v_a_430_, v_x_431_);
lean_dec(v_x_431_);
lean_dec_ref(v_a_430_);
return v_res_432_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg(){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg___closed__0));
return v___x_436_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_437_;
v_res_437_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg();
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg___boxed(lean_object* v___dummy_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg();
return v_res_439_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0(void){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg();
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(lean_object* v_s_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___boxed(lean_object* v_s_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(v_s_443_);
lean_dec_ref(v_s_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(lean_object* v_path_445_, lean_object* v___x_446_, lean_object* v___x_447_, lean_object* v_a_448_, lean_object* v_b_449_){
_start:
{
lean_object* v_it_451_; lean_object* v_startInclusive_452_; lean_object* v_endExclusive_453_; 
if (lean_obj_tag(v_a_448_) == 0)
{
lean_object* v_currPos_458_; lean_object* v_searcher_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_482_; 
v_currPos_458_ = lean_ctor_get(v_a_448_, 0);
v_searcher_459_ = lean_ctor_get(v_a_448_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_a_448_);
if (v_isSharedCheck_482_ == 0)
{
v___x_461_ = v_a_448_;
v_isShared_462_ = v_isSharedCheck_482_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_searcher_459_);
lean_inc(v_currPos_458_);
lean_dec(v_a_448_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_482_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
uint8_t v_decide_463_; 
v_decide_463_ = lean_nat_dec_eq(v_searcher_459_, v___x_447_);
if (v_decide_463_ == 0)
{
uint32_t v___x_464_; uint32_t v___x_465_; uint8_t v___x_466_; 
v___x_464_ = 47;
v___x_465_ = lean_string_utf8_get_fast(v_path_445_, v_searcher_459_);
v___x_466_ = lean_uint32_dec_eq(v___x_465_, v___x_464_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = lean_string_utf8_next_fast(v_path_445_, v_searcher_459_);
lean_dec(v_searcher_459_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_467_);
v___x_469_ = v___x_461_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_currPos_458_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_467_);
v___x_469_ = v_reuseFailAlloc_471_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
v_a_448_ = v___x_469_;
goto _start;
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_slice_475_; lean_object* v_nextIt_477_; 
v___x_472_ = lean_string_utf8_next_fast(v_path_445_, v_searcher_459_);
v___x_473_ = lean_nat_sub(v___x_472_, v_searcher_459_);
v___x_474_ = lean_nat_add(v_searcher_459_, v___x_473_);
lean_dec(v___x_473_);
v_slice_475_ = l_String_Slice_subslice_x21(v___x_446_, v_currPos_458_, v_searcher_459_);
lean_inc(v___x_474_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_474_);
lean_ctor_set(v___x_461_, 0, v___x_474_);
v_nextIt_477_ = v___x_461_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_474_);
v_nextIt_477_ = v_reuseFailAlloc_480_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v_startInclusive_478_; lean_object* v_endExclusive_479_; 
v_startInclusive_478_ = lean_ctor_get(v_slice_475_, 0);
lean_inc(v_startInclusive_478_);
v_endExclusive_479_ = lean_ctor_get(v_slice_475_, 1);
lean_inc(v_endExclusive_479_);
lean_dec_ref(v_slice_475_);
v_it_451_ = v_nextIt_477_;
v_startInclusive_452_ = v_startInclusive_478_;
v_endExclusive_453_ = v_endExclusive_479_;
goto v___jp_450_;
}
}
}
else
{
lean_object* v___x_481_; 
lean_del_object(v___x_461_);
lean_dec(v_searcher_459_);
v___x_481_ = lean_box(1);
lean_inc(v___x_447_);
v_it_451_ = v___x_481_;
v_startInclusive_452_ = v_currPos_458_;
v_endExclusive_453_ = v___x_447_;
goto v___jp_450_;
}
}
}
else
{
lean_dec(v___x_447_);
lean_dec_ref(v_path_445_);
return v_b_449_;
}
v___jp_450_:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_inc_ref(v_path_445_);
v___x_454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_454_, 0, v_path_445_);
lean_ctor_set(v___x_454_, 1, v_startInclusive_452_);
lean_ctor_set(v___x_454_, 2, v_endExclusive_453_);
v___x_455_ = l_String_Slice_toString(v___x_454_);
lean_dec_ref_known(v___x_454_, 3);
v___x_456_ = lean_array_push(v_b_449_, v___x_455_);
v_a_448_ = v_it_451_;
v_b_449_ = v___x_456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg___boxed(lean_object* v_path_483_, lean_object* v___x_484_, lean_object* v___x_485_, lean_object* v_a_486_, lean_object* v_b_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_483_, v___x_484_, v___x_485_, v_a_486_, v_b_487_);
lean_dec_ref(v___x_484_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
return v_x_489_;
}
else
{
lean_object* v_head_491_; lean_object* v_tail_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_head_491_ = lean_ctor_get(v_x_490_, 0);
v_tail_492_ = lean_ctor_get(v_x_490_, 1);
v___x_493_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_494_ = lean_string_append(v_x_489_, v___x_493_);
v___x_495_ = lean_string_append(v___x_494_, v_head_491_);
v_x_489_ = v___x_495_;
v_x_490_ = v_tail_492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0___boxed(lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v_x_497_, v_x_498_);
lean_dec(v_x_498_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(lean_object* v_x_503_){
_start:
{
if (lean_obj_tag(v_x_503_) == 0)
{
lean_object* v___x_504_; 
v___x_504_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0));
return v___x_504_;
}
else
{
lean_object* v_tail_505_; 
v_tail_505_ = lean_ctor_get(v_x_503_, 1);
if (lean_obj_tag(v_tail_505_) == 0)
{
lean_object* v_head_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_head_506_ = lean_ctor_get(v_x_503_, 0);
v___x_507_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_508_ = lean_string_append(v___x_507_, v_head_506_);
v___x_509_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2));
v___x_510_ = lean_string_append(v___x_508_, v___x_509_);
return v___x_510_;
}
else
{
lean_object* v_head_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint32_t v___x_515_; lean_object* v___x_516_; 
v_head_511_ = lean_ctor_get(v_x_503_, 0);
v___x_512_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_513_ = lean_string_append(v___x_512_, v_head_511_);
v___x_514_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v___x_513_, v_tail_505_);
v___x_515_ = 93;
v___x_516_ = lean_string_push(v___x_514_, v___x_515_);
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___boxed(lean_object* v_x_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v_x_517_);
lean_dec(v_x_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rw(lean_object* v_path_529_){
_start:
{
lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = lean_string_utf8_byte_size(v_path_529_);
lean_inc_ref(v_path_529_);
v___x_557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_557_, 0, v_path_529_);
lean_ctor_set(v___x_557_, 1, v___x_555_);
lean_ctor_set(v___x_557_, 2, v___x_556_);
v___x_558_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0);
v___x_559_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__4));
v___x_560_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_529_, v___x_557_, v___x_556_, v___x_558_, v___x_559_);
lean_dec_ref_known(v___x_557_, 3);
v___x_561_ = lean_array_to_list(v___x_560_);
if (lean_obj_tag(v___x_561_) == 0)
{
goto v___jp_553_;
}
else
{
lean_object* v_head_562_; lean_object* v_tail_563_; lean_object* v_kind_565_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_head_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_head_562_);
v_tail_563_ = lean_ctor_get(v___x_561_, 1);
lean_inc(v_tail_563_);
lean_dec_ref_known(v___x_561_, 2);
v___x_600_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_601_ = lean_string_dec_eq(v_head_562_, v___x_600_);
if (v___x_601_ == 0)
{
v_kind_565_ = v_head_562_;
goto v___jp_564_;
}
else
{
lean_dec(v_head_562_);
if (lean_obj_tag(v_tail_563_) == 0)
{
goto v___jp_553_;
}
else
{
v_kind_565_ = v___x_600_;
goto v___jp_564_;
}
}
v___jp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_566_, v_kind_565_);
if (lean_obj_tag(v___x_567_) == 1)
{
if (lean_obj_tag(v_tail_563_) == 1)
{
lean_object* v_tail_568_; 
v_tail_568_ = lean_ctor_get(v_tail_563_, 1);
if (lean_obj_tag(v_tail_568_) == 0)
{
lean_object* v_val_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_591_; 
v_val_569_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_591_ == 0)
{
v___x_571_ = v___x_567_;
v_isShared_572_ = v_isSharedCheck_591_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_val_569_);
lean_dec(v___x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_591_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v_head_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_head_573_ = lean_ctor_get(v_tail_563_, 0);
lean_inc(v_head_573_);
lean_dec_ref_known(v_tail_563_, 2);
v___x_574_ = lean_string_utf8_byte_size(v_head_573_);
v___x_575_ = lean_nat_dec_eq(v___x_574_, v___x_555_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
lean_dec_ref(v_kind_565_);
v___x_576_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_577_ = lean_string_append(v___x_576_, v_val_569_);
lean_dec(v_val_569_);
v___x_578_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_579_ = lean_string_append(v___x_577_, v___x_578_);
v___x_580_ = lean_string_append(v___x_579_, v_head_573_);
lean_dec(v_head_573_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_580_);
v___x_582_ = v___x_571_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
lean_dec(v_head_573_);
lean_dec(v_val_569_);
v___x_584_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__5));
v___x_585_ = lean_string_append(v___x_584_, v_kind_565_);
lean_dec_ref(v_kind_565_);
v___x_586_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__6));
v___x_587_ = lean_string_append(v___x_585_, v___x_586_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 0);
lean_ctor_set(v___x_571_, 0, v___x_587_);
v___x_589_ = v___x_571_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_567_, 1);
v___y_544_ = v_tail_563_;
v___y_545_ = v_kind_565_;
goto v___jp_543_;
}
}
else
{
lean_dec_ref_known(v___x_567_, 1);
v___y_544_ = v_tail_563_;
v___y_545_ = v_kind_565_;
goto v___jp_543_;
}
}
else
{
lean_object* v_buckets_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
lean_dec(v___x_567_);
lean_dec(v_tail_563_);
v_buckets_592_ = lean_ctor_get(v___x_566_, 1);
v___x_593_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_594_ = lean_box(0);
v___x_595_ = lean_array_get_size(v_buckets_592_);
v___x_596_ = lean_nat_dec_lt(v___x_555_, v___x_595_);
if (v___x_596_ == 0)
{
v___y_531_ = v_kind_565_;
v___y_532_ = v___x_593_;
v___y_533_ = v___x_594_;
goto v___jp_530_;
}
else
{
size_t v___x_597_; size_t v___x_598_; lean_object* v___x_599_; 
v___x_597_ = lean_usize_of_nat(v___x_595_);
v___x_598_ = ((size_t)0ULL);
v___x_599_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_592_, v___x_597_, v___x_598_, v___x_594_);
v___y_531_ = v_kind_565_;
v___y_532_ = v___x_593_;
v___y_533_ = v___x_599_;
goto v___jp_530_;
}
}
}
}
v___jp_530_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v_acceptableKinds_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_534_ = lean_box(0);
v___x_535_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_533_, v___x_534_);
v_acceptableKinds_536_ = l_String_intercalate(v___y_532_, v___x_535_);
v___x_537_ = ((lean_object*)(l_Lean_manualLink___closed__3));
v___x_538_ = lean_string_append(v___x_537_, v___y_531_);
lean_dec_ref(v___y_531_);
v___x_539_ = ((lean_object*)(l_Lean_manualLink___closed__4));
v___x_540_ = lean_string_append(v___x_538_, v___x_539_);
v___x_541_ = lean_string_append(v___x_540_, v_acceptableKinds_536_);
lean_dec_ref(v_acceptableKinds_536_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
v___jp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_546_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__0));
v___x_547_ = lean_string_append(v___x_546_, v___y_545_);
lean_dec_ref(v___y_545_);
v___x_548_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__1));
v___x_549_ = lean_string_append(v___x_547_, v___x_548_);
v___x_550_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v___y_544_);
lean_dec(v___y_544_);
v___x_551_ = lean_string_append(v___x_549_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
v___jp_553_:
{
lean_object* v___x_554_; 
v___x_554_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__3));
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(lean_object* v_path_602_, lean_object* v___x_603_, lean_object* v___x_604_, lean_object* v_inst_605_, lean_object* v_R_606_, lean_object* v_a_607_, lean_object* v_b_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_602_, v___x_603_, v___x_604_, v_a_607_, v_b_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___boxed(lean_object* v_path_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v_inst_613_, lean_object* v_R_614_, lean_object* v_a_615_, lean_object* v_b_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(v_path_610_, v___x_611_, v___x_612_, v_inst_613_, v_R_614_, v_a_615_, v_b_616_);
lean_dec_ref(v___x_611_);
return v_res_617_;
}
}
uint8_t l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(uint32_t v_c_618_){
_start:
{
uint32_t v___x_670_; uint8_t v___x_671_; 
v___x_670_ = 65;
v___x_671_ = lean_uint32_dec_le(v___x_670_, v_c_618_);
if (v___x_671_ == 0)
{
goto v___jp_665_;
}
else
{
uint32_t v___x_672_; uint8_t v___x_673_; 
v___x_672_ = 90;
v___x_673_ = lean_uint32_dec_le(v_c_618_, v___x_672_);
if (v___x_673_ == 0)
{
goto v___jp_665_;
}
else
{
return v___x_673_;
}
}
v___jp_619_:
{
uint32_t v___x_620_; uint8_t v___x_621_; 
v___x_620_ = 45;
v___x_621_ = lean_uint32_dec_eq(v_c_618_, v___x_620_);
if (v___x_621_ == 0)
{
uint32_t v___x_622_; uint8_t v___x_623_; 
v___x_622_ = 46;
v___x_623_ = lean_uint32_dec_eq(v_c_618_, v___x_622_);
if (v___x_623_ == 0)
{
uint32_t v___x_624_; uint8_t v___x_625_; 
v___x_624_ = 95;
v___x_625_ = lean_uint32_dec_eq(v_c_618_, v___x_624_);
if (v___x_625_ == 0)
{
uint32_t v___x_626_; uint8_t v___x_627_; 
v___x_626_ = 126;
v___x_627_ = lean_uint32_dec_eq(v_c_618_, v___x_626_);
if (v___x_627_ == 0)
{
uint32_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 58;
v___x_629_ = lean_uint32_dec_eq(v_c_618_, v___x_628_);
if (v___x_629_ == 0)
{
uint32_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = 47;
v___x_631_ = lean_uint32_dec_eq(v_c_618_, v___x_630_);
if (v___x_631_ == 0)
{
uint32_t v___x_632_; uint8_t v___x_633_; 
v___x_632_ = 63;
v___x_633_ = lean_uint32_dec_eq(v_c_618_, v___x_632_);
if (v___x_633_ == 0)
{
uint32_t v___x_634_; uint8_t v___x_635_; 
v___x_634_ = 35;
v___x_635_ = lean_uint32_dec_eq(v_c_618_, v___x_634_);
if (v___x_635_ == 0)
{
uint32_t v___x_636_; uint8_t v___x_637_; 
v___x_636_ = 91;
v___x_637_ = lean_uint32_dec_eq(v_c_618_, v___x_636_);
if (v___x_637_ == 0)
{
uint32_t v___x_638_; uint8_t v___x_639_; 
v___x_638_ = 93;
v___x_639_ = lean_uint32_dec_eq(v_c_618_, v___x_638_);
if (v___x_639_ == 0)
{
uint32_t v___x_640_; uint8_t v___x_641_; 
v___x_640_ = 64;
v___x_641_ = lean_uint32_dec_eq(v_c_618_, v___x_640_);
if (v___x_641_ == 0)
{
uint32_t v___x_642_; uint8_t v___x_643_; 
v___x_642_ = 33;
v___x_643_ = lean_uint32_dec_eq(v_c_618_, v___x_642_);
if (v___x_643_ == 0)
{
uint32_t v___x_644_; uint8_t v___x_645_; 
v___x_644_ = 36;
v___x_645_ = lean_uint32_dec_eq(v_c_618_, v___x_644_);
if (v___x_645_ == 0)
{
uint32_t v___x_646_; uint8_t v___x_647_; 
v___x_646_ = 38;
v___x_647_ = lean_uint32_dec_eq(v_c_618_, v___x_646_);
if (v___x_647_ == 0)
{
uint32_t v___x_648_; uint8_t v___x_649_; 
v___x_648_ = 39;
v___x_649_ = lean_uint32_dec_eq(v_c_618_, v___x_648_);
if (v___x_649_ == 0)
{
uint32_t v___x_650_; uint8_t v___x_651_; 
v___x_650_ = 42;
v___x_651_ = lean_uint32_dec_eq(v_c_618_, v___x_650_);
if (v___x_651_ == 0)
{
uint32_t v___x_652_; uint8_t v___x_653_; 
v___x_652_ = 43;
v___x_653_ = lean_uint32_dec_eq(v_c_618_, v___x_652_);
if (v___x_653_ == 0)
{
uint32_t v___x_654_; uint8_t v___x_655_; 
v___x_654_ = 44;
v___x_655_ = lean_uint32_dec_eq(v_c_618_, v___x_654_);
if (v___x_655_ == 0)
{
uint32_t v___x_656_; uint8_t v___x_657_; 
v___x_656_ = 59;
v___x_657_ = lean_uint32_dec_eq(v_c_618_, v___x_656_);
if (v___x_657_ == 0)
{
uint32_t v___x_658_; uint8_t v___x_659_; 
v___x_658_ = 61;
v___x_659_ = lean_uint32_dec_eq(v_c_618_, v___x_658_);
return v___x_659_;
}
else
{
return v___x_657_;
}
}
else
{
return v___x_655_;
}
}
else
{
return v___x_653_;
}
}
else
{
return v___x_651_;
}
}
else
{
return v___x_649_;
}
}
else
{
return v___x_647_;
}
}
else
{
return v___x_645_;
}
}
else
{
return v___x_643_;
}
}
else
{
return v___x_641_;
}
}
else
{
return v___x_639_;
}
}
else
{
return v___x_637_;
}
}
else
{
return v___x_635_;
}
}
else
{
return v___x_633_;
}
}
else
{
return v___x_631_;
}
}
else
{
return v___x_629_;
}
}
else
{
return v___x_627_;
}
}
else
{
return v___x_625_;
}
}
else
{
return v___x_623_;
}
}
else
{
return v___x_621_;
}
}
v___jp_660_:
{
uint32_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 48;
v___x_662_ = lean_uint32_dec_le(v___x_661_, v_c_618_);
if (v___x_662_ == 0)
{
goto v___jp_619_;
}
else
{
uint32_t v___x_663_; uint8_t v___x_664_; 
v___x_663_ = 57;
v___x_664_ = lean_uint32_dec_le(v_c_618_, v___x_663_);
if (v___x_664_ == 0)
{
goto v___jp_619_;
}
else
{
return v___x_664_;
}
}
}
v___jp_665_:
{
uint32_t v___x_666_; uint8_t v___x_667_; 
v___x_666_ = 97;
v___x_667_ = lean_uint32_dec_le(v___x_666_, v_c_618_);
if (v___x_667_ == 0)
{
goto v___jp_660_;
}
else
{
uint32_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = 122;
v___x_669_ = lean_uint32_dec_le(v_c_618_, v___x_668_);
if (v___x_669_ == 0)
{
goto v___jp_660_;
}
else
{
return v___x_669_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_618_ = stack[0].m_num;
uint8_t v_res_674_;
v_res_674_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v_c_618_);
stack->m_num = v_res_674_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar___boxed(lean_object* v_c_675_){
_start:
{
uint32_t v_c_boxed_676_; uint8_t v_res_677_; lean_object* v_r_678_; 
v_c_boxed_676_ = lean_unbox_uint32(v_c_675_);
lean_dec(v_c_675_);
v_res_677_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v_c_boxed_676_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(lean_object* v_s_679_, lean_object* v___x_680_, lean_object* v___x_681_, uint32_t v___x_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_snd_684_; lean_object* v_snd_685_; lean_object* v_fst_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_754_; 
v_snd_684_ = lean_ctor_get(v_a_683_, 1);
lean_inc(v_snd_684_);
v_snd_685_ = lean_ctor_get(v_snd_684_, 1);
lean_inc(v_snd_685_);
v_fst_686_ = lean_ctor_get(v_a_683_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v_a_683_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v_a_683_, 1);
lean_dec(v_unused_755_);
v___x_688_ = v_a_683_;
v_isShared_689_ = v_isSharedCheck_754_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_fst_686_);
lean_dec(v_a_683_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_754_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_fst_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_752_; 
v_fst_690_ = lean_ctor_get(v_snd_684_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v_snd_684_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v_snd_684_, 1);
lean_dec(v_unused_753_);
v___x_692_ = v_snd_684_;
v_isShared_693_ = v_isSharedCheck_752_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_fst_690_);
lean_dec(v_snd_684_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_752_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_fst_694_; lean_object* v_snd_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_751_; 
v_fst_694_ = lean_ctor_get(v_snd_685_, 0);
v_snd_695_ = lean_ctor_get(v_snd_685_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_snd_685_);
if (v_isSharedCheck_751_ == 0)
{
v___x_697_ = v_snd_685_;
v_isShared_698_ = v_isSharedCheck_751_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snd_695_);
lean_inc(v_fst_694_);
lean_dec(v_snd_685_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_751_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; uint8_t v_decide_700_; 
v___x_699_ = lean_string_utf8_byte_size(v_s_679_);
v_decide_700_ = lean_nat_dec_eq(v_snd_695_, v___x_699_);
if (v_decide_700_ == 0)
{
uint32_t v___x_701_; lean_object* v___x_702_; uint8_t v___y_735_; uint8_t v___x_740_; 
v___x_701_ = lean_string_utf8_get_fast(v_s_679_, v_snd_695_);
v___x_702_ = lean_string_utf8_next_fast(v_s_679_, v_snd_695_);
v___x_740_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v___x_701_);
if (v___x_740_ == 0)
{
v___y_735_ = v___x_740_;
goto v___jp_734_;
}
else
{
uint8_t v_decide_741_; 
v_decide_741_ = lean_nat_dec_eq(v___x_702_, v___x_699_);
if (v_decide_741_ == 0)
{
v___y_735_ = v___x_740_;
goto v___jp_734_;
}
else
{
goto v___jp_703_;
}
}
v___jp_703_:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_string_utf8_extract_fast(v_s_679_, v___x_680_, v_snd_695_);
v___x_705_ = l___private_Lean_DocString_Links_0__Lean_rw(v___x_704_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_681_);
lean_ctor_set(v___x_707_, 1, v_snd_695_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v_a_706_);
lean_ctor_set(v___x_697_, 0, v___x_707_);
v___x_709_ = v___x_697_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_a_706_);
v___x_709_ = v_reuseFailAlloc_719_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_710_ = lean_array_push(v_fst_690_, v___x_709_);
v___x_711_ = lean_string_push(v_fst_686_, v___x_682_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_702_);
lean_ctor_set(v___x_692_, 0, v_fst_694_);
v___x_713_ = v___x_692_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_fst_694_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_702_);
v___x_713_ = v_reuseFailAlloc_718_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_713_);
lean_ctor_set(v___x_688_, 0, v___x_710_);
v___x_715_ = v___x_688_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_713_);
v___x_715_ = v_reuseFailAlloc_717_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; 
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_711_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
return v___x_716_;
}
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
lean_dec(v_snd_695_);
lean_dec(v_fst_694_);
lean_dec(v___x_681_);
v_a_720_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_705_, 1);
v___x_721_ = l_Lean_manualRoot;
v___x_722_ = lean_string_append(v_fst_686_, v___x_721_);
v___x_723_ = lean_string_append(v___x_722_, v_a_720_);
lean_dec(v_a_720_);
v___x_724_ = lean_string_push(v___x_723_, v___x_701_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v___x_702_);
lean_ctor_set(v___x_697_, 0, v___x_702_);
v___x_726_ = v___x_697_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_702_);
v___x_726_ = v_reuseFailAlloc_733_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_726_);
v___x_728_ = v___x_692_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_fst_690_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_728_);
lean_ctor_set(v___x_688_, 0, v___x_724_);
v___x_730_ = v___x_688_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
v___jp_734_:
{
if (v___y_735_ == 0)
{
goto v___jp_703_;
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
lean_del_object(v___x_697_);
lean_dec(v_snd_695_);
lean_del_object(v___x_692_);
lean_del_object(v___x_688_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v_fst_694_);
lean_ctor_set(v___x_736_, 1, v___x_702_);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_fst_690_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v_fst_686_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v_a_683_ = v___x_738_;
goto _start;
}
}
}
else
{
lean_object* v___x_743_; 
lean_dec(v___x_681_);
if (v_isShared_698_ == 0)
{
v___x_743_ = v___x_697_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_fst_694_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_snd_695_);
v___x_743_ = v_reuseFailAlloc_750_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_743_);
v___x_745_ = v___x_692_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_fst_690_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_743_);
v___x_745_ = v_reuseFailAlloc_749_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_747_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_745_);
v___x_747_ = v___x_688_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_fst_686_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_679_ = stack[0].m_obj;
lean_object* v___x_680_ = stack[1].m_obj;
lean_object* v___x_681_ = stack[2].m_obj;
uint32_t v___x_682_ = stack[3].m_num;
lean_object* v_a_683_ = stack[4].m_obj;
lean_object* v_res_756_;
v_res_756_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_679_, v___x_680_, v___x_681_, v___x_682_, v_a_683_);
stack->m_obj
 = v_res_756_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg___boxed(lean_object* v_s_757_, lean_object* v___x_758_, lean_object* v___x_759_, lean_object* v___x_760_, lean_object* v_a_761_){
_start:
{
uint32_t v___x_2315__boxed_762_; lean_object* v_res_763_; 
v___x_2315__boxed_762_ = lean_unbox_uint32(v___x_760_);
lean_dec(v___x_760_);
v_res_763_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_757_, v___x_758_, v___x_759_, v___x_2315__boxed_762_, v_a_761_);
lean_dec(v___x_758_);
lean_dec_ref(v_s_757_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(lean_object* v_s_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_snd_767_; lean_object* v_fst_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_832_; 
v_snd_767_ = lean_ctor_get(v_a_766_, 1);
v_fst_768_ = lean_ctor_get(v_a_766_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v_a_766_);
if (v_isSharedCheck_832_ == 0)
{
v___x_770_ = v_a_766_;
v_isShared_771_ = v_isSharedCheck_832_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_snd_767_);
lean_inc(v_fst_768_);
lean_dec(v_a_766_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_832_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v_fst_772_; lean_object* v_snd_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_831_; 
v_fst_772_ = lean_ctor_get(v_snd_767_, 0);
v_snd_773_ = lean_ctor_get(v_snd_767_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_snd_767_);
if (v_isSharedCheck_831_ == 0)
{
v___x_775_ = v_snd_767_;
v_isShared_776_ = v_isSharedCheck_831_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_snd_773_);
lean_inc(v_fst_772_);
lean_dec(v_snd_767_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_831_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; uint8_t v_decide_778_; 
v___x_777_ = lean_string_utf8_byte_size(v_s_765_);
v_decide_778_ = lean_nat_dec_eq(v_snd_773_, v___x_777_);
if (v_decide_778_ == 0)
{
uint32_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_779_ = lean_string_utf8_get_fast(v_s_765_, v_snd_773_);
v___x_780_ = lean_string_utf8_next_fast(v_s_765_, v_snd_773_);
v___x_790_ = lean_unsigned_to_nat(14u);
v___x_791_ = lean_nat_sub(v___x_777_, v_snd_773_);
v___x_792_ = lean_nat_dec_le(v___x_790_, v___x_791_);
lean_dec(v___x_791_);
if (v___x_792_ == 0)
{
lean_dec(v_snd_773_);
goto v___jp_781_;
}
else
{
lean_object* v_scheme_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_scheme_793_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0));
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_string_memcmp(v_s_765_, v_scheme_793_, v_snd_773_, v___x_794_, v___x_790_);
if (v___x_795_ == 0)
{
lean_dec(v_snd_773_);
goto v___jp_781_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_snd_803_; lean_object* v_snd_804_; lean_object* v_fst_805_; lean_object* v_fst_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_823_; 
lean_del_object(v___x_775_);
lean_del_object(v___x_770_);
lean_inc(v_snd_773_);
lean_inc_ref(v_s_765_);
v___x_796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_796_, 0, v_s_765_);
lean_ctor_set(v___x_796_, 1, v_snd_773_);
lean_ctor_set(v___x_796_, 2, v___x_777_);
v___x_797_ = l_String_Slice_pos_x21(v___x_796_, v___x_790_);
lean_dec_ref_known(v___x_796_, 3);
v___x_798_ = lean_nat_add(v_snd_773_, v___x_797_);
lean_dec(v___x_797_);
lean_inc(v___x_798_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_780_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_fst_772_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_fst_768_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_765_, v___x_798_, v_snd_773_, v___x_779_, v___x_801_);
lean_dec(v___x_798_);
v_snd_803_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_snd_803_);
v_snd_804_ = lean_ctor_get(v_snd_803_, 1);
lean_inc(v_snd_804_);
v_fst_805_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_fst_805_);
lean_dec_ref(v___x_802_);
v_fst_806_ = lean_ctor_get(v_snd_803_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_snd_803_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v_snd_803_, 1);
lean_dec(v_unused_824_);
v___x_808_ = v_snd_803_;
v_isShared_809_ = v_isSharedCheck_823_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_fst_806_);
lean_dec(v_snd_803_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_823_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_fst_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_821_; 
v_fst_810_ = lean_ctor_get(v_snd_804_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_snd_804_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_snd_804_, 1);
lean_dec(v_unused_822_);
v___x_812_ = v_snd_804_;
v_isShared_813_ = v_isSharedCheck_821_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_fst_810_);
lean_dec(v_snd_804_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_821_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 1, v_fst_810_);
lean_ctor_set(v___x_812_, 0, v_fst_806_);
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_fst_806_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_fst_810_);
v___x_815_ = v_reuseFailAlloc_820_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v___x_815_);
lean_ctor_set(v___x_808_, 0, v_fst_805_);
v___x_817_ = v___x_808_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_fst_805_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_815_);
v___x_817_ = v_reuseFailAlloc_819_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
v_a_766_ = v___x_817_;
goto _start;
}
}
}
}
}
}
v___jp_781_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_string_push(v_fst_768_, v___x_779_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v___x_780_);
v___x_784_ = v___x_775_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_fst_772_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_780_);
v___x_784_ = v_reuseFailAlloc_789_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_786_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v___x_784_);
lean_ctor_set(v___x_770_, 0, v___x_782_);
v___x_786_ = v___x_770_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_784_);
v___x_786_ = v_reuseFailAlloc_788_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
v_a_766_ = v___x_786_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_826_; 
lean_dec_ref(v_s_765_);
if (v_isShared_776_ == 0)
{
v___x_826_ = v___x_775_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_fst_772_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_snd_773_);
v___x_826_ = v_reuseFailAlloc_830_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_828_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v___x_826_);
v___x_828_ = v___x_770_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_fst_768_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore(lean_object* v_s_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_snd_844_; lean_object* v_fst_845_; lean_object* v_fst_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v___x_842_ = ((lean_object*)(l_Lean_rewriteManualLinksCore___closed__2));
v___x_843_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(v_s_841_, v___x_842_);
v_snd_844_ = lean_ctor_get(v___x_843_, 1);
lean_inc(v_snd_844_);
v_fst_845_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_fst_845_);
lean_dec_ref(v___x_843_);
v_fst_846_ = lean_ctor_get(v_snd_844_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v_snd_844_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v_snd_844_, 1);
lean_dec(v_unused_854_);
v___x_848_ = v_snd_844_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_fst_846_);
lean_dec(v_snd_844_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v_fst_845_);
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_fst_846_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_fst_845_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0(lean_object* v_s_855_, lean_object* v___x_856_, lean_object* v___x_857_, uint32_t v___x_858_, lean_object* v_inst_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_855_, v___x_856_, v___x_857_, v___x_858_, v_a_860_);
return v___x_861_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_855_ = stack[0].m_obj;
lean_object* v___x_856_ = stack[1].m_obj;
lean_object* v___x_857_ = stack[2].m_obj;
uint32_t v___x_858_ = stack[3].m_num;
lean_object* v_a_860_ = stack[5].m_obj;
lean_object* v_res_862_;
v_res_862_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0(v_s_855_, v___x_856_, v___x_857_, v___x_858_, lean_box(0), v_a_860_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___boxed(lean_object* v_s_863_, lean_object* v___x_864_, lean_object* v___x_865_, lean_object* v___x_866_, lean_object* v_inst_867_, lean_object* v_a_868_){
_start:
{
uint32_t v___x_2738__boxed_869_; lean_object* v_res_870_; 
v___x_2738__boxed_869_ = lean_unbox_uint32(v___x_866_);
lean_dec(v___x_866_);
v_res_870_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0(v_s_863_, v___x_864_, v___x_865_, v___x_2738__boxed_869_, v_inst_867_, v_a_868_);
lean_dec(v___x_864_);
lean_dec_ref(v_s_863_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1(lean_object* v_s_871_, lean_object* v_inst_872_, lean_object* v_a_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(v_s_871_, v_a_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(lean_object* v_docString_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
if (lean_obj_tag(v_a_879_) == 0)
{
lean_object* v___x_881_; 
v___x_881_ = l_List_reverse___redArg(v_a_880_);
return v___x_881_;
}
else
{
lean_object* v_head_882_; lean_object* v_fst_883_; lean_object* v_tail_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_903_; 
v_head_882_ = lean_ctor_get(v_a_879_, 0);
lean_inc(v_head_882_);
v_fst_883_ = lean_ctor_get(v_head_882_, 0);
lean_inc(v_fst_883_);
v_tail_884_ = lean_ctor_get(v_a_879_, 1);
v_isSharedCheck_903_ = !lean_is_exclusive(v_a_879_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; 
v_unused_904_ = lean_ctor_get(v_a_879_, 0);
lean_dec(v_unused_904_);
v___x_886_ = v_a_879_;
v_isShared_887_ = v_isSharedCheck_903_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_tail_884_);
lean_dec(v_a_879_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_903_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_snd_888_; lean_object* v_start_889_; lean_object* v_stop_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v_snd_888_ = lean_ctor_get(v_head_882_, 1);
lean_inc(v_snd_888_);
lean_dec(v_head_882_);
v_start_889_ = lean_ctor_get(v_fst_883_, 0);
lean_inc(v_start_889_);
v_stop_890_ = lean_ctor_get(v_fst_883_, 1);
lean_inc(v_stop_890_);
lean_dec(v_fst_883_);
v___x_891_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0));
v___x_892_ = lean_string_utf8_extract(v_docString_878_, v_start_889_, v_stop_890_);
lean_dec(v_stop_890_);
lean_dec(v_start_889_);
v___x_893_ = lean_string_append(v___x_891_, v___x_892_);
lean_dec_ref(v___x_892_);
v___x_894_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1));
v___x_895_ = lean_string_append(v___x_893_, v___x_894_);
v___x_896_ = lean_string_append(v___x_895_, v_snd_888_);
lean_dec(v_snd_888_);
v___x_897_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_898_ = lean_string_append(v___x_896_, v___x_897_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 1, v_a_880_);
lean_ctor_set(v___x_886_, 0, v___x_898_);
v___x_900_ = v___x_886_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_a_880_);
v___x_900_ = v_reuseFailAlloc_902_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
v_a_879_ = v_tail_884_;
v_a_880_ = v___x_900_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___boxed(lean_object* v_docString_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_905_, v_a_906_, v_a_907_);
lean_dec_ref(v_docString_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
if (lean_obj_tag(v_x_910_) == 0)
{
return v_x_909_;
}
else
{
lean_object* v_head_911_; lean_object* v_tail_912_; lean_object* v___x_913_; 
v_head_911_ = lean_ctor_get(v_x_910_, 0);
v_tail_912_ = lean_ctor_get(v_x_910_, 1);
v___x_913_ = lean_string_append(v_x_909_, v_head_911_);
v_x_909_ = v___x_913_;
v_x_910_ = v_tail_912_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1___boxed(lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v_x_915_, v_x_916_);
lean_dec(v_x_916_);
return v_res_917_;
}
}
lean_object* l_Lean_rewriteManualLinks(lean_object* v_docString_919_){
_start:
{
lean_object* v___x_921_; lean_object* v_fst_922_; lean_object* v_snd_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
lean_inc_ref(v_docString_919_);
v___x_921_ = l_Lean_rewriteManualLinksCore(v_docString_919_);
v_fst_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_fst_922_);
v_snd_923_ = lean_ctor_get(v___x_921_, 1);
lean_inc(v_snd_923_);
lean_dec_ref(v___x_921_);
v___x_924_ = lean_array_get_size(v_fst_922_);
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = lean_nat_dec_eq(v___x_924_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_927_ = ((lean_object*)(l_Lean_rewriteManualLinks___closed__0));
v___x_928_ = lean_array_to_list(v_fst_922_);
v___x_929_ = lean_box(0);
v___x_930_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_919_, v___x_928_, v___x_929_);
lean_dec_ref(v_docString_919_);
v___x_931_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_932_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_931_, v___x_930_);
lean_dec(v___x_930_);
v___x_933_ = lean_string_append(v___x_927_, v___x_932_);
lean_dec_ref(v___x_932_);
v___x_934_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_935_ = lean_string_append(v_snd_923_, v___x_934_);
v___x_936_ = lean_string_append(v___x_935_, v___x_933_);
lean_dec_ref(v___x_933_);
return v___x_936_;
}
else
{
lean_dec(v_fst_922_);
lean_dec_ref(v_docString_919_);
return v_snd_923_;
}
}
}
LEAN_EXPORT void l_Lean_rewriteManualLinks_0interp(lean_interpreter_value* stack)
{
lean_object* v_docString_919_ = stack[0].m_obj;
lean_object* v_res_937_;
v_res_937_ = l_Lean_rewriteManualLinks(v_docString_919_);
stack->m_obj
 = v_res_937_;
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks___boxed(lean_object* v_docString_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_rewriteManualLinks(v_docString_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(lean_object* v_docString_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
if (lean_obj_tag(v_a_945_) == 0)
{
lean_object* v___x_947_; 
v___x_947_ = l_List_reverse___redArg(v_a_946_);
return v___x_947_;
}
else
{
lean_object* v_head_948_; lean_object* v_fst_949_; lean_object* v_tail_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_974_; 
v_head_948_ = lean_ctor_get(v_a_945_, 0);
lean_inc(v_head_948_);
v_fst_949_ = lean_ctor_get(v_head_948_, 0);
lean_inc(v_fst_949_);
v_tail_950_ = lean_ctor_get(v_a_945_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_a_945_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v_a_945_, 0);
lean_dec(v_unused_975_);
v___x_952_ = v_a_945_;
v_isShared_953_ = v_isSharedCheck_974_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_tail_950_);
lean_dec(v_a_945_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_974_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_snd_954_; lean_object* v_start_955_; lean_object* v_stop_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v_snd_954_ = lean_ctor_get(v_head_948_, 1);
lean_inc(v_snd_954_);
lean_dec(v_head_948_);
v_start_955_ = lean_ctor_get(v_fst_949_, 0);
lean_inc(v_start_955_);
v_stop_956_ = lean_ctor_get(v_fst_949_, 1);
lean_inc(v_stop_956_);
lean_dec(v_fst_949_);
v___x_957_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0));
v___x_958_ = lean_string_utf8_extract(v_docString_944_, v_start_955_, v_stop_956_);
lean_dec(v_stop_956_);
lean_dec(v_start_955_);
v___x_959_ = l_String_quote(v___x_958_);
v___x_960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
v___x_961_ = l_Std_Format_defWidth;
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = l_Std_Format_pretty(v___x_960_, v___x_961_, v___x_962_, v___x_962_);
v___x_964_ = lean_string_append(v___x_957_, v___x_963_);
lean_dec_ref(v___x_963_);
v___x_965_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1));
v___x_966_ = lean_string_append(v___x_964_, v___x_965_);
v___x_967_ = lean_string_append(v___x_966_, v_snd_954_);
lean_dec(v_snd_954_);
v___x_968_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2));
v___x_969_ = lean_string_append(v___x_967_, v___x_968_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v_a_946_);
lean_ctor_set(v___x_952_, 0, v___x_969_);
v___x_971_ = v___x_952_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_a_946_);
v___x_971_ = v_reuseFailAlloc_973_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
v_a_945_ = v_tail_950_;
v_a_946_ = v___x_971_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___boxed(lean_object* v_docString_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_976_, v_a_977_, v_a_978_);
lean_dec_ref(v_docString_976_);
return v_res_979_;
}
}
lean_object* l_Lean_validateBuiltinDocString(lean_object* v_docString_981_){
_start:
{
lean_object* v___x_983_; lean_object* v_fst_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
lean_inc_ref(v_docString_981_);
v___x_983_ = l_Lean_rewriteManualLinksCore(v_docString_981_);
v_fst_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_fst_984_);
lean_dec_ref(v___x_983_);
v___x_985_ = lean_array_get_size(v_fst_984_);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = lean_nat_dec_eq(v___x_985_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_988_ = ((lean_object*)(l_Lean_validateBuiltinDocString___closed__0));
v___x_989_ = lean_array_to_list(v_fst_984_);
v___x_990_ = lean_box(0);
v___x_991_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_981_, v___x_989_, v___x_990_);
lean_dec_ref(v_docString_981_);
v___x_992_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_993_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_992_, v___x_991_);
lean_dec(v___x_991_);
v___x_994_ = lean_string_append(v___x_988_, v___x_993_);
lean_dec_ref(v___x_993_);
v___x_995_ = lean_mk_io_user_error(v___x_994_);
v___x_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec(v_fst_984_);
lean_dec_ref(v_docString_981_);
v___x_997_ = lean_box(0);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
}
LEAN_EXPORT void l_Lean_validateBuiltinDocString_0interp(lean_interpreter_value* stack)
{
lean_object* v_docString_981_ = stack[0].m_obj;
lean_object* v_res_999_;
v_res_999_ = l_Lean_validateBuiltinDocString(v_docString_981_);
stack->m_obj
 = v_res_999_;
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString___boxed(lean_object* v_docString_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_validateBuiltinDocString(v_docString_1000_);
return v_res_1002_;
}
}
lean_object* runtime_initialize_Lean_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Links(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_manualRoot = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_manualRoot);
lean_dec_ref(res);
l___private_Lean_DocString_Links_0__Lean_domainMap = _init_l___private_Lean_DocString_Links_0__Lean_domainMap();
lean_mark_persistent(l___private_Lean_DocString_Links_0__Lean_domainMap);
l_Lean_manualDomains = _init_l_Lean_manualDomains();
lean_mark_persistent(l_Lean_manualDomains);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_Links(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Syntax(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Links(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Links(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_Links(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_Links(builtin);
}
#ifdef __cplusplus
}
#endif
