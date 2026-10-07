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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_getManualRoot___boxed(lean_object* v_a_00___x40___internal___hyg_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lean_manual_get_root(v_a_00___x40___internal___hyg_2_);
return v_res_3_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_box(0);
v___x_9_ = lean_manual_get_root(v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
v___x_11_ = lean_string_utf8_byte_size(v___x_10_);
return v___x_11_;
}
}
static uint8_t _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
v___x_14_ = lean_nat_dec_eq(v___x_13_, v___x_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_(){
_start:
{
lean_object* v___y_17_; lean_object* v___y_18_; lean_object* v_r_22_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_));
v___x_32_ = lean_io_getenv(v___x_31_);
if (lean_obj_tag(v___x_32_) == 1)
{
lean_object* v_val_33_; 
v_val_33_ = lean_ctor_get(v___x_32_, 0);
lean_inc(v_val_33_);
lean_dec_ref_known(v___x_32_, 1);
v_r_22_ = v_val_33_;
goto v___jp_21_;
}
else
{
lean_object* v___x_34_; uint8_t v___x_35_; 
lean_dec(v___x_32_);
v___x_34_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
v___x_35_ = lean_uint8_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
if (v___x_35_ == 0)
{
v_r_22_ = v___x_34_;
goto v___jp_21_;
}
else
{
lean_object* v___x_36_; 
v___x_36_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot___closed__0));
v_r_22_ = v___x_36_;
goto v___jp_21_;
}
}
v___jp_16_:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_string_append(v___y_18_, v___y_17_);
v___x_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
return v___x_20_;
}
v___jp_21_:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_23_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_));
v___x_24_ = lean_string_utf8_byte_size(v_r_22_);
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_dec_le(v___x_25_, v___x_24_);
if (v___x_26_ == 0)
{
v___y_17_ = v___x_23_;
v___y_18_ = v_r_22_;
goto v___jp_16_;
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_27_ = lean_unsigned_to_nat(0u);
v___x_28_ = lean_nat_sub(v___x_24_, v___x_25_);
v___x_29_ = lean_string_memcmp(v_r_22_, v___x_23_, v___x_28_, v___x_27_, v___x_25_);
lean_dec(v___x_28_);
if (v___x_29_ == 0)
{
v___y_17_ = v___x_23_;
v___y_18_ = v_r_22_;
goto v___jp_16_;
}
else
{
lean_object* v___x_30_; 
v___x_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_30_, 0, v_r_22_);
return v___x_30_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2____boxed(lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_();
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
return v_x_41_;
}
else
{
lean_object* v_key_43_; lean_object* v_value_44_; lean_object* v_tail_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_68_; 
v_key_43_ = lean_ctor_get(v_x_42_, 0);
v_value_44_ = lean_ctor_get(v_x_42_, 1);
v_tail_45_ = lean_ctor_get(v_x_42_, 2);
v_isSharedCheck_68_ = !lean_is_exclusive(v_x_42_);
if (v_isSharedCheck_68_ == 0)
{
v___x_47_ = v_x_42_;
v_isShared_48_ = v_isSharedCheck_68_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_tail_45_);
lean_inc(v_value_44_);
lean_inc(v_key_43_);
lean_dec(v_x_42_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_68_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; uint64_t v___x_50_; uint64_t v___x_51_; uint64_t v___x_52_; uint64_t v_fold_53_; uint64_t v___x_54_; uint64_t v___x_55_; uint64_t v___x_56_; size_t v___x_57_; size_t v___x_58_; size_t v___x_59_; size_t v___x_60_; size_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_49_ = lean_array_get_size(v_x_41_);
v___x_50_ = lean_string_hash(v_key_43_);
v___x_51_ = 32ULL;
v___x_52_ = lean_uint64_shift_right(v___x_50_, v___x_51_);
v_fold_53_ = lean_uint64_xor(v___x_50_, v___x_52_);
v___x_54_ = 16ULL;
v___x_55_ = lean_uint64_shift_right(v_fold_53_, v___x_54_);
v___x_56_ = lean_uint64_xor(v_fold_53_, v___x_55_);
v___x_57_ = lean_uint64_to_usize(v___x_56_);
v___x_58_ = lean_usize_of_nat(v___x_49_);
v___x_59_ = ((size_t)1ULL);
v___x_60_ = lean_usize_sub(v___x_58_, v___x_59_);
v___x_61_ = lean_usize_land(v___x_57_, v___x_60_);
v___x_62_ = lean_array_uget_borrowed(v_x_41_, v___x_61_);
lean_inc(v___x_62_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 2, v___x_62_);
v___x_64_ = v___x_47_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_key_43_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_value_44_);
lean_ctor_set(v_reuseFailAlloc_67_, 2, v___x_62_);
v___x_64_ = v_reuseFailAlloc_67_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; 
v___x_65_ = lean_array_uset(v_x_41_, v___x_61_, v___x_64_);
v_x_41_ = v___x_65_;
v_x_42_ = v_tail_45_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_69_, lean_object* v_source_70_, lean_object* v_target_71_){
_start:
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_array_get_size(v_source_70_);
v___x_73_ = lean_nat_dec_lt(v_i_69_, v___x_72_);
if (v___x_73_ == 0)
{
lean_dec_ref(v_source_70_);
lean_dec(v_i_69_);
return v_target_71_;
}
else
{
lean_object* v_es_74_; lean_object* v___x_75_; lean_object* v_source_76_; lean_object* v_target_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_es_74_ = lean_array_fget(v_source_70_, v_i_69_);
v___x_75_ = lean_box(0);
v_source_76_ = lean_array_fset(v_source_70_, v_i_69_, v___x_75_);
v_target_77_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_71_, v_es_74_);
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_add(v_i_69_, v___x_78_);
lean_dec(v_i_69_);
v_i_69_ = v___x_79_;
v_source_70_ = v_source_76_;
v_target_71_ = v_target_77_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(lean_object* v_data_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v_nbuckets_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_82_ = lean_array_get_size(v_data_81_);
v___x_83_ = lean_unsigned_to_nat(2u);
v_nbuckets_84_ = lean_nat_mul(v___x_82_, v___x_83_);
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = lean_box(0);
v___x_87_ = lean_mk_array(v_nbuckets_84_, v___x_86_);
v___x_88_ = lean_array_propagate_mark(v_data_81_, v___x_87_);
v___x_89_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(v___x_85_, v_data_81_, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(lean_object* v_a_90_, lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
else
{
lean_object* v_key_93_; lean_object* v_tail_94_; uint8_t v___x_95_; 
v_key_93_ = lean_ctor_get(v_x_91_, 0);
v_tail_94_ = lean_ctor_get(v_x_91_, 2);
v___x_95_ = lean_string_dec_eq(v_key_93_, v_a_90_);
if (v___x_95_ == 0)
{
v_x_91_ = v_tail_94_;
goto _start;
}
else
{
return v___x_95_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_97_, lean_object* v_x_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_97_, v_x_98_);
lean_dec(v_x_98_);
lean_dec_ref(v_a_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(lean_object* v_a_101_, lean_object* v_b_102_, lean_object* v_x_103_){
_start:
{
if (lean_obj_tag(v_x_103_) == 0)
{
lean_dec(v_b_102_);
lean_dec_ref(v_a_101_);
return v_x_103_;
}
else
{
lean_object* v_key_104_; lean_object* v_value_105_; lean_object* v_tail_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_118_; 
v_key_104_ = lean_ctor_get(v_x_103_, 0);
v_value_105_ = lean_ctor_get(v_x_103_, 1);
v_tail_106_ = lean_ctor_get(v_x_103_, 2);
v_isSharedCheck_118_ = !lean_is_exclusive(v_x_103_);
if (v_isSharedCheck_118_ == 0)
{
v___x_108_ = v_x_103_;
v_isShared_109_ = v_isSharedCheck_118_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_tail_106_);
lean_inc(v_value_105_);
lean_inc(v_key_104_);
lean_dec(v_x_103_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_118_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
uint8_t v___x_110_; 
v___x_110_ = lean_string_dec_eq(v_key_104_, v_a_101_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_111_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_101_, v_b_102_, v_tail_106_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 2, v___x_111_);
v___x_113_ = v___x_108_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_key_104_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_value_105_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
else
{
lean_object* v___x_116_; 
lean_dec(v_value_105_);
lean_dec(v_key_104_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v_b_102_);
lean_ctor_set(v___x_108_, 0, v_a_101_);
v___x_116_ = v___x_108_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_101_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_b_102_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v_tail_106_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(lean_object* v_m_119_, lean_object* v_a_120_, lean_object* v_b_121_){
_start:
{
lean_object* v_size_122_; lean_object* v_buckets_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_166_; 
v_size_122_ = lean_ctor_get(v_m_119_, 0);
v_buckets_123_ = lean_ctor_get(v_m_119_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_m_119_);
if (v_isSharedCheck_166_ == 0)
{
v___x_125_ = v_m_119_;
v_isShared_126_ = v_isSharedCheck_166_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_buckets_123_);
lean_inc(v_size_122_);
lean_dec(v_m_119_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_166_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint64_t v___x_130_; uint64_t v_fold_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; size_t v___x_138_; size_t v___x_139_; lean_object* v_bkt_140_; uint8_t v___x_141_; 
v___x_127_ = lean_array_get_size(v_buckets_123_);
v___x_128_ = lean_string_hash(v_a_120_);
v___x_129_ = 32ULL;
v___x_130_ = lean_uint64_shift_right(v___x_128_, v___x_129_);
v_fold_131_ = lean_uint64_xor(v___x_128_, v___x_130_);
v___x_132_ = 16ULL;
v___x_133_ = lean_uint64_shift_right(v_fold_131_, v___x_132_);
v___x_134_ = lean_uint64_xor(v_fold_131_, v___x_133_);
v___x_135_ = lean_uint64_to_usize(v___x_134_);
v___x_136_ = lean_usize_of_nat(v___x_127_);
v___x_137_ = ((size_t)1ULL);
v___x_138_ = lean_usize_sub(v___x_136_, v___x_137_);
v___x_139_ = lean_usize_land(v___x_135_, v___x_138_);
v_bkt_140_ = lean_array_uget_borrowed(v_buckets_123_, v___x_139_);
v___x_141_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_120_, v_bkt_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v_size_x27_143_; lean_object* v___x_144_; lean_object* v_buckets_x27_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_142_ = lean_unsigned_to_nat(1u);
v_size_x27_143_ = lean_nat_add(v_size_122_, v___x_142_);
lean_dec(v_size_122_);
lean_inc(v_bkt_140_);
v___x_144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_144_, 0, v_a_120_);
lean_ctor_set(v___x_144_, 1, v_b_121_);
lean_ctor_set(v___x_144_, 2, v_bkt_140_);
v_buckets_x27_145_ = lean_array_uset(v_buckets_123_, v___x_139_, v___x_144_);
v___x_146_ = lean_unsigned_to_nat(4u);
v___x_147_ = lean_nat_mul(v_size_x27_143_, v___x_146_);
v___x_148_ = lean_unsigned_to_nat(3u);
v___x_149_ = lean_nat_div(v___x_147_, v___x_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_array_get_size(v_buckets_x27_145_);
v___x_151_ = lean_nat_dec_le(v___x_149_, v___x_150_);
lean_dec(v___x_149_);
if (v___x_151_ == 0)
{
lean_object* v_val_152_; lean_object* v___x_154_; 
v_val_152_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(v_buckets_x27_145_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v_val_152_);
lean_ctor_set(v___x_125_, 0, v_size_x27_143_);
v___x_154_ = v___x_125_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_size_x27_143_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_val_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
else
{
lean_object* v___x_157_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v_buckets_x27_145_);
lean_ctor_set(v___x_125_, 0, v_size_x27_143_);
v___x_157_ = v___x_125_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_size_x27_143_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_buckets_x27_145_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
else
{
lean_object* v___x_159_; lean_object* v_buckets_x27_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
lean_inc(v_bkt_140_);
v___x_159_ = lean_box(0);
v_buckets_x27_160_ = lean_array_uset(v_buckets_123_, v___x_139_, v___x_159_);
v___x_161_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_120_, v_b_121_, v_bkt_140_);
v___x_162_ = lean_array_uset(v_buckets_x27_160_, v___x_139_, v___x_161_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_162_);
v___x_164_ = v___x_125_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_size_122_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(lean_object* v_as_x27_167_, lean_object* v_b_168_){
_start:
{
if (lean_obj_tag(v_as_x27_167_) == 0)
{
return v_b_168_;
}
else
{
lean_object* v_head_169_; lean_object* v_tail_170_; lean_object* v_fst_171_; lean_object* v_snd_172_; lean_object* v_r_173_; 
v_head_169_ = lean_ctor_get(v_as_x27_167_, 0);
v_tail_170_ = lean_ctor_get(v_as_x27_167_, 1);
v_fst_171_ = lean_ctor_get(v_head_169_, 0);
v_snd_172_ = lean_ctor_get(v_head_169_, 1);
lean_inc(v_snd_172_);
lean_inc(v_fst_171_);
v_r_173_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_b_168_, v_fst_171_, v_snd_172_);
v_as_x27_167_ = v_tail_170_;
v_b_168_ = v_r_173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_175_, lean_object* v_b_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_as_x27_175_, v_b_176_);
lean_dec(v_as_x27_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(lean_object* v_m_178_, lean_object* v_l_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_l_179_, v_m_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0___boxed(lean_object* v_m_181_, lean_object* v_l_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(v_m_181_, v_l_182_);
lean_dec(v_l_182_);
return v_res_183_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_box(0);
v___x_200_ = lean_unsigned_to_nat(16u);
v___x_201_ = lean_mk_array(v___x_200_, v___x_199_);
return v___x_201_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7);
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
return v___x_204_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8);
v___x_206_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__6));
v___x_207_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v___x_206_, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap(void){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0(lean_object* v_00_u03b2_209_, lean_object* v_m_210_, lean_object* v_a_211_, lean_object* v_b_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_m_210_, v_a_211_, v_b_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(lean_object* v_as_214_, lean_object* v_as_x27_215_, lean_object* v_b_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_as_x27_215_, v_b_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___boxed(lean_object* v_as_219_, lean_object* v_as_x27_220_, lean_object* v_b_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(v_as_219_, v_as_x27_220_, v_b_221_, v_a_222_);
lean_dec(v_as_x27_220_);
lean_dec(v_as_219_);
return v_res_223_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_224_, lean_object* v_a_225_, lean_object* v_x_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_225_, v_x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_228_, lean_object* v_a_229_, lean_object* v_x_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(v_00_u03b2_228_, v_a_229_, v_x_230_);
lean_dec(v_x_230_);
lean_dec_ref(v_a_229_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_233_, lean_object* v_data_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(v_data_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_236_, lean_object* v_a_237_, lean_object* v_b_238_, lean_object* v_x_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_237_, v_b_238_, v_x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_241_, lean_object* v_i_242_, lean_object* v_source_243_, lean_object* v_target_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_242_, v_source_243_, v_target_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_247_, v_x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
lean_inc(v_x_250_);
return v_x_250_;
}
else
{
lean_object* v_key_252_; lean_object* v_tail_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_key_252_ = lean_ctor_get(v_x_251_, 0);
v_tail_253_ = lean_ctor_get(v_x_251_, 2);
v___x_254_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_x_250_, v_tail_253_);
lean_inc(v_key_252_);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v_key_252_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0___boxed(lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_x_256_, v_x_257_);
lean_dec(v_x_257_);
lean_dec(v_x_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(lean_object* v_as_259_, size_t v_i_260_, size_t v_stop_261_, lean_object* v_b_262_){
_start:
{
uint8_t v___x_263_; 
v___x_263_ = lean_usize_dec_eq(v_i_260_, v_stop_261_);
if (v___x_263_ == 0)
{
size_t v___x_264_; size_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_264_ = ((size_t)1ULL);
v___x_265_ = lean_usize_sub(v_i_260_, v___x_264_);
v___x_266_ = lean_array_uget_borrowed(v_as_259_, v___x_265_);
v___x_267_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_b_262_, v___x_266_);
lean_dec(v_b_262_);
v_i_260_ = v___x_265_;
v_b_262_ = v___x_267_;
goto _start;
}
else
{
return v_b_262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1___boxed(lean_object* v_as_269_, lean_object* v_i_270_, lean_object* v_stop_271_, lean_object* v_b_272_){
_start:
{
size_t v_i_boxed_273_; size_t v_stop_boxed_274_; lean_object* v_res_275_; 
v_i_boxed_273_ = lean_unbox_usize(v_i_270_);
lean_dec(v_i_270_);
v_stop_boxed_274_ = lean_unbox_usize(v_stop_271_);
lean_dec(v_stop_271_);
v_res_275_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(v_as_269_, v_i_boxed_273_, v_stop_boxed_274_, v_b_272_);
lean_dec_ref(v_as_269_);
return v_res_275_;
}
}
static lean_object* _init_l_Lean_manualDomains(void){
_start:
{
lean_object* v___x_276_; lean_object* v_buckets_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_276_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v_buckets_277_ = lean_ctor_get(v___x_276_, 1);
v___x_278_ = lean_box(0);
v___x_279_ = lean_array_get_size(v_buckets_277_);
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_nat_dec_lt(v___x_280_, v___x_279_);
if (v___x_281_ == 0)
{
return v___x_278_;
}
else
{
size_t v___x_282_; size_t v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_usize_of_nat(v___x_279_);
v___x_283_ = ((size_t)0ULL);
v___x_284_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(v_buckets_277_, v___x_282_, v___x_283_, v___x_278_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(lean_object* v_a_285_, lean_object* v_x_286_){
_start:
{
if (lean_obj_tag(v_x_286_) == 0)
{
lean_object* v___x_287_; 
v___x_287_ = lean_box(0);
return v___x_287_;
}
else
{
lean_object* v_key_288_; lean_object* v_value_289_; lean_object* v_tail_290_; uint8_t v___x_291_; 
v_key_288_ = lean_ctor_get(v_x_286_, 0);
v_value_289_ = lean_ctor_get(v_x_286_, 1);
v_tail_290_ = lean_ctor_get(v_x_286_, 2);
v___x_291_ = lean_string_dec_eq(v_key_288_, v_a_285_);
if (v___x_291_ == 0)
{
v_x_286_ = v_tail_290_;
goto _start;
}
else
{
lean_object* v___x_293_; 
lean_inc(v_value_289_);
v___x_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_293_, 0, v_value_289_);
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg___boxed(lean_object* v_a_294_, lean_object* v_x_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_294_, v_x_295_);
lean_dec(v_x_295_);
lean_dec_ref(v_a_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(lean_object* v_m_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_buckets_299_; lean_object* v___x_300_; uint64_t v___x_301_; uint64_t v___x_302_; uint64_t v___x_303_; uint64_t v_fold_304_; uint64_t v___x_305_; uint64_t v___x_306_; uint64_t v___x_307_; size_t v___x_308_; size_t v___x_309_; size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_buckets_299_ = lean_ctor_get(v_m_297_, 1);
v___x_300_ = lean_array_get_size(v_buckets_299_);
v___x_301_ = lean_string_hash(v_a_298_);
v___x_302_ = 32ULL;
v___x_303_ = lean_uint64_shift_right(v___x_301_, v___x_302_);
v_fold_304_ = lean_uint64_xor(v___x_301_, v___x_303_);
v___x_305_ = 16ULL;
v___x_306_ = lean_uint64_shift_right(v_fold_304_, v___x_305_);
v___x_307_ = lean_uint64_xor(v_fold_304_, v___x_306_);
v___x_308_ = lean_uint64_to_usize(v___x_307_);
v___x_309_ = lean_usize_of_nat(v___x_300_);
v___x_310_ = ((size_t)1ULL);
v___x_311_ = lean_usize_sub(v___x_309_, v___x_310_);
v___x_312_ = lean_usize_land(v___x_308_, v___x_311_);
v___x_313_ = lean_array_uget_borrowed(v_buckets_299_, v___x_312_);
v___x_314_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_298_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg___boxed(lean_object* v_m_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v_m_315_, v_a_316_);
lean_dec_ref(v_a_316_);
lean_dec_ref(v_m_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_inc(v_x_318_);
return v_x_318_;
}
else
{
lean_object* v_key_320_; lean_object* v_value_321_; lean_object* v_tail_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_key_320_ = lean_ctor_get(v_x_319_, 0);
v_value_321_ = lean_ctor_get(v_x_319_, 1);
v_tail_322_ = lean_ctor_get(v_x_319_, 2);
v___x_323_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_x_318_, v_tail_322_);
lean_inc(v_value_321_);
lean_inc(v_key_320_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v_key_320_);
lean_ctor_set(v___x_324_, 1, v_value_321_);
v___x_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_323_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2___boxed(lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_x_326_, v_x_327_);
lean_dec(v_x_327_);
lean_dec(v_x_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(lean_object* v_as_329_, size_t v_i_330_, size_t v_stop_331_, lean_object* v_b_332_){
_start:
{
uint8_t v___x_333_; 
v___x_333_ = lean_usize_dec_eq(v_i_330_, v_stop_331_);
if (v___x_333_ == 0)
{
size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_334_ = ((size_t)1ULL);
v___x_335_ = lean_usize_sub(v_i_330_, v___x_334_);
v___x_336_ = lean_array_uget_borrowed(v_as_329_, v___x_335_);
v___x_337_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_b_332_, v___x_336_);
lean_dec(v_b_332_);
v_i_330_ = v___x_335_;
v_b_332_ = v___x_337_;
goto _start;
}
else
{
return v_b_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3___boxed(lean_object* v_as_339_, lean_object* v_i_340_, lean_object* v_stop_341_, lean_object* v_b_342_){
_start:
{
size_t v_i_boxed_343_; size_t v_stop_boxed_344_; lean_object* v_res_345_; 
v_i_boxed_343_ = lean_unbox_usize(v_i_340_);
lean_dec(v_i_340_);
v_stop_boxed_344_ = lean_unbox_usize(v_stop_341_);
lean_dec(v_stop_341_);
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_as_339_, v_i_boxed_343_, v_stop_boxed_344_, v_b_342_);
lean_dec_ref(v_as_339_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_manualLink_spec__1(lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
if (lean_obj_tag(v_a_347_) == 0)
{
lean_object* v___x_349_; 
v___x_349_ = l_List_reverse___redArg(v_a_348_);
return v___x_349_;
}
else
{
lean_object* v_head_350_; lean_object* v_tail_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_363_; 
v_head_350_ = lean_ctor_get(v_a_347_, 0);
v_tail_351_ = lean_ctor_get(v_a_347_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_a_347_);
if (v_isSharedCheck_363_ == 0)
{
v___x_353_ = v_a_347_;
v_isShared_354_ = v_isSharedCheck_363_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_tail_351_);
lean_inc(v_head_350_);
lean_dec(v_a_347_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_363_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v_fst_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v_fst_355_ = lean_ctor_get(v_head_350_, 0);
lean_inc(v_fst_355_);
lean_dec(v_head_350_);
v___x_356_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_manualLink_spec__1___closed__0));
v___x_357_ = lean_string_append(v___x_356_, v_fst_355_);
lean_dec(v_fst_355_);
v___x_358_ = lean_string_append(v___x_357_, v___x_356_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v_a_348_);
lean_ctor_set(v___x_353_, 0, v___x_358_);
v___x_360_ = v___x_353_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_a_348_);
v___x_360_ = v_reuseFailAlloc_362_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
v_a_347_ = v_tail_351_;
v_a_348_ = v___x_360_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_manualLink(lean_object* v_kind_369_, lean_object* v_name_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_372_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_371_, v_kind_369_);
if (lean_obj_tag(v___x_372_) == 1)
{
lean_object* v_val_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_387_; 
v_val_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_387_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_387_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_val_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_387_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_377_ = l_Lean_manualRoot;
v___x_378_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_379_ = lean_string_append(v___x_378_, v_val_373_);
lean_dec(v_val_373_);
v___x_380_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_381_ = lean_string_append(v___x_379_, v___x_380_);
v___x_382_ = lean_string_append(v___x_381_, v_name_370_);
v___x_383_ = lean_string_append(v___x_377_, v___x_382_);
lean_dec_ref(v___x_382_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_383_);
v___x_385_ = v___x_375_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
else
{
lean_object* v_buckets_388_; lean_object* v___x_389_; lean_object* v___y_391_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
lean_dec(v___x_372_);
v_buckets_388_ = lean_ctor_get(v___x_371_, 1);
v___x_389_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_401_ = lean_box(0);
v___x_402_ = lean_array_get_size(v_buckets_388_);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_nat_dec_lt(v___x_403_, v___x_402_);
if (v___x_404_ == 0)
{
v___y_391_ = v___x_401_;
goto v___jp_390_;
}
else
{
size_t v___x_405_; size_t v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_usize_of_nat(v___x_402_);
v___x_406_ = ((size_t)0ULL);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_388_, v___x_405_, v___x_406_, v___x_401_);
v___y_391_ = v___x_407_;
goto v___jp_390_;
}
v___jp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_acceptableKinds_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_392_ = lean_box(0);
v___x_393_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_391_, v___x_392_);
v_acceptableKinds_394_ = l_String_intercalate(v___x_389_, v___x_393_);
v___x_395_ = ((lean_object*)(l_Lean_manualLink___closed__3));
v___x_396_ = lean_string_append(v___x_395_, v_kind_369_);
v___x_397_ = ((lean_object*)(l_Lean_manualLink___closed__4));
v___x_398_ = lean_string_append(v___x_396_, v___x_397_);
v___x_399_ = lean_string_append(v___x_398_, v_acceptableKinds_394_);
lean_dec_ref(v_acceptableKinds_394_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_manualLink___boxed(lean_object* v_kind_408_, lean_object* v_name_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_manualLink(v_kind_408_, v_name_409_);
lean_dec_ref(v_name_409_);
lean_dec_ref(v_kind_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(lean_object* v_00_u03b2_411_, lean_object* v_m_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v_m_412_, v_a_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___boxed(lean_object* v_00_u03b2_415_, lean_object* v_m_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(v_00_u03b2_415_, v_m_416_, v_a_417_);
lean_dec_ref(v_a_417_);
lean_dec_ref(v_m_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(lean_object* v_00_u03b2_419_, lean_object* v_a_420_, lean_object* v_x_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_420_, v_x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___boxed(lean_object* v_00_u03b2_423_, lean_object* v_a_424_, lean_object* v_x_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(v_00_u03b2_423_, v_a_424_, v_x_425_);
lean_dec(v_x_425_);
lean_dec_ref(v_a_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg(){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg___closed__0));
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg___boxed(lean_object* v___dummy_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg();
return v_res_432_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0(void){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg();
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(lean_object* v_s_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___boxed(lean_object* v_s_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(v_s_436_);
lean_dec_ref(v_s_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(lean_object* v_path_438_, lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v_a_441_, lean_object* v_b_442_){
_start:
{
lean_object* v_it_444_; lean_object* v_startInclusive_445_; lean_object* v_endExclusive_446_; 
if (lean_obj_tag(v_a_441_) == 0)
{
lean_object* v_currPos_451_; lean_object* v_searcher_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_475_; 
v_currPos_451_ = lean_ctor_get(v_a_441_, 0);
v_searcher_452_ = lean_ctor_get(v_a_441_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_a_441_);
if (v_isSharedCheck_475_ == 0)
{
v___x_454_ = v_a_441_;
v_isShared_455_ = v_isSharedCheck_475_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_searcher_452_);
lean_inc(v_currPos_451_);
lean_dec(v_a_441_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_475_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
uint8_t v_decide_456_; 
v_decide_456_ = lean_nat_dec_eq(v_searcher_452_, v___x_440_);
if (v_decide_456_ == 0)
{
uint32_t v___x_457_; uint32_t v___x_458_; uint8_t v___x_459_; 
v___x_457_ = 47;
v___x_458_ = lean_string_utf8_get_fast(v_path_438_, v_searcher_452_);
v___x_459_ = lean_uint32_dec_eq(v___x_458_, v___x_457_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = lean_string_utf8_next_fast(v_path_438_, v_searcher_452_);
lean_dec(v_searcher_452_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_460_);
v___x_462_ = v___x_454_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_currPos_451_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_460_);
v___x_462_ = v_reuseFailAlloc_464_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
v_a_441_ = v___x_462_;
goto _start;
}
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_slice_468_; lean_object* v_nextIt_470_; 
v___x_465_ = lean_string_utf8_next_fast(v_path_438_, v_searcher_452_);
v___x_466_ = lean_nat_sub(v___x_465_, v_searcher_452_);
v___x_467_ = lean_nat_add(v_searcher_452_, v___x_466_);
lean_dec(v___x_466_);
v_slice_468_ = l_String_Slice_subslice_x21(v___x_439_, v_currPos_451_, v_searcher_452_);
lean_inc(v___x_467_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_467_);
lean_ctor_set(v___x_454_, 0, v___x_467_);
v_nextIt_470_ = v___x_454_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v___x_467_);
v_nextIt_470_ = v_reuseFailAlloc_473_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v_startInclusive_471_; lean_object* v_endExclusive_472_; 
v_startInclusive_471_ = lean_ctor_get(v_slice_468_, 0);
lean_inc(v_startInclusive_471_);
v_endExclusive_472_ = lean_ctor_get(v_slice_468_, 1);
lean_inc(v_endExclusive_472_);
lean_dec_ref(v_slice_468_);
v_it_444_ = v_nextIt_470_;
v_startInclusive_445_ = v_startInclusive_471_;
v_endExclusive_446_ = v_endExclusive_472_;
goto v___jp_443_;
}
}
}
else
{
lean_object* v___x_474_; 
lean_del_object(v___x_454_);
lean_dec(v_searcher_452_);
v___x_474_ = lean_box(1);
lean_inc(v___x_440_);
v_it_444_ = v___x_474_;
v_startInclusive_445_ = v_currPos_451_;
v_endExclusive_446_ = v___x_440_;
goto v___jp_443_;
}
}
}
else
{
lean_dec(v___x_440_);
lean_dec_ref(v_path_438_);
return v_b_442_;
}
v___jp_443_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
lean_inc_ref(v_path_438_);
v___x_447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_447_, 0, v_path_438_);
lean_ctor_set(v___x_447_, 1, v_startInclusive_445_);
lean_ctor_set(v___x_447_, 2, v_endExclusive_446_);
v___x_448_ = l_String_Slice_toString(v___x_447_);
lean_dec_ref_known(v___x_447_, 3);
v___x_449_ = lean_array_push(v_b_442_, v___x_448_);
v_a_441_ = v_it_444_;
v_b_442_ = v___x_449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg___boxed(lean_object* v_path_476_, lean_object* v___x_477_, lean_object* v___x_478_, lean_object* v_a_479_, lean_object* v_b_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_476_, v___x_477_, v___x_478_, v_a_479_, v_b_480_);
lean_dec_ref(v___x_477_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
return v_x_482_;
}
else
{
lean_object* v_head_484_; lean_object* v_tail_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_head_484_ = lean_ctor_get(v_x_483_, 0);
v_tail_485_ = lean_ctor_get(v_x_483_, 1);
v___x_486_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_487_ = lean_string_append(v_x_482_, v___x_486_);
v___x_488_ = lean_string_append(v___x_487_, v_head_484_);
v_x_482_ = v___x_488_;
v_x_483_ = v_tail_485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0___boxed(lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v_x_490_, v_x_491_);
lean_dec(v_x_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(lean_object* v_x_496_){
_start:
{
if (lean_obj_tag(v_x_496_) == 0)
{
lean_object* v___x_497_; 
v___x_497_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0));
return v___x_497_;
}
else
{
lean_object* v_tail_498_; 
v_tail_498_ = lean_ctor_get(v_x_496_, 1);
if (lean_obj_tag(v_tail_498_) == 0)
{
lean_object* v_head_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_head_499_ = lean_ctor_get(v_x_496_, 0);
v___x_500_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_501_ = lean_string_append(v___x_500_, v_head_499_);
v___x_502_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2));
v___x_503_ = lean_string_append(v___x_501_, v___x_502_);
return v___x_503_;
}
else
{
lean_object* v_head_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint32_t v___x_508_; lean_object* v___x_509_; 
v_head_504_ = lean_ctor_get(v_x_496_, 0);
v___x_505_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_506_ = lean_string_append(v___x_505_, v_head_504_);
v___x_507_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v___x_506_, v_tail_498_);
v___x_508_ = 93;
v___x_509_ = lean_string_push(v___x_507_, v___x_508_);
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___boxed(lean_object* v_x_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v_x_510_);
lean_dec(v_x_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rw(lean_object* v_path_522_){
_start:
{
lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_string_utf8_byte_size(v_path_522_);
lean_inc_ref(v_path_522_);
v___x_550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_550_, 0, v_path_522_);
lean_ctor_set(v___x_550_, 1, v___x_548_);
lean_ctor_set(v___x_550_, 2, v___x_549_);
v___x_551_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0);
v___x_552_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__4));
v___x_553_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_522_, v___x_550_, v___x_549_, v___x_551_, v___x_552_);
lean_dec_ref_known(v___x_550_, 3);
v___x_554_ = lean_array_to_list(v___x_553_);
if (lean_obj_tag(v___x_554_) == 0)
{
goto v___jp_546_;
}
else
{
lean_object* v_head_555_; lean_object* v_tail_556_; lean_object* v_kind_558_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_head_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_head_555_);
v_tail_556_ = lean_ctor_get(v___x_554_, 1);
lean_inc(v_tail_556_);
lean_dec_ref_known(v___x_554_, 2);
v___x_593_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_594_ = lean_string_dec_eq(v_head_555_, v___x_593_);
if (v___x_594_ == 0)
{
v_kind_558_ = v_head_555_;
goto v___jp_557_;
}
else
{
lean_dec(v_head_555_);
if (lean_obj_tag(v_tail_556_) == 0)
{
goto v___jp_546_;
}
else
{
v_kind_558_ = v___x_593_;
goto v___jp_557_;
}
}
v___jp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_559_, v_kind_558_);
if (lean_obj_tag(v___x_560_) == 1)
{
if (lean_obj_tag(v_tail_556_) == 1)
{
lean_object* v_tail_561_; 
v_tail_561_ = lean_ctor_get(v_tail_556_, 1);
if (lean_obj_tag(v_tail_561_) == 0)
{
lean_object* v_val_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_584_; 
v_val_562_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_584_ == 0)
{
v___x_564_ = v___x_560_;
v_isShared_565_ = v_isSharedCheck_584_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_val_562_);
lean_dec(v___x_560_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_584_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_head_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_head_566_ = lean_ctor_get(v_tail_556_, 0);
lean_inc(v_head_566_);
lean_dec_ref_known(v_tail_556_, 2);
v___x_567_ = lean_string_utf8_byte_size(v_head_566_);
v___x_568_ = lean_nat_dec_eq(v___x_567_, v___x_548_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
lean_dec_ref(v_kind_558_);
v___x_569_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_570_ = lean_string_append(v___x_569_, v_val_562_);
lean_dec(v_val_562_);
v___x_571_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_572_ = lean_string_append(v___x_570_, v___x_571_);
v___x_573_ = lean_string_append(v___x_572_, v_head_566_);
lean_dec(v_head_566_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_573_);
v___x_575_ = v___x_564_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
lean_dec(v_head_566_);
lean_dec(v_val_562_);
v___x_577_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__5));
v___x_578_ = lean_string_append(v___x_577_, v_kind_558_);
lean_dec_ref(v_kind_558_);
v___x_579_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__6));
v___x_580_ = lean_string_append(v___x_578_, v___x_579_);
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 0);
lean_ctor_set(v___x_564_, 0, v___x_580_);
v___x_582_ = v___x_564_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_560_, 1);
v___y_537_ = v_tail_556_;
v___y_538_ = v_kind_558_;
goto v___jp_536_;
}
}
else
{
lean_dec_ref_known(v___x_560_, 1);
v___y_537_ = v_tail_556_;
v___y_538_ = v_kind_558_;
goto v___jp_536_;
}
}
else
{
lean_object* v_buckets_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
lean_dec(v___x_560_);
lean_dec(v_tail_556_);
v_buckets_585_ = lean_ctor_get(v___x_559_, 1);
v___x_586_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_587_ = lean_box(0);
v___x_588_ = lean_array_get_size(v_buckets_585_);
v___x_589_ = lean_nat_dec_lt(v___x_548_, v___x_588_);
if (v___x_589_ == 0)
{
v___y_524_ = v_kind_558_;
v___y_525_ = v___x_586_;
v___y_526_ = v___x_587_;
goto v___jp_523_;
}
else
{
size_t v___x_590_; size_t v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_usize_of_nat(v___x_588_);
v___x_591_ = ((size_t)0ULL);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_585_, v___x_590_, v___x_591_, v___x_587_);
v___y_524_ = v_kind_558_;
v___y_525_ = v___x_586_;
v___y_526_ = v___x_592_;
goto v___jp_523_;
}
}
}
}
v___jp_523_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_acceptableKinds_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_527_ = lean_box(0);
v___x_528_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_526_, v___x_527_);
v_acceptableKinds_529_ = l_String_intercalate(v___y_525_, v___x_528_);
v___x_530_ = ((lean_object*)(l_Lean_manualLink___closed__3));
v___x_531_ = lean_string_append(v___x_530_, v___y_524_);
lean_dec_ref(v___y_524_);
v___x_532_ = ((lean_object*)(l_Lean_manualLink___closed__4));
v___x_533_ = lean_string_append(v___x_531_, v___x_532_);
v___x_534_ = lean_string_append(v___x_533_, v_acceptableKinds_529_);
lean_dec_ref(v_acceptableKinds_529_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
v___jp_536_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_539_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__0));
v___x_540_ = lean_string_append(v___x_539_, v___y_538_);
lean_dec_ref(v___y_538_);
v___x_541_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__1));
v___x_542_ = lean_string_append(v___x_540_, v___x_541_);
v___x_543_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v___y_537_);
lean_dec(v___y_537_);
v___x_544_ = lean_string_append(v___x_542_, v___x_543_);
lean_dec_ref(v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
v___jp_546_:
{
lean_object* v___x_547_; 
v___x_547_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__3));
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(lean_object* v_path_595_, lean_object* v___x_596_, lean_object* v___x_597_, lean_object* v_inst_598_, lean_object* v_R_599_, lean_object* v_a_600_, lean_object* v_b_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_595_, v___x_596_, v___x_597_, v_a_600_, v_b_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___boxed(lean_object* v_path_603_, lean_object* v___x_604_, lean_object* v___x_605_, lean_object* v_inst_606_, lean_object* v_R_607_, lean_object* v_a_608_, lean_object* v_b_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(v_path_603_, v___x_604_, v___x_605_, v_inst_606_, v_R_607_, v_a_608_, v_b_609_);
lean_dec_ref(v___x_604_);
return v_res_610_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(uint32_t v_c_611_){
_start:
{
uint32_t v___x_663_; uint8_t v___x_664_; 
v___x_663_ = 65;
v___x_664_ = lean_uint32_dec_le(v___x_663_, v_c_611_);
if (v___x_664_ == 0)
{
goto v___jp_658_;
}
else
{
uint32_t v___x_665_; uint8_t v___x_666_; 
v___x_665_ = 90;
v___x_666_ = lean_uint32_dec_le(v_c_611_, v___x_665_);
if (v___x_666_ == 0)
{
goto v___jp_658_;
}
else
{
return v___x_666_;
}
}
v___jp_612_:
{
uint32_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = 45;
v___x_614_ = lean_uint32_dec_eq(v_c_611_, v___x_613_);
if (v___x_614_ == 0)
{
uint32_t v___x_615_; uint8_t v___x_616_; 
v___x_615_ = 46;
v___x_616_ = lean_uint32_dec_eq(v_c_611_, v___x_615_);
if (v___x_616_ == 0)
{
uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 95;
v___x_618_ = lean_uint32_dec_eq(v_c_611_, v___x_617_);
if (v___x_618_ == 0)
{
uint32_t v___x_619_; uint8_t v___x_620_; 
v___x_619_ = 126;
v___x_620_ = lean_uint32_dec_eq(v_c_611_, v___x_619_);
if (v___x_620_ == 0)
{
uint32_t v___x_621_; uint8_t v___x_622_; 
v___x_621_ = 58;
v___x_622_ = lean_uint32_dec_eq(v_c_611_, v___x_621_);
if (v___x_622_ == 0)
{
uint32_t v___x_623_; uint8_t v___x_624_; 
v___x_623_ = 47;
v___x_624_ = lean_uint32_dec_eq(v_c_611_, v___x_623_);
if (v___x_624_ == 0)
{
uint32_t v___x_625_; uint8_t v___x_626_; 
v___x_625_ = 63;
v___x_626_ = lean_uint32_dec_eq(v_c_611_, v___x_625_);
if (v___x_626_ == 0)
{
uint32_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = 35;
v___x_628_ = lean_uint32_dec_eq(v_c_611_, v___x_627_);
if (v___x_628_ == 0)
{
uint32_t v___x_629_; uint8_t v___x_630_; 
v___x_629_ = 91;
v___x_630_ = lean_uint32_dec_eq(v_c_611_, v___x_629_);
if (v___x_630_ == 0)
{
uint32_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 93;
v___x_632_ = lean_uint32_dec_eq(v_c_611_, v___x_631_);
if (v___x_632_ == 0)
{
uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 64;
v___x_634_ = lean_uint32_dec_eq(v_c_611_, v___x_633_);
if (v___x_634_ == 0)
{
uint32_t v___x_635_; uint8_t v___x_636_; 
v___x_635_ = 33;
v___x_636_ = lean_uint32_dec_eq(v_c_611_, v___x_635_);
if (v___x_636_ == 0)
{
uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = 36;
v___x_638_ = lean_uint32_dec_eq(v_c_611_, v___x_637_);
if (v___x_638_ == 0)
{
uint32_t v___x_639_; uint8_t v___x_640_; 
v___x_639_ = 38;
v___x_640_ = lean_uint32_dec_eq(v_c_611_, v___x_639_);
if (v___x_640_ == 0)
{
uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = 39;
v___x_642_ = lean_uint32_dec_eq(v_c_611_, v___x_641_);
if (v___x_642_ == 0)
{
uint32_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = 42;
v___x_644_ = lean_uint32_dec_eq(v_c_611_, v___x_643_);
if (v___x_644_ == 0)
{
uint32_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = 43;
v___x_646_ = lean_uint32_dec_eq(v_c_611_, v___x_645_);
if (v___x_646_ == 0)
{
uint32_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = 44;
v___x_648_ = lean_uint32_dec_eq(v_c_611_, v___x_647_);
if (v___x_648_ == 0)
{
uint32_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = 59;
v___x_650_ = lean_uint32_dec_eq(v_c_611_, v___x_649_);
if (v___x_650_ == 0)
{
uint32_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = 61;
v___x_652_ = lean_uint32_dec_eq(v_c_611_, v___x_651_);
return v___x_652_;
}
else
{
return v___x_650_;
}
}
else
{
return v___x_648_;
}
}
else
{
return v___x_646_;
}
}
else
{
return v___x_644_;
}
}
else
{
return v___x_642_;
}
}
else
{
return v___x_640_;
}
}
else
{
return v___x_638_;
}
}
else
{
return v___x_636_;
}
}
else
{
return v___x_634_;
}
}
else
{
return v___x_632_;
}
}
else
{
return v___x_630_;
}
}
else
{
return v___x_628_;
}
}
else
{
return v___x_626_;
}
}
else
{
return v___x_624_;
}
}
else
{
return v___x_622_;
}
}
else
{
return v___x_620_;
}
}
else
{
return v___x_618_;
}
}
else
{
return v___x_616_;
}
}
else
{
return v___x_614_;
}
}
v___jp_653_:
{
uint32_t v___x_654_; uint8_t v___x_655_; 
v___x_654_ = 48;
v___x_655_ = lean_uint32_dec_le(v___x_654_, v_c_611_);
if (v___x_655_ == 0)
{
goto v___jp_612_;
}
else
{
uint32_t v___x_656_; uint8_t v___x_657_; 
v___x_656_ = 57;
v___x_657_ = lean_uint32_dec_le(v_c_611_, v___x_656_);
if (v___x_657_ == 0)
{
goto v___jp_612_;
}
else
{
return v___x_657_;
}
}
}
v___jp_658_:
{
uint32_t v___x_659_; uint8_t v___x_660_; 
v___x_659_ = 97;
v___x_660_ = lean_uint32_dec_le(v___x_659_, v_c_611_);
if (v___x_660_ == 0)
{
goto v___jp_653_;
}
else
{
uint32_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 122;
v___x_662_ = lean_uint32_dec_le(v_c_611_, v___x_661_);
if (v___x_662_ == 0)
{
goto v___jp_653_;
}
else
{
return v___x_662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar___boxed(lean_object* v_c_667_){
_start:
{
uint32_t v_c_boxed_668_; uint8_t v_res_669_; lean_object* v_r_670_; 
v_c_boxed_668_ = lean_unbox_uint32(v_c_667_);
lean_dec(v_c_667_);
v_res_669_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v_c_boxed_668_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(lean_object* v_s_671_, lean_object* v___x_672_, lean_object* v___x_673_, uint32_t v___x_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_snd_676_; lean_object* v_snd_677_; lean_object* v_fst_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_746_; 
v_snd_676_ = lean_ctor_get(v_a_675_, 1);
lean_inc(v_snd_676_);
v_snd_677_ = lean_ctor_get(v_snd_676_, 1);
lean_inc(v_snd_677_);
v_fst_678_ = lean_ctor_get(v_a_675_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v_a_675_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v_a_675_, 1);
lean_dec(v_unused_747_);
v___x_680_ = v_a_675_;
v_isShared_681_ = v_isSharedCheck_746_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_fst_678_);
lean_dec(v_a_675_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_746_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_fst_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_744_; 
v_fst_682_ = lean_ctor_get(v_snd_676_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_snd_676_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_snd_676_, 1);
lean_dec(v_unused_745_);
v___x_684_ = v_snd_676_;
v_isShared_685_ = v_isSharedCheck_744_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_fst_682_);
lean_dec(v_snd_676_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_744_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v_fst_686_; lean_object* v_snd_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_743_; 
v_fst_686_ = lean_ctor_get(v_snd_677_, 0);
v_snd_687_ = lean_ctor_get(v_snd_677_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_snd_677_);
if (v_isSharedCheck_743_ == 0)
{
v___x_689_ = v_snd_677_;
v_isShared_690_ = v_isSharedCheck_743_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_snd_687_);
lean_inc(v_fst_686_);
lean_dec(v_snd_677_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_743_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; uint8_t v_decide_692_; 
v___x_691_ = lean_string_utf8_byte_size(v_s_671_);
v_decide_692_ = lean_nat_dec_eq(v_snd_687_, v___x_691_);
if (v_decide_692_ == 0)
{
uint32_t v___x_693_; lean_object* v___x_694_; uint8_t v___y_727_; uint8_t v___x_732_; 
v___x_693_ = lean_string_utf8_get_fast(v_s_671_, v_snd_687_);
v___x_694_ = lean_string_utf8_next_fast(v_s_671_, v_snd_687_);
v___x_732_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v___x_693_);
if (v___x_732_ == 0)
{
v___y_727_ = v___x_732_;
goto v___jp_726_;
}
else
{
uint8_t v_decide_733_; 
v_decide_733_ = lean_nat_dec_eq(v___x_694_, v___x_691_);
if (v_decide_733_ == 0)
{
v___y_727_ = v___x_732_;
goto v___jp_726_;
}
else
{
goto v___jp_695_;
}
}
v___jp_695_:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_string_utf8_extract_fast(v_s_671_, v___x_672_, v_snd_687_);
v___x_697_ = l___private_Lean_DocString_Links_0__Lean_rw(v___x_696_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_673_);
lean_ctor_set(v___x_699_, 1, v_snd_687_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v_a_698_);
lean_ctor_set(v___x_689_, 0, v___x_699_);
v___x_701_ = v___x_689_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_a_698_);
v___x_701_ = v_reuseFailAlloc_711_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_702_ = lean_array_push(v_fst_682_, v___x_701_);
v___x_703_ = lean_string_push(v_fst_678_, v___x_674_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_694_);
lean_ctor_set(v___x_684_, 0, v_fst_686_);
v___x_705_ = v___x_684_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_fst_686_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_694_);
v___x_705_ = v_reuseFailAlloc_710_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_707_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_705_);
lean_ctor_set(v___x_680_, 0, v___x_702_);
v___x_707_ = v___x_680_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_705_);
v___x_707_ = v_reuseFailAlloc_709_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; 
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_703_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
return v___x_708_;
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
lean_dec(v_snd_687_);
lean_dec(v_fst_686_);
lean_dec(v___x_673_);
v_a_712_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_697_, 1);
v___x_713_ = l_Lean_manualRoot;
v___x_714_ = lean_string_append(v_fst_678_, v___x_713_);
v___x_715_ = lean_string_append(v___x_714_, v_a_712_);
lean_dec(v_a_712_);
v___x_716_ = lean_string_push(v___x_715_, v___x_693_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_694_);
lean_ctor_set(v___x_689_, 0, v___x_694_);
v___x_718_ = v___x_689_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_694_);
v___x_718_ = v_reuseFailAlloc_725_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_718_);
v___x_720_ = v___x_684_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_fst_682_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_724_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_720_);
lean_ctor_set(v___x_680_, 0, v___x_716_);
v___x_722_ = v___x_680_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
v___jp_726_:
{
if (v___y_727_ == 0)
{
goto v___jp_695_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_del_object(v___x_689_);
lean_dec(v_snd_687_);
lean_del_object(v___x_684_);
lean_del_object(v___x_680_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v_fst_686_);
lean_ctor_set(v___x_728_, 1, v___x_694_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v_fst_682_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v_fst_678_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v_a_675_ = v___x_730_;
goto _start;
}
}
}
else
{
lean_object* v___x_735_; 
lean_dec(v___x_673_);
if (v_isShared_690_ == 0)
{
v___x_735_ = v___x_689_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_fst_686_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_snd_687_);
v___x_735_ = v_reuseFailAlloc_742_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_735_);
v___x_737_ = v___x_684_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_fst_682_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_741_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_739_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_737_);
v___x_739_ = v___x_680_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_fst_678_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg___boxed(lean_object* v_s_748_, lean_object* v___x_749_, lean_object* v___x_750_, lean_object* v___x_751_, lean_object* v_a_752_){
_start:
{
uint32_t v___x_2315__boxed_753_; lean_object* v_res_754_; 
v___x_2315__boxed_753_ = lean_unbox_uint32(v___x_751_);
lean_dec(v___x_751_);
v_res_754_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_748_, v___x_749_, v___x_750_, v___x_2315__boxed_753_, v_a_752_);
lean_dec(v___x_749_);
lean_dec_ref(v_s_748_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(lean_object* v_s_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_snd_758_; lean_object* v_fst_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_823_; 
v_snd_758_ = lean_ctor_get(v_a_757_, 1);
v_fst_759_ = lean_ctor_get(v_a_757_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_a_757_);
if (v_isSharedCheck_823_ == 0)
{
v___x_761_ = v_a_757_;
v_isShared_762_ = v_isSharedCheck_823_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_snd_758_);
lean_inc(v_fst_759_);
lean_dec(v_a_757_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_823_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_fst_763_; lean_object* v_snd_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_822_; 
v_fst_763_ = lean_ctor_get(v_snd_758_, 0);
v_snd_764_ = lean_ctor_get(v_snd_758_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_snd_758_);
if (v_isSharedCheck_822_ == 0)
{
v___x_766_ = v_snd_758_;
v_isShared_767_ = v_isSharedCheck_822_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_snd_764_);
lean_inc(v_fst_763_);
lean_dec(v_snd_758_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_822_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; uint8_t v_decide_769_; 
v___x_768_ = lean_string_utf8_byte_size(v_s_756_);
v_decide_769_ = lean_nat_dec_eq(v_snd_764_, v___x_768_);
if (v_decide_769_ == 0)
{
uint32_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_770_ = lean_string_utf8_get_fast(v_s_756_, v_snd_764_);
v___x_771_ = lean_string_utf8_next_fast(v_s_756_, v_snd_764_);
v___x_781_ = lean_unsigned_to_nat(14u);
v___x_782_ = lean_nat_sub(v___x_768_, v_snd_764_);
v___x_783_ = lean_nat_dec_le(v___x_781_, v___x_782_);
lean_dec(v___x_782_);
if (v___x_783_ == 0)
{
lean_dec(v_snd_764_);
goto v___jp_772_;
}
else
{
lean_object* v_scheme_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v_scheme_784_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0));
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = lean_string_memcmp(v_s_756_, v_scheme_784_, v_snd_764_, v___x_785_, v___x_781_);
if (v___x_786_ == 0)
{
lean_dec(v_snd_764_);
goto v___jp_772_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v_snd_794_; lean_object* v_snd_795_; lean_object* v_fst_796_; lean_object* v_fst_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_814_; 
lean_del_object(v___x_766_);
lean_del_object(v___x_761_);
lean_inc(v_snd_764_);
lean_inc_ref(v_s_756_);
v___x_787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_787_, 0, v_s_756_);
lean_ctor_set(v___x_787_, 1, v_snd_764_);
lean_ctor_set(v___x_787_, 2, v___x_768_);
v___x_788_ = l_String_Slice_pos_x21(v___x_787_, v___x_781_);
lean_dec_ref_known(v___x_787_, 3);
v___x_789_ = lean_nat_add(v_snd_764_, v___x_788_);
lean_dec(v___x_788_);
lean_inc(v___x_789_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_771_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_fst_763_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v_fst_759_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_756_, v___x_789_, v_snd_764_, v___x_770_, v___x_792_);
lean_dec(v___x_789_);
v_snd_794_ = lean_ctor_get(v___x_793_, 1);
lean_inc(v_snd_794_);
v_snd_795_ = lean_ctor_get(v_snd_794_, 1);
lean_inc(v_snd_795_);
v_fst_796_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_fst_796_);
lean_dec_ref(v___x_793_);
v_fst_797_ = lean_ctor_get(v_snd_794_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_snd_794_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v_snd_794_, 1);
lean_dec(v_unused_815_);
v___x_799_ = v_snd_794_;
v_isShared_800_ = v_isSharedCheck_814_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_fst_797_);
lean_dec(v_snd_794_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_814_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_fst_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_812_; 
v_fst_801_ = lean_ctor_get(v_snd_795_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v_snd_795_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v_snd_795_, 1);
lean_dec(v_unused_813_);
v___x_803_ = v_snd_795_;
v_isShared_804_ = v_isSharedCheck_812_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_fst_801_);
lean_dec(v_snd_795_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_812_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v_fst_801_);
lean_ctor_set(v___x_803_, 0, v_fst_797_);
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_fst_797_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_fst_801_);
v___x_806_ = v_reuseFailAlloc_811_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v___x_806_);
lean_ctor_set(v___x_799_, 0, v_fst_796_);
v___x_808_ = v___x_799_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_fst_796_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_806_);
v___x_808_ = v_reuseFailAlloc_810_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
v_a_757_ = v___x_808_;
goto _start;
}
}
}
}
}
}
v___jp_772_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = lean_string_push(v_fst_759_, v___x_770_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v___x_771_);
v___x_775_ = v___x_766_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_fst_763_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_771_);
v___x_775_ = v_reuseFailAlloc_780_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___x_775_);
lean_ctor_set(v___x_761_, 0, v___x_773_);
v___x_777_ = v___x_761_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_775_);
v___x_777_ = v_reuseFailAlloc_779_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
v_a_757_ = v___x_777_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_817_; 
lean_dec_ref(v_s_756_);
if (v_isShared_767_ == 0)
{
v___x_817_ = v___x_766_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_fst_763_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_snd_764_);
v___x_817_ = v_reuseFailAlloc_821_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___x_817_);
v___x_819_ = v___x_761_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_fst_759_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore(lean_object* v_s_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_snd_835_; lean_object* v_fst_836_; lean_object* v_fst_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
v___x_833_ = ((lean_object*)(l_Lean_rewriteManualLinksCore___closed__2));
v___x_834_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(v_s_832_, v___x_833_);
v_snd_835_ = lean_ctor_get(v___x_834_, 1);
lean_inc(v_snd_835_);
v_fst_836_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_fst_836_);
lean_dec_ref(v___x_834_);
v_fst_837_ = lean_ctor_get(v_snd_835_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v_snd_835_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v_snd_835_, 1);
lean_dec(v_unused_845_);
v___x_839_ = v_snd_835_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_fst_837_);
lean_dec(v_snd_835_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v_fst_836_);
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_fst_837_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_fst_836_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0(lean_object* v_s_846_, lean_object* v___x_847_, lean_object* v___x_848_, uint32_t v___x_849_, lean_object* v_inst_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_846_, v___x_847_, v___x_848_, v___x_849_, v_a_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___boxed(lean_object* v_s_853_, lean_object* v___x_854_, lean_object* v___x_855_, lean_object* v___x_856_, lean_object* v_inst_857_, lean_object* v_a_858_){
_start:
{
uint32_t v___x_2597__boxed_859_; lean_object* v_res_860_; 
v___x_2597__boxed_859_ = lean_unbox_uint32(v___x_856_);
lean_dec(v___x_856_);
v_res_860_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0(v_s_853_, v___x_854_, v___x_855_, v___x_2597__boxed_859_, v_inst_857_, v_a_858_);
lean_dec(v___x_854_);
lean_dec_ref(v_s_853_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1(lean_object* v_s_861_, lean_object* v_inst_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(v_s_861_, v_a_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(lean_object* v_docString_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
if (lean_obj_tag(v_a_869_) == 0)
{
lean_object* v___x_871_; 
v___x_871_ = l_List_reverse___redArg(v_a_870_);
return v___x_871_;
}
else
{
lean_object* v_head_872_; lean_object* v_fst_873_; lean_object* v_tail_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_893_; 
v_head_872_ = lean_ctor_get(v_a_869_, 0);
lean_inc(v_head_872_);
v_fst_873_ = lean_ctor_get(v_head_872_, 0);
lean_inc(v_fst_873_);
v_tail_874_ = lean_ctor_get(v_a_869_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v_a_869_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v_a_869_, 0);
lean_dec(v_unused_894_);
v___x_876_ = v_a_869_;
v_isShared_877_ = v_isSharedCheck_893_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_tail_874_);
lean_dec(v_a_869_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_893_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v_snd_878_; lean_object* v_start_879_; lean_object* v_stop_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v_snd_878_ = lean_ctor_get(v_head_872_, 1);
lean_inc(v_snd_878_);
lean_dec(v_head_872_);
v_start_879_ = lean_ctor_get(v_fst_873_, 0);
lean_inc(v_start_879_);
v_stop_880_ = lean_ctor_get(v_fst_873_, 1);
lean_inc(v_stop_880_);
lean_dec(v_fst_873_);
v___x_881_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0));
v___x_882_ = lean_string_utf8_extract(v_docString_868_, v_start_879_, v_stop_880_);
lean_dec(v_stop_880_);
lean_dec(v_start_879_);
v___x_883_ = lean_string_append(v___x_881_, v___x_882_);
lean_dec_ref(v___x_882_);
v___x_884_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1));
v___x_885_ = lean_string_append(v___x_883_, v___x_884_);
v___x_886_ = lean_string_append(v___x_885_, v_snd_878_);
lean_dec(v_snd_878_);
v___x_887_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_888_ = lean_string_append(v___x_886_, v___x_887_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v_a_870_);
lean_ctor_set(v___x_876_, 0, v___x_888_);
v___x_890_ = v___x_876_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_a_870_);
v___x_890_ = v_reuseFailAlloc_892_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
v_a_869_ = v_tail_874_;
v_a_870_ = v___x_890_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___boxed(lean_object* v_docString_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_895_, v_a_896_, v_a_897_);
lean_dec_ref(v_docString_895_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
if (lean_obj_tag(v_x_900_) == 0)
{
return v_x_899_;
}
else
{
lean_object* v_head_901_; lean_object* v_tail_902_; lean_object* v___x_903_; 
v_head_901_ = lean_ctor_get(v_x_900_, 0);
v_tail_902_ = lean_ctor_get(v_x_900_, 1);
v___x_903_ = lean_string_append(v_x_899_, v_head_901_);
v_x_899_ = v___x_903_;
v_x_900_ = v_tail_902_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1___boxed(lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v_x_905_, v_x_906_);
lean_dec(v_x_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks(lean_object* v_docString_909_){
_start:
{
lean_object* v___x_911_; lean_object* v_fst_912_; lean_object* v_snd_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
lean_inc_ref(v_docString_909_);
v___x_911_ = l_Lean_rewriteManualLinksCore(v_docString_909_);
v_fst_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_fst_912_);
v_snd_913_ = lean_ctor_get(v___x_911_, 1);
lean_inc(v_snd_913_);
lean_dec_ref(v___x_911_);
v___x_914_ = lean_array_get_size(v_fst_912_);
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = lean_nat_dec_eq(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_917_ = ((lean_object*)(l_Lean_rewriteManualLinks___closed__0));
v___x_918_ = lean_array_to_list(v_fst_912_);
v___x_919_ = lean_box(0);
v___x_920_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_909_, v___x_918_, v___x_919_);
lean_dec_ref(v_docString_909_);
v___x_921_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_922_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_921_, v___x_920_);
lean_dec(v___x_920_);
v___x_923_ = lean_string_append(v___x_917_, v___x_922_);
lean_dec_ref(v___x_922_);
v___x_924_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_925_ = lean_string_append(v_snd_913_, v___x_924_);
v___x_926_ = lean_string_append(v___x_925_, v___x_923_);
lean_dec_ref(v___x_923_);
return v___x_926_;
}
else
{
lean_dec(v_fst_912_);
lean_dec_ref(v_docString_909_);
return v_snd_913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks___boxed(lean_object* v_docString_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_rewriteManualLinks(v_docString_927_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(lean_object* v_docString_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
if (lean_obj_tag(v_a_934_) == 0)
{
lean_object* v___x_936_; 
v___x_936_ = l_List_reverse___redArg(v_a_935_);
return v___x_936_;
}
else
{
lean_object* v_head_937_; lean_object* v_fst_938_; lean_object* v_tail_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_963_; 
v_head_937_ = lean_ctor_get(v_a_934_, 0);
lean_inc(v_head_937_);
v_fst_938_ = lean_ctor_get(v_head_937_, 0);
lean_inc(v_fst_938_);
v_tail_939_ = lean_ctor_get(v_a_934_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v_a_934_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v_a_934_, 0);
lean_dec(v_unused_964_);
v___x_941_ = v_a_934_;
v_isShared_942_ = v_isSharedCheck_963_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_tail_939_);
lean_dec(v_a_934_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_963_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_snd_943_; lean_object* v_start_944_; lean_object* v_stop_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
v_snd_943_ = lean_ctor_get(v_head_937_, 1);
lean_inc(v_snd_943_);
lean_dec(v_head_937_);
v_start_944_ = lean_ctor_get(v_fst_938_, 0);
lean_inc(v_start_944_);
v_stop_945_ = lean_ctor_get(v_fst_938_, 1);
lean_inc(v_stop_945_);
lean_dec(v_fst_938_);
v___x_946_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0));
v___x_947_ = lean_string_utf8_extract(v_docString_933_, v_start_944_, v_stop_945_);
lean_dec(v_stop_945_);
lean_dec(v_start_944_);
v___x_948_ = l_String_quote(v___x_947_);
v___x_949_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
v___x_950_ = l_Std_Format_defWidth;
v___x_951_ = lean_unsigned_to_nat(0u);
v___x_952_ = l_Std_Format_pretty(v___x_949_, v___x_950_, v___x_951_, v___x_951_);
v___x_953_ = lean_string_append(v___x_946_, v___x_952_);
lean_dec_ref(v___x_952_);
v___x_954_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1));
v___x_955_ = lean_string_append(v___x_953_, v___x_954_);
v___x_956_ = lean_string_append(v___x_955_, v_snd_943_);
lean_dec(v_snd_943_);
v___x_957_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2));
v___x_958_ = lean_string_append(v___x_956_, v___x_957_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v_a_935_);
lean_ctor_set(v___x_941_, 0, v___x_958_);
v___x_960_ = v___x_941_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_a_935_);
v___x_960_ = v_reuseFailAlloc_962_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
v_a_934_ = v_tail_939_;
v_a_935_ = v___x_960_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___boxed(lean_object* v_docString_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_965_, v_a_966_, v_a_967_);
lean_dec_ref(v_docString_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString(lean_object* v_docString_970_){
_start:
{
lean_object* v___x_972_; lean_object* v_fst_973_; lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
lean_inc_ref(v_docString_970_);
v___x_972_ = l_Lean_rewriteManualLinksCore(v_docString_970_);
v_fst_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_fst_973_);
lean_dec_ref(v___x_972_);
v___x_974_ = lean_array_get_size(v_fst_973_);
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = lean_nat_dec_eq(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_977_ = ((lean_object*)(l_Lean_validateBuiltinDocString___closed__0));
v___x_978_ = lean_array_to_list(v_fst_973_);
v___x_979_ = lean_box(0);
v___x_980_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_970_, v___x_978_, v___x_979_);
lean_dec_ref(v_docString_970_);
v___x_981_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_982_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_981_, v___x_980_);
lean_dec(v___x_980_);
v___x_983_ = lean_string_append(v___x_977_, v___x_982_);
lean_dec_ref(v___x_982_);
v___x_984_ = lean_mk_io_user_error(v___x_983_);
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec(v_fst_973_);
lean_dec_ref(v_docString_970_);
v___x_986_ = lean_box(0);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString___boxed(lean_object* v_docString_988_, lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_validateBuiltinDocString(v_docString_988_);
return v_res_990_;
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
