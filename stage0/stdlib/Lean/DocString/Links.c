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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "LEAN_MANUAL_ROOT"};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_;
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0_value;
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
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1;
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
v___x_8_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_));
v___x_9_ = lean_string_utf8_byte_size(v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_box(0);
v___x_11_ = lean_manual_get_root(v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
v___x_13_ = lean_string_utf8_byte_size(v___x_12_);
return v___x_13_;
}
}
static uint8_t _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
v___x_16_ = lean_nat_dec_eq(v___x_15_, v___x_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_(){
_start:
{
lean_object* v___y_19_; lean_object* v___y_20_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_r_26_; 
v___x_23_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_));
v___x_24_ = lean_io_getenv(v___x_23_);
if (lean_obj_tag(v___x_24_) == 1)
{
lean_object* v_val_35_; 
v_val_35_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_val_35_);
lean_dec_ref_known(v___x_24_, 1);
v_r_26_ = v_val_35_;
goto v___jp_25_;
}
else
{
lean_object* v___x_36_; uint8_t v___x_37_; 
lean_dec(v___x_24_);
v___x_36_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
v___x_37_ = lean_uint8_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
if (v___x_37_ == 0)
{
v_r_26_ = v___x_36_;
goto v___jp_25_;
}
else
{
lean_object* v___x_38_; 
v___x_38_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot___closed__0));
v_r_26_ = v___x_38_;
goto v___jp_25_;
}
}
v___jp_18_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_string_append(v___y_20_, v___y_19_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
v___jp_25_:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_27_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_));
v___x_28_ = lean_string_utf8_byte_size(v_r_26_);
v___x_29_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
v___x_30_ = lean_nat_dec_le(v___x_29_, v___x_28_);
if (v___x_30_ == 0)
{
v___y_19_ = v___x_27_;
v___y_20_ = v_r_26_;
goto v___jp_18_;
}
else
{
lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_nat_sub(v___x_28_, v___x_29_);
v___x_33_ = lean_string_memcmp(v_r_26_, v___x_27_, v___x_32_, v___x_31_, v___x_29_);
lean_dec(v___x_32_);
if (v___x_33_ == 0)
{
v___y_19_ = v___x_27_;
v___y_20_ = v_r_26_;
goto v___jp_18_;
}
else
{
lean_object* v___x_34_; 
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v_r_26_);
return v___x_34_;
}
}
}
}
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
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_nbuckets_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_84_ = lean_array_get_size(v_data_83_);
v___x_85_ = lean_unsigned_to_nat(2u);
v_nbuckets_86_ = lean_nat_mul(v___x_84_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_box(0);
v___x_89_ = lean_mk_array(v_nbuckets_86_, v___x_88_);
v___x_90_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(v___x_87_, v_data_83_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(lean_object* v_a_91_, lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
else
{
lean_object* v_key_94_; lean_object* v_tail_95_; uint8_t v___x_96_; 
v_key_94_ = lean_ctor_get(v_x_92_, 0);
v_tail_95_ = lean_ctor_get(v_x_92_, 2);
v___x_96_ = lean_string_dec_eq(v_key_94_, v_a_91_);
if (v___x_96_ == 0)
{
v_x_92_ = v_tail_95_;
goto _start;
}
else
{
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_98_, lean_object* v_x_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_98_, v_x_99_);
lean_dec(v_x_99_);
lean_dec_ref(v_a_98_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(lean_object* v_a_102_, lean_object* v_b_103_, lean_object* v_x_104_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
lean_dec(v_b_103_);
lean_dec_ref(v_a_102_);
return v_x_104_;
}
else
{
lean_object* v_key_105_; lean_object* v_value_106_; lean_object* v_tail_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_119_; 
v_key_105_ = lean_ctor_get(v_x_104_, 0);
v_value_106_ = lean_ctor_get(v_x_104_, 1);
v_tail_107_ = lean_ctor_get(v_x_104_, 2);
v_isSharedCheck_119_ = !lean_is_exclusive(v_x_104_);
if (v_isSharedCheck_119_ == 0)
{
v___x_109_ = v_x_104_;
v_isShared_110_ = v_isSharedCheck_119_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_tail_107_);
lean_inc(v_value_106_);
lean_inc(v_key_105_);
lean_dec(v_x_104_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_119_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
uint8_t v___x_111_; 
v___x_111_ = lean_string_dec_eq(v_key_105_, v_a_102_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_102_, v_b_103_, v_tail_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 2, v___x_112_);
v___x_114_ = v___x_109_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_key_105_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_value_106_);
lean_ctor_set(v_reuseFailAlloc_115_, 2, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
else
{
lean_object* v___x_117_; 
lean_dec(v_value_106_);
lean_dec(v_key_105_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v_b_103_);
lean_ctor_set(v___x_109_, 0, v_a_102_);
v___x_117_ = v___x_109_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_102_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_b_103_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v_tail_107_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(lean_object* v_m_120_, lean_object* v_a_121_, lean_object* v_b_122_){
_start:
{
lean_object* v_size_123_; lean_object* v_buckets_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_167_; 
v_size_123_ = lean_ctor_get(v_m_120_, 0);
v_buckets_124_ = lean_ctor_get(v_m_120_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_m_120_);
if (v_isSharedCheck_167_ == 0)
{
v___x_126_ = v_m_120_;
v_isShared_127_ = v_isSharedCheck_167_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_buckets_124_);
lean_inc(v_size_123_);
lean_dec(v_m_120_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_167_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; uint64_t v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v_fold_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; size_t v___x_136_; size_t v___x_137_; size_t v___x_138_; size_t v___x_139_; size_t v___x_140_; lean_object* v_bkt_141_; uint8_t v___x_142_; 
v___x_128_ = lean_array_get_size(v_buckets_124_);
v___x_129_ = lean_string_hash(v_a_121_);
v___x_130_ = 32ULL;
v___x_131_ = lean_uint64_shift_right(v___x_129_, v___x_130_);
v_fold_132_ = lean_uint64_xor(v___x_129_, v___x_131_);
v___x_133_ = 16ULL;
v___x_134_ = lean_uint64_shift_right(v_fold_132_, v___x_133_);
v___x_135_ = lean_uint64_xor(v_fold_132_, v___x_134_);
v___x_136_ = lean_uint64_to_usize(v___x_135_);
v___x_137_ = lean_usize_of_nat(v___x_128_);
v___x_138_ = ((size_t)1ULL);
v___x_139_ = lean_usize_sub(v___x_137_, v___x_138_);
v___x_140_ = lean_usize_land(v___x_136_, v___x_139_);
v_bkt_141_ = lean_array_uget_borrowed(v_buckets_124_, v___x_140_);
v___x_142_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_121_, v_bkt_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v_size_x27_144_; lean_object* v___x_145_; lean_object* v_buckets_x27_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_143_ = lean_unsigned_to_nat(1u);
v_size_x27_144_ = lean_nat_add(v_size_123_, v___x_143_);
lean_dec(v_size_123_);
lean_inc(v_bkt_141_);
v___x_145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_145_, 0, v_a_121_);
lean_ctor_set(v___x_145_, 1, v_b_122_);
lean_ctor_set(v___x_145_, 2, v_bkt_141_);
v_buckets_x27_146_ = lean_array_uset(v_buckets_124_, v___x_140_, v___x_145_);
v___x_147_ = lean_unsigned_to_nat(4u);
v___x_148_ = lean_nat_mul(v_size_x27_144_, v___x_147_);
v___x_149_ = lean_unsigned_to_nat(3u);
v___x_150_ = lean_nat_div(v___x_148_, v___x_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_array_get_size(v_buckets_x27_146_);
v___x_152_ = lean_nat_dec_le(v___x_150_, v___x_151_);
lean_dec(v___x_150_);
if (v___x_152_ == 0)
{
lean_object* v_val_153_; lean_object* v___x_155_; 
v_val_153_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(v_buckets_x27_146_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v_val_153_);
lean_ctor_set(v___x_126_, 0, v_size_x27_144_);
v___x_155_ = v___x_126_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_size_x27_144_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_val_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
else
{
lean_object* v___x_158_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v_buckets_x27_146_);
lean_ctor_set(v___x_126_, 0, v_size_x27_144_);
v___x_158_ = v___x_126_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_size_x27_144_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_buckets_x27_146_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
else
{
lean_object* v___x_160_; lean_object* v_buckets_x27_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
lean_inc(v_bkt_141_);
v___x_160_ = lean_box(0);
v_buckets_x27_161_ = lean_array_uset(v_buckets_124_, v___x_140_, v___x_160_);
v___x_162_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_121_, v_b_122_, v_bkt_141_);
v___x_163_ = lean_array_uset(v_buckets_x27_161_, v___x_140_, v___x_162_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_163_);
v___x_165_ = v___x_126_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_size_123_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(lean_object* v_as_x27_168_, lean_object* v_b_169_){
_start:
{
if (lean_obj_tag(v_as_x27_168_) == 0)
{
return v_b_169_;
}
else
{
lean_object* v_head_170_; lean_object* v_tail_171_; lean_object* v_fst_172_; lean_object* v_snd_173_; lean_object* v_r_174_; 
v_head_170_ = lean_ctor_get(v_as_x27_168_, 0);
v_tail_171_ = lean_ctor_get(v_as_x27_168_, 1);
v_fst_172_ = lean_ctor_get(v_head_170_, 0);
v_snd_173_ = lean_ctor_get(v_head_170_, 1);
lean_inc(v_snd_173_);
lean_inc(v_fst_172_);
v_r_174_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_b_169_, v_fst_172_, v_snd_173_);
v_as_x27_168_ = v_tail_171_;
v_b_169_ = v_r_174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_176_, lean_object* v_b_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_as_x27_176_, v_b_177_);
lean_dec(v_as_x27_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(lean_object* v_m_179_, lean_object* v_l_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_l_180_, v_m_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0___boxed(lean_object* v_m_182_, lean_object* v_l_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(v_m_182_, v_l_183_);
lean_dec(v_l_183_);
return v_res_184_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_box(0);
v___x_201_ = lean_unsigned_to_nat(16u);
v___x_202_ = lean_mk_array(v___x_201_, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
return v___x_205_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8);
v___x_207_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__6));
v___x_208_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v___x_207_, v___x_206_);
return v___x_208_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap(void){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0(lean_object* v_00_u03b2_210_, lean_object* v_m_211_, lean_object* v_a_212_, lean_object* v_b_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_m_211_, v_a_212_, v_b_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(lean_object* v_as_215_, lean_object* v_as_x27_216_, lean_object* v_b_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_as_x27_216_, v_b_217_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___boxed(lean_object* v_as_220_, lean_object* v_as_x27_221_, lean_object* v_b_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(v_as_220_, v_as_x27_221_, v_b_222_, v_a_223_);
lean_dec(v_as_x27_221_);
lean_dec(v_as_220_);
return v_res_224_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_225_, lean_object* v_a_226_, lean_object* v_x_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_226_, v_x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_229_, lean_object* v_a_230_, lean_object* v_x_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(v_00_u03b2_229_, v_a_230_, v_x_231_);
lean_dec(v_x_231_);
lean_dec_ref(v_a_230_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_234_, lean_object* v_data_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(v_data_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_237_, lean_object* v_a_238_, lean_object* v_b_239_, lean_object* v_x_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_238_, v_b_239_, v_x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_242_, lean_object* v_i_243_, lean_object* v_source_244_, lean_object* v_target_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_243_, v_source_244_, v_target_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_247_, lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_248_, v_x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_inc(v_x_251_);
return v_x_251_;
}
else
{
lean_object* v_key_253_; lean_object* v_tail_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_key_253_ = lean_ctor_get(v_x_252_, 0);
v_tail_254_ = lean_ctor_get(v_x_252_, 2);
v___x_255_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_x_251_, v_tail_254_);
lean_inc(v_key_253_);
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v_key_253_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0___boxed(lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_x_257_, v_x_258_);
lean_dec(v_x_258_);
lean_dec(v_x_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(lean_object* v_as_260_, size_t v_i_261_, size_t v_stop_262_, lean_object* v_b_263_){
_start:
{
uint8_t v___x_264_; 
v___x_264_ = lean_usize_dec_eq(v_i_261_, v_stop_262_);
if (v___x_264_ == 0)
{
size_t v___x_265_; size_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_sub(v_i_261_, v___x_265_);
v___x_267_ = lean_array_uget_borrowed(v_as_260_, v___x_266_);
v___x_268_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_b_263_, v___x_267_);
lean_dec(v_b_263_);
v_i_261_ = v___x_266_;
v_b_263_ = v___x_268_;
goto _start;
}
else
{
return v_b_263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1___boxed(lean_object* v_as_270_, lean_object* v_i_271_, lean_object* v_stop_272_, lean_object* v_b_273_){
_start:
{
size_t v_i_boxed_274_; size_t v_stop_boxed_275_; lean_object* v_res_276_; 
v_i_boxed_274_ = lean_unbox_usize(v_i_271_);
lean_dec(v_i_271_);
v_stop_boxed_275_ = lean_unbox_usize(v_stop_272_);
lean_dec(v_stop_272_);
v_res_276_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(v_as_270_, v_i_boxed_274_, v_stop_boxed_275_, v_b_273_);
lean_dec_ref(v_as_270_);
return v_res_276_;
}
}
static lean_object* _init_l_Lean_manualDomains(void){
_start:
{
lean_object* v___x_277_; lean_object* v_buckets_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_277_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v_buckets_278_ = lean_ctor_get(v___x_277_, 1);
v___x_279_ = lean_box(0);
v___x_280_ = lean_array_get_size(v_buckets_278_);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_nat_dec_lt(v___x_281_, v___x_280_);
if (v___x_282_ == 0)
{
return v___x_279_;
}
else
{
size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_usize_of_nat(v___x_280_);
v___x_284_ = ((size_t)0ULL);
v___x_285_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(v_buckets_278_, v___x_283_, v___x_284_, v___x_279_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(lean_object* v_a_286_, lean_object* v_x_287_){
_start:
{
if (lean_obj_tag(v_x_287_) == 0)
{
lean_object* v___x_288_; 
v___x_288_ = lean_box(0);
return v___x_288_;
}
else
{
lean_object* v_key_289_; lean_object* v_value_290_; lean_object* v_tail_291_; uint8_t v___x_292_; 
v_key_289_ = lean_ctor_get(v_x_287_, 0);
v_value_290_ = lean_ctor_get(v_x_287_, 1);
v_tail_291_ = lean_ctor_get(v_x_287_, 2);
v___x_292_ = lean_string_dec_eq(v_key_289_, v_a_286_);
if (v___x_292_ == 0)
{
v_x_287_ = v_tail_291_;
goto _start;
}
else
{
lean_object* v___x_294_; 
lean_inc(v_value_290_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v_value_290_);
return v___x_294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg___boxed(lean_object* v_a_295_, lean_object* v_x_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_295_, v_x_296_);
lean_dec(v_x_296_);
lean_dec_ref(v_a_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(lean_object* v_m_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_buckets_300_; lean_object* v___x_301_; uint64_t v___x_302_; uint64_t v___x_303_; uint64_t v___x_304_; uint64_t v_fold_305_; uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v___x_308_; size_t v___x_309_; size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_buckets_300_ = lean_ctor_get(v_m_298_, 1);
v___x_301_ = lean_array_get_size(v_buckets_300_);
v___x_302_ = lean_string_hash(v_a_299_);
v___x_303_ = 32ULL;
v___x_304_ = lean_uint64_shift_right(v___x_302_, v___x_303_);
v_fold_305_ = lean_uint64_xor(v___x_302_, v___x_304_);
v___x_306_ = 16ULL;
v___x_307_ = lean_uint64_shift_right(v_fold_305_, v___x_306_);
v___x_308_ = lean_uint64_xor(v_fold_305_, v___x_307_);
v___x_309_ = lean_uint64_to_usize(v___x_308_);
v___x_310_ = lean_usize_of_nat(v___x_301_);
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_sub(v___x_310_, v___x_311_);
v___x_313_ = lean_usize_land(v___x_309_, v___x_312_);
v___x_314_ = lean_array_uget_borrowed(v_buckets_300_, v___x_313_);
v___x_315_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_299_, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg___boxed(lean_object* v_m_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v_m_316_, v_a_317_);
lean_dec_ref(v_a_317_);
lean_dec_ref(v_m_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_320_) == 0)
{
lean_inc(v_x_319_);
return v_x_319_;
}
else
{
lean_object* v_key_321_; lean_object* v_value_322_; lean_object* v_tail_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_key_321_ = lean_ctor_get(v_x_320_, 0);
v_value_322_ = lean_ctor_get(v_x_320_, 1);
v_tail_323_ = lean_ctor_get(v_x_320_, 2);
v___x_324_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_x_319_, v_tail_323_);
lean_inc(v_value_322_);
lean_inc(v_key_321_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v_key_321_);
lean_ctor_set(v___x_325_, 1, v_value_322_);
v___x_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2___boxed(lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_x_327_, v_x_328_);
lean_dec(v_x_328_);
lean_dec(v_x_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(lean_object* v_as_330_, size_t v_i_331_, size_t v_stop_332_, lean_object* v_b_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = lean_usize_dec_eq(v_i_331_, v_stop_332_);
if (v___x_334_ == 0)
{
size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_sub(v_i_331_, v___x_335_);
v___x_337_ = lean_array_uget_borrowed(v_as_330_, v___x_336_);
v___x_338_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_b_333_, v___x_337_);
lean_dec(v_b_333_);
v_i_331_ = v___x_336_;
v_b_333_ = v___x_338_;
goto _start;
}
else
{
return v_b_333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3___boxed(lean_object* v_as_340_, lean_object* v_i_341_, lean_object* v_stop_342_, lean_object* v_b_343_){
_start:
{
size_t v_i_boxed_344_; size_t v_stop_boxed_345_; lean_object* v_res_346_; 
v_i_boxed_344_ = lean_unbox_usize(v_i_341_);
lean_dec(v_i_341_);
v_stop_boxed_345_ = lean_unbox_usize(v_stop_342_);
lean_dec(v_stop_342_);
v_res_346_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_as_340_, v_i_boxed_344_, v_stop_boxed_345_, v_b_343_);
lean_dec_ref(v_as_340_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_manualLink_spec__1(lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
if (lean_obj_tag(v_a_348_) == 0)
{
lean_object* v___x_350_; 
v___x_350_ = l_List_reverse___redArg(v_a_349_);
return v___x_350_;
}
else
{
lean_object* v_head_351_; lean_object* v_tail_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_364_; 
v_head_351_ = lean_ctor_get(v_a_348_, 0);
v_tail_352_ = lean_ctor_get(v_a_348_, 1);
v_isSharedCheck_364_ = !lean_is_exclusive(v_a_348_);
if (v_isSharedCheck_364_ == 0)
{
v___x_354_ = v_a_348_;
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_tail_352_);
lean_inc(v_head_351_);
lean_dec(v_a_348_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v_fst_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v_fst_356_ = lean_ctor_get(v_head_351_, 0);
lean_inc(v_fst_356_);
lean_dec(v_head_351_);
v___x_357_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_manualLink_spec__1___closed__0));
v___x_358_ = lean_string_append(v___x_357_, v_fst_356_);
lean_dec(v_fst_356_);
v___x_359_ = lean_string_append(v___x_358_, v___x_357_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v_a_349_);
lean_ctor_set(v___x_354_, 0, v___x_359_);
v___x_361_ = v___x_354_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_a_349_);
v___x_361_ = v_reuseFailAlloc_363_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
v_a_348_ = v_tail_352_;
v_a_349_ = v___x_361_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_manualLink(lean_object* v_kind_370_, lean_object* v_name_371_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_373_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_372_, v_kind_370_);
if (lean_obj_tag(v___x_373_) == 1)
{
lean_object* v_val_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_388_; 
v_val_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_388_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_388_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_val_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_388_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_378_ = l_Lean_manualRoot;
v___x_379_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_380_ = lean_string_append(v___x_379_, v_val_374_);
lean_dec(v_val_374_);
v___x_381_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_382_ = lean_string_append(v___x_380_, v___x_381_);
v___x_383_ = lean_string_append(v___x_382_, v_name_371_);
v___x_384_ = lean_string_append(v___x_378_, v___x_383_);
lean_dec_ref(v___x_383_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_384_);
v___x_386_ = v___x_376_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
else
{
lean_object* v_buckets_389_; lean_object* v___x_390_; lean_object* v___y_392_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
lean_dec(v___x_373_);
v_buckets_389_ = lean_ctor_get(v___x_372_, 1);
v___x_390_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_402_ = lean_box(0);
v___x_403_ = lean_array_get_size(v_buckets_389_);
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_nat_dec_lt(v___x_404_, v___x_403_);
if (v___x_405_ == 0)
{
v___y_392_ = v___x_402_;
goto v___jp_391_;
}
else
{
size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_usize_of_nat(v___x_403_);
v___x_407_ = ((size_t)0ULL);
v___x_408_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_389_, v___x_406_, v___x_407_, v___x_402_);
v___y_392_ = v___x_408_;
goto v___jp_391_;
}
v___jp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_acceptableKinds_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_393_ = lean_box(0);
v___x_394_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_392_, v___x_393_);
v_acceptableKinds_395_ = l_String_intercalate(v___x_390_, v___x_394_);
v___x_396_ = ((lean_object*)(l_Lean_manualLink___closed__3));
v___x_397_ = lean_string_append(v___x_396_, v_kind_370_);
v___x_398_ = ((lean_object*)(l_Lean_manualLink___closed__4));
v___x_399_ = lean_string_append(v___x_397_, v___x_398_);
v___x_400_ = lean_string_append(v___x_399_, v_acceptableKinds_395_);
lean_dec_ref(v_acceptableKinds_395_);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_manualLink___boxed(lean_object* v_kind_409_, lean_object* v_name_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_manualLink(v_kind_409_, v_name_410_);
lean_dec_ref(v_name_410_);
lean_dec_ref(v_kind_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(lean_object* v_00_u03b2_412_, lean_object* v_m_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v_m_413_, v_a_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___boxed(lean_object* v_00_u03b2_416_, lean_object* v_m_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(v_00_u03b2_416_, v_m_417_, v_a_418_);
lean_dec_ref(v_a_418_);
lean_dec_ref(v_m_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(lean_object* v_00_u03b2_420_, lean_object* v_a_421_, lean_object* v_x_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_421_, v_x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___boxed(lean_object* v_00_u03b2_424_, lean_object* v_a_425_, lean_object* v_x_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(v_00_u03b2_424_, v_a_425_, v_x_426_);
lean_dec(v_x_426_);
lean_dec_ref(v_a_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(lean_object* v_s_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0));
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___boxed(lean_object* v_s_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(v_s_432_);
lean_dec_ref(v_s_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(lean_object* v_path_434_, lean_object* v___x_435_, lean_object* v___x_436_, lean_object* v_a_437_, lean_object* v_b_438_){
_start:
{
lean_object* v_it_440_; lean_object* v_startInclusive_441_; lean_object* v_endExclusive_442_; 
if (lean_obj_tag(v_a_437_) == 0)
{
lean_object* v_currPos_447_; lean_object* v_searcher_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_471_; 
v_currPos_447_ = lean_ctor_get(v_a_437_, 0);
v_searcher_448_ = lean_ctor_get(v_a_437_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v_a_437_);
if (v_isSharedCheck_471_ == 0)
{
v___x_450_ = v_a_437_;
v_isShared_451_ = v_isSharedCheck_471_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_searcher_448_);
lean_inc(v_currPos_447_);
lean_dec(v_a_437_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_471_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
uint8_t v_decide_452_; 
v_decide_452_ = lean_nat_dec_eq(v_searcher_448_, v___x_436_);
if (v_decide_452_ == 0)
{
uint32_t v___x_453_; uint32_t v___x_454_; uint8_t v___x_455_; 
v___x_453_ = 47;
v___x_454_ = lean_string_utf8_get_fast(v_path_434_, v_searcher_448_);
v___x_455_ = lean_uint32_dec_eq(v___x_454_, v___x_453_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = lean_string_utf8_next_fast(v_path_434_, v_searcher_448_);
lean_dec(v_searcher_448_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_456_);
v___x_458_ = v___x_450_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_currPos_447_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_456_);
v___x_458_ = v_reuseFailAlloc_460_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
v_a_437_ = v___x_458_;
goto _start;
}
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_slice_464_; lean_object* v_nextIt_466_; 
v___x_461_ = lean_string_utf8_next_fast(v_path_434_, v_searcher_448_);
v___x_462_ = lean_nat_sub(v___x_461_, v_searcher_448_);
v___x_463_ = lean_nat_add(v_searcher_448_, v___x_462_);
lean_dec(v___x_462_);
v_slice_464_ = l_String_Slice_subslice_x21(v___x_435_, v_currPos_447_, v_searcher_448_);
lean_inc(v___x_463_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_463_);
lean_ctor_set(v___x_450_, 0, v___x_463_);
v_nextIt_466_ = v___x_450_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v___x_463_);
v_nextIt_466_ = v_reuseFailAlloc_469_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v_startInclusive_467_; lean_object* v_endExclusive_468_; 
v_startInclusive_467_ = lean_ctor_get(v_slice_464_, 0);
lean_inc(v_startInclusive_467_);
v_endExclusive_468_ = lean_ctor_get(v_slice_464_, 1);
lean_inc(v_endExclusive_468_);
lean_dec_ref(v_slice_464_);
v_it_440_ = v_nextIt_466_;
v_startInclusive_441_ = v_startInclusive_467_;
v_endExclusive_442_ = v_endExclusive_468_;
goto v___jp_439_;
}
}
}
else
{
lean_object* v___x_470_; 
lean_del_object(v___x_450_);
lean_dec(v_searcher_448_);
v___x_470_ = lean_box(1);
lean_inc(v___x_436_);
v_it_440_ = v___x_470_;
v_startInclusive_441_ = v_currPos_447_;
v_endExclusive_442_ = v___x_436_;
goto v___jp_439_;
}
}
}
else
{
lean_dec(v___x_436_);
lean_dec_ref(v_path_434_);
return v_b_438_;
}
v___jp_439_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
lean_inc_ref(v_path_434_);
v___x_443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_443_, 0, v_path_434_);
lean_ctor_set(v___x_443_, 1, v_startInclusive_441_);
lean_ctor_set(v___x_443_, 2, v_endExclusive_442_);
v___x_444_ = l_String_Slice_toString(v___x_443_);
lean_dec_ref_known(v___x_443_, 3);
v___x_445_ = lean_array_push(v_b_438_, v___x_444_);
v_a_437_ = v_it_440_;
v_b_438_ = v___x_445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg___boxed(lean_object* v_path_472_, lean_object* v___x_473_, lean_object* v___x_474_, lean_object* v_a_475_, lean_object* v_b_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_472_, v___x_473_, v___x_474_, v_a_475_, v_b_476_);
lean_dec_ref(v___x_473_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
if (lean_obj_tag(v_x_479_) == 0)
{
return v_x_478_;
}
else
{
lean_object* v_head_480_; lean_object* v_tail_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_head_480_ = lean_ctor_get(v_x_479_, 0);
v_tail_481_ = lean_ctor_get(v_x_479_, 1);
v___x_482_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_483_ = lean_string_append(v_x_478_, v___x_482_);
v___x_484_ = lean_string_append(v___x_483_, v_head_480_);
v_x_478_ = v___x_484_;
v_x_479_ = v_tail_481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0___boxed(lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v_x_486_, v_x_487_);
lean_dec(v_x_487_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(lean_object* v_x_492_){
_start:
{
if (lean_obj_tag(v_x_492_) == 0)
{
lean_object* v___x_493_; 
v___x_493_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0));
return v___x_493_;
}
else
{
lean_object* v_tail_494_; 
v_tail_494_ = lean_ctor_get(v_x_492_, 1);
if (lean_obj_tag(v_tail_494_) == 0)
{
lean_object* v_head_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_head_495_ = lean_ctor_get(v_x_492_, 0);
v___x_496_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_497_ = lean_string_append(v___x_496_, v_head_495_);
v___x_498_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2));
v___x_499_ = lean_string_append(v___x_497_, v___x_498_);
return v___x_499_;
}
else
{
lean_object* v_head_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint32_t v___x_504_; lean_object* v___x_505_; 
v_head_500_ = lean_ctor_get(v_x_492_, 0);
v___x_501_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_502_ = lean_string_append(v___x_501_, v_head_500_);
v___x_503_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v___x_502_, v_tail_494_);
v___x_504_ = 93;
v___x_505_ = lean_string_push(v___x_503_, v___x_504_);
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___boxed(lean_object* v_x_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v_x_506_);
lean_dec(v_x_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rw(lean_object* v_path_518_){
_start:
{
lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_string_utf8_byte_size(v_path_518_);
lean_inc_ref(v_path_518_);
v___x_546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_546_, 0, v_path_518_);
lean_ctor_set(v___x_546_, 1, v___x_544_);
lean_ctor_set(v___x_546_, 2, v___x_545_);
v___x_547_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(v___x_546_);
v___x_548_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__4));
v___x_549_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_518_, v___x_546_, v___x_545_, v___x_547_, v___x_548_);
lean_dec_ref_known(v___x_546_, 3);
v___x_550_ = lean_array_to_list(v___x_549_);
if (lean_obj_tag(v___x_550_) == 0)
{
goto v___jp_542_;
}
else
{
lean_object* v_head_551_; lean_object* v_tail_552_; lean_object* v_kind_554_; lean_object* v___x_589_; uint8_t v___x_590_; 
v_head_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_head_551_);
v_tail_552_ = lean_ctor_get(v___x_550_, 1);
lean_inc(v_tail_552_);
lean_dec_ref_known(v___x_550_, 2);
v___x_589_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_590_ = lean_string_dec_eq(v_head_551_, v___x_589_);
if (v___x_590_ == 0)
{
v_kind_554_ = v_head_551_;
goto v___jp_553_;
}
else
{
lean_dec(v_head_551_);
if (lean_obj_tag(v_tail_552_) == 0)
{
goto v___jp_542_;
}
else
{
v_kind_554_ = v___x_589_;
goto v___jp_553_;
}
}
v___jp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_555_, v_kind_554_);
if (lean_obj_tag(v___x_556_) == 1)
{
if (lean_obj_tag(v_tail_552_) == 1)
{
lean_object* v_tail_557_; 
v_tail_557_ = lean_ctor_get(v_tail_552_, 1);
if (lean_obj_tag(v_tail_557_) == 0)
{
lean_object* v_val_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_580_; 
v_val_558_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_580_ == 0)
{
v___x_560_ = v___x_556_;
v_isShared_561_ = v_isSharedCheck_580_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_val_558_);
lean_dec(v___x_556_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_580_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v_head_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_head_562_ = lean_ctor_get(v_tail_552_, 0);
lean_inc(v_head_562_);
lean_dec_ref_known(v_tail_552_, 2);
v___x_563_ = lean_string_utf8_byte_size(v_head_562_);
v___x_564_ = lean_nat_dec_eq(v___x_563_, v___x_544_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
lean_dec_ref(v_kind_554_);
v___x_565_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_566_ = lean_string_append(v___x_565_, v_val_558_);
lean_dec(v_val_558_);
v___x_567_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_568_ = lean_string_append(v___x_566_, v___x_567_);
v___x_569_ = lean_string_append(v___x_568_, v_head_562_);
lean_dec(v_head_562_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_569_);
v___x_571_ = v___x_560_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
lean_dec(v_head_562_);
lean_dec(v_val_558_);
v___x_573_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__5));
v___x_574_ = lean_string_append(v___x_573_, v_kind_554_);
lean_dec_ref(v_kind_554_);
v___x_575_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__6));
v___x_576_ = lean_string_append(v___x_574_, v___x_575_);
if (v_isShared_561_ == 0)
{
lean_ctor_set_tag(v___x_560_, 0);
lean_ctor_set(v___x_560_, 0, v___x_576_);
v___x_578_ = v___x_560_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_556_, 1);
v___y_533_ = v_tail_552_;
v___y_534_ = v_kind_554_;
goto v___jp_532_;
}
}
else
{
lean_dec_ref_known(v___x_556_, 1);
v___y_533_ = v_tail_552_;
v___y_534_ = v_kind_554_;
goto v___jp_532_;
}
}
else
{
lean_object* v_buckets_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
lean_dec(v___x_556_);
lean_dec(v_tail_552_);
v_buckets_581_ = lean_ctor_get(v___x_555_, 1);
v___x_582_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_583_ = lean_box(0);
v___x_584_ = lean_array_get_size(v_buckets_581_);
v___x_585_ = lean_nat_dec_lt(v___x_544_, v___x_584_);
if (v___x_585_ == 0)
{
v___y_520_ = v_kind_554_;
v___y_521_ = v___x_582_;
v___y_522_ = v___x_583_;
goto v___jp_519_;
}
else
{
size_t v___x_586_; size_t v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_usize_of_nat(v___x_584_);
v___x_587_ = ((size_t)0ULL);
v___x_588_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_581_, v___x_586_, v___x_587_, v___x_583_);
v___y_520_ = v_kind_554_;
v___y_521_ = v___x_582_;
v___y_522_ = v___x_588_;
goto v___jp_519_;
}
}
}
}
v___jp_519_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_acceptableKinds_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_523_ = lean_box(0);
v___x_524_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_522_, v___x_523_);
v_acceptableKinds_525_ = l_String_intercalate(v___y_521_, v___x_524_);
v___x_526_ = ((lean_object*)(l_Lean_manualLink___closed__3));
v___x_527_ = lean_string_append(v___x_526_, v___y_520_);
lean_dec_ref(v___y_520_);
v___x_528_ = ((lean_object*)(l_Lean_manualLink___closed__4));
v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
v___x_530_ = lean_string_append(v___x_529_, v_acceptableKinds_525_);
lean_dec_ref(v_acceptableKinds_525_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
v___jp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_535_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__0));
v___x_536_ = lean_string_append(v___x_535_, v___y_534_);
lean_dec_ref(v___y_534_);
v___x_537_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__1));
v___x_538_ = lean_string_append(v___x_536_, v___x_537_);
v___x_539_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v___y_533_);
lean_dec(v___y_533_);
v___x_540_ = lean_string_append(v___x_538_, v___x_539_);
lean_dec_ref(v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
v___jp_542_:
{
lean_object* v___x_543_; 
v___x_543_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__3));
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(lean_object* v_path_591_, lean_object* v___x_592_, lean_object* v___x_593_, lean_object* v_inst_594_, lean_object* v_R_595_, lean_object* v_a_596_, lean_object* v_b_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_591_, v___x_592_, v___x_593_, v_a_596_, v_b_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___boxed(lean_object* v_path_599_, lean_object* v___x_600_, lean_object* v___x_601_, lean_object* v_inst_602_, lean_object* v_R_603_, lean_object* v_a_604_, lean_object* v_b_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(v_path_599_, v___x_600_, v___x_601_, v_inst_602_, v_R_603_, v_a_604_, v_b_605_);
lean_dec_ref(v___x_600_);
return v_res_606_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(uint32_t v_c_607_){
_start:
{
uint8_t v___y_655_; uint32_t v___x_660_; uint8_t v___x_661_; 
v___x_660_ = 65;
v___x_661_ = lean_uint32_dec_le(v___x_660_, v_c_607_);
if (v___x_661_ == 0)
{
v___y_655_ = v___x_661_;
goto v___jp_654_;
}
else
{
uint32_t v___x_662_; uint8_t v___x_663_; 
v___x_662_ = 90;
v___x_663_ = lean_uint32_dec_le(v_c_607_, v___x_662_);
v___y_655_ = v___x_663_;
goto v___jp_654_;
}
v___jp_608_:
{
uint32_t v___x_609_; uint8_t v___x_610_; 
v___x_609_ = 45;
v___x_610_ = lean_uint32_dec_eq(v_c_607_, v___x_609_);
if (v___x_610_ == 0)
{
uint32_t v___x_611_; uint8_t v___x_612_; 
v___x_611_ = 46;
v___x_612_ = lean_uint32_dec_eq(v_c_607_, v___x_611_);
if (v___x_612_ == 0)
{
uint32_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = 95;
v___x_614_ = lean_uint32_dec_eq(v_c_607_, v___x_613_);
if (v___x_614_ == 0)
{
uint32_t v___x_615_; uint8_t v___x_616_; 
v___x_615_ = 126;
v___x_616_ = lean_uint32_dec_eq(v_c_607_, v___x_615_);
if (v___x_616_ == 0)
{
uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 58;
v___x_618_ = lean_uint32_dec_eq(v_c_607_, v___x_617_);
if (v___x_618_ == 0)
{
uint32_t v___x_619_; uint8_t v___x_620_; 
v___x_619_ = 47;
v___x_620_ = lean_uint32_dec_eq(v_c_607_, v___x_619_);
if (v___x_620_ == 0)
{
uint32_t v___x_621_; uint8_t v___x_622_; 
v___x_621_ = 63;
v___x_622_ = lean_uint32_dec_eq(v_c_607_, v___x_621_);
if (v___x_622_ == 0)
{
uint32_t v___x_623_; uint8_t v___x_624_; 
v___x_623_ = 35;
v___x_624_ = lean_uint32_dec_eq(v_c_607_, v___x_623_);
if (v___x_624_ == 0)
{
uint32_t v___x_625_; uint8_t v___x_626_; 
v___x_625_ = 91;
v___x_626_ = lean_uint32_dec_eq(v_c_607_, v___x_625_);
if (v___x_626_ == 0)
{
uint32_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = 93;
v___x_628_ = lean_uint32_dec_eq(v_c_607_, v___x_627_);
if (v___x_628_ == 0)
{
uint32_t v___x_629_; uint8_t v___x_630_; 
v___x_629_ = 64;
v___x_630_ = lean_uint32_dec_eq(v_c_607_, v___x_629_);
if (v___x_630_ == 0)
{
uint32_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 33;
v___x_632_ = lean_uint32_dec_eq(v_c_607_, v___x_631_);
if (v___x_632_ == 0)
{
uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 36;
v___x_634_ = lean_uint32_dec_eq(v_c_607_, v___x_633_);
if (v___x_634_ == 0)
{
uint32_t v___x_635_; uint8_t v___x_636_; 
v___x_635_ = 38;
v___x_636_ = lean_uint32_dec_eq(v_c_607_, v___x_635_);
if (v___x_636_ == 0)
{
uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = 39;
v___x_638_ = lean_uint32_dec_eq(v_c_607_, v___x_637_);
if (v___x_638_ == 0)
{
uint32_t v___x_639_; uint8_t v___x_640_; 
v___x_639_ = 42;
v___x_640_ = lean_uint32_dec_eq(v_c_607_, v___x_639_);
if (v___x_640_ == 0)
{
uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = 43;
v___x_642_ = lean_uint32_dec_eq(v_c_607_, v___x_641_);
if (v___x_642_ == 0)
{
uint32_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = 44;
v___x_644_ = lean_uint32_dec_eq(v_c_607_, v___x_643_);
if (v___x_644_ == 0)
{
uint32_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = 59;
v___x_646_ = lean_uint32_dec_eq(v_c_607_, v___x_645_);
if (v___x_646_ == 0)
{
uint32_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = 61;
v___x_648_ = lean_uint32_dec_eq(v_c_607_, v___x_647_);
return v___x_648_;
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
else
{
return v___x_612_;
}
}
else
{
return v___x_610_;
}
}
v___jp_649_:
{
uint32_t v___x_650_; uint8_t v___x_651_; 
v___x_650_ = 48;
v___x_651_ = lean_uint32_dec_le(v___x_650_, v_c_607_);
if (v___x_651_ == 0)
{
goto v___jp_608_;
}
else
{
uint32_t v___x_652_; uint8_t v___x_653_; 
v___x_652_ = 57;
v___x_653_ = lean_uint32_dec_le(v_c_607_, v___x_652_);
if (v___x_653_ == 0)
{
goto v___jp_608_;
}
else
{
return v___x_653_;
}
}
}
v___jp_654_:
{
if (v___y_655_ == 0)
{
uint32_t v___x_656_; uint8_t v___x_657_; 
v___x_656_ = 97;
v___x_657_ = lean_uint32_dec_le(v___x_656_, v_c_607_);
if (v___x_657_ == 0)
{
goto v___jp_649_;
}
else
{
uint32_t v___x_658_; uint8_t v___x_659_; 
v___x_658_ = 122;
v___x_659_ = lean_uint32_dec_le(v_c_607_, v___x_658_);
if (v___x_659_ == 0)
{
goto v___jp_649_;
}
else
{
return v___x_659_;
}
}
}
else
{
return v___y_655_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar___boxed(lean_object* v_c_664_){
_start:
{
uint32_t v_c_boxed_665_; uint8_t v_res_666_; lean_object* v_r_667_; 
v_c_boxed_665_ = lean_unbox_uint32(v_c_664_);
lean_dec(v_c_664_);
v_res_666_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v_c_boxed_665_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(lean_object* v_s_668_, lean_object* v___x_669_, lean_object* v___x_670_, uint32_t v___x_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_snd_673_; lean_object* v_snd_674_; lean_object* v_fst_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_743_; 
v_snd_673_ = lean_ctor_get(v_a_672_, 1);
lean_inc(v_snd_673_);
v_snd_674_ = lean_ctor_get(v_snd_673_, 1);
lean_inc(v_snd_674_);
v_fst_675_ = lean_ctor_get(v_a_672_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v_a_672_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v_a_672_, 1);
lean_dec(v_unused_744_);
v___x_677_ = v_a_672_;
v_isShared_678_ = v_isSharedCheck_743_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_fst_675_);
lean_dec(v_a_672_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_743_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_fst_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_741_; 
v_fst_679_ = lean_ctor_get(v_snd_673_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_snd_673_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v_snd_673_, 1);
lean_dec(v_unused_742_);
v___x_681_ = v_snd_673_;
v_isShared_682_ = v_isSharedCheck_741_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_fst_679_);
lean_dec(v_snd_673_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_741_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_fst_683_; lean_object* v_snd_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_740_; 
v_fst_683_ = lean_ctor_get(v_snd_674_, 0);
v_snd_684_ = lean_ctor_get(v_snd_674_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_snd_674_);
if (v_isSharedCheck_740_ == 0)
{
v___x_686_ = v_snd_674_;
v_isShared_687_ = v_isSharedCheck_740_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_snd_684_);
lean_inc(v_fst_683_);
lean_dec(v_snd_674_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_740_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; uint8_t v_decide_689_; 
v___x_688_ = lean_string_utf8_byte_size(v_s_668_);
v_decide_689_ = lean_nat_dec_eq(v_snd_684_, v___x_688_);
if (v_decide_689_ == 0)
{
uint32_t v___x_690_; lean_object* v___x_691_; uint8_t v___y_724_; uint8_t v___x_729_; 
v___x_690_ = lean_string_utf8_get_fast(v_s_668_, v_snd_684_);
v___x_691_ = lean_string_utf8_next_fast(v_s_668_, v_snd_684_);
v___x_729_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v___x_690_);
if (v___x_729_ == 0)
{
v___y_724_ = v___x_729_;
goto v___jp_723_;
}
else
{
uint8_t v_decide_730_; 
v_decide_730_ = lean_nat_dec_eq(v___x_691_, v___x_688_);
if (v_decide_730_ == 0)
{
v___y_724_ = v___x_729_;
goto v___jp_723_;
}
else
{
goto v___jp_692_;
}
}
v___jp_692_:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_string_utf8_extract_fast(v_s_668_, v___x_669_, v_snd_684_);
v___x_694_ = l___private_Lean_DocString_Links_0__Lean_rw(v___x_693_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_670_);
lean_ctor_set(v___x_696_, 1, v_snd_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v_a_695_);
lean_ctor_set(v___x_686_, 0, v___x_696_);
v___x_698_ = v___x_686_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_a_695_);
v___x_698_ = v_reuseFailAlloc_708_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_699_ = lean_array_push(v_fst_679_, v___x_698_);
v___x_700_ = lean_string_push(v_fst_675_, v___x_671_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_691_);
lean_ctor_set(v___x_681_, 0, v_fst_683_);
v___x_702_ = v___x_681_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_fst_683_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_691_);
v___x_702_ = v_reuseFailAlloc_707_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v___x_702_);
lean_ctor_set(v___x_677_, 0, v___x_699_);
v___x_704_ = v___x_677_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_702_);
v___x_704_ = v_reuseFailAlloc_706_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; 
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_700_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
return v___x_705_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
lean_dec(v_snd_684_);
lean_dec(v_fst_683_);
lean_dec(v___x_670_);
v_a_709_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_694_, 1);
v___x_710_ = l_Lean_manualRoot;
v___x_711_ = lean_string_append(v_fst_675_, v___x_710_);
v___x_712_ = lean_string_append(v___x_711_, v_a_709_);
lean_dec(v_a_709_);
v___x_713_ = lean_string_push(v___x_712_, v___x_690_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_691_);
lean_ctor_set(v___x_686_, 0, v___x_691_);
v___x_715_ = v___x_686_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_691_);
v___x_715_ = v_reuseFailAlloc_722_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_715_);
v___x_717_ = v___x_681_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_fst_679_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_715_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v___x_717_);
lean_ctor_set(v___x_677_, 0, v___x_713_);
v___x_719_ = v___x_677_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
v___jp_723_:
{
if (v___y_724_ == 0)
{
goto v___jp_692_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
lean_del_object(v___x_686_);
lean_dec(v_snd_684_);
lean_del_object(v___x_681_);
lean_del_object(v___x_677_);
v___x_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_725_, 0, v_fst_683_);
lean_ctor_set(v___x_725_, 1, v___x_691_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_fst_679_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v_fst_675_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v_a_672_ = v___x_727_;
goto _start;
}
}
}
else
{
lean_object* v___x_732_; 
lean_dec(v___x_670_);
if (v_isShared_687_ == 0)
{
v___x_732_ = v___x_686_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_fst_683_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_snd_684_);
v___x_732_ = v_reuseFailAlloc_739_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_734_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_732_);
v___x_734_ = v___x_681_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_fst_679_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_732_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_736_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v___x_734_);
v___x_736_ = v___x_677_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_fst_675_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg___boxed(lean_object* v_s_745_, lean_object* v___x_746_, lean_object* v___x_747_, lean_object* v___x_748_, lean_object* v_a_749_){
_start:
{
uint32_t v___x_2314__boxed_750_; lean_object* v_res_751_; 
v___x_2314__boxed_750_ = lean_unbox_uint32(v___x_748_);
lean_dec(v___x_748_);
v_res_751_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_745_, v___x_746_, v___x_747_, v___x_2314__boxed_750_, v_a_749_);
lean_dec(v___x_746_);
lean_dec_ref(v_s_745_);
return v_res_751_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v_scheme_753_; lean_object* v___x_754_; 
v_scheme_753_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0));
v___x_754_ = lean_string_utf8_byte_size(v_scheme_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(lean_object* v_s_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_snd_757_; lean_object* v_fst_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_822_; 
v_snd_757_ = lean_ctor_get(v_a_756_, 1);
v_fst_758_ = lean_ctor_get(v_a_756_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_a_756_);
if (v_isSharedCheck_822_ == 0)
{
v___x_760_ = v_a_756_;
v_isShared_761_ = v_isSharedCheck_822_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_snd_757_);
lean_inc(v_fst_758_);
lean_dec(v_a_756_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_822_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_fst_762_; lean_object* v_snd_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_821_; 
v_fst_762_ = lean_ctor_get(v_snd_757_, 0);
v_snd_763_ = lean_ctor_get(v_snd_757_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_snd_757_);
if (v_isSharedCheck_821_ == 0)
{
v___x_765_ = v_snd_757_;
v_isShared_766_ = v_isSharedCheck_821_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_snd_763_);
lean_inc(v_fst_762_);
lean_dec(v_snd_757_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_821_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; uint8_t v_decide_768_; 
v___x_767_ = lean_string_utf8_byte_size(v_s_755_);
v_decide_768_ = lean_nat_dec_eq(v_snd_763_, v___x_767_);
if (v_decide_768_ == 0)
{
lean_object* v_scheme_769_; uint32_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_scheme_769_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0));
v___x_770_ = lean_string_utf8_get_fast(v_s_755_, v_snd_763_);
v___x_771_ = lean_string_utf8_next_fast(v_s_755_, v_snd_763_);
v___x_781_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1);
v___x_782_ = lean_nat_sub(v___x_767_, v_snd_763_);
v___x_783_ = lean_nat_dec_le(v___x_781_, v___x_782_);
lean_dec(v___x_782_);
if (v___x_783_ == 0)
{
lean_dec(v_snd_763_);
goto v___jp_772_;
}
else
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = lean_string_memcmp(v_s_755_, v_scheme_769_, v_snd_763_, v___x_784_, v___x_781_);
if (v___x_785_ == 0)
{
lean_dec(v_snd_763_);
goto v___jp_772_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_snd_793_; lean_object* v_snd_794_; lean_object* v_fst_795_; lean_object* v_fst_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_813_; 
lean_del_object(v___x_765_);
lean_del_object(v___x_760_);
lean_inc(v_snd_763_);
lean_inc_ref(v_s_755_);
v___x_786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_786_, 0, v_s_755_);
lean_ctor_set(v___x_786_, 1, v_snd_763_);
lean_ctor_set(v___x_786_, 2, v___x_767_);
v___x_787_ = l_String_Slice_pos_x21(v___x_786_, v___x_781_);
lean_dec_ref_known(v___x_786_, 3);
v___x_788_ = lean_nat_add(v_snd_763_, v___x_787_);
lean_dec(v___x_787_);
lean_inc(v___x_788_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_771_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_fst_762_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_fst_758_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_755_, v___x_788_, v_snd_763_, v___x_770_, v___x_791_);
lean_dec(v___x_788_);
v_snd_793_ = lean_ctor_get(v___x_792_, 1);
lean_inc(v_snd_793_);
v_snd_794_ = lean_ctor_get(v_snd_793_, 1);
lean_inc(v_snd_794_);
v_fst_795_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_fst_795_);
lean_dec_ref(v___x_792_);
v_fst_796_ = lean_ctor_get(v_snd_793_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v_snd_793_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v_snd_793_, 1);
lean_dec(v_unused_814_);
v___x_798_ = v_snd_793_;
v_isShared_799_ = v_isSharedCheck_813_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_fst_796_);
lean_dec(v_snd_793_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_813_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_fst_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_811_; 
v_fst_800_ = lean_ctor_get(v_snd_794_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v_snd_794_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; 
v_unused_812_ = lean_ctor_get(v_snd_794_, 1);
lean_dec(v_unused_812_);
v___x_802_ = v_snd_794_;
v_isShared_803_ = v_isSharedCheck_811_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_fst_800_);
lean_dec(v_snd_794_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_811_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v_fst_800_);
lean_ctor_set(v___x_802_, 0, v_fst_796_);
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_fst_796_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_fst_800_);
v___x_805_ = v_reuseFailAlloc_810_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v___x_805_);
lean_ctor_set(v___x_798_, 0, v_fst_795_);
v___x_807_ = v___x_798_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_fst_795_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_805_);
v___x_807_ = v_reuseFailAlloc_809_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
v_a_756_ = v___x_807_;
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
v___x_773_ = lean_string_push(v_fst_758_, v___x_770_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v___x_771_);
v___x_775_ = v___x_765_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_fst_762_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_771_);
v___x_775_ = v_reuseFailAlloc_780_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v___x_775_);
lean_ctor_set(v___x_760_, 0, v___x_773_);
v___x_777_ = v___x_760_;
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
v_a_756_ = v___x_777_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_816_; 
lean_dec_ref(v_s_755_);
if (v_isShared_766_ == 0)
{
v___x_816_ = v___x_765_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_fst_762_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_snd_763_);
v___x_816_ = v_reuseFailAlloc_820_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v___x_816_);
v___x_818_ = v___x_760_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_fst_758_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore(lean_object* v_s_831_){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v_snd_834_; lean_object* v_fst_835_; lean_object* v_fst_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v___x_832_ = ((lean_object*)(l_Lean_rewriteManualLinksCore___closed__2));
v___x_833_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(v_s_831_, v___x_832_);
v_snd_834_ = lean_ctor_get(v___x_833_, 1);
lean_inc(v_snd_834_);
v_fst_835_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_fst_835_);
lean_dec_ref(v___x_833_);
v_fst_836_ = lean_ctor_get(v_snd_834_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v_snd_834_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v_snd_834_, 1);
lean_dec(v_unused_844_);
v___x_838_ = v_snd_834_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_fst_836_);
lean_dec(v_snd_834_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_fst_835_);
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_fst_836_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_fst_835_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0(lean_object* v_s_845_, lean_object* v___x_846_, lean_object* v___x_847_, uint32_t v___x_848_, lean_object* v_inst_849_, lean_object* v_a_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_845_, v___x_846_, v___x_847_, v___x_848_, v_a_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___boxed(lean_object* v_s_852_, lean_object* v___x_853_, lean_object* v___x_854_, lean_object* v___x_855_, lean_object* v_inst_856_, lean_object* v_a_857_){
_start:
{
uint32_t v___x_2599__boxed_858_; lean_object* v_res_859_; 
v___x_2599__boxed_858_ = lean_unbox_uint32(v___x_855_);
lean_dec(v___x_855_);
v_res_859_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0(v_s_852_, v___x_853_, v___x_854_, v___x_2599__boxed_858_, v_inst_856_, v_a_857_);
lean_dec(v___x_853_);
lean_dec_ref(v_s_852_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1(lean_object* v_s_860_, lean_object* v_inst_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(v_s_860_, v_a_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(lean_object* v_docString_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
if (lean_obj_tag(v_a_868_) == 0)
{
lean_object* v___x_870_; 
v___x_870_ = l_List_reverse___redArg(v_a_869_);
return v___x_870_;
}
else
{
lean_object* v_head_871_; lean_object* v_fst_872_; lean_object* v_tail_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_892_; 
v_head_871_ = lean_ctor_get(v_a_868_, 0);
lean_inc(v_head_871_);
v_fst_872_ = lean_ctor_get(v_head_871_, 0);
lean_inc(v_fst_872_);
v_tail_873_ = lean_ctor_get(v_a_868_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v_a_868_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_a_868_, 0);
lean_dec(v_unused_893_);
v___x_875_ = v_a_868_;
v_isShared_876_ = v_isSharedCheck_892_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_tail_873_);
lean_dec(v_a_868_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_892_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_snd_877_; lean_object* v_start_878_; lean_object* v_stop_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v_snd_877_ = lean_ctor_get(v_head_871_, 1);
lean_inc(v_snd_877_);
lean_dec(v_head_871_);
v_start_878_ = lean_ctor_get(v_fst_872_, 0);
lean_inc(v_start_878_);
v_stop_879_ = lean_ctor_get(v_fst_872_, 1);
lean_inc(v_stop_879_);
lean_dec(v_fst_872_);
v___x_880_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0));
v___x_881_ = lean_string_utf8_extract(v_docString_867_, v_start_878_, v_stop_879_);
lean_dec(v_stop_879_);
lean_dec(v_start_878_);
v___x_882_ = lean_string_append(v___x_880_, v___x_881_);
lean_dec_ref(v___x_881_);
v___x_883_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1));
v___x_884_ = lean_string_append(v___x_882_, v___x_883_);
v___x_885_ = lean_string_append(v___x_884_, v_snd_877_);
lean_dec(v_snd_877_);
v___x_886_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_887_ = lean_string_append(v___x_885_, v___x_886_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v_a_869_);
lean_ctor_set(v___x_875_, 0, v___x_887_);
v___x_889_ = v___x_875_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_a_869_);
v___x_889_ = v_reuseFailAlloc_891_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
v_a_868_ = v_tail_873_;
v_a_869_ = v___x_889_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___boxed(lean_object* v_docString_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_894_, v_a_895_, v_a_896_);
lean_dec_ref(v_docString_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
if (lean_obj_tag(v_x_899_) == 0)
{
return v_x_898_;
}
else
{
lean_object* v_head_900_; lean_object* v_tail_901_; lean_object* v___x_902_; 
v_head_900_ = lean_ctor_get(v_x_899_, 0);
v_tail_901_ = lean_ctor_get(v_x_899_, 1);
v___x_902_ = lean_string_append(v_x_898_, v_head_900_);
v_x_898_ = v___x_902_;
v_x_899_ = v_tail_901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1___boxed(lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v_x_904_, v_x_905_);
lean_dec(v_x_905_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks(lean_object* v_docString_908_){
_start:
{
lean_object* v___x_910_; lean_object* v_fst_911_; lean_object* v_snd_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
lean_inc_ref(v_docString_908_);
v___x_910_ = l_Lean_rewriteManualLinksCore(v_docString_908_);
v_fst_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_fst_911_);
v_snd_912_ = lean_ctor_get(v___x_910_, 1);
lean_inc(v_snd_912_);
lean_dec_ref(v___x_910_);
v___x_913_ = lean_array_get_size(v_fst_911_);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = lean_nat_dec_eq(v___x_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_916_ = ((lean_object*)(l_Lean_rewriteManualLinks___closed__0));
v___x_917_ = lean_array_to_list(v_fst_911_);
v___x_918_ = lean_box(0);
v___x_919_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_908_, v___x_917_, v___x_918_);
lean_dec_ref(v_docString_908_);
v___x_920_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_921_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_920_, v___x_919_);
lean_dec(v___x_919_);
v___x_922_ = lean_string_append(v___x_916_, v___x_921_);
lean_dec_ref(v___x_921_);
v___x_923_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_924_ = lean_string_append(v_snd_912_, v___x_923_);
v___x_925_ = lean_string_append(v___x_924_, v___x_922_);
lean_dec_ref(v___x_922_);
return v___x_925_;
}
else
{
lean_dec(v_fst_911_);
lean_dec_ref(v_docString_908_);
return v_snd_912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks___boxed(lean_object* v_docString_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_rewriteManualLinks(v_docString_926_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(lean_object* v_docString_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
if (lean_obj_tag(v_a_933_) == 0)
{
lean_object* v___x_935_; 
v___x_935_ = l_List_reverse___redArg(v_a_934_);
return v___x_935_;
}
else
{
lean_object* v_head_936_; lean_object* v_fst_937_; lean_object* v_tail_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_962_; 
v_head_936_ = lean_ctor_get(v_a_933_, 0);
lean_inc(v_head_936_);
v_fst_937_ = lean_ctor_get(v_head_936_, 0);
lean_inc(v_fst_937_);
v_tail_938_ = lean_ctor_get(v_a_933_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_a_933_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_a_933_, 0);
lean_dec(v_unused_963_);
v___x_940_ = v_a_933_;
v_isShared_941_ = v_isSharedCheck_962_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_tail_938_);
lean_dec(v_a_933_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_962_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_snd_942_; lean_object* v_start_943_; lean_object* v_stop_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v_snd_942_ = lean_ctor_get(v_head_936_, 1);
lean_inc(v_snd_942_);
lean_dec(v_head_936_);
v_start_943_ = lean_ctor_get(v_fst_937_, 0);
lean_inc(v_start_943_);
v_stop_944_ = lean_ctor_get(v_fst_937_, 1);
lean_inc(v_stop_944_);
lean_dec(v_fst_937_);
v___x_945_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0));
v___x_946_ = lean_string_utf8_extract(v_docString_932_, v_start_943_, v_stop_944_);
lean_dec(v_stop_944_);
lean_dec(v_start_943_);
v___x_947_ = l_String_quote(v___x_946_);
v___x_948_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
v___x_949_ = l_Std_Format_defWidth;
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = l_Std_Format_pretty(v___x_948_, v___x_949_, v___x_950_, v___x_950_);
v___x_952_ = lean_string_append(v___x_945_, v___x_951_);
lean_dec_ref(v___x_951_);
v___x_953_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1));
v___x_954_ = lean_string_append(v___x_952_, v___x_953_);
v___x_955_ = lean_string_append(v___x_954_, v_snd_942_);
lean_dec(v_snd_942_);
v___x_956_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2));
v___x_957_ = lean_string_append(v___x_955_, v___x_956_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v_a_934_);
lean_ctor_set(v___x_940_, 0, v___x_957_);
v___x_959_ = v___x_940_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_a_934_);
v___x_959_ = v_reuseFailAlloc_961_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
v_a_933_ = v_tail_938_;
v_a_934_ = v___x_959_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___boxed(lean_object* v_docString_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_964_, v_a_965_, v_a_966_);
lean_dec_ref(v_docString_964_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString(lean_object* v_docString_969_){
_start:
{
lean_object* v___x_971_; lean_object* v_fst_972_; lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
lean_inc_ref(v_docString_969_);
v___x_971_ = l_Lean_rewriteManualLinksCore(v_docString_969_);
v_fst_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_fst_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = lean_array_get_size(v_fst_972_);
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = lean_nat_dec_eq(v___x_973_, v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_976_ = ((lean_object*)(l_Lean_validateBuiltinDocString___closed__0));
v___x_977_ = lean_array_to_list(v_fst_972_);
v___x_978_ = lean_box(0);
v___x_979_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_969_, v___x_977_, v___x_978_);
lean_dec_ref(v_docString_969_);
v___x_980_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_981_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_980_, v___x_979_);
lean_dec(v___x_979_);
v___x_982_ = lean_string_append(v___x_976_, v___x_981_);
lean_dec_ref(v___x_981_);
v___x_983_ = lean_mk_io_user_error(v___x_982_);
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; 
lean_dec(v_fst_972_);
lean_dec_ref(v_docString_969_);
v___x_985_ = lean_box(0);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString___boxed(lean_object* v_docString_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_validateBuiltinDocString(v_docString_987_);
return v_res_989_;
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
