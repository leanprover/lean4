// Lean compiler output
// Module: Lean.DocString.Links
// Imports: public import Lean.Syntax import Init.Data.String.TakeDrop import Init.Data.String.Search import Init.Data.ToString.Macro import Init.While
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
uint8_t l_String_Pos_Raw_substrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_lookingAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_lookingAt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__0(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lean-manual://"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__1___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__1(lean_object*, lean_object*);
static const lean_array_object l_Lean_rewriteManualLinksCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_rewriteManualLinksCore___closed__0 = (const lean_object*)&l_Lean_rewriteManualLinksCore___closed__0_value;
static const lean_ctor_object l_Lean_rewriteManualLinksCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_rewriteManualLinksCore___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_rewriteManualLinksCore___closed__1 = (const lean_object*)&l_Lean_rewriteManualLinksCore___closed__1_value;
static const lean_ctor_object l_Lean_rewriteManualLinksCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Links_0__Lean_rw___closed__7_value),((lean_object*)&l_Lean_rewriteManualLinksCore___closed__1_value)}};
static const lean_object* l_Lean_rewriteManualLinksCore___closed__2 = (const lean_object*)&l_Lean_rewriteManualLinksCore___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore(lean_object*);
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
lean_dec_ref(v___x_24_);
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
v___x_21_ = lean_string_append(v___y_19_, v___y_20_);
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
v___y_19_ = v_r_26_;
v___y_20_ = v___x_27_;
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
v___y_19_ = v_r_26_;
v___y_20_ = v___x_27_;
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
lean_inc(v_head_170_);
v_tail_171_ = lean_ctor_get(v_as_x27_168_, 1);
lean_inc(v_tail_171_);
lean_dec_ref(v_as_x27_168_);
v_fst_172_ = lean_ctor_get(v_head_170_, 0);
lean_inc(v_fst_172_);
v_snd_173_ = lean_ctor_get(v_head_170_, 1);
lean_inc(v_snd_173_);
lean_dec(v_head_170_);
v_r_174_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_b_169_, v_fst_172_, v_snd_173_);
v_as_x27_168_ = v_tail_171_;
v_b_169_ = v_r_174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(lean_object* v_m_176_, lean_object* v_l_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_l_177_, v_m_176_);
return v___x_178_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_box(0);
v___x_195_ = lean_unsigned_to_nat(16u);
v___x_196_ = lean_mk_array(v___x_195_, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7);
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8);
v___x_201_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__6));
v___x_202_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v___x_201_, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap(void){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0(lean_object* v_00_u03b2_204_, lean_object* v_m_205_, lean_object* v_a_206_, lean_object* v_b_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_m_205_, v_a_206_, v_b_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(lean_object* v_as_209_, lean_object* v_as_x27_210_, lean_object* v_b_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_as_x27_210_, v_b_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___boxed(lean_object* v_as_214_, lean_object* v_as_x27_215_, lean_object* v_b_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(v_as_214_, v_as_x27_215_, v_b_216_, v_a_217_);
lean_dec(v_as_214_);
return v_res_218_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_219_, lean_object* v_a_220_, lean_object* v_x_221_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_220_, v_x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_223_, lean_object* v_a_224_, lean_object* v_x_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(v_00_u03b2_223_, v_a_224_, v_x_225_);
lean_dec(v_x_225_);
lean_dec_ref(v_a_224_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_228_, lean_object* v_data_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(v_data_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_231_, lean_object* v_a_232_, lean_object* v_b_233_, lean_object* v_x_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_232_, v_b_233_, v_x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_236_, lean_object* v_i_237_, lean_object* v_source_238_, lean_object* v_target_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_237_, v_source_238_, v_target_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_242_, v_x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
lean_inc(v_x_245_);
return v_x_245_;
}
else
{
lean_object* v_key_247_; lean_object* v_tail_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_key_247_ = lean_ctor_get(v_x_246_, 0);
v_tail_248_ = lean_ctor_get(v_x_246_, 2);
v___x_249_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_x_245_, v_tail_248_);
lean_inc(v_key_247_);
v___x_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_250_, 0, v_key_247_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0___boxed(lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_x_251_, v_x_252_);
lean_dec(v_x_252_);
lean_dec(v_x_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(lean_object* v_as_254_, size_t v_i_255_, size_t v_stop_256_, lean_object* v_b_257_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = lean_usize_dec_eq(v_i_255_, v_stop_256_);
if (v___x_258_ == 0)
{
size_t v___x_259_; size_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_259_ = ((size_t)1ULL);
v___x_260_ = lean_usize_sub(v_i_255_, v___x_259_);
v___x_261_ = lean_array_uget_borrowed(v_as_254_, v___x_260_);
v___x_262_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_b_257_, v___x_261_);
lean_dec(v_b_257_);
v_i_255_ = v___x_260_;
v_b_257_ = v___x_262_;
goto _start;
}
else
{
return v_b_257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1___boxed(lean_object* v_as_264_, lean_object* v_i_265_, lean_object* v_stop_266_, lean_object* v_b_267_){
_start:
{
size_t v_i_boxed_268_; size_t v_stop_boxed_269_; lean_object* v_res_270_; 
v_i_boxed_268_ = lean_unbox_usize(v_i_265_);
lean_dec(v_i_265_);
v_stop_boxed_269_ = lean_unbox_usize(v_stop_266_);
lean_dec(v_stop_266_);
v_res_270_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(v_as_264_, v_i_boxed_268_, v_stop_boxed_269_, v_b_267_);
lean_dec_ref(v_as_264_);
return v_res_270_;
}
}
static lean_object* _init_l_Lean_manualDomains(void){
_start:
{
lean_object* v___x_271_; lean_object* v_buckets_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_271_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v_buckets_272_ = lean_ctor_get(v___x_271_, 1);
v___x_273_ = lean_box(0);
v___x_274_ = lean_array_get_size(v_buckets_272_);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_nat_dec_lt(v___x_275_, v___x_274_);
if (v___x_276_ == 0)
{
return v___x_273_;
}
else
{
size_t v___x_277_; size_t v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_usize_of_nat(v___x_274_);
v___x_278_ = ((size_t)0ULL);
v___x_279_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(v_buckets_272_, v___x_277_, v___x_278_, v___x_273_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(lean_object* v_a_280_, lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v___x_282_; 
v___x_282_ = lean_box(0);
return v___x_282_;
}
else
{
lean_object* v_key_283_; lean_object* v_value_284_; lean_object* v_tail_285_; uint8_t v___x_286_; 
v_key_283_ = lean_ctor_get(v_x_281_, 0);
v_value_284_ = lean_ctor_get(v_x_281_, 1);
v_tail_285_ = lean_ctor_get(v_x_281_, 2);
v___x_286_ = lean_string_dec_eq(v_key_283_, v_a_280_);
if (v___x_286_ == 0)
{
v_x_281_ = v_tail_285_;
goto _start;
}
else
{
lean_object* v___x_288_; 
lean_inc(v_value_284_);
v___x_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_288_, 0, v_value_284_);
return v___x_288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg___boxed(lean_object* v_a_289_, lean_object* v_x_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_289_, v_x_290_);
lean_dec(v_x_290_);
lean_dec_ref(v_a_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(lean_object* v_m_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_buckets_294_; lean_object* v___x_295_; uint64_t v___x_296_; uint64_t v___x_297_; uint64_t v___x_298_; uint64_t v_fold_299_; uint64_t v___x_300_; uint64_t v___x_301_; uint64_t v___x_302_; size_t v___x_303_; size_t v___x_304_; size_t v___x_305_; size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_buckets_294_ = lean_ctor_get(v_m_292_, 1);
v___x_295_ = lean_array_get_size(v_buckets_294_);
v___x_296_ = lean_string_hash(v_a_293_);
v___x_297_ = 32ULL;
v___x_298_ = lean_uint64_shift_right(v___x_296_, v___x_297_);
v_fold_299_ = lean_uint64_xor(v___x_296_, v___x_298_);
v___x_300_ = 16ULL;
v___x_301_ = lean_uint64_shift_right(v_fold_299_, v___x_300_);
v___x_302_ = lean_uint64_xor(v_fold_299_, v___x_301_);
v___x_303_ = lean_uint64_to_usize(v___x_302_);
v___x_304_ = lean_usize_of_nat(v___x_295_);
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_sub(v___x_304_, v___x_305_);
v___x_307_ = lean_usize_land(v___x_303_, v___x_306_);
v___x_308_ = lean_array_uget_borrowed(v_buckets_294_, v___x_307_);
v___x_309_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_293_, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg___boxed(lean_object* v_m_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v_m_310_, v_a_311_);
lean_dec_ref(v_a_311_);
lean_dec_ref(v_m_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
lean_inc(v_x_313_);
return v_x_313_;
}
else
{
lean_object* v_key_315_; lean_object* v_value_316_; lean_object* v_tail_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_key_315_ = lean_ctor_get(v_x_314_, 0);
v_value_316_ = lean_ctor_get(v_x_314_, 1);
v_tail_317_ = lean_ctor_get(v_x_314_, 2);
v___x_318_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_x_313_, v_tail_317_);
lean_inc(v_value_316_);
lean_inc(v_key_315_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_key_315_);
lean_ctor_set(v___x_319_, 1, v_value_316_);
v___x_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2___boxed(lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_x_321_, v_x_322_);
lean_dec(v_x_322_);
lean_dec(v_x_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(lean_object* v_as_324_, size_t v_i_325_, size_t v_stop_326_, lean_object* v_b_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_usize_dec_eq(v_i_325_, v_stop_326_);
if (v___x_328_ == 0)
{
size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = ((size_t)1ULL);
v___x_330_ = lean_usize_sub(v_i_325_, v___x_329_);
v___x_331_ = lean_array_uget_borrowed(v_as_324_, v___x_330_);
v___x_332_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_b_327_, v___x_331_);
lean_dec(v_b_327_);
v_i_325_ = v___x_330_;
v_b_327_ = v___x_332_;
goto _start;
}
else
{
return v_b_327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3___boxed(lean_object* v_as_334_, lean_object* v_i_335_, lean_object* v_stop_336_, lean_object* v_b_337_){
_start:
{
size_t v_i_boxed_338_; size_t v_stop_boxed_339_; lean_object* v_res_340_; 
v_i_boxed_338_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_stop_boxed_339_ = lean_unbox_usize(v_stop_336_);
lean_dec(v_stop_336_);
v_res_340_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_as_334_, v_i_boxed_338_, v_stop_boxed_339_, v_b_337_);
lean_dec_ref(v_as_334_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_manualLink_spec__1(lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
if (lean_obj_tag(v_a_342_) == 0)
{
lean_object* v___x_344_; 
v___x_344_ = l_List_reverse___redArg(v_a_343_);
return v___x_344_;
}
else
{
lean_object* v_head_345_; lean_object* v_tail_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_358_; 
v_head_345_ = lean_ctor_get(v_a_342_, 0);
v_tail_346_ = lean_ctor_get(v_a_342_, 1);
v_isSharedCheck_358_ = !lean_is_exclusive(v_a_342_);
if (v_isSharedCheck_358_ == 0)
{
v___x_348_ = v_a_342_;
v_isShared_349_ = v_isSharedCheck_358_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_tail_346_);
lean_inc(v_head_345_);
lean_dec(v_a_342_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_358_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v_fst_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v_fst_350_ = lean_ctor_get(v_head_345_, 0);
lean_inc(v_fst_350_);
lean_dec(v_head_345_);
v___x_351_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_manualLink_spec__1___closed__0));
v___x_352_ = lean_string_append(v___x_351_, v_fst_350_);
lean_dec(v_fst_350_);
v___x_353_ = lean_string_append(v___x_352_, v___x_351_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v_a_343_);
lean_ctor_set(v___x_348_, 0, v___x_353_);
v___x_355_ = v___x_348_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_a_343_);
v___x_355_ = v_reuseFailAlloc_357_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
v_a_342_ = v_tail_346_;
v_a_343_ = v___x_355_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_manualLink(lean_object* v_kind_364_, lean_object* v_name_365_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_366_, v_kind_364_);
if (lean_obj_tag(v___x_367_) == 1)
{
lean_object* v_val_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_382_; 
v_val_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_382_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_382_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_val_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_382_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_372_ = l_Lean_manualRoot;
v___x_373_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_374_ = lean_string_append(v___x_373_, v_val_368_);
lean_dec(v_val_368_);
v___x_375_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_376_ = lean_string_append(v___x_374_, v___x_375_);
v___x_377_ = lean_string_append(v___x_376_, v_name_365_);
v___x_378_ = lean_string_append(v___x_372_, v___x_377_);
lean_dec_ref(v___x_377_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_378_);
v___x_380_ = v___x_370_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
else
{
lean_object* v_buckets_383_; lean_object* v___x_384_; lean_object* v___y_386_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
lean_dec(v___x_367_);
v_buckets_383_ = lean_ctor_get(v___x_366_, 1);
v___x_384_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_396_ = lean_box(0);
v___x_397_ = lean_array_get_size(v_buckets_383_);
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_nat_dec_lt(v___x_398_, v___x_397_);
if (v___x_399_ == 0)
{
v___y_386_ = v___x_396_;
goto v___jp_385_;
}
else
{
size_t v___x_400_; size_t v___x_401_; lean_object* v___x_402_; 
v___x_400_ = lean_usize_of_nat(v___x_397_);
v___x_401_ = ((size_t)0ULL);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_383_, v___x_400_, v___x_401_, v___x_396_);
v___y_386_ = v___x_402_;
goto v___jp_385_;
}
v___jp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v_acceptableKinds_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_387_ = lean_box(0);
v___x_388_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_386_, v___x_387_);
v_acceptableKinds_389_ = l_String_intercalate(v___x_384_, v___x_388_);
v___x_390_ = ((lean_object*)(l_Lean_manualLink___closed__3));
v___x_391_ = lean_string_append(v___x_390_, v_kind_364_);
v___x_392_ = ((lean_object*)(l_Lean_manualLink___closed__4));
v___x_393_ = lean_string_append(v___x_391_, v___x_392_);
v___x_394_ = lean_string_append(v___x_393_, v_acceptableKinds_389_);
lean_dec_ref(v_acceptableKinds_389_);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_manualLink___boxed(lean_object* v_kind_403_, lean_object* v_name_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_manualLink(v_kind_403_, v_name_404_);
lean_dec_ref(v_name_404_);
lean_dec_ref(v_kind_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(lean_object* v_00_u03b2_406_, lean_object* v_m_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v_m_407_, v_a_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___boxed(lean_object* v_00_u03b2_410_, lean_object* v_m_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(v_00_u03b2_410_, v_m_411_, v_a_412_);
lean_dec_ref(v_a_412_);
lean_dec_ref(v_m_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(lean_object* v_00_u03b2_414_, lean_object* v_a_415_, lean_object* v_x_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_415_, v_x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___boxed(lean_object* v_00_u03b2_418_, lean_object* v_a_419_, lean_object* v_x_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(v_00_u03b2_418_, v_a_419_, v_x_420_);
lean_dec(v_x_420_);
lean_dec_ref(v_a_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(lean_object* v_s_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0));
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___boxed(lean_object* v_s_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(v_s_426_);
lean_dec_ref(v_s_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(lean_object* v_path_428_, lean_object* v___x_429_, lean_object* v___x_430_, lean_object* v_a_431_, lean_object* v_b_432_){
_start:
{
lean_object* v_it_434_; lean_object* v_startInclusive_435_; lean_object* v_endExclusive_436_; 
if (lean_obj_tag(v_a_431_) == 0)
{
lean_object* v_currPos_441_; lean_object* v_searcher_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_468_; 
v_currPos_441_ = lean_ctor_get(v_a_431_, 0);
v_searcher_442_ = lean_ctor_get(v_a_431_, 1);
v_isSharedCheck_468_ = !lean_is_exclusive(v_a_431_);
if (v_isSharedCheck_468_ == 0)
{
v___x_444_ = v_a_431_;
v_isShared_445_ = v_isSharedCheck_468_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_searcher_442_);
lean_inc(v_currPos_441_);
lean_dec(v_a_431_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_468_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_startInclusive_446_; lean_object* v_endExclusive_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_startInclusive_446_ = lean_ctor_get(v___x_429_, 1);
v_endExclusive_447_ = lean_ctor_get(v___x_429_, 2);
v___x_448_ = lean_nat_sub(v_endExclusive_447_, v_startInclusive_446_);
v___x_449_ = lean_nat_dec_eq(v_searcher_442_, v___x_448_);
lean_dec(v___x_448_);
if (v___x_449_ == 0)
{
uint32_t v___x_450_; uint32_t v___x_451_; uint8_t v___x_452_; 
v___x_450_ = 47;
v___x_451_ = lean_string_utf8_get_fast(v_path_428_, v_searcher_442_);
v___x_452_ = lean_uint32_dec_eq(v___x_451_, v___x_450_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = lean_string_utf8_next_fast(v_path_428_, v_searcher_442_);
lean_dec(v_searcher_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_453_);
v___x_455_ = v___x_444_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_currPos_441_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_453_);
v___x_455_ = v_reuseFailAlloc_457_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
v_a_431_ = v___x_455_;
goto _start;
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v_slice_461_; lean_object* v_nextIt_463_; 
v___x_458_ = lean_string_utf8_next_fast(v_path_428_, v_searcher_442_);
v___x_459_ = lean_nat_sub(v___x_458_, v_searcher_442_);
v___x_460_ = lean_nat_add(v_searcher_442_, v___x_459_);
lean_dec(v___x_459_);
v_slice_461_ = l_String_Slice_subslice_x21(v___x_429_, v_currPos_441_, v_searcher_442_);
lean_inc(v___x_460_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_460_);
lean_ctor_set(v___x_444_, 0, v___x_460_);
v_nextIt_463_ = v___x_444_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_460_);
v_nextIt_463_ = v_reuseFailAlloc_466_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v_startInclusive_464_; lean_object* v_endExclusive_465_; 
v_startInclusive_464_ = lean_ctor_get(v_slice_461_, 0);
lean_inc(v_startInclusive_464_);
v_endExclusive_465_ = lean_ctor_get(v_slice_461_, 1);
lean_inc(v_endExclusive_465_);
lean_dec_ref(v_slice_461_);
v_it_434_ = v_nextIt_463_;
v_startInclusive_435_ = v_startInclusive_464_;
v_endExclusive_436_ = v_endExclusive_465_;
goto v___jp_433_;
}
}
}
else
{
lean_object* v___x_467_; 
lean_del_object(v___x_444_);
lean_dec(v_searcher_442_);
v___x_467_ = lean_box(1);
lean_inc(v___x_430_);
v_it_434_ = v___x_467_;
v_startInclusive_435_ = v_currPos_441_;
v_endExclusive_436_ = v___x_430_;
goto v___jp_433_;
}
}
}
else
{
lean_dec(v___x_430_);
lean_dec_ref(v_path_428_);
return v_b_432_;
}
v___jp_433_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
lean_inc_ref(v_path_428_);
v___x_437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_437_, 0, v_path_428_);
lean_ctor_set(v___x_437_, 1, v_startInclusive_435_);
lean_ctor_set(v___x_437_, 2, v_endExclusive_436_);
v___x_438_ = l_String_Slice_toString(v___x_437_);
lean_dec_ref(v___x_437_);
v___x_439_ = lean_array_push(v_b_432_, v___x_438_);
v_a_431_ = v_it_434_;
v_b_432_ = v___x_439_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg___boxed(lean_object* v_path_469_, lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v_a_472_, lean_object* v_b_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_469_, v___x_470_, v___x_471_, v_a_472_, v_b_473_);
lean_dec_ref(v___x_470_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
return v_x_475_;
}
else
{
lean_object* v_head_477_; lean_object* v_tail_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_head_477_ = lean_ctor_get(v_x_476_, 0);
v_tail_478_ = lean_ctor_get(v_x_476_, 1);
v___x_479_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_480_ = lean_string_append(v_x_475_, v___x_479_);
v___x_481_ = lean_string_append(v___x_480_, v_head_477_);
v_x_475_ = v___x_481_;
v_x_476_ = v_tail_478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0___boxed(lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v_x_483_, v_x_484_);
lean_dec(v_x_484_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(lean_object* v_x_489_){
_start:
{
if (lean_obj_tag(v_x_489_) == 0)
{
lean_object* v___x_490_; 
v___x_490_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0));
return v___x_490_;
}
else
{
lean_object* v_tail_491_; 
v_tail_491_ = lean_ctor_get(v_x_489_, 1);
if (lean_obj_tag(v_tail_491_) == 0)
{
lean_object* v_head_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_head_492_ = lean_ctor_get(v_x_489_, 0);
v___x_493_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_494_ = lean_string_append(v___x_493_, v_head_492_);
v___x_495_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2));
v___x_496_ = lean_string_append(v___x_494_, v___x_495_);
return v___x_496_;
}
else
{
lean_object* v_head_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint32_t v___x_501_; lean_object* v___x_502_; 
v_head_497_ = lean_ctor_get(v_x_489_, 0);
v___x_498_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_499_ = lean_string_append(v___x_498_, v_head_497_);
v___x_500_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v___x_499_, v_tail_491_);
v___x_501_ = 93;
v___x_502_ = lean_string_push(v___x_500_, v___x_501_);
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___boxed(lean_object* v_x_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v_x_503_);
lean_dec(v_x_503_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rw(lean_object* v_path_515_){
_start:
{
lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_string_utf8_byte_size(v_path_515_);
lean_inc_ref(v_path_515_);
v___x_543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_543_, 0, v_path_515_);
lean_ctor_set(v___x_543_, 1, v___x_541_);
lean_ctor_set(v___x_543_, 2, v___x_542_);
v___x_544_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(v___x_543_);
v___x_545_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__4));
v___x_546_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_515_, v___x_543_, v___x_542_, v___x_544_, v___x_545_);
lean_dec_ref(v___x_543_);
v___x_547_ = lean_array_to_list(v___x_546_);
if (lean_obj_tag(v___x_547_) == 0)
{
goto v___jp_539_;
}
else
{
lean_object* v_head_548_; lean_object* v_tail_549_; lean_object* v_kind_551_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_head_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_head_548_);
v_tail_549_ = lean_ctor_get(v___x_547_, 1);
lean_inc(v_tail_549_);
lean_dec_ref(v___x_547_);
v___x_586_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_587_ = lean_string_dec_eq(v_head_548_, v___x_586_);
if (v___x_587_ == 0)
{
v_kind_551_ = v_head_548_;
goto v___jp_550_;
}
else
{
lean_dec(v_head_548_);
if (lean_obj_tag(v_tail_549_) == 0)
{
goto v___jp_539_;
}
else
{
v_kind_551_ = v___x_586_;
goto v___jp_550_;
}
}
v___jp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_552_, v_kind_551_);
if (lean_obj_tag(v___x_553_) == 1)
{
if (lean_obj_tag(v_tail_549_) == 1)
{
lean_object* v_tail_554_; 
v_tail_554_ = lean_ctor_get(v_tail_549_, 1);
if (lean_obj_tag(v_tail_554_) == 0)
{
lean_object* v_val_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_577_; 
v_val_555_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_577_ == 0)
{
v___x_557_ = v___x_553_;
v_isShared_558_ = v_isSharedCheck_577_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_val_555_);
lean_dec(v___x_553_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_577_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_head_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_head_559_ = lean_ctor_get(v_tail_549_, 0);
lean_inc(v_head_559_);
lean_dec_ref(v_tail_549_);
v___x_560_ = lean_string_utf8_byte_size(v_head_559_);
v___x_561_ = lean_nat_dec_eq(v___x_560_, v___x_541_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
lean_dec_ref(v_kind_551_);
v___x_562_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_563_ = lean_string_append(v___x_562_, v_val_555_);
lean_dec(v_val_555_);
v___x_564_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_565_ = lean_string_append(v___x_563_, v___x_564_);
v___x_566_ = lean_string_append(v___x_565_, v_head_559_);
lean_dec(v_head_559_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_566_);
v___x_568_ = v___x_557_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
lean_dec(v_head_559_);
lean_dec(v_val_555_);
v___x_570_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__5));
v___x_571_ = lean_string_append(v___x_570_, v_kind_551_);
lean_dec_ref(v_kind_551_);
v___x_572_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__6));
v___x_573_ = lean_string_append(v___x_571_, v___x_572_);
if (v_isShared_558_ == 0)
{
lean_ctor_set_tag(v___x_557_, 0);
lean_ctor_set(v___x_557_, 0, v___x_573_);
v___x_575_ = v___x_557_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
else
{
lean_dec_ref(v___x_553_);
v___y_530_ = v_tail_549_;
v___y_531_ = v_kind_551_;
goto v___jp_529_;
}
}
else
{
lean_dec_ref(v___x_553_);
v___y_530_ = v_tail_549_;
v___y_531_ = v_kind_551_;
goto v___jp_529_;
}
}
else
{
lean_object* v_buckets_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
lean_dec(v___x_553_);
lean_dec(v_tail_549_);
v_buckets_578_ = lean_ctor_get(v___x_552_, 1);
v___x_579_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_580_ = lean_box(0);
v___x_581_ = lean_array_get_size(v_buckets_578_);
v___x_582_ = lean_nat_dec_lt(v___x_541_, v___x_581_);
if (v___x_582_ == 0)
{
v___y_517_ = v___x_579_;
v___y_518_ = v_kind_551_;
v___y_519_ = v___x_580_;
goto v___jp_516_;
}
else
{
size_t v___x_583_; size_t v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_usize_of_nat(v___x_581_);
v___x_584_ = ((size_t)0ULL);
v___x_585_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_578_, v___x_583_, v___x_584_, v___x_580_);
v___y_517_ = v___x_579_;
v___y_518_ = v_kind_551_;
v___y_519_ = v___x_585_;
goto v___jp_516_;
}
}
}
}
v___jp_516_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_acceptableKinds_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_520_ = lean_box(0);
v___x_521_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_519_, v___x_520_);
v_acceptableKinds_522_ = l_String_intercalate(v___y_517_, v___x_521_);
v___x_523_ = ((lean_object*)(l_Lean_manualLink___closed__3));
v___x_524_ = lean_string_append(v___x_523_, v___y_518_);
lean_dec_ref(v___y_518_);
v___x_525_ = ((lean_object*)(l_Lean_manualLink___closed__4));
v___x_526_ = lean_string_append(v___x_524_, v___x_525_);
v___x_527_ = lean_string_append(v___x_526_, v_acceptableKinds_522_);
lean_dec_ref(v_acceptableKinds_522_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
v___jp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_532_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__0));
v___x_533_ = lean_string_append(v___x_532_, v___y_531_);
lean_dec_ref(v___y_531_);
v___x_534_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__1));
v___x_535_ = lean_string_append(v___x_533_, v___x_534_);
v___x_536_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v___y_530_);
lean_dec(v___y_530_);
v___x_537_ = lean_string_append(v___x_535_, v___x_536_);
lean_dec_ref(v___x_536_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
v___jp_539_:
{
lean_object* v___x_540_; 
v___x_540_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__3));
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(lean_object* v_path_588_, lean_object* v___x_589_, lean_object* v___x_590_, lean_object* v_inst_591_, lean_object* v_R_592_, lean_object* v_a_593_, lean_object* v_b_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_588_, v___x_589_, v___x_590_, v_a_593_, v_b_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___boxed(lean_object* v_path_596_, lean_object* v___x_597_, lean_object* v___x_598_, lean_object* v_inst_599_, lean_object* v_R_600_, lean_object* v_a_601_, lean_object* v_b_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(v_path_596_, v___x_597_, v___x_598_, v_inst_599_, v_R_600_, v_a_601_, v_b_602_);
lean_dec_ref(v___x_597_);
return v_res_603_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(uint32_t v_c_604_){
_start:
{
uint8_t v___y_606_; uint8_t v___y_648_; uint32_t v___x_658_; uint8_t v___x_659_; 
v___x_658_ = 65;
v___x_659_ = lean_uint32_dec_le(v___x_658_, v_c_604_);
if (v___x_659_ == 0)
{
goto v___jp_653_;
}
else
{
uint32_t v___x_660_; uint8_t v___x_661_; 
v___x_660_ = 90;
v___x_661_ = lean_uint32_dec_le(v_c_604_, v___x_660_);
if (v___x_661_ == 0)
{
goto v___jp_653_;
}
else
{
return v___x_661_;
}
}
v___jp_605_:
{
if (v___y_606_ == 0)
{
uint32_t v___x_607_; uint8_t v___x_608_; 
v___x_607_ = 45;
v___x_608_ = lean_uint32_dec_eq(v_c_604_, v___x_607_);
if (v___x_608_ == 0)
{
uint32_t v___x_609_; uint8_t v___x_610_; 
v___x_609_ = 46;
v___x_610_ = lean_uint32_dec_eq(v_c_604_, v___x_609_);
if (v___x_610_ == 0)
{
uint32_t v___x_611_; uint8_t v___x_612_; 
v___x_611_ = 95;
v___x_612_ = lean_uint32_dec_eq(v_c_604_, v___x_611_);
if (v___x_612_ == 0)
{
uint32_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = 126;
v___x_614_ = lean_uint32_dec_eq(v_c_604_, v___x_613_);
if (v___x_614_ == 0)
{
uint32_t v___x_615_; uint8_t v___x_616_; 
v___x_615_ = 58;
v___x_616_ = lean_uint32_dec_eq(v_c_604_, v___x_615_);
if (v___x_616_ == 0)
{
uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 47;
v___x_618_ = lean_uint32_dec_eq(v_c_604_, v___x_617_);
if (v___x_618_ == 0)
{
uint32_t v___x_619_; uint8_t v___x_620_; 
v___x_619_ = 63;
v___x_620_ = lean_uint32_dec_eq(v_c_604_, v___x_619_);
if (v___x_620_ == 0)
{
uint32_t v___x_621_; uint8_t v___x_622_; 
v___x_621_ = 35;
v___x_622_ = lean_uint32_dec_eq(v_c_604_, v___x_621_);
if (v___x_622_ == 0)
{
uint32_t v___x_623_; uint8_t v___x_624_; 
v___x_623_ = 91;
v___x_624_ = lean_uint32_dec_eq(v_c_604_, v___x_623_);
if (v___x_624_ == 0)
{
uint32_t v___x_625_; uint8_t v___x_626_; 
v___x_625_ = 93;
v___x_626_ = lean_uint32_dec_eq(v_c_604_, v___x_625_);
if (v___x_626_ == 0)
{
uint32_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = 64;
v___x_628_ = lean_uint32_dec_eq(v_c_604_, v___x_627_);
if (v___x_628_ == 0)
{
uint32_t v___x_629_; uint8_t v___x_630_; 
v___x_629_ = 33;
v___x_630_ = lean_uint32_dec_eq(v_c_604_, v___x_629_);
if (v___x_630_ == 0)
{
uint32_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 36;
v___x_632_ = lean_uint32_dec_eq(v_c_604_, v___x_631_);
if (v___x_632_ == 0)
{
uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 38;
v___x_634_ = lean_uint32_dec_eq(v_c_604_, v___x_633_);
if (v___x_634_ == 0)
{
uint32_t v___x_635_; uint8_t v___x_636_; 
v___x_635_ = 39;
v___x_636_ = lean_uint32_dec_eq(v_c_604_, v___x_635_);
if (v___x_636_ == 0)
{
uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = 42;
v___x_638_ = lean_uint32_dec_eq(v_c_604_, v___x_637_);
if (v___x_638_ == 0)
{
uint32_t v___x_639_; uint8_t v___x_640_; 
v___x_639_ = 43;
v___x_640_ = lean_uint32_dec_eq(v_c_604_, v___x_639_);
if (v___x_640_ == 0)
{
uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = 44;
v___x_642_ = lean_uint32_dec_eq(v_c_604_, v___x_641_);
if (v___x_642_ == 0)
{
uint32_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = 59;
v___x_644_ = lean_uint32_dec_eq(v_c_604_, v___x_643_);
if (v___x_644_ == 0)
{
uint32_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = 61;
v___x_646_ = lean_uint32_dec_eq(v_c_604_, v___x_645_);
return v___x_646_;
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
else
{
return v___x_608_;
}
}
else
{
return v___y_606_;
}
}
v___jp_647_:
{
if (v___y_648_ == 0)
{
uint32_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = 48;
v___x_650_ = lean_uint32_dec_le(v___x_649_, v_c_604_);
if (v___x_650_ == 0)
{
v___y_606_ = v___x_650_;
goto v___jp_605_;
}
else
{
uint32_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = 57;
v___x_652_ = lean_uint32_dec_le(v_c_604_, v___x_651_);
v___y_606_ = v___x_652_;
goto v___jp_605_;
}
}
else
{
return v___y_648_;
}
}
v___jp_653_:
{
uint32_t v___x_654_; uint8_t v___x_655_; 
v___x_654_ = 97;
v___x_655_ = lean_uint32_dec_le(v___x_654_, v_c_604_);
if (v___x_655_ == 0)
{
v___y_648_ = v___x_655_;
goto v___jp_647_;
}
else
{
uint32_t v___x_656_; uint8_t v___x_657_; 
v___x_656_ = 122;
v___x_657_ = lean_uint32_dec_le(v_c_604_, v___x_656_);
v___y_648_ = v___x_657_;
goto v___jp_647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar___boxed(lean_object* v_c_662_){
_start:
{
uint32_t v_c_boxed_663_; uint8_t v_res_664_; lean_object* v_r_665_; 
v_c_boxed_663_ = lean_unbox_uint32(v_c_662_);
lean_dec(v_c_662_);
v_res_664_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v_c_boxed_663_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_lookingAt(lean_object* v_goal_666_, lean_object* v_s_667_, lean_object* v_iter_668_){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_string_utf8_byte_size(v_goal_666_);
v___x_671_ = l_String_Pos_Raw_substrEq(v_s_667_, v_iter_668_, v_goal_666_, v___x_669_, v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_lookingAt___boxed(lean_object* v_goal_672_, lean_object* v_s_673_, lean_object* v_iter_674_){
_start:
{
uint8_t v_res_675_; lean_object* v_r_676_; 
v_res_675_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_lookingAt(v_goal_672_, v_s_673_, v_iter_674_);
lean_dec_ref(v_s_673_);
lean_dec_ref(v_goal_672_);
v_r_676_ = lean_box(v_res_675_);
return v_r_676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__0(lean_object* v_s_677_, lean_object* v_iter_x27_678_, lean_object* v_pre_679_, uint32_t v_c_680_, lean_object* v_b_681_){
_start:
{
lean_object* v_snd_682_; lean_object* v_snd_683_; lean_object* v_fst_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_752_; 
v_snd_682_ = lean_ctor_get(v_b_681_, 1);
lean_inc(v_snd_682_);
v_snd_683_ = lean_ctor_get(v_snd_682_, 1);
lean_inc(v_snd_683_);
v_fst_684_ = lean_ctor_get(v_b_681_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v_b_681_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v_b_681_, 1);
lean_dec(v_unused_753_);
v___x_686_ = v_b_681_;
v_isShared_687_ = v_isSharedCheck_752_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_fst_684_);
lean_dec(v_b_681_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_752_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_fst_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_750_; 
v_fst_688_ = lean_ctor_get(v_snd_682_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v_snd_682_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v_snd_682_, 1);
lean_dec(v_unused_751_);
v___x_690_ = v_snd_682_;
v_isShared_691_ = v_isSharedCheck_750_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_fst_688_);
lean_dec(v_snd_682_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_750_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_fst_692_; lean_object* v_snd_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_749_; 
v_fst_692_ = lean_ctor_get(v_snd_683_, 0);
v_snd_693_ = lean_ctor_get(v_snd_683_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v_snd_683_);
if (v_isSharedCheck_749_ == 0)
{
v___x_695_ = v_snd_683_;
v_isShared_696_ = v_isSharedCheck_749_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_snd_693_);
lean_inc(v_fst_692_);
lean_dec(v_snd_683_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_749_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = lean_string_utf8_byte_size(v_s_677_);
v___x_698_ = lean_nat_dec_eq(v_snd_693_, v___x_697_);
if (v___x_698_ == 0)
{
uint32_t v_c_x27_699_; lean_object* v_iter_700_; uint8_t v___y_733_; uint8_t v___x_738_; 
v_c_x27_699_ = lean_string_utf8_get_fast(v_s_677_, v_snd_693_);
v_iter_700_ = lean_string_utf8_next_fast(v_s_677_, v_snd_693_);
v___x_738_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v_c_x27_699_);
if (v___x_738_ == 0)
{
v___y_733_ = v___x_738_;
goto v___jp_732_;
}
else
{
uint8_t v___x_739_; 
v___x_739_ = lean_nat_dec_eq(v_iter_700_, v___x_697_);
if (v___x_739_ == 0)
{
v___y_733_ = v___x_738_;
goto v___jp_732_;
}
else
{
goto v___jp_701_;
}
}
v___jp_701_:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_string_utf8_extract(v_s_677_, v_iter_x27_678_, v_snd_693_);
v___x_703_ = l___private_Lean_DocString_Links_0__Lean_rw(v___x_702_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref(v___x_703_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_pre_679_);
lean_ctor_set(v___x_705_, 1, v_snd_693_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_a_704_);
lean_ctor_set(v___x_695_, 0, v___x_705_);
v___x_707_ = v___x_695_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_a_704_);
v___x_707_ = v_reuseFailAlloc_717_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v_errors_708_; lean_object* v_out_709_; lean_object* v___x_711_; 
v_errors_708_ = lean_array_push(v_fst_688_, v___x_707_);
v_out_709_ = lean_string_push(v_fst_684_, v_c_680_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v_iter_700_);
lean_ctor_set(v___x_690_, 0, v_fst_692_);
v___x_711_ = v___x_690_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_fst_692_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_iter_700_);
v___x_711_ = v_reuseFailAlloc_716_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_711_);
lean_ctor_set(v___x_686_, 0, v_errors_708_);
v___x_713_ = v___x_686_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_errors_708_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_715_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v_out_709_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
return v___x_714_;
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v_out_721_; lean_object* v_out_722_; lean_object* v___x_724_; 
lean_dec(v_snd_693_);
lean_dec(v_fst_692_);
lean_dec(v_pre_679_);
v_a_718_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_718_);
lean_dec_ref(v___x_703_);
v___x_719_ = l_Lean_manualRoot;
v___x_720_ = lean_string_append(v_fst_684_, v___x_719_);
v_out_721_ = lean_string_append(v___x_720_, v_a_718_);
lean_dec(v_a_718_);
v_out_722_ = lean_string_push(v_out_721_, v_c_x27_699_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_iter_700_);
lean_ctor_set(v___x_695_, 0, v_iter_700_);
v___x_724_ = v___x_695_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_iter_700_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_iter_700_);
v___x_724_ = v_reuseFailAlloc_731_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_726_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_724_);
v___x_726_ = v___x_690_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_fst_688_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_724_);
v___x_726_ = v_reuseFailAlloc_730_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_726_);
lean_ctor_set(v___x_686_, 0, v_out_722_);
v___x_728_ = v___x_686_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_out_722_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
v___jp_732_:
{
if (v___y_733_ == 0)
{
goto v___jp_701_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_del_object(v___x_695_);
lean_dec(v_snd_693_);
lean_del_object(v___x_690_);
lean_del_object(v___x_686_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v_fst_692_);
lean_ctor_set(v___x_734_, 1, v_iter_700_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v_fst_688_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v_fst_684_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v_b_681_ = v___x_736_;
goto _start;
}
}
}
else
{
lean_object* v___x_741_; 
lean_dec(v_pre_679_);
if (v_isShared_696_ == 0)
{
v___x_741_ = v___x_695_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_fst_692_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_snd_693_);
v___x_741_ = v_reuseFailAlloc_748_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_741_);
v___x_743_ = v___x_690_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_fst_688_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_741_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_743_);
v___x_745_ = v___x_686_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_fst_684_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__0___boxed(lean_object* v_s_754_, lean_object* v_iter_x27_755_, lean_object* v_pre_756_, lean_object* v_c_757_, lean_object* v_b_758_){
_start:
{
uint32_t v_c_boxed_759_; lean_object* v_res_760_; 
v_c_boxed_759_ = lean_unbox_uint32(v_c_757_);
lean_dec(v_c_757_);
v_res_760_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__0(v_s_754_, v_iter_x27_755_, v_pre_756_, v_c_boxed_759_, v_b_758_);
lean_dec(v_iter_x27_755_);
lean_dec_ref(v_s_754_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__1(lean_object* v_s_762_, lean_object* v_b_763_){
_start:
{
lean_object* v_snd_764_; lean_object* v_fst_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_829_; 
v_snd_764_ = lean_ctor_get(v_b_763_, 1);
v_fst_765_ = lean_ctor_get(v_b_763_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v_b_763_);
if (v_isSharedCheck_829_ == 0)
{
v___x_767_ = v_b_763_;
v_isShared_768_ = v_isSharedCheck_829_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_snd_764_);
lean_inc(v_fst_765_);
lean_dec(v_b_763_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_829_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_fst_769_; lean_object* v_snd_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_828_; 
v_fst_769_ = lean_ctor_get(v_snd_764_, 0);
v_snd_770_ = lean_ctor_get(v_snd_764_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_snd_764_);
if (v_isSharedCheck_828_ == 0)
{
v___x_772_ = v_snd_764_;
v_isShared_773_ = v_isSharedCheck_828_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_snd_770_);
lean_inc(v_fst_769_);
lean_dec(v_snd_764_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_828_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_string_utf8_byte_size(v_s_762_);
v___x_775_ = lean_nat_dec_eq(v_snd_770_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v_scheme_776_; uint32_t v_c_777_; lean_object* v_iter_778_; uint8_t v___x_779_; 
v_scheme_776_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__1___closed__0));
v_c_777_ = lean_string_utf8_get_fast(v_s_762_, v_snd_770_);
v_iter_778_ = lean_string_utf8_next_fast(v_s_762_, v_snd_770_);
lean_inc(v_snd_770_);
v___x_779_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_lookingAt(v_scheme_776_, v_s_762_, v_snd_770_);
if (v___x_779_ == 0)
{
lean_object* v_out_780_; lean_object* v___x_782_; 
lean_dec(v_snd_770_);
v_out_780_ = lean_string_push(v_fst_765_, v_c_777_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v_iter_778_);
v___x_782_ = v___x_772_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_fst_769_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_iter_778_);
v___x_782_ = v_reuseFailAlloc_787_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_784_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_782_);
lean_ctor_set(v___x_767_, 0, v_out_780_);
v___x_784_ = v___x_767_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_out_780_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_782_);
v___x_784_ = v_reuseFailAlloc_786_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
v_b_763_ = v___x_784_;
goto _start;
}
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v_iter_x27_791_; lean_object* v___x_793_; 
v___x_788_ = lean_unsigned_to_nat(14u);
v___x_789_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_762_);
v___x_790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_790_, 0, v_s_762_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
lean_ctor_set(v___x_790_, 2, v___x_774_);
lean_inc(v_snd_770_);
v_iter_x27_791_ = l_String_Slice_Pos_nextn(v___x_790_, v_snd_770_, v___x_788_);
lean_dec_ref(v___x_790_);
lean_inc(v_iter_x27_791_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v_iter_x27_791_);
lean_ctor_set(v___x_772_, 0, v_iter_778_);
v___x_793_ = v___x_772_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_iter_778_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_iter_x27_791_);
v___x_793_ = v_reuseFailAlloc_821_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_793_);
lean_ctor_set(v___x_767_, 0, v_fst_769_);
v___x_795_ = v___x_767_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_fst_769_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_793_);
v___x_795_ = v_reuseFailAlloc_820_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_snd_798_; lean_object* v_snd_799_; lean_object* v_fst_800_; lean_object* v_fst_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_818_; 
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_fst_765_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__0(v_s_762_, v_iter_x27_791_, v_snd_770_, v_c_777_, v___x_796_);
lean_dec(v_iter_x27_791_);
v_snd_798_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_snd_798_);
v_snd_799_ = lean_ctor_get(v_snd_798_, 1);
lean_inc(v_snd_799_);
v_fst_800_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_fst_800_);
lean_dec_ref(v___x_797_);
v_fst_801_ = lean_ctor_get(v_snd_798_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v_snd_798_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_snd_798_, 1);
lean_dec(v_unused_819_);
v___x_803_ = v_snd_798_;
v_isShared_804_ = v_isSharedCheck_818_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_fst_801_);
lean_dec(v_snd_798_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_818_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_fst_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_816_; 
v_fst_805_ = lean_ctor_get(v_snd_799_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v_snd_799_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v_snd_799_, 1);
lean_dec(v_unused_817_);
v___x_807_ = v_snd_799_;
v_isShared_808_ = v_isSharedCheck_816_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_fst_805_);
lean_dec(v_snd_799_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_816_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v_fst_805_);
lean_ctor_set(v___x_807_, 0, v_fst_801_);
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_fst_801_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_fst_805_);
v___x_810_ = v_reuseFailAlloc_815_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_812_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_810_);
lean_ctor_set(v___x_803_, 0, v_fst_800_);
v___x_812_ = v___x_803_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_fst_800_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_810_);
v___x_812_ = v_reuseFailAlloc_814_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v_b_763_ = v___x_812_;
goto _start;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_823_; 
lean_dec_ref(v_s_762_);
if (v_isShared_773_ == 0)
{
v___x_823_ = v___x_772_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_fst_769_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_snd_770_);
v___x_823_ = v_reuseFailAlloc_827_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_825_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_823_);
v___x_825_ = v___x_767_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_fst_765_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore(lean_object* v_s_838_){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v_snd_841_; lean_object* v_fst_842_; lean_object* v_fst_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v___x_839_ = ((lean_object*)(l_Lean_rewriteManualLinksCore___closed__2));
v___x_840_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__1(v_s_838_, v___x_839_);
v_snd_841_ = lean_ctor_get(v___x_840_, 1);
lean_inc(v_snd_841_);
v_fst_842_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_fst_842_);
lean_dec_ref(v___x_840_);
v_fst_843_ = lean_ctor_get(v_snd_841_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v_snd_841_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v_snd_841_, 1);
lean_dec(v_unused_851_);
v___x_845_ = v_snd_841_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_fst_843_);
lean_dec(v_snd_841_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v_fst_842_);
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_fst_843_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_fst_842_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(lean_object* v_docString_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
if (lean_obj_tag(v_a_856_) == 0)
{
lean_object* v___x_858_; 
v___x_858_ = l_List_reverse___redArg(v_a_857_);
return v___x_858_;
}
else
{
lean_object* v_head_859_; lean_object* v_fst_860_; lean_object* v_tail_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_880_; 
v_head_859_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_head_859_);
v_fst_860_ = lean_ctor_get(v_head_859_, 0);
lean_inc(v_fst_860_);
v_tail_861_ = lean_ctor_get(v_a_856_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v_a_856_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; 
v_unused_881_ = lean_ctor_get(v_a_856_, 0);
lean_dec(v_unused_881_);
v___x_863_ = v_a_856_;
v_isShared_864_ = v_isSharedCheck_880_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_tail_861_);
lean_dec(v_a_856_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_880_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_snd_865_; lean_object* v_start_866_; lean_object* v_stop_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v_snd_865_ = lean_ctor_get(v_head_859_, 1);
lean_inc(v_snd_865_);
lean_dec(v_head_859_);
v_start_866_ = lean_ctor_get(v_fst_860_, 0);
lean_inc(v_start_866_);
v_stop_867_ = lean_ctor_get(v_fst_860_, 1);
lean_inc(v_stop_867_);
lean_dec(v_fst_860_);
v___x_868_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0));
v___x_869_ = lean_string_utf8_extract(v_docString_855_, v_start_866_, v_stop_867_);
lean_dec(v_stop_867_);
lean_dec(v_start_866_);
v___x_870_ = lean_string_append(v___x_868_, v___x_869_);
lean_dec_ref(v___x_869_);
v___x_871_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1));
v___x_872_ = lean_string_append(v___x_870_, v___x_871_);
v___x_873_ = lean_string_append(v___x_872_, v_snd_865_);
lean_dec(v_snd_865_);
v___x_874_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_875_ = lean_string_append(v___x_873_, v___x_874_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v_a_857_);
lean_ctor_set(v___x_863_, 0, v___x_875_);
v___x_877_ = v___x_863_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_a_857_);
v___x_877_ = v_reuseFailAlloc_879_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
v_a_856_ = v_tail_861_;
v_a_857_ = v___x_877_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___boxed(lean_object* v_docString_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_882_, v_a_883_, v_a_884_);
lean_dec_ref(v_docString_882_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
if (lean_obj_tag(v_x_887_) == 0)
{
return v_x_886_;
}
else
{
lean_object* v_head_888_; lean_object* v_tail_889_; lean_object* v___x_890_; 
v_head_888_ = lean_ctor_get(v_x_887_, 0);
v_tail_889_ = lean_ctor_get(v_x_887_, 1);
v___x_890_ = lean_string_append(v_x_886_, v_head_888_);
v_x_886_ = v___x_890_;
v_x_887_ = v_tail_889_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1___boxed(lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v_x_892_, v_x_893_);
lean_dec(v_x_893_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks(lean_object* v_docString_896_){
_start:
{
lean_object* v___x_898_; lean_object* v_fst_899_; lean_object* v_snd_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
lean_inc_ref(v_docString_896_);
v___x_898_ = l_Lean_rewriteManualLinksCore(v_docString_896_);
v_fst_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_fst_899_);
v_snd_900_ = lean_ctor_get(v___x_898_, 1);
lean_inc(v_snd_900_);
lean_dec_ref(v___x_898_);
v___x_901_ = lean_array_get_size(v_fst_899_);
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_nat_dec_eq(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_904_ = ((lean_object*)(l_Lean_rewriteManualLinks___closed__0));
v___x_905_ = lean_array_to_list(v_fst_899_);
v___x_906_ = lean_box(0);
v___x_907_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_896_, v___x_905_, v___x_906_);
lean_dec_ref(v_docString_896_);
v___x_908_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_909_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_908_, v___x_907_);
lean_dec(v___x_907_);
v___x_910_ = lean_string_append(v___x_904_, v___x_909_);
lean_dec_ref(v___x_909_);
v___x_911_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_912_ = lean_string_append(v_snd_900_, v___x_911_);
v___x_913_ = lean_string_append(v___x_912_, v___x_910_);
lean_dec_ref(v___x_910_);
return v___x_913_;
}
else
{
lean_dec(v_fst_899_);
lean_dec_ref(v_docString_896_);
return v_snd_900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks___boxed(lean_object* v_docString_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_rewriteManualLinks(v_docString_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(lean_object* v_docString_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
if (lean_obj_tag(v_a_921_) == 0)
{
lean_object* v___x_923_; 
v___x_923_ = l_List_reverse___redArg(v_a_922_);
return v___x_923_;
}
else
{
lean_object* v_head_924_; lean_object* v_fst_925_; lean_object* v_tail_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_950_; 
v_head_924_ = lean_ctor_get(v_a_921_, 0);
lean_inc(v_head_924_);
v_fst_925_ = lean_ctor_get(v_head_924_, 0);
lean_inc(v_fst_925_);
v_tail_926_ = lean_ctor_get(v_a_921_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_a_921_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_a_921_, 0);
lean_dec(v_unused_951_);
v___x_928_ = v_a_921_;
v_isShared_929_ = v_isSharedCheck_950_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_tail_926_);
lean_dec(v_a_921_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_950_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_snd_930_; lean_object* v_start_931_; lean_object* v_stop_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
v_snd_930_ = lean_ctor_get(v_head_924_, 1);
lean_inc(v_snd_930_);
lean_dec(v_head_924_);
v_start_931_ = lean_ctor_get(v_fst_925_, 0);
lean_inc(v_start_931_);
v_stop_932_ = lean_ctor_get(v_fst_925_, 1);
lean_inc(v_stop_932_);
lean_dec(v_fst_925_);
v___x_933_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0));
v___x_934_ = lean_string_utf8_extract(v_docString_920_, v_start_931_, v_stop_932_);
lean_dec(v_stop_932_);
lean_dec(v_start_931_);
v___x_935_ = l_String_quote(v___x_934_);
v___x_936_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
v___x_937_ = l_Std_Format_defWidth;
v___x_938_ = lean_unsigned_to_nat(0u);
v___x_939_ = l_Std_Format_pretty(v___x_936_, v___x_937_, v___x_938_, v___x_938_);
v___x_940_ = lean_string_append(v___x_933_, v___x_939_);
lean_dec_ref(v___x_939_);
v___x_941_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1));
v___x_942_ = lean_string_append(v___x_940_, v___x_941_);
v___x_943_ = lean_string_append(v___x_942_, v_snd_930_);
lean_dec(v_snd_930_);
v___x_944_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2));
v___x_945_ = lean_string_append(v___x_943_, v___x_944_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 1, v_a_922_);
lean_ctor_set(v___x_928_, 0, v___x_945_);
v___x_947_ = v___x_928_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_a_922_);
v___x_947_ = v_reuseFailAlloc_949_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
v_a_921_ = v_tail_926_;
v_a_922_ = v___x_947_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___boxed(lean_object* v_docString_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_952_, v_a_953_, v_a_954_);
lean_dec_ref(v_docString_952_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString(lean_object* v_docString_957_){
_start:
{
lean_object* v___x_959_; lean_object* v_fst_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
lean_inc_ref(v_docString_957_);
v___x_959_ = l_Lean_rewriteManualLinksCore(v_docString_957_);
v_fst_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_fst_960_);
lean_dec_ref(v___x_959_);
v___x_961_ = lean_array_get_size(v_fst_960_);
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = lean_nat_dec_eq(v___x_961_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_964_ = ((lean_object*)(l_Lean_validateBuiltinDocString___closed__0));
v___x_965_ = lean_array_to_list(v_fst_960_);
v___x_966_ = lean_box(0);
v___x_967_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_957_, v___x_965_, v___x_966_);
lean_dec_ref(v_docString_957_);
v___x_968_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_969_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_968_, v___x_967_);
lean_dec(v___x_967_);
v___x_970_ = lean_string_append(v___x_964_, v___x_969_);
lean_dec_ref(v___x_969_);
v___x_971_ = lean_mk_io_user_error(v___x_970_);
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec(v_fst_960_);
lean_dec_ref(v_docString_957_);
v___x_973_ = lean_box(0);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString___boxed(lean_object* v_docString_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_validateBuiltinDocString(v_docString_975_);
return v_res_977_;
}
}
lean_object* runtime_initialize_Lean_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Links(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
