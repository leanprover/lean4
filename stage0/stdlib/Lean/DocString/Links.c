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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(lean_object* v_a_92_, lean_object* v_x_93_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_99_, lean_object* v_x_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_99_, v_x_100_);
lean_dec(v_x_100_);
lean_dec_ref(v_a_99_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(lean_object* v_a_103_, lean_object* v_b_104_, lean_object* v_x_105_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_dec(v_b_104_);
lean_dec_ref(v_a_103_);
return v_x_105_;
}
else
{
lean_object* v_key_106_; lean_object* v_value_107_; lean_object* v_tail_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_120_; 
v_key_106_ = lean_ctor_get(v_x_105_, 0);
v_value_107_ = lean_ctor_get(v_x_105_, 1);
v_tail_108_ = lean_ctor_get(v_x_105_, 2);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_105_);
if (v_isSharedCheck_120_ == 0)
{
v___x_110_ = v_x_105_;
v_isShared_111_ = v_isSharedCheck_120_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_tail_108_);
lean_inc(v_value_107_);
lean_inc(v_key_106_);
lean_dec(v_x_105_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_120_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
uint8_t v___x_112_; 
v___x_112_ = lean_string_dec_eq(v_key_106_, v_a_103_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_103_, v_b_104_, v_tail_108_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 2, v___x_113_);
v___x_115_ = v___x_110_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_key_106_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_value_107_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
else
{
lean_object* v___x_118_; 
lean_dec(v_value_107_);
lean_dec(v_key_106_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v_b_104_);
lean_ctor_set(v___x_110_, 0, v_a_103_);
v___x_118_ = v___x_110_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_103_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_b_104_);
lean_ctor_set(v_reuseFailAlloc_119_, 2, v_tail_108_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(lean_object* v_m_121_, lean_object* v_a_122_, lean_object* v_b_123_){
_start:
{
lean_object* v_size_124_; lean_object* v_buckets_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_168_; 
v_size_124_ = lean_ctor_get(v_m_121_, 0);
v_buckets_125_ = lean_ctor_get(v_m_121_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_m_121_);
if (v_isSharedCheck_168_ == 0)
{
v___x_127_ = v_m_121_;
v_isShared_128_ = v_isSharedCheck_168_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_buckets_125_);
lean_inc(v_size_124_);
lean_dec(v_m_121_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_168_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; uint64_t v_fold_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; size_t v___x_137_; size_t v___x_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; lean_object* v_bkt_142_; uint8_t v___x_143_; 
v___x_129_ = lean_array_get_size(v_buckets_125_);
v___x_130_ = lean_string_hash(v_a_122_);
v___x_131_ = 32ULL;
v___x_132_ = lean_uint64_shift_right(v___x_130_, v___x_131_);
v_fold_133_ = lean_uint64_xor(v___x_130_, v___x_132_);
v___x_134_ = 16ULL;
v___x_135_ = lean_uint64_shift_right(v_fold_133_, v___x_134_);
v___x_136_ = lean_uint64_xor(v_fold_133_, v___x_135_);
v___x_137_ = lean_uint64_to_usize(v___x_136_);
v___x_138_ = lean_usize_of_nat(v___x_129_);
v___x_139_ = ((size_t)1ULL);
v___x_140_ = lean_usize_sub(v___x_138_, v___x_139_);
v___x_141_ = lean_usize_land(v___x_137_, v___x_140_);
v_bkt_142_ = lean_array_uget_borrowed(v_buckets_125_, v___x_141_);
v___x_143_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_122_, v_bkt_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v_size_x27_145_; lean_object* v___x_146_; lean_object* v_buckets_x27_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v_size_x27_145_ = lean_nat_add(v_size_124_, v___x_144_);
lean_dec(v_size_124_);
lean_inc(v_bkt_142_);
v___x_146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_146_, 0, v_a_122_);
lean_ctor_set(v___x_146_, 1, v_b_123_);
lean_ctor_set(v___x_146_, 2, v_bkt_142_);
v_buckets_x27_147_ = lean_array_uset(v_buckets_125_, v___x_141_, v___x_146_);
v___x_148_ = lean_unsigned_to_nat(4u);
v___x_149_ = lean_nat_mul(v_size_x27_145_, v___x_148_);
v___x_150_ = lean_unsigned_to_nat(3u);
v___x_151_ = lean_nat_div(v___x_149_, v___x_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_array_get_size(v_buckets_x27_147_);
v___x_153_ = lean_nat_dec_le(v___x_151_, v___x_152_);
lean_dec(v___x_151_);
if (v___x_153_ == 0)
{
lean_object* v_val_154_; lean_object* v___x_156_; 
v_val_154_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(v_buckets_x27_147_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v_val_154_);
lean_ctor_set(v___x_127_, 0, v_size_x27_145_);
v___x_156_ = v___x_127_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_size_x27_145_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_val_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
else
{
lean_object* v___x_159_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v_buckets_x27_147_);
lean_ctor_set(v___x_127_, 0, v_size_x27_145_);
v___x_159_ = v___x_127_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_size_x27_145_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_buckets_x27_147_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
else
{
lean_object* v___x_161_; lean_object* v_buckets_x27_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
lean_inc(v_bkt_142_);
v___x_161_ = lean_box(0);
v_buckets_x27_162_ = lean_array_uset(v_buckets_125_, v___x_141_, v___x_161_);
v___x_163_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_122_, v_b_123_, v_bkt_142_);
v___x_164_ = lean_array_uset(v_buckets_x27_162_, v___x_141_, v___x_163_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_164_);
v___x_166_ = v___x_127_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_size_124_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(lean_object* v_as_x27_169_, lean_object* v_b_170_){
_start:
{
if (lean_obj_tag(v_as_x27_169_) == 0)
{
return v_b_170_;
}
else
{
lean_object* v_head_171_; lean_object* v_tail_172_; lean_object* v_fst_173_; lean_object* v_snd_174_; lean_object* v_r_175_; 
v_head_171_ = lean_ctor_get(v_as_x27_169_, 0);
v_tail_172_ = lean_ctor_get(v_as_x27_169_, 1);
v_fst_173_ = lean_ctor_get(v_head_171_, 0);
v_snd_174_ = lean_ctor_get(v_head_171_, 1);
lean_inc(v_snd_174_);
lean_inc(v_fst_173_);
v_r_175_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_b_170_, v_fst_173_, v_snd_174_);
v_as_x27_169_ = v_tail_172_;
v_b_170_ = v_r_175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_177_, lean_object* v_b_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_as_x27_177_, v_b_178_);
lean_dec(v_as_x27_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(lean_object* v_m_180_, lean_object* v_l_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_l_181_, v_m_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0___boxed(lean_object* v_m_183_, lean_object* v_l_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(v_m_183_, v_l_184_);
lean_dec(v_l_184_);
return v_res_185_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_box(0);
v___x_202_ = lean_unsigned_to_nat(16u);
v___x_203_ = lean_mk_array(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_204_);
return v___x_206_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8);
v___x_208_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__6));
v___x_209_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap(void){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0(lean_object* v_00_u03b2_211_, lean_object* v_m_212_, lean_object* v_a_213_, lean_object* v_b_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_m_212_, v_a_213_, v_b_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(lean_object* v_as_216_, lean_object* v_as_x27_217_, lean_object* v_b_218_, lean_object* v_a_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_as_x27_217_, v_b_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___boxed(lean_object* v_as_221_, lean_object* v_as_x27_222_, lean_object* v_b_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(v_as_221_, v_as_x27_222_, v_b_223_, v_a_224_);
lean_dec(v_as_x27_222_);
lean_dec(v_as_221_);
return v_res_225_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_226_, lean_object* v_a_227_, lean_object* v_x_228_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_227_, v_x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_230_, lean_object* v_a_231_, lean_object* v_x_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(v_00_u03b2_230_, v_a_231_, v_x_232_);
lean_dec(v_x_232_);
lean_dec_ref(v_a_231_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_235_, lean_object* v_data_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(v_data_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_238_, lean_object* v_a_239_, lean_object* v_b_240_, lean_object* v_x_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_239_, v_b_240_, v_x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_243_, lean_object* v_i_244_, lean_object* v_source_245_, lean_object* v_target_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_244_, v_source_245_, v_target_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_249_, v_x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
lean_inc(v_x_252_);
return v_x_252_;
}
else
{
lean_object* v_key_254_; lean_object* v_tail_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_key_254_ = lean_ctor_get(v_x_253_, 0);
v_tail_255_ = lean_ctor_get(v_x_253_, 2);
v___x_256_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_x_252_, v_tail_255_);
lean_inc(v_key_254_);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v_key_254_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0___boxed(lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_x_258_, v_x_259_);
lean_dec(v_x_259_);
lean_dec(v_x_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(lean_object* v_as_261_, size_t v_i_262_, size_t v_stop_263_, lean_object* v_b_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = lean_usize_dec_eq(v_i_262_, v_stop_263_);
if (v___x_265_ == 0)
{
size_t v___x_266_; size_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_266_ = ((size_t)1ULL);
v___x_267_ = lean_usize_sub(v_i_262_, v___x_266_);
v___x_268_ = lean_array_uget_borrowed(v_as_261_, v___x_267_);
v___x_269_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_b_264_, v___x_268_);
lean_dec(v_b_264_);
v_i_262_ = v___x_267_;
v_b_264_ = v___x_269_;
goto _start;
}
else
{
return v_b_264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1___boxed(lean_object* v_as_271_, lean_object* v_i_272_, lean_object* v_stop_273_, lean_object* v_b_274_){
_start:
{
size_t v_i_boxed_275_; size_t v_stop_boxed_276_; lean_object* v_res_277_; 
v_i_boxed_275_ = lean_unbox_usize(v_i_272_);
lean_dec(v_i_272_);
v_stop_boxed_276_ = lean_unbox_usize(v_stop_273_);
lean_dec(v_stop_273_);
v_res_277_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(v_as_271_, v_i_boxed_275_, v_stop_boxed_276_, v_b_274_);
lean_dec_ref(v_as_271_);
return v_res_277_;
}
}
static lean_object* _init_l_Lean_manualDomains(void){
_start:
{
lean_object* v___x_278_; lean_object* v_buckets_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_278_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v_buckets_279_ = lean_ctor_get(v___x_278_, 1);
v___x_280_ = lean_box(0);
v___x_281_ = lean_array_get_size(v_buckets_279_);
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = lean_nat_dec_lt(v___x_282_, v___x_281_);
if (v___x_283_ == 0)
{
return v___x_280_;
}
else
{
size_t v___x_284_; size_t v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_usize_of_nat(v___x_281_);
v___x_285_ = ((size_t)0ULL);
v___x_286_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(v_buckets_279_, v___x_284_, v___x_285_, v___x_280_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(lean_object* v_a_287_, lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_288_) == 0)
{
lean_object* v___x_289_; 
v___x_289_ = lean_box(0);
return v___x_289_;
}
else
{
lean_object* v_key_290_; lean_object* v_value_291_; lean_object* v_tail_292_; uint8_t v___x_293_; 
v_key_290_ = lean_ctor_get(v_x_288_, 0);
v_value_291_ = lean_ctor_get(v_x_288_, 1);
v_tail_292_ = lean_ctor_get(v_x_288_, 2);
v___x_293_ = lean_string_dec_eq(v_key_290_, v_a_287_);
if (v___x_293_ == 0)
{
v_x_288_ = v_tail_292_;
goto _start;
}
else
{
lean_object* v___x_295_; 
lean_inc(v_value_291_);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v_value_291_);
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg___boxed(lean_object* v_a_296_, lean_object* v_x_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_296_, v_x_297_);
lean_dec(v_x_297_);
lean_dec_ref(v_a_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(lean_object* v_m_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_buckets_301_; lean_object* v___x_302_; uint64_t v___x_303_; uint64_t v___x_304_; uint64_t v___x_305_; uint64_t v_fold_306_; uint64_t v___x_307_; uint64_t v___x_308_; uint64_t v___x_309_; size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_buckets_301_ = lean_ctor_get(v_m_299_, 1);
v___x_302_ = lean_array_get_size(v_buckets_301_);
v___x_303_ = lean_string_hash(v_a_300_);
v___x_304_ = 32ULL;
v___x_305_ = lean_uint64_shift_right(v___x_303_, v___x_304_);
v_fold_306_ = lean_uint64_xor(v___x_303_, v___x_305_);
v___x_307_ = 16ULL;
v___x_308_ = lean_uint64_shift_right(v_fold_306_, v___x_307_);
v___x_309_ = lean_uint64_xor(v_fold_306_, v___x_308_);
v___x_310_ = lean_uint64_to_usize(v___x_309_);
v___x_311_ = lean_usize_of_nat(v___x_302_);
v___x_312_ = ((size_t)1ULL);
v___x_313_ = lean_usize_sub(v___x_311_, v___x_312_);
v___x_314_ = lean_usize_land(v___x_310_, v___x_313_);
v___x_315_ = lean_array_uget_borrowed(v_buckets_301_, v___x_314_);
v___x_316_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_300_, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg___boxed(lean_object* v_m_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v_m_317_, v_a_318_);
lean_dec_ref(v_a_318_);
lean_dec_ref(v_m_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
lean_inc(v_x_320_);
return v_x_320_;
}
else
{
lean_object* v_key_322_; lean_object* v_value_323_; lean_object* v_tail_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_key_322_ = lean_ctor_get(v_x_321_, 0);
v_value_323_ = lean_ctor_get(v_x_321_, 1);
v_tail_324_ = lean_ctor_get(v_x_321_, 2);
v___x_325_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_x_320_, v_tail_324_);
lean_inc(v_value_323_);
lean_inc(v_key_322_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v_key_322_);
lean_ctor_set(v___x_326_, 1, v_value_323_);
v___x_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2___boxed(lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_x_328_, v_x_329_);
lean_dec(v_x_329_);
lean_dec(v_x_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(lean_object* v_as_331_, size_t v_i_332_, size_t v_stop_333_, lean_object* v_b_334_){
_start:
{
uint8_t v___x_335_; 
v___x_335_ = lean_usize_dec_eq(v_i_332_, v_stop_333_);
if (v___x_335_ == 0)
{
size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_sub(v_i_332_, v___x_336_);
v___x_338_ = lean_array_uget_borrowed(v_as_331_, v___x_337_);
v___x_339_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(v_b_334_, v___x_338_);
lean_dec(v_b_334_);
v_i_332_ = v___x_337_;
v_b_334_ = v___x_339_;
goto _start;
}
else
{
return v_b_334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3___boxed(lean_object* v_as_341_, lean_object* v_i_342_, lean_object* v_stop_343_, lean_object* v_b_344_){
_start:
{
size_t v_i_boxed_345_; size_t v_stop_boxed_346_; lean_object* v_res_347_; 
v_i_boxed_345_ = lean_unbox_usize(v_i_342_);
lean_dec(v_i_342_);
v_stop_boxed_346_ = lean_unbox_usize(v_stop_343_);
lean_dec(v_stop_343_);
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_as_341_, v_i_boxed_345_, v_stop_boxed_346_, v_b_344_);
lean_dec_ref(v_as_341_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_manualLink_spec__1(lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
if (lean_obj_tag(v_a_349_) == 0)
{
lean_object* v___x_351_; 
v___x_351_ = l_List_reverse___redArg(v_a_350_);
return v___x_351_;
}
else
{
lean_object* v_head_352_; lean_object* v_tail_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_365_; 
v_head_352_ = lean_ctor_get(v_a_349_, 0);
v_tail_353_ = lean_ctor_get(v_a_349_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v_a_349_);
if (v_isSharedCheck_365_ == 0)
{
v___x_355_ = v_a_349_;
v_isShared_356_ = v_isSharedCheck_365_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_tail_353_);
lean_inc(v_head_352_);
lean_dec(v_a_349_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_365_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v_fst_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v_fst_357_ = lean_ctor_get(v_head_352_, 0);
lean_inc(v_fst_357_);
lean_dec(v_head_352_);
v___x_358_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_manualLink_spec__1___closed__0));
v___x_359_ = lean_string_append(v___x_358_, v_fst_357_);
lean_dec(v_fst_357_);
v___x_360_ = lean_string_append(v___x_359_, v___x_358_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v_a_350_);
lean_ctor_set(v___x_355_, 0, v___x_360_);
v___x_362_ = v___x_355_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_a_350_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
v_a_349_ = v_tail_353_;
v_a_350_ = v___x_362_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_manualLink(lean_object* v_kind_371_, lean_object* v_name_372_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_373_, v_kind_371_);
if (lean_obj_tag(v___x_374_) == 1)
{
lean_object* v_val_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_389_; 
v_val_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_389_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_389_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_val_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_389_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_379_ = l_Lean_manualRoot;
v___x_380_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_381_ = lean_string_append(v___x_380_, v_val_375_);
lean_dec(v_val_375_);
v___x_382_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_383_ = lean_string_append(v___x_381_, v___x_382_);
v___x_384_ = lean_string_append(v___x_383_, v_name_372_);
v___x_385_ = lean_string_append(v___x_379_, v___x_384_);
lean_dec_ref(v___x_384_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_385_);
v___x_387_ = v___x_377_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
else
{
lean_object* v_buckets_390_; lean_object* v___x_391_; lean_object* v___y_393_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
lean_dec(v___x_374_);
v_buckets_390_ = lean_ctor_get(v___x_373_, 1);
v___x_391_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_403_ = lean_box(0);
v___x_404_ = lean_array_get_size(v_buckets_390_);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_nat_dec_lt(v___x_405_, v___x_404_);
if (v___x_406_ == 0)
{
v___y_393_ = v___x_403_;
goto v___jp_392_;
}
else
{
size_t v___x_407_; size_t v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_usize_of_nat(v___x_404_);
v___x_408_ = ((size_t)0ULL);
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_390_, v___x_407_, v___x_408_, v___x_403_);
v___y_393_ = v___x_409_;
goto v___jp_392_;
}
v___jp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_acceptableKinds_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_394_ = lean_box(0);
v___x_395_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_393_, v___x_394_);
v_acceptableKinds_396_ = l_String_intercalate(v___x_391_, v___x_395_);
v___x_397_ = ((lean_object*)(l_Lean_manualLink___closed__3));
v___x_398_ = lean_string_append(v___x_397_, v_kind_371_);
v___x_399_ = ((lean_object*)(l_Lean_manualLink___closed__4));
v___x_400_ = lean_string_append(v___x_398_, v___x_399_);
v___x_401_ = lean_string_append(v___x_400_, v_acceptableKinds_396_);
lean_dec_ref(v_acceptableKinds_396_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_manualLink___boxed(lean_object* v_kind_410_, lean_object* v_name_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_manualLink(v_kind_410_, v_name_411_);
lean_dec_ref(v_name_411_);
lean_dec_ref(v_kind_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(lean_object* v_00_u03b2_413_, lean_object* v_m_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v_m_414_, v_a_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___boxed(lean_object* v_00_u03b2_417_, lean_object* v_m_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(v_00_u03b2_417_, v_m_418_, v_a_419_);
lean_dec_ref(v_a_419_);
lean_dec_ref(v_m_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(lean_object* v_00_u03b2_421_, lean_object* v_a_422_, lean_object* v_x_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_422_, v_x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___boxed(lean_object* v_00_u03b2_425_, lean_object* v_a_426_, lean_object* v_x_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(v_00_u03b2_425_, v_a_426_, v_x_427_);
lean_dec(v_x_427_);
lean_dec_ref(v_a_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(lean_object* v_s_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0));
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___boxed(lean_object* v_s_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(v_s_433_);
lean_dec_ref(v_s_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(lean_object* v_path_435_, lean_object* v___x_436_, lean_object* v___x_437_, lean_object* v_a_438_, lean_object* v_b_439_){
_start:
{
lean_object* v_it_441_; lean_object* v_startInclusive_442_; lean_object* v_endExclusive_443_; 
if (lean_obj_tag(v_a_438_) == 0)
{
lean_object* v_currPos_448_; lean_object* v_searcher_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_472_; 
v_currPos_448_ = lean_ctor_get(v_a_438_, 0);
v_searcher_449_ = lean_ctor_get(v_a_438_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v_a_438_);
if (v_isSharedCheck_472_ == 0)
{
v___x_451_ = v_a_438_;
v_isShared_452_ = v_isSharedCheck_472_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_searcher_449_);
lean_inc(v_currPos_448_);
lean_dec(v_a_438_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_472_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
uint8_t v_decide_453_; 
v_decide_453_ = lean_nat_dec_eq(v_searcher_449_, v___x_437_);
if (v_decide_453_ == 0)
{
uint32_t v___x_454_; uint32_t v___x_455_; uint8_t v___x_456_; 
v___x_454_ = 47;
v___x_455_ = lean_string_utf8_get_fast(v_path_435_, v_searcher_449_);
v___x_456_ = lean_uint32_dec_eq(v___x_455_, v___x_454_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_457_ = lean_string_utf8_next_fast(v_path_435_, v_searcher_449_);
lean_dec(v_searcher_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_457_);
v___x_459_ = v___x_451_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_currPos_448_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_457_);
v___x_459_ = v_reuseFailAlloc_461_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
v_a_438_ = v___x_459_;
goto _start;
}
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_slice_465_; lean_object* v_nextIt_467_; 
v___x_462_ = lean_string_utf8_next_fast(v_path_435_, v_searcher_449_);
v___x_463_ = lean_nat_sub(v___x_462_, v_searcher_449_);
v___x_464_ = lean_nat_add(v_searcher_449_, v___x_463_);
lean_dec(v___x_463_);
v_slice_465_ = l_String_Slice_subslice_x21(v___x_436_, v_currPos_448_, v_searcher_449_);
lean_inc(v___x_464_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_464_);
lean_ctor_set(v___x_451_, 0, v___x_464_);
v_nextIt_467_ = v___x_451_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_464_);
v_nextIt_467_ = v_reuseFailAlloc_470_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v_startInclusive_468_; lean_object* v_endExclusive_469_; 
v_startInclusive_468_ = lean_ctor_get(v_slice_465_, 0);
lean_inc(v_startInclusive_468_);
v_endExclusive_469_ = lean_ctor_get(v_slice_465_, 1);
lean_inc(v_endExclusive_469_);
lean_dec_ref(v_slice_465_);
v_it_441_ = v_nextIt_467_;
v_startInclusive_442_ = v_startInclusive_468_;
v_endExclusive_443_ = v_endExclusive_469_;
goto v___jp_440_;
}
}
}
else
{
lean_object* v___x_471_; 
lean_del_object(v___x_451_);
lean_dec(v_searcher_449_);
v___x_471_ = lean_box(1);
lean_inc(v___x_437_);
v_it_441_ = v___x_471_;
v_startInclusive_442_ = v_currPos_448_;
v_endExclusive_443_ = v___x_437_;
goto v___jp_440_;
}
}
}
else
{
lean_dec(v___x_437_);
lean_dec_ref(v_path_435_);
return v_b_439_;
}
v___jp_440_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
lean_inc_ref(v_path_435_);
v___x_444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_444_, 0, v_path_435_);
lean_ctor_set(v___x_444_, 1, v_startInclusive_442_);
lean_ctor_set(v___x_444_, 2, v_endExclusive_443_);
v___x_445_ = l_String_Slice_toString(v___x_444_);
lean_dec_ref_known(v___x_444_, 3);
v___x_446_ = lean_array_push(v_b_439_, v___x_445_);
v_a_438_ = v_it_441_;
v_b_439_ = v___x_446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg___boxed(lean_object* v_path_473_, lean_object* v___x_474_, lean_object* v___x_475_, lean_object* v_a_476_, lean_object* v_b_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_473_, v___x_474_, v___x_475_, v_a_476_, v_b_477_);
lean_dec_ref(v___x_474_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
return v_x_479_;
}
else
{
lean_object* v_head_481_; lean_object* v_tail_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_head_481_ = lean_ctor_get(v_x_480_, 0);
v_tail_482_ = lean_ctor_get(v_x_480_, 1);
v___x_483_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_484_ = lean_string_append(v_x_479_, v___x_483_);
v___x_485_ = lean_string_append(v___x_484_, v_head_481_);
v_x_479_ = v___x_485_;
v_x_480_ = v_tail_482_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0___boxed(lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v_x_487_, v_x_488_);
lean_dec(v_x_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(lean_object* v_x_493_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v___x_494_; 
v___x_494_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0));
return v___x_494_;
}
else
{
lean_object* v_tail_495_; 
v_tail_495_ = lean_ctor_get(v_x_493_, 1);
if (lean_obj_tag(v_tail_495_) == 0)
{
lean_object* v_head_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_head_496_ = lean_ctor_get(v_x_493_, 0);
v___x_497_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_498_ = lean_string_append(v___x_497_, v_head_496_);
v___x_499_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2));
v___x_500_ = lean_string_append(v___x_498_, v___x_499_);
return v___x_500_;
}
else
{
lean_object* v_head_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint32_t v___x_505_; lean_object* v___x_506_; 
v_head_501_ = lean_ctor_get(v_x_493_, 0);
v___x_502_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_503_ = lean_string_append(v___x_502_, v_head_501_);
v___x_504_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v___x_503_, v_tail_495_);
v___x_505_ = 93;
v___x_506_ = lean_string_push(v___x_504_, v___x_505_);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___boxed(lean_object* v_x_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v_x_507_);
lean_dec(v_x_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rw(lean_object* v_path_519_){
_start:
{
lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_string_utf8_byte_size(v_path_519_);
lean_inc_ref(v_path_519_);
v___x_547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_547_, 0, v_path_519_);
lean_ctor_set(v___x_547_, 1, v___x_545_);
lean_ctor_set(v___x_547_, 2, v___x_546_);
v___x_548_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(v___x_547_);
v___x_549_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__4));
v___x_550_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_519_, v___x_547_, v___x_546_, v___x_548_, v___x_549_);
lean_dec_ref_known(v___x_547_, 3);
v___x_551_ = lean_array_to_list(v___x_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
goto v___jp_543_;
}
else
{
lean_object* v_head_552_; lean_object* v_tail_553_; lean_object* v_kind_555_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_head_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_head_552_);
v_tail_553_ = lean_ctor_get(v___x_551_, 1);
lean_inc(v_tail_553_);
lean_dec_ref_known(v___x_551_, 2);
v___x_590_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_591_ = lean_string_dec_eq(v_head_552_, v___x_590_);
if (v___x_591_ == 0)
{
v_kind_555_ = v_head_552_;
goto v___jp_554_;
}
else
{
lean_dec(v_head_552_);
if (lean_obj_tag(v_tail_553_) == 0)
{
goto v___jp_543_;
}
else
{
v_kind_555_ = v___x_590_;
goto v___jp_554_;
}
}
v___jp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_556_, v_kind_555_);
if (lean_obj_tag(v___x_557_) == 1)
{
if (lean_obj_tag(v_tail_553_) == 1)
{
lean_object* v_tail_558_; 
v_tail_558_ = lean_ctor_get(v_tail_553_, 1);
if (lean_obj_tag(v_tail_558_) == 0)
{
lean_object* v_val_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_581_; 
v_val_559_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_581_ == 0)
{
v___x_561_ = v___x_557_;
v_isShared_562_ = v_isSharedCheck_581_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_val_559_);
lean_dec(v___x_557_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_581_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_head_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_head_563_ = lean_ctor_get(v_tail_553_, 0);
lean_inc(v_head_563_);
lean_dec_ref_known(v_tail_553_, 2);
v___x_564_ = lean_string_utf8_byte_size(v_head_563_);
v___x_565_ = lean_nat_dec_eq(v___x_564_, v___x_545_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
lean_dec_ref(v_kind_555_);
v___x_566_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_567_ = lean_string_append(v___x_566_, v_val_559_);
lean_dec(v_val_559_);
v___x_568_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_569_ = lean_string_append(v___x_567_, v___x_568_);
v___x_570_ = lean_string_append(v___x_569_, v_head_563_);
lean_dec(v_head_563_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_570_);
v___x_572_ = v___x_561_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
lean_dec(v_head_563_);
lean_dec(v_val_559_);
v___x_574_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__5));
v___x_575_ = lean_string_append(v___x_574_, v_kind_555_);
lean_dec_ref(v_kind_555_);
v___x_576_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__6));
v___x_577_ = lean_string_append(v___x_575_, v___x_576_);
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 0);
lean_ctor_set(v___x_561_, 0, v___x_577_);
v___x_579_ = v___x_561_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_557_, 1);
v___y_534_ = v_tail_553_;
v___y_535_ = v_kind_555_;
goto v___jp_533_;
}
}
else
{
lean_dec_ref_known(v___x_557_, 1);
v___y_534_ = v_tail_553_;
v___y_535_ = v_kind_555_;
goto v___jp_533_;
}
}
else
{
lean_object* v_buckets_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
lean_dec(v___x_557_);
lean_dec(v_tail_553_);
v_buckets_582_ = lean_ctor_get(v___x_556_, 1);
v___x_583_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_584_ = lean_box(0);
v___x_585_ = lean_array_get_size(v_buckets_582_);
v___x_586_ = lean_nat_dec_lt(v___x_545_, v___x_585_);
if (v___x_586_ == 0)
{
v___y_521_ = v_kind_555_;
v___y_522_ = v___x_583_;
v___y_523_ = v___x_584_;
goto v___jp_520_;
}
else
{
size_t v___x_587_; size_t v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_usize_of_nat(v___x_585_);
v___x_588_ = ((size_t)0ULL);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_582_, v___x_587_, v___x_588_, v___x_584_);
v___y_521_ = v_kind_555_;
v___y_522_ = v___x_583_;
v___y_523_ = v___x_589_;
goto v___jp_520_;
}
}
}
}
v___jp_520_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v_acceptableKinds_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_524_ = lean_box(0);
v___x_525_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_523_, v___x_524_);
v_acceptableKinds_526_ = l_String_intercalate(v___y_522_, v___x_525_);
v___x_527_ = ((lean_object*)(l_Lean_manualLink___closed__3));
v___x_528_ = lean_string_append(v___x_527_, v___y_521_);
lean_dec_ref(v___y_521_);
v___x_529_ = ((lean_object*)(l_Lean_manualLink___closed__4));
v___x_530_ = lean_string_append(v___x_528_, v___x_529_);
v___x_531_ = lean_string_append(v___x_530_, v_acceptableKinds_526_);
lean_dec_ref(v_acceptableKinds_526_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
v___jp_533_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_536_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__0));
v___x_537_ = lean_string_append(v___x_536_, v___y_535_);
lean_dec_ref(v___y_535_);
v___x_538_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__1));
v___x_539_ = lean_string_append(v___x_537_, v___x_538_);
v___x_540_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v___y_534_);
lean_dec(v___y_534_);
v___x_541_ = lean_string_append(v___x_539_, v___x_540_);
lean_dec_ref(v___x_540_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
v___jp_543_:
{
lean_object* v___x_544_; 
v___x_544_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__3));
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(lean_object* v_path_592_, lean_object* v___x_593_, lean_object* v___x_594_, lean_object* v_inst_595_, lean_object* v_R_596_, lean_object* v_a_597_, lean_object* v_b_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_592_, v___x_593_, v___x_594_, v_a_597_, v_b_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___boxed(lean_object* v_path_600_, lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v_inst_603_, lean_object* v_R_604_, lean_object* v_a_605_, lean_object* v_b_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(v_path_600_, v___x_601_, v___x_602_, v_inst_603_, v_R_604_, v_a_605_, v_b_606_);
lean_dec_ref(v___x_601_);
return v_res_607_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(uint32_t v_c_608_){
_start:
{
uint8_t v___y_656_; uint32_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 65;
v___x_662_ = lean_uint32_dec_le(v___x_661_, v_c_608_);
if (v___x_662_ == 0)
{
v___y_656_ = v___x_662_;
goto v___jp_655_;
}
else
{
uint32_t v___x_663_; uint8_t v___x_664_; 
v___x_663_ = 90;
v___x_664_ = lean_uint32_dec_le(v_c_608_, v___x_663_);
v___y_656_ = v___x_664_;
goto v___jp_655_;
}
v___jp_609_:
{
uint32_t v___x_610_; uint8_t v___x_611_; 
v___x_610_ = 45;
v___x_611_ = lean_uint32_dec_eq(v_c_608_, v___x_610_);
if (v___x_611_ == 0)
{
uint32_t v___x_612_; uint8_t v___x_613_; 
v___x_612_ = 46;
v___x_613_ = lean_uint32_dec_eq(v_c_608_, v___x_612_);
if (v___x_613_ == 0)
{
uint32_t v___x_614_; uint8_t v___x_615_; 
v___x_614_ = 95;
v___x_615_ = lean_uint32_dec_eq(v_c_608_, v___x_614_);
if (v___x_615_ == 0)
{
uint32_t v___x_616_; uint8_t v___x_617_; 
v___x_616_ = 126;
v___x_617_ = lean_uint32_dec_eq(v_c_608_, v___x_616_);
if (v___x_617_ == 0)
{
uint32_t v___x_618_; uint8_t v___x_619_; 
v___x_618_ = 58;
v___x_619_ = lean_uint32_dec_eq(v_c_608_, v___x_618_);
if (v___x_619_ == 0)
{
uint32_t v___x_620_; uint8_t v___x_621_; 
v___x_620_ = 47;
v___x_621_ = lean_uint32_dec_eq(v_c_608_, v___x_620_);
if (v___x_621_ == 0)
{
uint32_t v___x_622_; uint8_t v___x_623_; 
v___x_622_ = 63;
v___x_623_ = lean_uint32_dec_eq(v_c_608_, v___x_622_);
if (v___x_623_ == 0)
{
uint32_t v___x_624_; uint8_t v___x_625_; 
v___x_624_ = 35;
v___x_625_ = lean_uint32_dec_eq(v_c_608_, v___x_624_);
if (v___x_625_ == 0)
{
uint32_t v___x_626_; uint8_t v___x_627_; 
v___x_626_ = 91;
v___x_627_ = lean_uint32_dec_eq(v_c_608_, v___x_626_);
if (v___x_627_ == 0)
{
uint32_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 93;
v___x_629_ = lean_uint32_dec_eq(v_c_608_, v___x_628_);
if (v___x_629_ == 0)
{
uint32_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = 64;
v___x_631_ = lean_uint32_dec_eq(v_c_608_, v___x_630_);
if (v___x_631_ == 0)
{
uint32_t v___x_632_; uint8_t v___x_633_; 
v___x_632_ = 33;
v___x_633_ = lean_uint32_dec_eq(v_c_608_, v___x_632_);
if (v___x_633_ == 0)
{
uint32_t v___x_634_; uint8_t v___x_635_; 
v___x_634_ = 36;
v___x_635_ = lean_uint32_dec_eq(v_c_608_, v___x_634_);
if (v___x_635_ == 0)
{
uint32_t v___x_636_; uint8_t v___x_637_; 
v___x_636_ = 38;
v___x_637_ = lean_uint32_dec_eq(v_c_608_, v___x_636_);
if (v___x_637_ == 0)
{
uint32_t v___x_638_; uint8_t v___x_639_; 
v___x_638_ = 39;
v___x_639_ = lean_uint32_dec_eq(v_c_608_, v___x_638_);
if (v___x_639_ == 0)
{
uint32_t v___x_640_; uint8_t v___x_641_; 
v___x_640_ = 42;
v___x_641_ = lean_uint32_dec_eq(v_c_608_, v___x_640_);
if (v___x_641_ == 0)
{
uint32_t v___x_642_; uint8_t v___x_643_; 
v___x_642_ = 43;
v___x_643_ = lean_uint32_dec_eq(v_c_608_, v___x_642_);
if (v___x_643_ == 0)
{
uint32_t v___x_644_; uint8_t v___x_645_; 
v___x_644_ = 44;
v___x_645_ = lean_uint32_dec_eq(v_c_608_, v___x_644_);
if (v___x_645_ == 0)
{
uint32_t v___x_646_; uint8_t v___x_647_; 
v___x_646_ = 59;
v___x_647_ = lean_uint32_dec_eq(v_c_608_, v___x_646_);
if (v___x_647_ == 0)
{
uint32_t v___x_648_; uint8_t v___x_649_; 
v___x_648_ = 61;
v___x_649_ = lean_uint32_dec_eq(v_c_608_, v___x_648_);
return v___x_649_;
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
else
{
return v___x_619_;
}
}
else
{
return v___x_617_;
}
}
else
{
return v___x_615_;
}
}
else
{
return v___x_613_;
}
}
else
{
return v___x_611_;
}
}
v___jp_650_:
{
uint32_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = 48;
v___x_652_ = lean_uint32_dec_le(v___x_651_, v_c_608_);
if (v___x_652_ == 0)
{
goto v___jp_609_;
}
else
{
uint32_t v___x_653_; uint8_t v___x_654_; 
v___x_653_ = 57;
v___x_654_ = lean_uint32_dec_le(v_c_608_, v___x_653_);
if (v___x_654_ == 0)
{
goto v___jp_609_;
}
else
{
return v___x_654_;
}
}
}
v___jp_655_:
{
if (v___y_656_ == 0)
{
uint32_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = 97;
v___x_658_ = lean_uint32_dec_le(v___x_657_, v_c_608_);
if (v___x_658_ == 0)
{
goto v___jp_650_;
}
else
{
uint32_t v___x_659_; uint8_t v___x_660_; 
v___x_659_ = 122;
v___x_660_ = lean_uint32_dec_le(v_c_608_, v___x_659_);
if (v___x_660_ == 0)
{
goto v___jp_650_;
}
else
{
return v___x_660_;
}
}
}
else
{
return v___y_656_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar___boxed(lean_object* v_c_665_){
_start:
{
uint32_t v_c_boxed_666_; uint8_t v_res_667_; lean_object* v_r_668_; 
v_c_boxed_666_ = lean_unbox_uint32(v_c_665_);
lean_dec(v_c_665_);
v_res_667_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v_c_boxed_666_);
v_r_668_ = lean_box(v_res_667_);
return v_r_668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(lean_object* v_s_669_, lean_object* v___x_670_, lean_object* v___x_671_, uint32_t v___x_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_snd_674_; lean_object* v_snd_675_; lean_object* v_fst_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_744_; 
v_snd_674_ = lean_ctor_get(v_a_673_, 1);
lean_inc(v_snd_674_);
v_snd_675_ = lean_ctor_get(v_snd_674_, 1);
lean_inc(v_snd_675_);
v_fst_676_ = lean_ctor_get(v_a_673_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_a_673_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_a_673_, 1);
lean_dec(v_unused_745_);
v___x_678_ = v_a_673_;
v_isShared_679_ = v_isSharedCheck_744_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_fst_676_);
lean_dec(v_a_673_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_744_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_fst_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_742_; 
v_fst_680_ = lean_ctor_get(v_snd_674_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v_snd_674_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v_snd_674_, 1);
lean_dec(v_unused_743_);
v___x_682_ = v_snd_674_;
v_isShared_683_ = v_isSharedCheck_742_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_fst_680_);
lean_dec(v_snd_674_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_742_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_fst_684_; lean_object* v_snd_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_741_; 
v_fst_684_ = lean_ctor_get(v_snd_675_, 0);
v_snd_685_ = lean_ctor_get(v_snd_675_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_snd_675_);
if (v_isSharedCheck_741_ == 0)
{
v___x_687_ = v_snd_675_;
v_isShared_688_ = v_isSharedCheck_741_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_snd_685_);
lean_inc(v_fst_684_);
lean_dec(v_snd_675_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_741_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; uint8_t v_decide_690_; 
v___x_689_ = lean_string_utf8_byte_size(v_s_669_);
v_decide_690_ = lean_nat_dec_eq(v_snd_685_, v___x_689_);
if (v_decide_690_ == 0)
{
uint32_t v___x_691_; lean_object* v___x_692_; uint8_t v___y_725_; uint8_t v___x_730_; 
v___x_691_ = lean_string_utf8_get_fast(v_s_669_, v_snd_685_);
v___x_692_ = lean_string_utf8_next_fast(v_s_669_, v_snd_685_);
v___x_730_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v___x_691_);
if (v___x_730_ == 0)
{
v___y_725_ = v___x_730_;
goto v___jp_724_;
}
else
{
uint8_t v_decide_731_; 
v_decide_731_ = lean_nat_dec_eq(v___x_692_, v___x_689_);
if (v_decide_731_ == 0)
{
v___y_725_ = v___x_730_;
goto v___jp_724_;
}
else
{
goto v___jp_693_;
}
}
v___jp_693_:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_string_utf8_extract_fast(v_s_669_, v___x_670_, v_snd_685_);
v___x_695_ = l___private_Lean_DocString_Links_0__Lean_rw(v___x_694_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_671_);
lean_ctor_set(v___x_697_, 1, v_snd_685_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v_a_696_);
lean_ctor_set(v___x_687_, 0, v___x_697_);
v___x_699_ = v___x_687_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_a_696_);
v___x_699_ = v_reuseFailAlloc_709_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_700_ = lean_array_push(v_fst_680_, v___x_699_);
v___x_701_ = lean_string_push(v_fst_676_, v___x_672_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_692_);
lean_ctor_set(v___x_682_, 0, v_fst_684_);
v___x_703_ = v___x_682_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_fst_684_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v___x_692_);
v___x_703_ = v_reuseFailAlloc_708_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_705_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___x_703_);
lean_ctor_set(v___x_678_, 0, v___x_700_);
v___x_705_ = v___x_678_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_703_);
v___x_705_ = v_reuseFailAlloc_707_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_701_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
lean_dec(v_snd_685_);
lean_dec(v_fst_684_);
lean_dec(v___x_671_);
v_a_710_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_695_, 1);
v___x_711_ = l_Lean_manualRoot;
v___x_712_ = lean_string_append(v_fst_676_, v___x_711_);
v___x_713_ = lean_string_append(v___x_712_, v_a_710_);
lean_dec(v_a_710_);
v___x_714_ = lean_string_push(v___x_713_, v___x_691_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_692_);
lean_ctor_set(v___x_687_, 0, v___x_692_);
v___x_716_ = v___x_687_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_692_);
v___x_716_ = v_reuseFailAlloc_723_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_716_);
v___x_718_ = v___x_682_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_fst_680_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_722_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___x_718_);
lean_ctor_set(v___x_678_, 0, v___x_714_);
v___x_720_ = v___x_678_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
v___jp_724_:
{
if (v___y_725_ == 0)
{
goto v___jp_693_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
lean_del_object(v___x_687_);
lean_dec(v_snd_685_);
lean_del_object(v___x_682_);
lean_del_object(v___x_678_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_fst_684_);
lean_ctor_set(v___x_726_, 1, v___x_692_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v_fst_680_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v_fst_676_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v_a_673_ = v___x_728_;
goto _start;
}
}
}
else
{
lean_object* v___x_733_; 
lean_dec(v___x_671_);
if (v_isShared_688_ == 0)
{
v___x_733_ = v___x_687_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_fst_684_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_snd_685_);
v___x_733_ = v_reuseFailAlloc_740_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_733_);
v___x_735_ = v___x_682_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_fst_680_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_733_);
v___x_735_ = v_reuseFailAlloc_739_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___x_735_);
v___x_737_ = v___x_678_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_fst_676_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg___boxed(lean_object* v_s_746_, lean_object* v___x_747_, lean_object* v___x_748_, lean_object* v___x_749_, lean_object* v_a_750_){
_start:
{
uint32_t v___x_2314__boxed_751_; lean_object* v_res_752_; 
v___x_2314__boxed_751_ = lean_unbox_uint32(v___x_749_);
lean_dec(v___x_749_);
v_res_752_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_746_, v___x_747_, v___x_748_, v___x_2314__boxed_751_, v_a_750_);
lean_dec(v___x_747_);
lean_dec_ref(v_s_746_);
return v_res_752_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v_scheme_754_; lean_object* v___x_755_; 
v_scheme_754_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0));
v___x_755_ = lean_string_utf8_byte_size(v_scheme_754_);
return v___x_755_;
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
lean_object* v_scheme_770_; uint32_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_scheme_770_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0));
v___x_771_ = lean_string_utf8_get_fast(v_s_756_, v_snd_764_);
v___x_772_ = lean_string_utf8_next_fast(v_s_756_, v_snd_764_);
v___x_782_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1);
v___x_783_ = lean_nat_sub(v___x_768_, v_snd_764_);
v___x_784_ = lean_nat_dec_le(v___x_782_, v___x_783_);
lean_dec(v___x_783_);
if (v___x_784_ == 0)
{
lean_dec(v_snd_764_);
goto v___jp_773_;
}
else
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = lean_string_memcmp(v_s_756_, v_scheme_770_, v_snd_764_, v___x_785_, v___x_782_);
if (v___x_786_ == 0)
{
lean_dec(v_snd_764_);
goto v___jp_773_;
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
v___x_788_ = l_String_Slice_pos_x21(v___x_787_, v___x_782_);
lean_dec_ref_known(v___x_787_, 3);
v___x_789_ = lean_nat_add(v_snd_764_, v___x_788_);
lean_dec(v___x_788_);
lean_inc(v___x_789_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_772_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_fst_763_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v_fst_759_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_756_, v___x_789_, v_snd_764_, v___x_771_, v___x_792_);
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
v___jp_773_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_string_push(v_fst_759_, v___x_771_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v___x_772_);
v___x_776_ = v___x_766_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_fst_763_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_772_);
v___x_776_ = v_reuseFailAlloc_781_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___x_776_);
lean_ctor_set(v___x_761_, 0, v___x_774_);
v___x_778_ = v___x_761_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_780_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
v_a_757_ = v___x_778_;
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
uint32_t v___x_2599__boxed_859_; lean_object* v_res_860_; 
v___x_2599__boxed_859_ = lean_unbox_uint32(v___x_856_);
lean_dec(v___x_856_);
v_res_860_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0(v_s_853_, v___x_854_, v___x_855_, v___x_2599__boxed_859_, v_inst_857_, v_a_858_);
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
