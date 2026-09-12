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
static lean_once_cell_t l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "LEAN_MANUAL_ROOT"};
static const lean_object* l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value;
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
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_));
v___x_8_ = lean_string_utf8_byte_size(v___x_7_);
return v___x_8_;
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
lean_object* v___y_19_; lean_object* v___y_20_; lean_object* v_r_24_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_));
v___x_34_ = lean_io_getenv(v___x_33_);
if (lean_obj_tag(v___x_34_) == 1)
{
lean_object* v_val_35_; 
v_val_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_val_35_);
lean_dec_ref_known(v___x_34_, 1);
v_r_24_ = v_val_35_;
goto v___jp_23_;
}
else
{
lean_object* v___x_36_; uint8_t v___x_37_; 
lean_dec(v___x_34_);
v___x_36_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
v___x_37_ = lean_uint8_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
if (v___x_37_ == 0)
{
v_r_24_ = v___x_36_;
goto v___jp_23_;
}
else
{
lean_object* v___x_38_; 
v___x_38_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot___closed__0));
v_r_24_ = v___x_38_;
goto v___jp_23_;
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
v___jp_23_:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_25_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_));
v___x_26_ = lean_string_utf8_byte_size(v_r_24_);
v___x_27_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_, &l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
v___x_28_ = lean_nat_dec_le(v___x_27_, v___x_26_);
if (v___x_28_ == 0)
{
v___y_19_ = v___x_25_;
v___y_20_ = v_r_24_;
goto v___jp_18_;
}
else
{
lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = lean_nat_sub(v___x_26_, v___x_27_);
v___x_31_ = lean_string_memcmp(v_r_24_, v___x_25_, v___x_30_, v___x_29_, v___x_27_);
lean_dec(v___x_30_);
if (v___x_31_ == 0)
{
v___y_19_ = v___x_25_;
v___y_20_ = v_r_24_;
goto v___jp_18_;
}
else
{
lean_object* v___x_32_; 
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v_r_24_);
return v___x_32_;
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg(){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg___closed__0));
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg___boxed(lean_object* v___dummy_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg();
return v_res_434_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0(void){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___redArg();
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(lean_object* v_s_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___boxed(lean_object* v_s_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(v_s_438_);
lean_dec_ref(v_s_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(lean_object* v_path_440_, lean_object* v___x_441_, lean_object* v___x_442_, lean_object* v_a_443_, lean_object* v_b_444_){
_start:
{
lean_object* v_it_446_; lean_object* v_startInclusive_447_; lean_object* v_endExclusive_448_; 
if (lean_obj_tag(v_a_443_) == 0)
{
lean_object* v_currPos_453_; lean_object* v_searcher_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_477_; 
v_currPos_453_ = lean_ctor_get(v_a_443_, 0);
v_searcher_454_ = lean_ctor_get(v_a_443_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_477_ == 0)
{
v___x_456_ = v_a_443_;
v_isShared_457_ = v_isSharedCheck_477_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_searcher_454_);
lean_inc(v_currPos_453_);
lean_dec(v_a_443_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_477_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
uint8_t v_decide_458_; 
v_decide_458_ = lean_nat_dec_eq(v_searcher_454_, v___x_442_);
if (v_decide_458_ == 0)
{
uint32_t v___x_459_; uint32_t v___x_460_; uint8_t v___x_461_; 
v___x_459_ = 47;
v___x_460_ = lean_string_utf8_get_fast(v_path_440_, v_searcher_454_);
v___x_461_ = lean_uint32_dec_eq(v___x_460_, v___x_459_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_string_utf8_next_fast(v_path_440_, v_searcher_454_);
lean_dec(v_searcher_454_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 1, v___x_462_);
v___x_464_ = v___x_456_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_currPos_453_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_462_);
v___x_464_ = v_reuseFailAlloc_466_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
v_a_443_ = v___x_464_;
goto _start;
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_slice_470_; lean_object* v_nextIt_472_; 
v___x_467_ = lean_string_utf8_next_fast(v_path_440_, v_searcher_454_);
v___x_468_ = lean_nat_sub(v___x_467_, v_searcher_454_);
v___x_469_ = lean_nat_add(v_searcher_454_, v___x_468_);
lean_dec(v___x_468_);
v_slice_470_ = l_String_Slice_subslice_x21(v___x_441_, v_currPos_453_, v_searcher_454_);
lean_inc(v___x_469_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 1, v___x_469_);
lean_ctor_set(v___x_456_, 0, v___x_469_);
v_nextIt_472_ = v___x_456_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_469_);
v_nextIt_472_ = v_reuseFailAlloc_475_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v_startInclusive_473_; lean_object* v_endExclusive_474_; 
v_startInclusive_473_ = lean_ctor_get(v_slice_470_, 0);
lean_inc(v_startInclusive_473_);
v_endExclusive_474_ = lean_ctor_get(v_slice_470_, 1);
lean_inc(v_endExclusive_474_);
lean_dec_ref(v_slice_470_);
v_it_446_ = v_nextIt_472_;
v_startInclusive_447_ = v_startInclusive_473_;
v_endExclusive_448_ = v_endExclusive_474_;
goto v___jp_445_;
}
}
}
else
{
lean_object* v___x_476_; 
lean_del_object(v___x_456_);
lean_dec(v_searcher_454_);
v___x_476_ = lean_box(1);
lean_inc(v___x_442_);
v_it_446_ = v___x_476_;
v_startInclusive_447_ = v_currPos_453_;
v_endExclusive_448_ = v___x_442_;
goto v___jp_445_;
}
}
}
else
{
lean_dec(v___x_442_);
lean_dec_ref(v_path_440_);
return v_b_444_;
}
v___jp_445_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
lean_inc_ref(v_path_440_);
v___x_449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_449_, 0, v_path_440_);
lean_ctor_set(v___x_449_, 1, v_startInclusive_447_);
lean_ctor_set(v___x_449_, 2, v_endExclusive_448_);
v___x_450_ = l_String_Slice_toString(v___x_449_);
lean_dec_ref_known(v___x_449_, 3);
v___x_451_ = lean_array_push(v_b_444_, v___x_450_);
v_a_443_ = v_it_446_;
v_b_444_ = v___x_451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg___boxed(lean_object* v_path_478_, lean_object* v___x_479_, lean_object* v___x_480_, lean_object* v_a_481_, lean_object* v_b_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_478_, v___x_479_, v___x_480_, v_a_481_, v_b_482_);
lean_dec_ref(v___x_479_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
return v_x_484_;
}
else
{
lean_object* v_head_486_; lean_object* v_tail_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_head_486_ = lean_ctor_get(v_x_485_, 0);
v_tail_487_ = lean_ctor_get(v_x_485_, 1);
v___x_488_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_489_ = lean_string_append(v_x_484_, v___x_488_);
v___x_490_ = lean_string_append(v___x_489_, v_head_486_);
v_x_484_ = v___x_490_;
v_x_485_ = v_tail_487_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0___boxed(lean_object* v_x_492_, lean_object* v_x_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v_x_492_, v_x_493_);
lean_dec(v_x_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(lean_object* v_x_498_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v___x_499_; 
v___x_499_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0));
return v___x_499_;
}
else
{
lean_object* v_tail_500_; 
v_tail_500_ = lean_ctor_get(v_x_498_, 1);
if (lean_obj_tag(v_tail_500_) == 0)
{
lean_object* v_head_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_head_501_ = lean_ctor_get(v_x_498_, 0);
v___x_502_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_503_ = lean_string_append(v___x_502_, v_head_501_);
v___x_504_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2));
v___x_505_ = lean_string_append(v___x_503_, v___x_504_);
return v___x_505_;
}
else
{
lean_object* v_head_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint32_t v___x_510_; lean_object* v___x_511_; 
v_head_506_ = lean_ctor_get(v_x_498_, 0);
v___x_507_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_508_ = lean_string_append(v___x_507_, v_head_506_);
v___x_509_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v___x_508_, v_tail_500_);
v___x_510_ = 93;
v___x_511_ = lean_string_push(v___x_509_, v___x_510_);
return v___x_511_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___boxed(lean_object* v_x_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v_x_512_);
lean_dec(v_x_512_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rw(lean_object* v_path_524_){
_start:
{
lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = lean_string_utf8_byte_size(v_path_524_);
lean_inc_ref(v_path_524_);
v___x_552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_552_, 0, v_path_524_);
lean_ctor_set(v___x_552_, 1, v___x_550_);
lean_ctor_set(v___x_552_, 2, v___x_551_);
v___x_553_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0);
v___x_554_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__4));
v___x_555_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_524_, v___x_552_, v___x_551_, v___x_553_, v___x_554_);
lean_dec_ref_known(v___x_552_, 3);
v___x_556_ = lean_array_to_list(v___x_555_);
if (lean_obj_tag(v___x_556_) == 0)
{
goto v___jp_548_;
}
else
{
lean_object* v_head_557_; lean_object* v_tail_558_; lean_object* v_kind_560_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_head_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_head_557_);
v_tail_558_ = lean_ctor_get(v___x_556_, 1);
lean_inc(v_tail_558_);
lean_dec_ref_known(v___x_556_, 2);
v___x_595_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_596_ = lean_string_dec_eq(v_head_557_, v___x_595_);
if (v___x_596_ == 0)
{
v_kind_560_ = v_head_557_;
goto v___jp_559_;
}
else
{
lean_dec(v_head_557_);
if (lean_obj_tag(v_tail_558_) == 0)
{
goto v___jp_548_;
}
else
{
v_kind_560_ = v___x_595_;
goto v___jp_559_;
}
}
v___jp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_562_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_561_, v_kind_560_);
if (lean_obj_tag(v___x_562_) == 1)
{
if (lean_obj_tag(v_tail_558_) == 1)
{
lean_object* v_tail_563_; 
v_tail_563_ = lean_ctor_get(v_tail_558_, 1);
if (lean_obj_tag(v_tail_563_) == 0)
{
lean_object* v_val_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_586_; 
v_val_564_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_586_ == 0)
{
v___x_566_ = v___x_562_;
v_isShared_567_ = v_isSharedCheck_586_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_val_564_);
lean_dec(v___x_562_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_586_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v_head_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_head_568_ = lean_ctor_get(v_tail_558_, 0);
lean_inc(v_head_568_);
lean_dec_ref_known(v_tail_558_, 2);
v___x_569_ = lean_string_utf8_byte_size(v_head_568_);
v___x_570_ = lean_nat_dec_eq(v___x_569_, v___x_550_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
lean_dec_ref(v_kind_560_);
v___x_571_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_572_ = lean_string_append(v___x_571_, v_val_564_);
lean_dec(v_val_564_);
v___x_573_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
v___x_575_ = lean_string_append(v___x_574_, v_head_568_);
lean_dec(v_head_568_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_575_);
v___x_577_ = v___x_566_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
lean_dec(v_head_568_);
lean_dec(v_val_564_);
v___x_579_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__5));
v___x_580_ = lean_string_append(v___x_579_, v_kind_560_);
lean_dec_ref(v_kind_560_);
v___x_581_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__6));
v___x_582_ = lean_string_append(v___x_580_, v___x_581_);
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 0);
lean_ctor_set(v___x_566_, 0, v___x_582_);
v___x_584_ = v___x_566_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_562_, 1);
v___y_539_ = v_tail_558_;
v___y_540_ = v_kind_560_;
goto v___jp_538_;
}
}
else
{
lean_dec_ref_known(v___x_562_, 1);
v___y_539_ = v_tail_558_;
v___y_540_ = v_kind_560_;
goto v___jp_538_;
}
}
else
{
lean_object* v_buckets_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
lean_dec(v___x_562_);
lean_dec(v_tail_558_);
v_buckets_587_ = lean_ctor_get(v___x_561_, 1);
v___x_588_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_589_ = lean_box(0);
v___x_590_ = lean_array_get_size(v_buckets_587_);
v___x_591_ = lean_nat_dec_lt(v___x_550_, v___x_590_);
if (v___x_591_ == 0)
{
v___y_526_ = v_kind_560_;
v___y_527_ = v___x_588_;
v___y_528_ = v___x_589_;
goto v___jp_525_;
}
else
{
size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_usize_of_nat(v___x_590_);
v___x_593_ = ((size_t)0ULL);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_587_, v___x_592_, v___x_593_, v___x_589_);
v___y_526_ = v_kind_560_;
v___y_527_ = v___x_588_;
v___y_528_ = v___x_594_;
goto v___jp_525_;
}
}
}
}
v___jp_525_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_acceptableKinds_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_529_ = lean_box(0);
v___x_530_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_528_, v___x_529_);
v_acceptableKinds_531_ = l_String_intercalate(v___y_527_, v___x_530_);
v___x_532_ = ((lean_object*)(l_Lean_manualLink___closed__3));
v___x_533_ = lean_string_append(v___x_532_, v___y_526_);
lean_dec_ref(v___y_526_);
v___x_534_ = ((lean_object*)(l_Lean_manualLink___closed__4));
v___x_535_ = lean_string_append(v___x_533_, v___x_534_);
v___x_536_ = lean_string_append(v___x_535_, v_acceptableKinds_531_);
lean_dec_ref(v_acceptableKinds_531_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
v___jp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_541_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__0));
v___x_542_ = lean_string_append(v___x_541_, v___y_540_);
lean_dec_ref(v___y_540_);
v___x_543_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__1));
v___x_544_ = lean_string_append(v___x_542_, v___x_543_);
v___x_545_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v___y_539_);
lean_dec(v___y_539_);
v___x_546_ = lean_string_append(v___x_544_, v___x_545_);
lean_dec_ref(v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
v___jp_548_:
{
lean_object* v___x_549_; 
v___x_549_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__3));
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(lean_object* v_path_597_, lean_object* v___x_598_, lean_object* v___x_599_, lean_object* v_inst_600_, lean_object* v_R_601_, lean_object* v_a_602_, lean_object* v_b_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_597_, v___x_598_, v___x_599_, v_a_602_, v_b_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___boxed(lean_object* v_path_605_, lean_object* v___x_606_, lean_object* v___x_607_, lean_object* v_inst_608_, lean_object* v_R_609_, lean_object* v_a_610_, lean_object* v_b_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(v_path_605_, v___x_606_, v___x_607_, v_inst_608_, v_R_609_, v_a_610_, v_b_611_);
lean_dec_ref(v___x_606_);
return v_res_612_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(uint32_t v_c_613_){
_start:
{
uint8_t v___y_661_; uint32_t v___x_666_; uint8_t v___x_667_; 
v___x_666_ = 65;
v___x_667_ = lean_uint32_dec_le(v___x_666_, v_c_613_);
if (v___x_667_ == 0)
{
v___y_661_ = v___x_667_;
goto v___jp_660_;
}
else
{
uint32_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = 90;
v___x_669_ = lean_uint32_dec_le(v_c_613_, v___x_668_);
v___y_661_ = v___x_669_;
goto v___jp_660_;
}
v___jp_614_:
{
uint32_t v___x_615_; uint8_t v___x_616_; 
v___x_615_ = 45;
v___x_616_ = lean_uint32_dec_eq(v_c_613_, v___x_615_);
if (v___x_616_ == 0)
{
uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 46;
v___x_618_ = lean_uint32_dec_eq(v_c_613_, v___x_617_);
if (v___x_618_ == 0)
{
uint32_t v___x_619_; uint8_t v___x_620_; 
v___x_619_ = 95;
v___x_620_ = lean_uint32_dec_eq(v_c_613_, v___x_619_);
if (v___x_620_ == 0)
{
uint32_t v___x_621_; uint8_t v___x_622_; 
v___x_621_ = 126;
v___x_622_ = lean_uint32_dec_eq(v_c_613_, v___x_621_);
if (v___x_622_ == 0)
{
uint32_t v___x_623_; uint8_t v___x_624_; 
v___x_623_ = 58;
v___x_624_ = lean_uint32_dec_eq(v_c_613_, v___x_623_);
if (v___x_624_ == 0)
{
uint32_t v___x_625_; uint8_t v___x_626_; 
v___x_625_ = 47;
v___x_626_ = lean_uint32_dec_eq(v_c_613_, v___x_625_);
if (v___x_626_ == 0)
{
uint32_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = 63;
v___x_628_ = lean_uint32_dec_eq(v_c_613_, v___x_627_);
if (v___x_628_ == 0)
{
uint32_t v___x_629_; uint8_t v___x_630_; 
v___x_629_ = 35;
v___x_630_ = lean_uint32_dec_eq(v_c_613_, v___x_629_);
if (v___x_630_ == 0)
{
uint32_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 91;
v___x_632_ = lean_uint32_dec_eq(v_c_613_, v___x_631_);
if (v___x_632_ == 0)
{
uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 93;
v___x_634_ = lean_uint32_dec_eq(v_c_613_, v___x_633_);
if (v___x_634_ == 0)
{
uint32_t v___x_635_; uint8_t v___x_636_; 
v___x_635_ = 64;
v___x_636_ = lean_uint32_dec_eq(v_c_613_, v___x_635_);
if (v___x_636_ == 0)
{
uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = 33;
v___x_638_ = lean_uint32_dec_eq(v_c_613_, v___x_637_);
if (v___x_638_ == 0)
{
uint32_t v___x_639_; uint8_t v___x_640_; 
v___x_639_ = 36;
v___x_640_ = lean_uint32_dec_eq(v_c_613_, v___x_639_);
if (v___x_640_ == 0)
{
uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = 38;
v___x_642_ = lean_uint32_dec_eq(v_c_613_, v___x_641_);
if (v___x_642_ == 0)
{
uint32_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = 39;
v___x_644_ = lean_uint32_dec_eq(v_c_613_, v___x_643_);
if (v___x_644_ == 0)
{
uint32_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = 42;
v___x_646_ = lean_uint32_dec_eq(v_c_613_, v___x_645_);
if (v___x_646_ == 0)
{
uint32_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = 43;
v___x_648_ = lean_uint32_dec_eq(v_c_613_, v___x_647_);
if (v___x_648_ == 0)
{
uint32_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = 44;
v___x_650_ = lean_uint32_dec_eq(v_c_613_, v___x_649_);
if (v___x_650_ == 0)
{
uint32_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = 59;
v___x_652_ = lean_uint32_dec_eq(v_c_613_, v___x_651_);
if (v___x_652_ == 0)
{
uint32_t v___x_653_; uint8_t v___x_654_; 
v___x_653_ = 61;
v___x_654_ = lean_uint32_dec_eq(v_c_613_, v___x_653_);
return v___x_654_;
}
else
{
return v___x_652_;
}
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
v___jp_655_:
{
uint32_t v___x_656_; uint8_t v___x_657_; 
v___x_656_ = 48;
v___x_657_ = lean_uint32_dec_le(v___x_656_, v_c_613_);
if (v___x_657_ == 0)
{
goto v___jp_614_;
}
else
{
uint32_t v___x_658_; uint8_t v___x_659_; 
v___x_658_ = 57;
v___x_659_ = lean_uint32_dec_le(v_c_613_, v___x_658_);
if (v___x_659_ == 0)
{
goto v___jp_614_;
}
else
{
return v___x_659_;
}
}
}
v___jp_660_:
{
if (v___y_661_ == 0)
{
uint32_t v___x_662_; uint8_t v___x_663_; 
v___x_662_ = 97;
v___x_663_ = lean_uint32_dec_le(v___x_662_, v_c_613_);
if (v___x_663_ == 0)
{
goto v___jp_655_;
}
else
{
uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = 122;
v___x_665_ = lean_uint32_dec_le(v_c_613_, v___x_664_);
if (v___x_665_ == 0)
{
goto v___jp_655_;
}
else
{
return v___x_665_;
}
}
}
else
{
return v___y_661_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar___boxed(lean_object* v_c_670_){
_start:
{
uint32_t v_c_boxed_671_; uint8_t v_res_672_; lean_object* v_r_673_; 
v_c_boxed_671_ = lean_unbox_uint32(v_c_670_);
lean_dec(v_c_670_);
v_res_672_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v_c_boxed_671_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(lean_object* v_s_674_, lean_object* v___x_675_, lean_object* v___x_676_, uint32_t v___x_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_snd_679_; lean_object* v_snd_680_; lean_object* v_fst_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_749_; 
v_snd_679_ = lean_ctor_get(v_a_678_, 1);
lean_inc(v_snd_679_);
v_snd_680_ = lean_ctor_get(v_snd_679_, 1);
lean_inc(v_snd_680_);
v_fst_681_ = lean_ctor_get(v_a_678_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v_a_678_, 1);
lean_dec(v_unused_750_);
v___x_683_ = v_a_678_;
v_isShared_684_ = v_isSharedCheck_749_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_fst_681_);
lean_dec(v_a_678_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_749_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v_fst_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_747_; 
v_fst_685_ = lean_ctor_get(v_snd_679_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v_snd_679_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v_snd_679_, 1);
lean_dec(v_unused_748_);
v___x_687_ = v_snd_679_;
v_isShared_688_ = v_isSharedCheck_747_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_fst_685_);
lean_dec(v_snd_679_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_747_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_fst_689_; lean_object* v_snd_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_746_; 
v_fst_689_ = lean_ctor_get(v_snd_680_, 0);
v_snd_690_ = lean_ctor_get(v_snd_680_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_snd_680_);
if (v_isSharedCheck_746_ == 0)
{
v___x_692_ = v_snd_680_;
v_isShared_693_ = v_isSharedCheck_746_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_snd_690_);
lean_inc(v_fst_689_);
lean_dec(v_snd_680_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_746_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; uint8_t v_decide_695_; 
v___x_694_ = lean_string_utf8_byte_size(v_s_674_);
v_decide_695_ = lean_nat_dec_eq(v_snd_690_, v___x_694_);
if (v_decide_695_ == 0)
{
uint32_t v___x_696_; lean_object* v___x_697_; uint8_t v___y_730_; uint8_t v___x_735_; 
v___x_696_ = lean_string_utf8_get_fast(v_s_674_, v_snd_690_);
v___x_697_ = lean_string_utf8_next_fast(v_s_674_, v_snd_690_);
v___x_735_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v___x_696_);
if (v___x_735_ == 0)
{
v___y_730_ = v___x_735_;
goto v___jp_729_;
}
else
{
uint8_t v_decide_736_; 
v_decide_736_ = lean_nat_dec_eq(v___x_697_, v___x_694_);
if (v_decide_736_ == 0)
{
v___y_730_ = v___x_735_;
goto v___jp_729_;
}
else
{
goto v___jp_698_;
}
}
v___jp_698_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_string_utf8_extract_fast(v_s_674_, v___x_675_, v_snd_690_);
v___x_700_ = l___private_Lean_DocString_Links_0__Lean_rw(v___x_699_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_676_);
lean_ctor_set(v___x_702_, 1, v_snd_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v_a_701_);
lean_ctor_set(v___x_692_, 0, v___x_702_);
v___x_704_ = v___x_692_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_a_701_);
v___x_704_ = v_reuseFailAlloc_714_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_705_ = lean_array_push(v_fst_685_, v___x_704_);
v___x_706_ = lean_string_push(v_fst_681_, v___x_677_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_697_);
lean_ctor_set(v___x_687_, 0, v_fst_689_);
v___x_708_ = v___x_687_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_fst_689_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_697_);
v___x_708_ = v_reuseFailAlloc_713_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_710_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v___x_708_);
lean_ctor_set(v___x_683_, 0, v___x_705_);
v___x_710_ = v___x_683_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_708_);
v___x_710_ = v_reuseFailAlloc_712_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_706_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
return v___x_711_;
}
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
lean_dec(v_snd_690_);
lean_dec(v_fst_689_);
lean_dec(v___x_676_);
v_a_715_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_700_, 1);
v___x_716_ = l_Lean_manualRoot;
v___x_717_ = lean_string_append(v_fst_681_, v___x_716_);
v___x_718_ = lean_string_append(v___x_717_, v_a_715_);
lean_dec(v_a_715_);
v___x_719_ = lean_string_push(v___x_718_, v___x_696_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_697_);
lean_ctor_set(v___x_692_, 0, v___x_697_);
v___x_721_ = v___x_692_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_697_);
v___x_721_ = v_reuseFailAlloc_728_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_721_);
v___x_723_ = v___x_687_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_fst_685_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_727_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v___x_723_);
lean_ctor_set(v___x_683_, 0, v___x_719_);
v___x_725_ = v___x_683_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
v___jp_729_:
{
if (v___y_730_ == 0)
{
goto v___jp_698_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_del_object(v___x_692_);
lean_dec(v_snd_690_);
lean_del_object(v___x_687_);
lean_del_object(v___x_683_);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v_fst_689_);
lean_ctor_set(v___x_731_, 1, v___x_697_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v_fst_685_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_fst_681_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v_a_678_ = v___x_733_;
goto _start;
}
}
}
else
{
lean_object* v___x_738_; 
lean_dec(v___x_676_);
if (v_isShared_693_ == 0)
{
v___x_738_ = v___x_692_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_fst_689_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_snd_690_);
v___x_738_ = v_reuseFailAlloc_745_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_740_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_738_);
v___x_740_ = v___x_687_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_fst_685_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___x_738_);
v___x_740_ = v_reuseFailAlloc_744_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_742_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v___x_740_);
v___x_742_ = v___x_683_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_fst_681_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg___boxed(lean_object* v_s_751_, lean_object* v___x_752_, lean_object* v___x_753_, lean_object* v___x_754_, lean_object* v_a_755_){
_start:
{
uint32_t v___x_2314__boxed_756_; lean_object* v_res_757_; 
v___x_2314__boxed_756_ = lean_unbox_uint32(v___x_754_);
lean_dec(v___x_754_);
v_res_757_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_751_, v___x_752_, v___x_753_, v___x_2314__boxed_756_, v_a_755_);
lean_dec(v___x_752_);
lean_dec_ref(v_s_751_);
return v_res_757_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v_scheme_759_; lean_object* v___x_760_; 
v_scheme_759_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0));
v___x_760_ = lean_string_utf8_byte_size(v_scheme_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(lean_object* v_s_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_snd_763_; lean_object* v_fst_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_828_; 
v_snd_763_ = lean_ctor_get(v_a_762_, 1);
v_fst_764_ = lean_ctor_get(v_a_762_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v_a_762_);
if (v_isSharedCheck_828_ == 0)
{
v___x_766_ = v_a_762_;
v_isShared_767_ = v_isSharedCheck_828_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_snd_763_);
lean_inc(v_fst_764_);
lean_dec(v_a_762_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_828_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v_fst_768_; lean_object* v_snd_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_827_; 
v_fst_768_ = lean_ctor_get(v_snd_763_, 0);
v_snd_769_ = lean_ctor_get(v_snd_763_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_snd_763_);
if (v_isSharedCheck_827_ == 0)
{
v___x_771_ = v_snd_763_;
v_isShared_772_ = v_isSharedCheck_827_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_snd_769_);
lean_inc(v_fst_768_);
lean_dec(v_snd_763_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_827_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; uint8_t v_decide_774_; 
v___x_773_ = lean_string_utf8_byte_size(v_s_761_);
v_decide_774_ = lean_nat_dec_eq(v_snd_769_, v___x_773_);
if (v_decide_774_ == 0)
{
lean_object* v_scheme_775_; uint32_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_scheme_775_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0));
v___x_776_ = lean_string_utf8_get_fast(v_s_761_, v_snd_769_);
v___x_777_ = lean_string_utf8_next_fast(v_s_761_, v_snd_769_);
v___x_787_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1);
v___x_788_ = lean_nat_sub(v___x_773_, v_snd_769_);
v___x_789_ = lean_nat_dec_le(v___x_787_, v___x_788_);
lean_dec(v___x_788_);
if (v___x_789_ == 0)
{
lean_dec(v_snd_769_);
goto v___jp_778_;
}
else
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_string_memcmp(v_s_761_, v_scheme_775_, v_snd_769_, v___x_790_, v___x_787_);
if (v___x_791_ == 0)
{
lean_dec(v_snd_769_);
goto v___jp_778_;
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_snd_799_; lean_object* v_snd_800_; lean_object* v_fst_801_; lean_object* v_fst_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_819_; 
lean_del_object(v___x_771_);
lean_del_object(v___x_766_);
lean_inc(v_snd_769_);
lean_inc_ref(v_s_761_);
v___x_792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_792_, 0, v_s_761_);
lean_ctor_set(v___x_792_, 1, v_snd_769_);
lean_ctor_set(v___x_792_, 2, v___x_773_);
v___x_793_ = l_String_Slice_pos_x21(v___x_792_, v___x_787_);
lean_dec_ref_known(v___x_792_, 3);
v___x_794_ = lean_nat_add(v_snd_769_, v___x_793_);
lean_dec(v___x_793_);
lean_inc(v___x_794_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_777_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_fst_768_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_fst_764_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_761_, v___x_794_, v_snd_769_, v___x_776_, v___x_797_);
lean_dec(v___x_794_);
v_snd_799_ = lean_ctor_get(v___x_798_, 1);
lean_inc(v_snd_799_);
v_snd_800_ = lean_ctor_get(v_snd_799_, 1);
lean_inc(v_snd_800_);
v_fst_801_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_fst_801_);
lean_dec_ref(v___x_798_);
v_fst_802_ = lean_ctor_get(v_snd_799_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_snd_799_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_snd_799_, 1);
lean_dec(v_unused_820_);
v___x_804_ = v_snd_799_;
v_isShared_805_ = v_isSharedCheck_819_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_fst_802_);
lean_dec(v_snd_799_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_819_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v_fst_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_817_; 
v_fst_806_ = lean_ctor_get(v_snd_800_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v_snd_800_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_snd_800_, 1);
lean_dec(v_unused_818_);
v___x_808_ = v_snd_800_;
v_isShared_809_ = v_isSharedCheck_817_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_fst_806_);
lean_dec(v_snd_800_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_817_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v_fst_806_);
lean_ctor_set(v___x_808_, 0, v_fst_802_);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_fst_802_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_fst_806_);
v___x_811_ = v_reuseFailAlloc_816_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_813_; 
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v___x_811_);
lean_ctor_set(v___x_804_, 0, v_fst_801_);
v___x_813_ = v___x_804_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_fst_801_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_811_);
v___x_813_ = v_reuseFailAlloc_815_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
v_a_762_ = v___x_813_;
goto _start;
}
}
}
}
}
}
v___jp_778_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = lean_string_push(v_fst_764_, v___x_776_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_777_);
v___x_781_ = v___x_771_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_fst_768_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_777_);
v___x_781_ = v_reuseFailAlloc_786_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v___x_781_);
lean_ctor_set(v___x_766_, 0, v___x_779_);
v___x_783_ = v___x_766_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___x_781_);
v___x_783_ = v_reuseFailAlloc_785_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
v_a_762_ = v___x_783_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_822_; 
lean_dec_ref(v_s_761_);
if (v_isShared_772_ == 0)
{
v___x_822_ = v___x_771_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_fst_768_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_snd_769_);
v___x_822_ = v_reuseFailAlloc_826_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_824_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v___x_822_);
v___x_824_ = v___x_766_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_fst_764_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore(lean_object* v_s_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v_snd_840_; lean_object* v_fst_841_; lean_object* v_fst_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v___x_838_ = ((lean_object*)(l_Lean_rewriteManualLinksCore___closed__2));
v___x_839_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(v_s_837_, v___x_838_);
v_snd_840_ = lean_ctor_get(v___x_839_, 1);
lean_inc(v_snd_840_);
v_fst_841_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_fst_841_);
lean_dec_ref(v___x_839_);
v_fst_842_ = lean_ctor_get(v_snd_840_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v_snd_840_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v_snd_840_, 1);
lean_dec(v_unused_850_);
v___x_844_ = v_snd_840_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_fst_842_);
lean_dec(v_snd_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_fst_841_);
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_fst_842_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_fst_841_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0(lean_object* v_s_851_, lean_object* v___x_852_, lean_object* v___x_853_, uint32_t v___x_854_, lean_object* v_inst_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_851_, v___x_852_, v___x_853_, v___x_854_, v_a_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___boxed(lean_object* v_s_858_, lean_object* v___x_859_, lean_object* v___x_860_, lean_object* v___x_861_, lean_object* v_inst_862_, lean_object* v_a_863_){
_start:
{
uint32_t v___x_2599__boxed_864_; lean_object* v_res_865_; 
v___x_2599__boxed_864_ = lean_unbox_uint32(v___x_861_);
lean_dec(v___x_861_);
v_res_865_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0(v_s_858_, v___x_859_, v___x_860_, v___x_2599__boxed_864_, v_inst_862_, v_a_863_);
lean_dec(v___x_859_);
lean_dec_ref(v_s_858_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1(lean_object* v_s_866_, lean_object* v_inst_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(v_s_866_, v_a_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(lean_object* v_docString_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
if (lean_obj_tag(v_a_874_) == 0)
{
lean_object* v___x_876_; 
v___x_876_ = l_List_reverse___redArg(v_a_875_);
return v___x_876_;
}
else
{
lean_object* v_head_877_; lean_object* v_fst_878_; lean_object* v_tail_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_898_; 
v_head_877_ = lean_ctor_get(v_a_874_, 0);
lean_inc(v_head_877_);
v_fst_878_ = lean_ctor_get(v_head_877_, 0);
lean_inc(v_fst_878_);
v_tail_879_ = lean_ctor_get(v_a_874_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_a_874_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_a_874_, 0);
lean_dec(v_unused_899_);
v___x_881_ = v_a_874_;
v_isShared_882_ = v_isSharedCheck_898_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_tail_879_);
lean_dec(v_a_874_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_898_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v_snd_883_; lean_object* v_start_884_; lean_object* v_stop_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v_snd_883_ = lean_ctor_get(v_head_877_, 1);
lean_inc(v_snd_883_);
lean_dec(v_head_877_);
v_start_884_ = lean_ctor_get(v_fst_878_, 0);
lean_inc(v_start_884_);
v_stop_885_ = lean_ctor_get(v_fst_878_, 1);
lean_inc(v_stop_885_);
lean_dec(v_fst_878_);
v___x_886_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0));
v___x_887_ = lean_string_utf8_extract(v_docString_873_, v_start_884_, v_stop_885_);
lean_dec(v_stop_885_);
lean_dec(v_start_884_);
v___x_888_ = lean_string_append(v___x_886_, v___x_887_);
lean_dec_ref(v___x_887_);
v___x_889_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1));
v___x_890_ = lean_string_append(v___x_888_, v___x_889_);
v___x_891_ = lean_string_append(v___x_890_, v_snd_883_);
lean_dec(v_snd_883_);
v___x_892_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_893_ = lean_string_append(v___x_891_, v___x_892_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v_a_875_);
lean_ctor_set(v___x_881_, 0, v___x_893_);
v___x_895_ = v___x_881_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_a_875_);
v___x_895_ = v_reuseFailAlloc_897_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
v_a_874_ = v_tail_879_;
v_a_875_ = v___x_895_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___boxed(lean_object* v_docString_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_900_, v_a_901_, v_a_902_);
lean_dec_ref(v_docString_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
if (lean_obj_tag(v_x_905_) == 0)
{
return v_x_904_;
}
else
{
lean_object* v_head_906_; lean_object* v_tail_907_; lean_object* v___x_908_; 
v_head_906_ = lean_ctor_get(v_x_905_, 0);
v_tail_907_ = lean_ctor_get(v_x_905_, 1);
v___x_908_ = lean_string_append(v_x_904_, v_head_906_);
v_x_904_ = v___x_908_;
v_x_905_ = v_tail_907_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1___boxed(lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v_x_910_, v_x_911_);
lean_dec(v_x_911_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks(lean_object* v_docString_914_){
_start:
{
lean_object* v___x_916_; lean_object* v_fst_917_; lean_object* v_snd_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
lean_inc_ref(v_docString_914_);
v___x_916_ = l_Lean_rewriteManualLinksCore(v_docString_914_);
v_fst_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_fst_917_);
v_snd_918_ = lean_ctor_get(v___x_916_, 1);
lean_inc(v_snd_918_);
lean_dec_ref(v___x_916_);
v___x_919_ = lean_array_get_size(v_fst_917_);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_nat_dec_eq(v___x_919_, v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_922_ = ((lean_object*)(l_Lean_rewriteManualLinks___closed__0));
v___x_923_ = lean_array_to_list(v_fst_917_);
v___x_924_ = lean_box(0);
v___x_925_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_914_, v___x_923_, v___x_924_);
lean_dec_ref(v_docString_914_);
v___x_926_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_927_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_926_, v___x_925_);
lean_dec(v___x_925_);
v___x_928_ = lean_string_append(v___x_922_, v___x_927_);
lean_dec_ref(v___x_927_);
v___x_929_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_930_ = lean_string_append(v_snd_918_, v___x_929_);
v___x_931_ = lean_string_append(v___x_930_, v___x_928_);
lean_dec_ref(v___x_928_);
return v___x_931_;
}
else
{
lean_dec(v_fst_917_);
lean_dec_ref(v_docString_914_);
return v_snd_918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks___boxed(lean_object* v_docString_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_rewriteManualLinks(v_docString_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(lean_object* v_docString_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
if (lean_obj_tag(v_a_939_) == 0)
{
lean_object* v___x_941_; 
v___x_941_ = l_List_reverse___redArg(v_a_940_);
return v___x_941_;
}
else
{
lean_object* v_head_942_; lean_object* v_fst_943_; lean_object* v_tail_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_968_; 
v_head_942_ = lean_ctor_get(v_a_939_, 0);
lean_inc(v_head_942_);
v_fst_943_ = lean_ctor_get(v_head_942_, 0);
lean_inc(v_fst_943_);
v_tail_944_ = lean_ctor_get(v_a_939_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v_a_939_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v_a_939_, 0);
lean_dec(v_unused_969_);
v___x_946_ = v_a_939_;
v_isShared_947_ = v_isSharedCheck_968_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_tail_944_);
lean_dec(v_a_939_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_968_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_snd_948_; lean_object* v_start_949_; lean_object* v_stop_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v_snd_948_ = lean_ctor_get(v_head_942_, 1);
lean_inc(v_snd_948_);
lean_dec(v_head_942_);
v_start_949_ = lean_ctor_get(v_fst_943_, 0);
lean_inc(v_start_949_);
v_stop_950_ = lean_ctor_get(v_fst_943_, 1);
lean_inc(v_stop_950_);
lean_dec(v_fst_943_);
v___x_951_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0));
v___x_952_ = lean_string_utf8_extract(v_docString_938_, v_start_949_, v_stop_950_);
lean_dec(v_stop_950_);
lean_dec(v_start_949_);
v___x_953_ = l_String_quote(v___x_952_);
v___x_954_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
v___x_955_ = l_Std_Format_defWidth;
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = l_Std_Format_pretty(v___x_954_, v___x_955_, v___x_956_, v___x_956_);
v___x_958_ = lean_string_append(v___x_951_, v___x_957_);
lean_dec_ref(v___x_957_);
v___x_959_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1));
v___x_960_ = lean_string_append(v___x_958_, v___x_959_);
v___x_961_ = lean_string_append(v___x_960_, v_snd_948_);
lean_dec(v_snd_948_);
v___x_962_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2));
v___x_963_ = lean_string_append(v___x_961_, v___x_962_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v_a_940_);
lean_ctor_set(v___x_946_, 0, v___x_963_);
v___x_965_ = v___x_946_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_a_940_);
v___x_965_ = v_reuseFailAlloc_967_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
v_a_939_ = v_tail_944_;
v_a_940_ = v___x_965_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___boxed(lean_object* v_docString_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_970_, v_a_971_, v_a_972_);
lean_dec_ref(v_docString_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString(lean_object* v_docString_975_){
_start:
{
lean_object* v___x_977_; lean_object* v_fst_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
lean_inc_ref(v_docString_975_);
v___x_977_ = l_Lean_rewriteManualLinksCore(v_docString_975_);
v_fst_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_fst_978_);
lean_dec_ref(v___x_977_);
v___x_979_ = lean_array_get_size(v_fst_978_);
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_nat_dec_eq(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_982_ = ((lean_object*)(l_Lean_validateBuiltinDocString___closed__0));
v___x_983_ = lean_array_to_list(v_fst_978_);
v___x_984_ = lean_box(0);
v___x_985_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_975_, v___x_983_, v___x_984_);
lean_dec_ref(v_docString_975_);
v___x_986_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_987_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_986_, v___x_985_);
lean_dec(v___x_985_);
v___x_988_ = lean_string_append(v___x_982_, v___x_987_);
lean_dec_ref(v___x_987_);
v___x_989_ = lean_mk_io_user_error(v___x_988_);
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; 
lean_dec(v_fst_978_);
lean_dec_ref(v_docString_975_);
v___x_991_ = lean_box(0);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString___boxed(lean_object* v_docString_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_validateBuiltinDocString(v_docString_993_);
return v_res_995_;
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
