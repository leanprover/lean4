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
lean_object* v_currPos_447_; lean_object* v_searcher_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_474_; 
v_currPos_447_ = lean_ctor_get(v_a_437_, 0);
v_searcher_448_ = lean_ctor_get(v_a_437_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_a_437_);
if (v_isSharedCheck_474_ == 0)
{
v___x_450_ = v_a_437_;
v_isShared_451_ = v_isSharedCheck_474_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_searcher_448_);
lean_inc(v_currPos_447_);
lean_dec(v_a_437_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_474_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_startInclusive_452_; lean_object* v_endExclusive_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_startInclusive_452_ = lean_ctor_get(v___x_435_, 1);
v_endExclusive_453_ = lean_ctor_get(v___x_435_, 2);
v___x_454_ = lean_nat_sub(v_endExclusive_453_, v_startInclusive_452_);
v___x_455_ = lean_nat_dec_eq(v_searcher_448_, v___x_454_);
lean_dec(v___x_454_);
if (v___x_455_ == 0)
{
uint32_t v___x_456_; uint32_t v___x_457_; uint8_t v___x_458_; 
v___x_456_ = 47;
v___x_457_ = lean_string_utf8_get_fast(v_path_434_, v_searcher_448_);
v___x_458_ = lean_uint32_dec_eq(v___x_457_, v___x_456_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = lean_string_utf8_next_fast(v_path_434_, v_searcher_448_);
lean_dec(v_searcher_448_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_459_);
v___x_461_ = v___x_450_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_currPos_447_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_459_);
v___x_461_ = v_reuseFailAlloc_463_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
v_a_437_ = v___x_461_;
goto _start;
}
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v_slice_467_; lean_object* v_nextIt_469_; 
v___x_464_ = lean_string_utf8_next_fast(v_path_434_, v_searcher_448_);
v___x_465_ = lean_nat_sub(v___x_464_, v_searcher_448_);
v___x_466_ = lean_nat_add(v_searcher_448_, v___x_465_);
lean_dec(v___x_465_);
v_slice_467_ = l_String_Slice_subslice_x21(v___x_435_, v_currPos_447_, v_searcher_448_);
lean_inc(v___x_466_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_466_);
lean_ctor_set(v___x_450_, 0, v___x_466_);
v_nextIt_469_ = v___x_450_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_466_);
v_nextIt_469_ = v_reuseFailAlloc_472_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v_startInclusive_470_; lean_object* v_endExclusive_471_; 
v_startInclusive_470_ = lean_ctor_get(v_slice_467_, 0);
lean_inc(v_startInclusive_470_);
v_endExclusive_471_ = lean_ctor_get(v_slice_467_, 1);
lean_inc(v_endExclusive_471_);
lean_dec_ref(v_slice_467_);
v_it_440_ = v_nextIt_469_;
v_startInclusive_441_ = v_startInclusive_470_;
v_endExclusive_442_ = v_endExclusive_471_;
goto v___jp_439_;
}
}
}
else
{
lean_object* v___x_473_; 
lean_del_object(v___x_450_);
lean_dec(v_searcher_448_);
v___x_473_ = lean_box(1);
lean_inc(v___x_436_);
v_it_440_ = v___x_473_;
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
lean_dec_ref(v___x_443_);
v___x_445_ = lean_array_push(v_b_438_, v___x_444_);
v_a_437_ = v_it_440_;
v_b_438_ = v___x_445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg___boxed(lean_object* v_path_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v_a_478_, lean_object* v_b_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_475_, v___x_476_, v___x_477_, v_a_478_, v_b_479_);
lean_dec_ref(v___x_476_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
return v_x_481_;
}
else
{
lean_object* v_head_483_; lean_object* v_tail_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_head_483_ = lean_ctor_get(v_x_482_, 0);
v_tail_484_ = lean_ctor_get(v_x_482_, 1);
v___x_485_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_486_ = lean_string_append(v_x_481_, v___x_485_);
v___x_487_ = lean_string_append(v___x_486_, v_head_483_);
v_x_481_ = v___x_487_;
v_x_482_ = v_tail_484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0___boxed(lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v_x_489_, v_x_490_);
lean_dec(v_x_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(lean_object* v_x_495_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
lean_object* v___x_496_; 
v___x_496_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0));
return v___x_496_;
}
else
{
lean_object* v_tail_497_; 
v_tail_497_ = lean_ctor_get(v_x_495_, 1);
if (lean_obj_tag(v_tail_497_) == 0)
{
lean_object* v_head_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_head_498_ = lean_ctor_get(v_x_495_, 0);
v___x_499_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_500_ = lean_string_append(v___x_499_, v_head_498_);
v___x_501_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2));
v___x_502_ = lean_string_append(v___x_500_, v___x_501_);
return v___x_502_;
}
else
{
lean_object* v_head_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint32_t v___x_507_; lean_object* v___x_508_; 
v_head_503_ = lean_ctor_get(v_x_495_, 0);
v___x_504_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_505_ = lean_string_append(v___x_504_, v_head_503_);
v___x_506_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v___x_505_, v_tail_497_);
v___x_507_ = 93;
v___x_508_ = lean_string_push(v___x_506_, v___x_507_);
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___boxed(lean_object* v_x_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v_x_509_);
lean_dec(v_x_509_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rw(lean_object* v_path_521_){
_start:
{
lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_string_utf8_byte_size(v_path_521_);
lean_inc_ref(v_path_521_);
v___x_549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_549_, 0, v_path_521_);
lean_ctor_set(v___x_549_, 1, v___x_547_);
lean_ctor_set(v___x_549_, 2, v___x_548_);
v___x_550_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(v___x_549_);
v___x_551_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__4));
v___x_552_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_521_, v___x_549_, v___x_548_, v___x_550_, v___x_551_);
lean_dec_ref(v___x_549_);
v___x_553_ = lean_array_to_list(v___x_552_);
if (lean_obj_tag(v___x_553_) == 0)
{
goto v___jp_545_;
}
else
{
lean_object* v_head_554_; lean_object* v_tail_555_; lean_object* v_kind_557_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_head_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_head_554_);
v_tail_555_ = lean_ctor_get(v___x_553_, 1);
lean_inc(v_tail_555_);
lean_dec_ref(v___x_553_);
v___x_592_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_593_ = lean_string_dec_eq(v_head_554_, v___x_592_);
if (v___x_593_ == 0)
{
v_kind_557_ = v_head_554_;
goto v___jp_556_;
}
else
{
lean_dec(v_head_554_);
if (lean_obj_tag(v_tail_555_) == 0)
{
goto v___jp_545_;
}
else
{
v_kind_557_ = v___x_592_;
goto v___jp_556_;
}
}
v___jp_556_:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_558_, v_kind_557_);
if (lean_obj_tag(v___x_559_) == 1)
{
if (lean_obj_tag(v_tail_555_) == 1)
{
lean_object* v_tail_560_; 
v_tail_560_ = lean_ctor_get(v_tail_555_, 1);
if (lean_obj_tag(v_tail_560_) == 0)
{
lean_object* v_val_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_583_; 
v_val_561_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_583_ == 0)
{
v___x_563_ = v___x_559_;
v_isShared_564_ = v_isSharedCheck_583_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_val_561_);
lean_dec(v___x_559_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_583_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_head_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v_head_565_ = lean_ctor_get(v_tail_555_, 0);
lean_inc(v_head_565_);
lean_dec_ref(v_tail_555_);
v___x_566_ = lean_string_utf8_byte_size(v_head_565_);
v___x_567_ = lean_nat_dec_eq(v___x_566_, v___x_547_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
lean_dec_ref(v_kind_557_);
v___x_568_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_569_ = lean_string_append(v___x_568_, v_val_561_);
lean_dec(v_val_561_);
v___x_570_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_571_ = lean_string_append(v___x_569_, v___x_570_);
v___x_572_ = lean_string_append(v___x_571_, v_head_565_);
lean_dec(v_head_565_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_572_);
v___x_574_ = v___x_563_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
lean_dec(v_head_565_);
lean_dec(v_val_561_);
v___x_576_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__5));
v___x_577_ = lean_string_append(v___x_576_, v_kind_557_);
lean_dec_ref(v_kind_557_);
v___x_578_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__6));
v___x_579_ = lean_string_append(v___x_577_, v___x_578_);
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 0);
lean_ctor_set(v___x_563_, 0, v___x_579_);
v___x_581_ = v___x_563_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_dec_ref(v___x_559_);
v___y_536_ = v_kind_557_;
v___y_537_ = v_tail_555_;
goto v___jp_535_;
}
}
else
{
lean_dec_ref(v___x_559_);
v___y_536_ = v_kind_557_;
v___y_537_ = v_tail_555_;
goto v___jp_535_;
}
}
else
{
lean_object* v_buckets_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
lean_dec(v___x_559_);
lean_dec(v_tail_555_);
v_buckets_584_ = lean_ctor_get(v___x_558_, 1);
v___x_585_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_586_ = lean_box(0);
v___x_587_ = lean_array_get_size(v_buckets_584_);
v___x_588_ = lean_nat_dec_lt(v___x_547_, v___x_587_);
if (v___x_588_ == 0)
{
v___y_523_ = v_kind_557_;
v___y_524_ = v___x_585_;
v___y_525_ = v___x_586_;
goto v___jp_522_;
}
else
{
size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_usize_of_nat(v___x_587_);
v___x_590_ = ((size_t)0ULL);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_584_, v___x_589_, v___x_590_, v___x_586_);
v___y_523_ = v_kind_557_;
v___y_524_ = v___x_585_;
v___y_525_ = v___x_591_;
goto v___jp_522_;
}
}
}
}
v___jp_522_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_acceptableKinds_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_526_ = lean_box(0);
v___x_527_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_525_, v___x_526_);
v_acceptableKinds_528_ = l_String_intercalate(v___y_524_, v___x_527_);
v___x_529_ = ((lean_object*)(l_Lean_manualLink___closed__3));
v___x_530_ = lean_string_append(v___x_529_, v___y_523_);
lean_dec_ref(v___y_523_);
v___x_531_ = ((lean_object*)(l_Lean_manualLink___closed__4));
v___x_532_ = lean_string_append(v___x_530_, v___x_531_);
v___x_533_ = lean_string_append(v___x_532_, v_acceptableKinds_528_);
lean_dec_ref(v_acceptableKinds_528_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
v___jp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_538_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__0));
v___x_539_ = lean_string_append(v___x_538_, v___y_536_);
lean_dec_ref(v___y_536_);
v___x_540_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__1));
v___x_541_ = lean_string_append(v___x_539_, v___x_540_);
v___x_542_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v___y_537_);
lean_dec(v___y_537_);
v___x_543_ = lean_string_append(v___x_541_, v___x_542_);
lean_dec_ref(v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
v___jp_545_:
{
lean_object* v___x_546_; 
v___x_546_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__3));
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(lean_object* v_path_594_, lean_object* v___x_595_, lean_object* v___x_596_, lean_object* v_inst_597_, lean_object* v_R_598_, lean_object* v_a_599_, lean_object* v_b_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_594_, v___x_595_, v___x_596_, v_a_599_, v_b_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___boxed(lean_object* v_path_602_, lean_object* v___x_603_, lean_object* v___x_604_, lean_object* v_inst_605_, lean_object* v_R_606_, lean_object* v_a_607_, lean_object* v_b_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(v_path_602_, v___x_603_, v___x_604_, v_inst_605_, v_R_606_, v_a_607_, v_b_608_);
lean_dec_ref(v___x_603_);
return v_res_609_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(uint32_t v_c_610_){
_start:
{
uint8_t v___y_612_; uint8_t v___y_654_; uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = 65;
v___x_665_ = lean_uint32_dec_le(v___x_664_, v_c_610_);
if (v___x_665_ == 0)
{
goto v___jp_659_;
}
else
{
uint32_t v___x_666_; uint8_t v___x_667_; 
v___x_666_ = 90;
v___x_667_ = lean_uint32_dec_le(v_c_610_, v___x_666_);
if (v___x_667_ == 0)
{
goto v___jp_659_;
}
else
{
return v___x_667_;
}
}
v___jp_611_:
{
if (v___y_612_ == 0)
{
uint32_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = 45;
v___x_614_ = lean_uint32_dec_eq(v_c_610_, v___x_613_);
if (v___x_614_ == 0)
{
uint32_t v___x_615_; uint8_t v___x_616_; 
v___x_615_ = 46;
v___x_616_ = lean_uint32_dec_eq(v_c_610_, v___x_615_);
if (v___x_616_ == 0)
{
uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 95;
v___x_618_ = lean_uint32_dec_eq(v_c_610_, v___x_617_);
if (v___x_618_ == 0)
{
uint32_t v___x_619_; uint8_t v___x_620_; 
v___x_619_ = 126;
v___x_620_ = lean_uint32_dec_eq(v_c_610_, v___x_619_);
if (v___x_620_ == 0)
{
uint32_t v___x_621_; uint8_t v___x_622_; 
v___x_621_ = 58;
v___x_622_ = lean_uint32_dec_eq(v_c_610_, v___x_621_);
if (v___x_622_ == 0)
{
uint32_t v___x_623_; uint8_t v___x_624_; 
v___x_623_ = 47;
v___x_624_ = lean_uint32_dec_eq(v_c_610_, v___x_623_);
if (v___x_624_ == 0)
{
uint32_t v___x_625_; uint8_t v___x_626_; 
v___x_625_ = 63;
v___x_626_ = lean_uint32_dec_eq(v_c_610_, v___x_625_);
if (v___x_626_ == 0)
{
uint32_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = 35;
v___x_628_ = lean_uint32_dec_eq(v_c_610_, v___x_627_);
if (v___x_628_ == 0)
{
uint32_t v___x_629_; uint8_t v___x_630_; 
v___x_629_ = 91;
v___x_630_ = lean_uint32_dec_eq(v_c_610_, v___x_629_);
if (v___x_630_ == 0)
{
uint32_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 93;
v___x_632_ = lean_uint32_dec_eq(v_c_610_, v___x_631_);
if (v___x_632_ == 0)
{
uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 64;
v___x_634_ = lean_uint32_dec_eq(v_c_610_, v___x_633_);
if (v___x_634_ == 0)
{
uint32_t v___x_635_; uint8_t v___x_636_; 
v___x_635_ = 33;
v___x_636_ = lean_uint32_dec_eq(v_c_610_, v___x_635_);
if (v___x_636_ == 0)
{
uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = 36;
v___x_638_ = lean_uint32_dec_eq(v_c_610_, v___x_637_);
if (v___x_638_ == 0)
{
uint32_t v___x_639_; uint8_t v___x_640_; 
v___x_639_ = 38;
v___x_640_ = lean_uint32_dec_eq(v_c_610_, v___x_639_);
if (v___x_640_ == 0)
{
uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = 39;
v___x_642_ = lean_uint32_dec_eq(v_c_610_, v___x_641_);
if (v___x_642_ == 0)
{
uint32_t v___x_643_; uint8_t v___x_644_; 
v___x_643_ = 42;
v___x_644_ = lean_uint32_dec_eq(v_c_610_, v___x_643_);
if (v___x_644_ == 0)
{
uint32_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = 43;
v___x_646_ = lean_uint32_dec_eq(v_c_610_, v___x_645_);
if (v___x_646_ == 0)
{
uint32_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = 44;
v___x_648_ = lean_uint32_dec_eq(v_c_610_, v___x_647_);
if (v___x_648_ == 0)
{
uint32_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = 59;
v___x_650_ = lean_uint32_dec_eq(v_c_610_, v___x_649_);
if (v___x_650_ == 0)
{
uint32_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = 61;
v___x_652_ = lean_uint32_dec_eq(v_c_610_, v___x_651_);
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
else
{
return v___y_612_;
}
}
v___jp_653_:
{
if (v___y_654_ == 0)
{
uint32_t v___x_655_; uint8_t v___x_656_; 
v___x_655_ = 48;
v___x_656_ = lean_uint32_dec_le(v___x_655_, v_c_610_);
if (v___x_656_ == 0)
{
v___y_612_ = v___x_656_;
goto v___jp_611_;
}
else
{
uint32_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = 57;
v___x_658_ = lean_uint32_dec_le(v_c_610_, v___x_657_);
v___y_612_ = v___x_658_;
goto v___jp_611_;
}
}
else
{
return v___y_654_;
}
}
v___jp_659_:
{
uint32_t v___x_660_; uint8_t v___x_661_; 
v___x_660_ = 97;
v___x_661_ = lean_uint32_dec_le(v___x_660_, v_c_610_);
if (v___x_661_ == 0)
{
v___y_654_ = v___x_661_;
goto v___jp_653_;
}
else
{
uint32_t v___x_662_; uint8_t v___x_663_; 
v___x_662_ = 122;
v___x_663_ = lean_uint32_dec_le(v_c_610_, v___x_662_);
v___y_654_ = v___x_663_;
goto v___jp_653_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar___boxed(lean_object* v_c_668_){
_start:
{
uint32_t v_c_boxed_669_; uint8_t v_res_670_; lean_object* v_r_671_; 
v_c_boxed_669_ = lean_unbox_uint32(v_c_668_);
lean_dec(v_c_668_);
v_res_670_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v_c_boxed_669_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_lookingAt(lean_object* v_goal_672_, lean_object* v_s_673_, lean_object* v_iter_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_string_utf8_byte_size(v_goal_672_);
v___x_677_ = l_String_Pos_Raw_substrEq(v_s_673_, v_iter_674_, v_goal_672_, v___x_675_, v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_lookingAt___boxed(lean_object* v_goal_678_, lean_object* v_s_679_, lean_object* v_iter_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_lookingAt(v_goal_678_, v_s_679_, v_iter_680_);
lean_dec_ref(v_s_679_);
lean_dec_ref(v_goal_678_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__0(lean_object* v_s_683_, lean_object* v_iter_x27_684_, lean_object* v_pre_685_, uint32_t v_c_686_, lean_object* v_b_687_){
_start:
{
lean_object* v_snd_688_; lean_object* v_snd_689_; lean_object* v_fst_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_758_; 
v_snd_688_ = lean_ctor_get(v_b_687_, 1);
lean_inc(v_snd_688_);
v_snd_689_ = lean_ctor_get(v_snd_688_, 1);
lean_inc(v_snd_689_);
v_fst_690_ = lean_ctor_get(v_b_687_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v_b_687_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v_b_687_, 1);
lean_dec(v_unused_759_);
v___x_692_ = v_b_687_;
v_isShared_693_ = v_isSharedCheck_758_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_fst_690_);
lean_dec(v_b_687_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_758_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_fst_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_756_; 
v_fst_694_ = lean_ctor_get(v_snd_688_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_snd_688_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v_snd_688_, 1);
lean_dec(v_unused_757_);
v___x_696_ = v_snd_688_;
v_isShared_697_ = v_isSharedCheck_756_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_fst_694_);
lean_dec(v_snd_688_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_756_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v_fst_698_; lean_object* v_snd_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_755_; 
v_fst_698_ = lean_ctor_get(v_snd_689_, 0);
v_snd_699_ = lean_ctor_get(v_snd_689_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_snd_689_);
if (v_isSharedCheck_755_ == 0)
{
v___x_701_ = v_snd_689_;
v_isShared_702_ = v_isSharedCheck_755_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_snd_699_);
lean_inc(v_fst_698_);
lean_dec(v_snd_689_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_755_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = lean_string_utf8_byte_size(v_s_683_);
v___x_704_ = lean_nat_dec_eq(v_snd_699_, v___x_703_);
if (v___x_704_ == 0)
{
uint32_t v_c_x27_705_; lean_object* v_iter_706_; uint8_t v___y_739_; uint8_t v___x_744_; 
v_c_x27_705_ = lean_string_utf8_get_fast(v_s_683_, v_snd_699_);
v_iter_706_ = lean_string_utf8_next_fast(v_s_683_, v_snd_699_);
v___x_744_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v_c_x27_705_);
if (v___x_744_ == 0)
{
v___y_739_ = v___x_744_;
goto v___jp_738_;
}
else
{
uint8_t v___x_745_; 
v___x_745_ = lean_nat_dec_eq(v_iter_706_, v___x_703_);
if (v___x_745_ == 0)
{
v___y_739_ = v___x_744_;
goto v___jp_738_;
}
else
{
goto v___jp_707_;
}
}
v___jp_707_:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_string_utf8_extract(v_s_683_, v_iter_x27_684_, v_snd_699_);
v___x_709_ = l___private_Lean_DocString_Links_0__Lean_rw(v___x_708_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref(v___x_709_);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_pre_685_);
lean_ctor_set(v___x_711_, 1, v_snd_699_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v_a_710_);
lean_ctor_set(v___x_701_, 0, v___x_711_);
v___x_713_ = v___x_701_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_a_710_);
v___x_713_ = v_reuseFailAlloc_723_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v_errors_714_; lean_object* v_out_715_; lean_object* v___x_717_; 
v_errors_714_ = lean_array_push(v_fst_694_, v___x_713_);
v_out_715_ = lean_string_push(v_fst_690_, v_c_686_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v_iter_706_);
lean_ctor_set(v___x_696_, 0, v_fst_698_);
v___x_717_ = v___x_696_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_fst_698_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_iter_706_);
v___x_717_ = v_reuseFailAlloc_722_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_717_);
lean_ctor_set(v___x_692_, 0, v_errors_714_);
v___x_719_ = v___x_692_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_errors_714_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_717_);
v___x_719_ = v_reuseFailAlloc_721_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; 
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_out_715_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
return v___x_720_;
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_out_727_; lean_object* v_out_728_; lean_object* v___x_730_; 
lean_dec(v_snd_699_);
lean_dec(v_fst_698_);
lean_dec(v_pre_685_);
v_a_724_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v___x_709_);
v___x_725_ = l_Lean_manualRoot;
v___x_726_ = lean_string_append(v_fst_690_, v___x_725_);
v_out_727_ = lean_string_append(v___x_726_, v_a_724_);
lean_dec(v_a_724_);
v_out_728_ = lean_string_push(v_out_727_, v_c_x27_705_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v_iter_706_);
lean_ctor_set(v___x_701_, 0, v_iter_706_);
v___x_730_ = v___x_701_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_iter_706_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_iter_706_);
v___x_730_ = v_reuseFailAlloc_737_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_732_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_730_);
v___x_732_ = v___x_696_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_fst_694_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_730_);
v___x_732_ = v_reuseFailAlloc_736_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_734_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_732_);
lean_ctor_set(v___x_692_, 0, v_out_728_);
v___x_734_ = v___x_692_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_out_728_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
v___jp_738_:
{
if (v___y_739_ == 0)
{
goto v___jp_707_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_del_object(v___x_701_);
lean_dec(v_snd_699_);
lean_del_object(v___x_696_);
lean_del_object(v___x_692_);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v_fst_698_);
lean_ctor_set(v___x_740_, 1, v_iter_706_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v_fst_694_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v_fst_690_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v_b_687_ = v___x_742_;
goto _start;
}
}
}
else
{
lean_object* v___x_747_; 
lean_dec(v_pre_685_);
if (v_isShared_702_ == 0)
{
v___x_747_ = v___x_701_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_fst_698_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_snd_699_);
v___x_747_ = v_reuseFailAlloc_754_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_749_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_747_);
v___x_749_ = v___x_696_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_fst_694_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___x_747_);
v___x_749_ = v_reuseFailAlloc_753_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_749_);
v___x_751_ = v___x_692_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_fst_690_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__0___boxed(lean_object* v_s_760_, lean_object* v_iter_x27_761_, lean_object* v_pre_762_, lean_object* v_c_763_, lean_object* v_b_764_){
_start:
{
uint32_t v_c_boxed_765_; lean_object* v_res_766_; 
v_c_boxed_765_ = lean_unbox_uint32(v_c_763_);
lean_dec(v_c_763_);
v_res_766_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__0(v_s_760_, v_iter_x27_761_, v_pre_762_, v_c_boxed_765_, v_b_764_);
lean_dec(v_iter_x27_761_);
lean_dec_ref(v_s_760_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__1(lean_object* v_s_768_, lean_object* v_b_769_){
_start:
{
lean_object* v_snd_770_; lean_object* v_fst_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_835_; 
v_snd_770_ = lean_ctor_get(v_b_769_, 1);
v_fst_771_ = lean_ctor_get(v_b_769_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v_b_769_);
if (v_isSharedCheck_835_ == 0)
{
v___x_773_ = v_b_769_;
v_isShared_774_ = v_isSharedCheck_835_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_snd_770_);
lean_inc(v_fst_771_);
lean_dec(v_b_769_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_835_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_fst_775_; lean_object* v_snd_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_834_; 
v_fst_775_ = lean_ctor_get(v_snd_770_, 0);
v_snd_776_ = lean_ctor_get(v_snd_770_, 1);
v_isSharedCheck_834_ = !lean_is_exclusive(v_snd_770_);
if (v_isSharedCheck_834_ == 0)
{
v___x_778_ = v_snd_770_;
v_isShared_779_ = v_isSharedCheck_834_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_snd_776_);
lean_inc(v_fst_775_);
lean_dec(v_snd_770_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_834_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_780_ = lean_string_utf8_byte_size(v_s_768_);
v___x_781_ = lean_nat_dec_eq(v_snd_776_, v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v_scheme_782_; uint32_t v_c_783_; lean_object* v_iter_784_; uint8_t v___x_785_; 
v_scheme_782_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__1___closed__0));
v_c_783_ = lean_string_utf8_get_fast(v_s_768_, v_snd_776_);
v_iter_784_ = lean_string_utf8_next_fast(v_s_768_, v_snd_776_);
lean_inc(v_snd_776_);
v___x_785_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_lookingAt(v_scheme_782_, v_s_768_, v_snd_776_);
if (v___x_785_ == 0)
{
lean_object* v_out_786_; lean_object* v___x_788_; 
lean_dec(v_snd_776_);
v_out_786_ = lean_string_push(v_fst_771_, v_c_783_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_iter_784_);
v___x_788_ = v___x_778_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_fst_775_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_iter_784_);
v___x_788_ = v_reuseFailAlloc_793_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_788_);
lean_ctor_set(v___x_773_, 0, v_out_786_);
v___x_790_ = v___x_773_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_out_786_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_788_);
v___x_790_ = v_reuseFailAlloc_792_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
v_b_769_ = v___x_790_;
goto _start;
}
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_iter_x27_797_; lean_object* v___x_799_; 
v___x_794_ = lean_unsigned_to_nat(14u);
v___x_795_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_768_);
v___x_796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_796_, 0, v_s_768_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
lean_ctor_set(v___x_796_, 2, v___x_780_);
lean_inc(v_snd_776_);
v_iter_x27_797_ = l_String_Slice_Pos_nextn(v___x_796_, v_snd_776_, v___x_794_);
lean_dec_ref(v___x_796_);
lean_inc(v_iter_x27_797_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_iter_x27_797_);
lean_ctor_set(v___x_778_, 0, v_iter_784_);
v___x_799_ = v___x_778_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_iter_784_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_iter_x27_797_);
v___x_799_ = v_reuseFailAlloc_827_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_799_);
lean_ctor_set(v___x_773_, 0, v_fst_775_);
v___x_801_ = v___x_773_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_fst_775_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___x_799_);
v___x_801_ = v_reuseFailAlloc_826_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_snd_804_; lean_object* v_snd_805_; lean_object* v_fst_806_; lean_object* v_fst_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_824_; 
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_fst_771_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__0(v_s_768_, v_iter_x27_797_, v_snd_776_, v_c_783_, v___x_802_);
lean_dec(v_iter_x27_797_);
v_snd_804_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_snd_804_);
v_snd_805_ = lean_ctor_get(v_snd_804_, 1);
lean_inc(v_snd_805_);
v_fst_806_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_fst_806_);
lean_dec_ref(v___x_803_);
v_fst_807_ = lean_ctor_get(v_snd_804_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_snd_804_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v_snd_804_, 1);
lean_dec(v_unused_825_);
v___x_809_ = v_snd_804_;
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_fst_807_);
lean_dec(v_snd_804_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_fst_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_822_; 
v_fst_811_ = lean_ctor_get(v_snd_805_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_snd_805_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_snd_805_, 1);
lean_dec(v_unused_823_);
v___x_813_ = v_snd_805_;
v_isShared_814_ = v_isSharedCheck_822_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_fst_811_);
lean_dec(v_snd_805_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_822_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v_fst_811_);
lean_ctor_set(v___x_813_, 0, v_fst_807_);
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_fst_807_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_fst_811_);
v___x_816_ = v_reuseFailAlloc_821_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 1, v___x_816_);
lean_ctor_set(v___x_809_, 0, v_fst_806_);
v___x_818_ = v___x_809_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_fst_806_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_816_);
v___x_818_ = v_reuseFailAlloc_820_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
v_b_769_ = v___x_818_;
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
lean_object* v___x_829_; 
lean_dec_ref(v_s_768_);
if (v_isShared_779_ == 0)
{
v___x_829_ = v___x_778_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_fst_775_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_snd_776_);
v___x_829_ = v_reuseFailAlloc_833_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_831_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_829_);
v___x_831_ = v___x_773_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_fst_771_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore(lean_object* v_s_844_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v_snd_847_; lean_object* v_fst_848_; lean_object* v_fst_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v___x_845_ = ((lean_object*)(l_Lean_rewriteManualLinksCore___closed__2));
v___x_846_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_rewriteManualLinksCore_spec__1(v_s_844_, v___x_845_);
v_snd_847_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_snd_847_);
v_fst_848_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_fst_848_);
lean_dec_ref(v___x_846_);
v_fst_849_ = lean_ctor_get(v_snd_847_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_snd_847_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v_snd_847_, 1);
lean_dec(v_unused_857_);
v___x_851_ = v_snd_847_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_fst_849_);
lean_dec(v_snd_847_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v_fst_848_);
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_fst_849_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_fst_848_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(lean_object* v_docString_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
if (lean_obj_tag(v_a_862_) == 0)
{
lean_object* v___x_864_; 
v___x_864_ = l_List_reverse___redArg(v_a_863_);
return v___x_864_;
}
else
{
lean_object* v_head_865_; lean_object* v_fst_866_; lean_object* v_tail_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_886_; 
v_head_865_ = lean_ctor_get(v_a_862_, 0);
lean_inc(v_head_865_);
v_fst_866_ = lean_ctor_get(v_head_865_, 0);
lean_inc(v_fst_866_);
v_tail_867_ = lean_ctor_get(v_a_862_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_a_862_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v_a_862_, 0);
lean_dec(v_unused_887_);
v___x_869_ = v_a_862_;
v_isShared_870_ = v_isSharedCheck_886_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_tail_867_);
lean_dec(v_a_862_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_886_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v_snd_871_; lean_object* v_start_872_; lean_object* v_stop_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v_snd_871_ = lean_ctor_get(v_head_865_, 1);
lean_inc(v_snd_871_);
lean_dec(v_head_865_);
v_start_872_ = lean_ctor_get(v_fst_866_, 0);
lean_inc(v_start_872_);
v_stop_873_ = lean_ctor_get(v_fst_866_, 1);
lean_inc(v_stop_873_);
lean_dec(v_fst_866_);
v___x_874_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0));
v___x_875_ = lean_string_utf8_extract(v_docString_861_, v_start_872_, v_stop_873_);
lean_dec(v_stop_873_);
lean_dec(v_start_872_);
v___x_876_ = lean_string_append(v___x_874_, v___x_875_);
lean_dec_ref(v___x_875_);
v___x_877_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1));
v___x_878_ = lean_string_append(v___x_876_, v___x_877_);
v___x_879_ = lean_string_append(v___x_878_, v_snd_871_);
lean_dec(v_snd_871_);
v___x_880_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_881_ = lean_string_append(v___x_879_, v___x_880_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v_a_863_);
lean_ctor_set(v___x_869_, 0, v___x_881_);
v___x_883_ = v___x_869_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_a_863_);
v___x_883_ = v_reuseFailAlloc_885_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
v_a_862_ = v_tail_867_;
v_a_863_ = v___x_883_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___boxed(lean_object* v_docString_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_888_, v_a_889_, v_a_890_);
lean_dec_ref(v_docString_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
return v_x_892_;
}
else
{
lean_object* v_head_894_; lean_object* v_tail_895_; lean_object* v___x_896_; 
v_head_894_ = lean_ctor_get(v_x_893_, 0);
v_tail_895_ = lean_ctor_get(v_x_893_, 1);
v___x_896_ = lean_string_append(v_x_892_, v_head_894_);
v_x_892_ = v___x_896_;
v_x_893_ = v_tail_895_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1___boxed(lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v_x_898_, v_x_899_);
lean_dec(v_x_899_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks(lean_object* v_docString_902_){
_start:
{
lean_object* v___x_904_; lean_object* v_fst_905_; lean_object* v_snd_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
lean_inc_ref(v_docString_902_);
v___x_904_ = l_Lean_rewriteManualLinksCore(v_docString_902_);
v_fst_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_fst_905_);
v_snd_906_ = lean_ctor_get(v___x_904_, 1);
lean_inc(v_snd_906_);
lean_dec_ref(v___x_904_);
v___x_907_ = lean_array_get_size(v_fst_905_);
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_nat_dec_eq(v___x_907_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_910_ = ((lean_object*)(l_Lean_rewriteManualLinks___closed__0));
v___x_911_ = lean_array_to_list(v_fst_905_);
v___x_912_ = lean_box(0);
v___x_913_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_902_, v___x_911_, v___x_912_);
lean_dec_ref(v_docString_902_);
v___x_914_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_915_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_914_, v___x_913_);
lean_dec(v___x_913_);
v___x_916_ = lean_string_append(v___x_910_, v___x_915_);
lean_dec_ref(v___x_915_);
v___x_917_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_918_ = lean_string_append(v_snd_906_, v___x_917_);
v___x_919_ = lean_string_append(v___x_918_, v___x_916_);
lean_dec_ref(v___x_916_);
return v___x_919_;
}
else
{
lean_dec(v_fst_905_);
lean_dec_ref(v_docString_902_);
return v_snd_906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks___boxed(lean_object* v_docString_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_rewriteManualLinks(v_docString_920_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(lean_object* v_docString_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
if (lean_obj_tag(v_a_927_) == 0)
{
lean_object* v___x_929_; 
v___x_929_ = l_List_reverse___redArg(v_a_928_);
return v___x_929_;
}
else
{
lean_object* v_head_930_; lean_object* v_fst_931_; lean_object* v_tail_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_956_; 
v_head_930_ = lean_ctor_get(v_a_927_, 0);
lean_inc(v_head_930_);
v_fst_931_ = lean_ctor_get(v_head_930_, 0);
lean_inc(v_fst_931_);
v_tail_932_ = lean_ctor_get(v_a_927_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v_a_927_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v_a_927_, 0);
lean_dec(v_unused_957_);
v___x_934_ = v_a_927_;
v_isShared_935_ = v_isSharedCheck_956_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_tail_932_);
lean_dec(v_a_927_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_956_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_snd_936_; lean_object* v_start_937_; lean_object* v_stop_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v_snd_936_ = lean_ctor_get(v_head_930_, 1);
lean_inc(v_snd_936_);
lean_dec(v_head_930_);
v_start_937_ = lean_ctor_get(v_fst_931_, 0);
lean_inc(v_start_937_);
v_stop_938_ = lean_ctor_get(v_fst_931_, 1);
lean_inc(v_stop_938_);
lean_dec(v_fst_931_);
v___x_939_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0));
v___x_940_ = lean_string_utf8_extract(v_docString_926_, v_start_937_, v_stop_938_);
lean_dec(v_stop_938_);
lean_dec(v_start_937_);
v___x_941_ = l_String_quote(v___x_940_);
v___x_942_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
v___x_943_ = l_Std_Format_defWidth;
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = l_Std_Format_pretty(v___x_942_, v___x_943_, v___x_944_, v___x_944_);
v___x_946_ = lean_string_append(v___x_939_, v___x_945_);
lean_dec_ref(v___x_945_);
v___x_947_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1));
v___x_948_ = lean_string_append(v___x_946_, v___x_947_);
v___x_949_ = lean_string_append(v___x_948_, v_snd_936_);
lean_dec(v_snd_936_);
v___x_950_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2));
v___x_951_ = lean_string_append(v___x_949_, v___x_950_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 1, v_a_928_);
lean_ctor_set(v___x_934_, 0, v___x_951_);
v___x_953_ = v___x_934_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_a_928_);
v___x_953_ = v_reuseFailAlloc_955_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
v_a_927_ = v_tail_932_;
v_a_928_ = v___x_953_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___boxed(lean_object* v_docString_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_958_, v_a_959_, v_a_960_);
lean_dec_ref(v_docString_958_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString(lean_object* v_docString_963_){
_start:
{
lean_object* v___x_965_; lean_object* v_fst_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
lean_inc_ref(v_docString_963_);
v___x_965_ = l_Lean_rewriteManualLinksCore(v_docString_963_);
v_fst_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_fst_966_);
lean_dec_ref(v___x_965_);
v___x_967_ = lean_array_get_size(v_fst_966_);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_nat_dec_eq(v___x_967_, v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_970_ = ((lean_object*)(l_Lean_validateBuiltinDocString___closed__0));
v___x_971_ = lean_array_to_list(v_fst_966_);
v___x_972_ = lean_box(0);
v___x_973_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_963_, v___x_971_, v___x_972_);
lean_dec_ref(v_docString_963_);
v___x_974_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_975_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_974_, v___x_973_);
lean_dec(v___x_973_);
v___x_976_ = lean_string_append(v___x_970_, v___x_975_);
lean_dec_ref(v___x_975_);
v___x_977_ = lean_mk_io_user_error(v___x_976_);
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec(v_fst_966_);
lean_dec_ref(v_docString_963_);
v___x_979_ = lean_box(0);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString___boxed(lean_object* v_docString_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_validateBuiltinDocString(v_docString_981_);
return v_res_983_;
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
