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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_DocString_Links_0__Lean_domainMap___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Links_0__Lean_domainMap___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_domainMap;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualDomains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualDomains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_manualDomains___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_manualDomains___closed__0;
LEAN_EXPORT lean_object* l_Lean_manualDomains;
static const lean_string_object l_List_mapTR_loop___at___00Lean_manualLink_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_List_mapTR_loop___at___00Lean_manualLink_spec__2___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_manualLink_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_manualLink_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualLink_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualLink_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_manualLink___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "find/\?domain="};
static const lean_object* l_Lean_manualLink___closed__0 = (const lean_object*)&l_Lean_manualLink___closed__0_value;
static const lean_string_object l_Lean_manualLink___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "&name="};
static const lean_object* l_Lean_manualLink___closed__1 = (const lean_object*)&l_Lean_manualLink___closed__1_value;
static const lean_string_object l_Lean_manualLink___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_manualLink___closed__2 = (const lean_object*)&l_Lean_manualLink___closed__2_value;
static lean_once_cell_t l_Lean_manualLink___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_manualLink___closed__3;
static lean_once_cell_t l_Lean_manualLink___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_manualLink___closed__4;
static lean_once_cell_t l_Lean_manualLink___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_manualLink___closed__5;
static const lean_string_object l_Lean_manualLink___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Unknown documentation type `"};
static const lean_object* l_Lean_manualLink___closed__6 = (const lean_object*)&l_Lean_manualLink___closed__6_value;
static const lean_string_object l_Lean_manualLink___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "`. Expected one of the following: "};
static const lean_object* l_Lean_manualLink___closed__7 = (const lean_object*)&l_Lean_manualLink___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_manualLink(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_manualLink___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(lean_object* v_m_43_, lean_object* v_query_44_, lean_object* v_x_45_, lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
lean_object* v_zero_48_; uint8_t v_isZero_49_; 
v_zero_48_ = lean_unsigned_to_nat(0u);
v_isZero_49_ = lean_nat_dec_eq(v_x_46_, v_zero_48_);
if (v_isZero_49_ == 1)
{
lean_dec(v_x_47_);
lean_dec(v_x_46_);
if (lean_obj_tag(v_x_45_) == 0)
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(2);
return v___x_50_;
}
else
{
lean_object* v_val_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_58_; 
v_val_51_ = lean_ctor_get(v_x_45_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v_x_45_);
if (v_isSharedCheck_58_ == 0)
{
v___x_53_ = v_x_45_;
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_val_51_);
lean_dec(v_x_45_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
if (v_isShared_54_ == 0)
{
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_val_51_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
else
{
lean_object* v_keyArray_59_; lean_object* v_valueArray_60_; lean_object* v___x_61_; uint8_t v_isSome_62_; 
v_keyArray_59_ = lean_ctor_get(v_m_43_, 1);
v_valueArray_60_ = lean_ctor_get(v_m_43_, 2);
v___x_61_ = lean_array_fget_borrowed(v_keyArray_59_, v_x_47_);
v_isSome_62_ = lean_noption_is_some(v___x_61_);
if (v_isSome_62_ == 0)
{
lean_dec(v_x_46_);
if (lean_obj_tag(v_x_45_) == 0)
{
lean_object* v___x_63_; 
v___x_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_63_, 0, v_x_47_);
return v___x_63_;
}
else
{
lean_object* v_val_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_71_; 
lean_dec(v_x_47_);
v_val_64_ = lean_ctor_get(v_x_45_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v_x_45_);
if (v_isSharedCheck_71_ == 0)
{
v___x_66_ = v_x_45_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_val_64_);
lean_dec(v_x_45_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_69_; 
if (v_isShared_67_ == 0)
{
v___x_69_ = v___x_66_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_val_64_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
else
{
lean_object* v_one_72_; lean_object* v_n_73_; lean_object* v___y_75_; 
v_one_72_ = lean_unsigned_to_nat(1u);
v_n_73_ = lean_nat_sub(v_x_46_, v_one_72_);
lean_dec(v_x_46_);
if (v_isSome_62_ == 0)
{
goto v___jp_81_;
}
else
{
lean_object* v___x_83_; uint8_t v_isSome_84_; 
v___x_83_ = lean_array_fget_borrowed(v_valueArray_60_, v_x_47_);
v_isSome_84_ = lean_noption_is_some(v___x_83_);
if (v_isSome_84_ == 0)
{
goto v___jp_81_;
}
else
{
lean_object* v_val_85_; uint8_t v___x_86_; 
lean_inc(v___x_61_);
v_val_85_ = lean_noption_get(v___x_61_);
v___x_86_ = lean_string_dec_eq(v_val_85_, v_query_44_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
lean_dec(v_val_85_);
v___x_87_ = lean_array_get_size(v_keyArray_59_);
v___x_88_ = lean_nat_add(v_x_47_, v_one_72_);
lean_dec(v_x_47_);
v___x_89_ = lean_nat_dec_lt(v___x_88_, v___x_87_);
if (v___x_89_ == 0)
{
lean_dec(v___x_88_);
v_x_46_ = v_n_73_;
v_x_47_ = v_zero_48_;
goto _start;
}
else
{
v_x_46_ = v_n_73_;
v_x_47_ = v___x_88_;
goto _start;
}
}
else
{
lean_object* v_val_92_; lean_object* v___x_93_; 
lean_dec(v_n_73_);
lean_dec(v_x_45_);
lean_inc(v___x_83_);
v_val_92_ = lean_noption_get(v___x_83_);
v___x_93_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_93_, 0, v_x_47_);
lean_ctor_set(v___x_93_, 1, v_val_85_);
lean_ctor_set(v___x_93_, 2, v_val_92_);
return v___x_93_;
}
}
}
v___jp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_76_ = lean_array_get_size(v_keyArray_59_);
v___x_77_ = lean_nat_add(v_x_47_, v_one_72_);
lean_dec(v_x_47_);
v___x_78_ = lean_nat_dec_lt(v___x_77_, v___x_76_);
if (v___x_78_ == 0)
{
lean_dec(v___x_77_);
v_x_45_ = v___y_75_;
v_x_46_ = v_n_73_;
v_x_47_ = v_zero_48_;
goto _start;
}
else
{
v_x_45_ = v___y_75_;
v_x_46_ = v_n_73_;
v_x_47_ = v___x_77_;
goto _start;
}
}
v___jp_81_:
{
if (lean_obj_tag(v_x_45_) == 0)
{
lean_object* v___x_82_; 
lean_inc(v_x_47_);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v_x_47_);
v___y_75_ = v___x_82_;
goto v___jp_74_;
}
else
{
v___y_75_ = v_x_45_;
goto v___jp_74_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_94_, lean_object* v_query_95_, lean_object* v_x_96_, lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_m_94_, v_query_95_, v_x_96_, v_x_97_, v_x_98_);
lean_dec_ref(v_query_95_);
lean_dec_ref(v_m_94_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(lean_object* v_m_100_, lean_object* v_query_101_){
_start:
{
lean_object* v_keyArray_102_; lean_object* v___x_103_; uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; uint64_t v_fold_107_; uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; size_t v___x_111_; size_t v___x_112_; size_t v___x_113_; size_t v___x_114_; size_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_keyArray_102_ = lean_ctor_get(v_m_100_, 1);
v___x_103_ = lean_array_get_size(v_keyArray_102_);
v___x_104_ = lean_string_hash(v_query_101_);
v___x_105_ = 32ULL;
v___x_106_ = lean_uint64_shift_right(v___x_104_, v___x_105_);
v_fold_107_ = lean_uint64_xor(v___x_104_, v___x_106_);
v___x_108_ = 16ULL;
v___x_109_ = lean_uint64_shift_right(v_fold_107_, v___x_108_);
v___x_110_ = lean_uint64_xor(v_fold_107_, v___x_109_);
v___x_111_ = lean_uint64_to_usize(v___x_110_);
v___x_112_ = lean_usize_of_nat(v___x_103_);
v___x_113_ = ((size_t)1ULL);
v___x_114_ = lean_usize_sub(v___x_112_, v___x_113_);
v___x_115_ = lean_usize_land(v___x_111_, v___x_114_);
v___x_116_ = lean_usize_to_nat(v___x_115_);
v___x_117_ = lean_box(0);
v___x_118_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_m_100_, v_query_101_, v___x_117_, v___x_103_, v___x_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg___boxed(lean_object* v_m_119_, lean_object* v_query_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_m_119_, v_query_120_);
lean_dec_ref(v_query_120_);
lean_dec_ref(v_m_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_b_122_, lean_object* v_acc_123_, lean_object* v_i_124_){
_start:
{
lean_object* v___y_126_; lean_object* v_keyArray_134_; lean_object* v_valueArray_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_keyArray_134_ = lean_ctor_get(v_b_122_, 1);
v_valueArray_135_ = lean_ctor_get(v_b_122_, 2);
v___x_136_ = lean_array_get_size(v_keyArray_134_);
v___x_137_ = lean_nat_dec_lt(v_i_124_, v___x_136_);
if (v___x_137_ == 0)
{
lean_dec(v_i_124_);
return v_acc_123_;
}
else
{
lean_object* v___x_138_; uint8_t v_isSome_139_; 
v___x_138_ = lean_array_fget_borrowed(v_keyArray_134_, v_i_124_);
v_isSome_139_ = lean_noption_is_some(v___x_138_);
if (v_isSome_139_ == 0)
{
goto v___jp_130_;
}
else
{
lean_object* v___x_140_; uint8_t v_isSome_141_; 
v___x_140_ = lean_array_fget_borrowed(v_valueArray_135_, v_i_124_);
v_isSome_141_ = lean_noption_is_some(v___x_140_);
if (v_isSome_141_ == 0)
{
goto v___jp_130_;
}
else
{
lean_object* v_val_142_; lean_object* v_val_143_; lean_object* v_i_145_; lean_object* v___x_150_; 
lean_inc(v___x_138_);
v_val_142_ = lean_noption_get(v___x_138_);
lean_inc(v___x_140_);
v_val_143_ = lean_noption_get(v___x_140_);
v___x_150_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_acc_123_, v_val_142_);
switch(lean_obj_tag(v___x_150_))
{
case 0:
{
lean_object* v_index_151_; lean_object* v_size_152_; lean_object* v___x_153_; 
v_index_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_index_151_);
lean_dec_ref_known(v___x_150_, 3);
v_size_152_ = lean_ctor_get(v_acc_123_, 0);
lean_inc(v_size_152_);
v___x_153_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_123_, v_size_152_, v_index_151_, v_val_142_, v_val_143_);
lean_dec(v_index_151_);
v___y_126_ = v___x_153_;
goto v___jp_125_;
}
case 1:
{
lean_object* v_index_154_; 
v_index_154_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_index_154_);
lean_dec_ref_known(v___x_150_, 1);
v_i_145_ = v_index_154_;
goto v___jp_144_;
}
default: 
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_123_, v___x_155_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_index_157_; 
v_index_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_index_157_);
lean_dec_ref_known(v___x_156_, 1);
v_i_145_ = v_index_157_;
goto v___jp_144_;
}
else
{
lean_dec(v_val_143_);
lean_dec(v_val_142_);
v___y_126_ = v_acc_123_;
goto v___jp_125_;
}
}
}
v___jp_144_:
{
lean_object* v_size_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_size_146_ = lean_ctor_get(v_acc_123_, 0);
v___x_147_ = lean_unsigned_to_nat(1u);
v___x_148_ = lean_nat_add(v_size_146_, v___x_147_);
v___x_149_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_123_, v___x_148_, v_i_145_, v_val_142_, v_val_143_);
lean_dec(v_i_145_);
v___y_126_ = v___x_149_;
goto v___jp_125_;
}
}
}
}
v___jp_125_:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_add(v_i_124_, v___x_127_);
lean_dec(v_i_124_);
v_acc_123_ = v___y_126_;
v_i_124_ = v___x_128_;
goto _start;
}
v___jp_130_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1u);
v___x_132_ = lean_nat_add(v_i_124_, v___x_131_);
lean_dec(v_i_124_);
v_i_124_ = v___x_132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_b_158_, lean_object* v_acc_159_, lean_object* v_i_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3_spec__4___redArg(v_b_158_, v_acc_159_, v_i_160_);
lean_dec_ref(v_b_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3___redArg(lean_object* v_init_162_, lean_object* v_b_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3_spec__4___redArg(v_b_163_, v_init_162_, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_init_166_, lean_object* v_b_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3___redArg(v_init_166_, v_b_167_);
lean_dec_ref(v_b_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(lean_object* v_m_169_){
_start:
{
lean_object* v_keyArray_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v_cellCount_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_target_177_; lean_object* v___x_178_; 
v_keyArray_170_ = lean_ctor_get(v_m_169_, 1);
v___x_171_ = lean_array_get_size(v_keyArray_170_);
v___x_172_ = lean_unsigned_to_nat(2u);
v_cellCount_173_ = lean_nat_mul(v___x_171_, v___x_172_);
v___x_174_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_173_);
v___x_175_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_173_);
v___x_176_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_173_);
v_target_177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_177_, 0, v___x_174_);
lean_ctor_set(v_target_177_, 1, v___x_175_);
lean_ctor_set(v_target_177_, 2, v___x_176_);
v___x_178_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3___redArg(v_target_177_, v_m_169_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg___boxed(lean_object* v_m_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_m_179_);
lean_dec_ref(v_m_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__2___redArg(lean_object* v_as_x27_181_, lean_object* v_b_182_){
_start:
{
if (lean_obj_tag(v_as_x27_181_) == 0)
{
return v_b_182_;
}
else
{
lean_object* v_head_183_; lean_object* v_tail_184_; lean_object* v_fst_185_; lean_object* v_snd_186_; lean_object* v___y_188_; lean_object* v_i_189_; lean_object* v___y_196_; lean_object* v___y_208_; lean_object* v_i_209_; lean_object* v___x_227_; 
v_head_183_ = lean_ctor_get(v_as_x27_181_, 0);
v_tail_184_ = lean_ctor_get(v_as_x27_181_, 1);
v_fst_185_ = lean_ctor_get(v_head_183_, 0);
v_snd_186_ = lean_ctor_get(v_head_183_, 1);
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_b_182_, v_fst_185_);
switch(lean_obj_tag(v___x_227_))
{
case 0:
{
lean_object* v_index_228_; lean_object* v_size_229_; lean_object* v___x_230_; 
v_index_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_index_228_);
lean_dec_ref_known(v___x_227_, 3);
v_size_229_ = lean_ctor_get(v_b_182_, 0);
lean_inc(v_size_229_);
lean_inc(v_snd_186_);
lean_inc(v_fst_185_);
v___x_230_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_182_, v_size_229_, v_index_228_, v_fst_185_, v_snd_186_);
lean_dec(v_index_228_);
v_as_x27_181_ = v_tail_184_;
v_b_182_ = v___x_230_;
goto _start;
}
case 1:
{
lean_object* v_index_232_; lean_object* v_size_233_; lean_object* v_keyArray_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_index_232_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_index_232_);
lean_dec_ref_known(v___x_227_, 1);
v_size_233_ = lean_ctor_get(v_b_182_, 0);
v_keyArray_234_ = lean_ctor_get(v_b_182_, 1);
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_nat_add(v_size_233_, v___x_235_);
v___x_237_ = lean_array_get_size(v_keyArray_234_);
v___x_238_ = lean_nat_dec_lt(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_dec(v___x_236_);
lean_dec(v_index_232_);
goto v___jp_215_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_239_ = lean_unsigned_to_nat(4u);
v___x_240_ = lean_nat_mul(v___x_236_, v___x_239_);
v___x_241_ = lean_unsigned_to_nat(3u);
v___x_242_ = lean_nat_mul(v___x_237_, v___x_241_);
v___x_243_ = lean_nat_dec_le(v___x_240_, v___x_242_);
lean_dec(v___x_242_);
lean_dec(v___x_240_);
if (v___x_243_ == 0)
{
lean_dec(v___x_236_);
lean_dec(v_index_232_);
goto v___jp_215_;
}
else
{
lean_object* v___x_244_; 
lean_inc(v_snd_186_);
lean_inc(v_fst_185_);
v___x_244_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_182_, v___x_236_, v_index_232_, v_fst_185_, v_snd_186_);
lean_dec(v_index_232_);
v_as_x27_181_ = v_tail_184_;
v_b_182_ = v___x_244_;
goto _start;
}
}
}
default: 
{
lean_object* v_size_246_; lean_object* v_keyArray_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_size_246_ = lean_ctor_get(v_b_182_, 0);
v_keyArray_247_ = lean_ctor_get(v_b_182_, 1);
v___x_248_ = lean_unsigned_to_nat(1u);
v___x_249_ = lean_nat_add(v_size_246_, v___x_248_);
v___x_250_ = lean_array_get_size(v_keyArray_247_);
v___x_251_ = lean_nat_dec_lt(v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec(v___x_249_);
v___x_252_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_b_182_);
lean_dec_ref(v_b_182_);
v___y_196_ = v___x_252_;
goto v___jp_195_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_253_ = lean_unsigned_to_nat(4u);
v___x_254_ = lean_nat_mul(v___x_249_, v___x_253_);
lean_dec(v___x_249_);
v___x_255_ = lean_unsigned_to_nat(3u);
v___x_256_ = lean_nat_mul(v___x_250_, v___x_255_);
v___x_257_ = lean_nat_dec_le(v___x_254_, v___x_256_);
lean_dec(v___x_256_);
lean_dec(v___x_254_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_b_182_);
lean_dec_ref(v_b_182_);
v___y_196_ = v___x_258_;
goto v___jp_195_;
}
else
{
v___y_196_ = v_b_182_;
goto v___jp_195_;
}
}
}
}
v___jp_187_:
{
lean_object* v_size_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_size_190_ = lean_ctor_get(v___y_188_, 0);
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_nat_add(v_size_190_, v___x_191_);
lean_inc(v_snd_186_);
lean_inc(v_fst_185_);
v___x_193_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_188_, v___x_192_, v_i_189_, v_fst_185_, v_snd_186_);
lean_dec(v_i_189_);
v_as_x27_181_ = v_tail_184_;
v_b_182_ = v___x_193_;
goto _start;
}
v___jp_195_:
{
lean_object* v___x_197_; 
v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v___y_196_, v_fst_185_);
switch(lean_obj_tag(v___x_197_))
{
case 0:
{
lean_object* v_index_198_; lean_object* v_size_199_; lean_object* v___x_200_; 
v_index_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_index_198_);
lean_dec_ref_known(v___x_197_, 3);
v_size_199_ = lean_ctor_get(v___y_196_, 0);
lean_inc(v_size_199_);
lean_inc(v_snd_186_);
lean_inc(v_fst_185_);
v___x_200_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_196_, v_size_199_, v_index_198_, v_fst_185_, v_snd_186_);
lean_dec(v_index_198_);
v_as_x27_181_ = v_tail_184_;
v_b_182_ = v___x_200_;
goto _start;
}
case 1:
{
lean_object* v_index_202_; 
v_index_202_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_index_202_);
lean_dec_ref_known(v___x_197_, 1);
v___y_188_ = v___y_196_;
v_i_189_ = v_index_202_;
goto v___jp_187_;
}
default: 
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_196_, v___x_203_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_index_205_; 
v_index_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_index_205_);
lean_dec_ref_known(v___x_204_, 1);
v___y_188_ = v___y_196_;
v_i_189_ = v_index_205_;
goto v___jp_187_;
}
else
{
v_as_x27_181_ = v_tail_184_;
v_b_182_ = v___y_196_;
goto _start;
}
}
}
}
v___jp_207_:
{
lean_object* v_size_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_size_210_ = lean_ctor_get(v___y_208_, 0);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_size_210_, v___x_211_);
lean_inc(v_snd_186_);
lean_inc(v_fst_185_);
v___x_213_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_208_, v___x_212_, v_i_209_, v_fst_185_, v_snd_186_);
lean_dec(v_i_209_);
v_as_x27_181_ = v_tail_184_;
v_b_182_ = v___x_213_;
goto _start;
}
v___jp_215_:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_b_182_);
lean_dec_ref(v_b_182_);
v___x_217_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v___x_216_, v_fst_185_);
switch(lean_obj_tag(v___x_217_))
{
case 0:
{
lean_object* v_index_218_; lean_object* v_size_219_; lean_object* v___x_220_; 
v_index_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_index_218_);
lean_dec_ref_known(v___x_217_, 3);
v_size_219_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_size_219_);
lean_inc(v_snd_186_);
lean_inc(v_fst_185_);
v___x_220_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_216_, v_size_219_, v_index_218_, v_fst_185_, v_snd_186_);
lean_dec(v_index_218_);
v_as_x27_181_ = v_tail_184_;
v_b_182_ = v___x_220_;
goto _start;
}
case 1:
{
lean_object* v_index_222_; 
v_index_222_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_index_222_);
lean_dec_ref_known(v___x_217_, 1);
v___y_208_ = v___x_216_;
v_i_209_ = v_index_222_;
goto v___jp_207_;
}
default: 
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_216_, v___x_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_index_225_; 
v_index_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_index_225_);
lean_dec_ref_known(v___x_224_, 1);
v___y_208_ = v___x_216_;
v_i_209_ = v_index_225_;
goto v___jp_207_;
}
else
{
v_as_x27_181_ = v_tail_184_;
v_b_182_ = v___x_216_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__2___redArg___boxed(lean_object* v_as_x27_259_, lean_object* v_b_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__2___redArg(v_as_x27_259_, v_b_260_);
lean_dec(v_as_x27_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(lean_object* v_m_262_, lean_object* v_l_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__2___redArg(v_l_263_, v_m_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0___boxed(lean_object* v_m_265_, lean_object* v_l_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(v_m_265_, v_l_266_);
lean_dec(v_l_266_);
return v_res_267_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7(void){
_start:
{
lean_object* v_cellCount_283_; lean_object* v___x_284_; 
v_cellCount_283_ = lean_unsigned_to_nat(16u);
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_283_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8(void){
_start:
{
lean_object* v_cellCount_285_; lean_object* v___x_286_; 
v_cellCount_285_ = lean_unsigned_to_nat(16u);
v___x_286_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_285_);
return v___x_286_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_287_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8);
v___x_288_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7);
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_288_);
lean_ctor_set(v___x_290_, 2, v___x_287_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__10(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9);
v___x_292_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__6));
v___x_293_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__2___redArg(v___x_292_, v___x_291_);
return v___x_293_;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_domainMap(void){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l___private_Lean_DocString_Links_0__Lean_domainMap___closed__10, &l___private_Lean_DocString_Links_0__Lean_domainMap___closed__10_once, _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__10);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0(lean_object* v_00_u03b2_295_, lean_object* v_m_296_, lean_object* v_query_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_m_296_, v_query_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___boxed(lean_object* v_00_u03b2_299_, lean_object* v_m_300_, lean_object* v_query_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0(v_00_u03b2_299_, v_m_300_, v_query_301_);
lean_dec_ref(v_query_301_);
lean_dec_ref(v_m_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(lean_object* v_00_u03b2_303_, lean_object* v_m_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_m_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___boxed(lean_object* v_00_u03b2_306_, lean_object* v_m_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(v_00_u03b2_306_, v_m_307_);
lean_dec_ref(v_m_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__2(lean_object* v_as_309_, lean_object* v_as_x27_310_, lean_object* v_b_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__2___redArg(v_as_x27_310_, v_b_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__2___boxed(lean_object* v_as_314_, lean_object* v_as_x27_315_, lean_object* v_b_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__2(v_as_314_, v_as_x27_315_, v_b_316_, v_a_317_);
lean_dec(v_as_x27_315_);
lean_dec(v_as_314_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_319_, lean_object* v_m_320_, lean_object* v_query_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_m_320_, v_query_321_, v_x_322_, v_x_323_, v_x_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_327_, lean_object* v_m_328_, lean_object* v_query_329_, lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(v_00_u03b2_327_, v_m_328_, v_query_329_, v_x_330_, v_x_331_, v_x_332_, v_x_333_);
lean_dec_ref(v_query_329_);
lean_dec_ref(v_m_328_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_335_, lean_object* v_init_336_, lean_object* v_b_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3___redArg(v_init_336_, v_b_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_339_, lean_object* v_init_340_, lean_object* v_b_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3(v_00_u03b2_339_, v_init_340_, v_b_341_);
lean_dec_ref(v_b_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_343_, lean_object* v_b_344_, lean_object* v_acc_345_, lean_object* v_i_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3_spec__4___redArg(v_b_344_, v_acc_345_, v_i_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b2_348_, lean_object* v_b_349_, lean_object* v_acc_350_, lean_object* v_i_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1_spec__3_spec__4(v_00_u03b2_348_, v_b_349_, v_acc_350_, v_i_351_);
lean_dec_ref(v_b_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualDomains_spec__0(lean_object* v_b_353_, lean_object* v_acc_354_, lean_object* v_i_355_){
_start:
{
lean_object* v_keyArray_360_; lean_object* v_valueArray_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_keyArray_360_ = lean_ctor_get(v_b_353_, 1);
v_valueArray_361_ = lean_ctor_get(v_b_353_, 2);
v___x_362_ = lean_array_get_size(v_keyArray_360_);
v___x_363_ = lean_nat_dec_lt(v_i_355_, v___x_362_);
if (v___x_363_ == 0)
{
lean_dec(v_i_355_);
lean_inc(v_acc_354_);
return v_acc_354_;
}
else
{
lean_object* v___x_364_; uint8_t v_isSome_365_; 
v___x_364_ = lean_array_fget_borrowed(v_keyArray_360_, v_i_355_);
v_isSome_365_ = lean_noption_is_some(v___x_364_);
if (v_isSome_365_ == 0)
{
goto v___jp_356_;
}
else
{
lean_object* v___x_366_; uint8_t v_isSome_367_; 
v___x_366_ = lean_array_fget_borrowed(v_valueArray_361_, v_i_355_);
v_isSome_367_ = lean_noption_is_some(v___x_366_);
if (v_isSome_367_ == 0)
{
goto v___jp_356_;
}
else
{
lean_object* v_val_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
lean_inc(v___x_364_);
v_val_368_ = lean_noption_get(v___x_364_);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v_i_355_, v___x_369_);
lean_dec(v_i_355_);
v___x_371_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualDomains_spec__0(v_b_353_, v_acc_354_, v___x_370_);
v___x_372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_372_, 0, v_val_368_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
return v___x_372_;
}
}
}
v___jp_356_:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_unsigned_to_nat(1u);
v___x_358_ = lean_nat_add(v_i_355_, v___x_357_);
lean_dec(v_i_355_);
v_i_355_ = v___x_358_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualDomains_spec__0___boxed(lean_object* v_b_373_, lean_object* v_acc_374_, lean_object* v_i_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualDomains_spec__0(v_b_373_, v_acc_374_, v_i_375_);
lean_dec(v_acc_374_);
lean_dec_ref(v_b_373_);
return v_res_376_;
}
}
static lean_object* _init_l_Lean_manualDomains___closed__0(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_378_ = lean_box(0);
v___x_379_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_380_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualDomains_spec__0(v___x_379_, v___x_378_, v___x_377_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_manualDomains(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_obj_once(&l_Lean_manualDomains___closed__0, &l_Lean_manualDomains___closed__0_once, _init_l_Lean_manualDomains___closed__0);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_manualLink_spec__2(lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
if (lean_obj_tag(v_a_383_) == 0)
{
lean_object* v___x_385_; 
v___x_385_ = l_List_reverse___redArg(v_a_384_);
return v___x_385_;
}
else
{
lean_object* v_head_386_; lean_object* v_tail_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_399_; 
v_head_386_ = lean_ctor_get(v_a_383_, 0);
v_tail_387_ = lean_ctor_get(v_a_383_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v_a_383_);
if (v_isSharedCheck_399_ == 0)
{
v___x_389_ = v_a_383_;
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_tail_387_);
lean_inc(v_head_386_);
lean_dec(v_a_383_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_fst_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v_fst_391_ = lean_ctor_get(v_head_386_, 0);
lean_inc(v_fst_391_);
lean_dec(v_head_386_);
v___x_392_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_manualLink_spec__2___closed__0));
v___x_393_ = lean_string_append(v___x_392_, v_fst_391_);
lean_dec(v_fst_391_);
v___x_394_ = lean_string_append(v___x_393_, v___x_392_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v_a_384_);
lean_ctor_set(v___x_389_, 0, v___x_394_);
v___x_396_ = v___x_389_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_a_384_);
v___x_396_ = v_reuseFailAlloc_398_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
v_a_383_ = v_tail_387_;
v_a_384_ = v___x_396_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(lean_object* v_m_400_, lean_object* v_query_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_m_400_, v_query_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_index_403_; lean_object* v_key_404_; lean_object* v_value_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
v_index_403_ = lean_ctor_get(v___x_402_, 0);
v_key_404_ = lean_ctor_get(v___x_402_, 1);
v_value_405_ = lean_ctor_get(v___x_402_, 2);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_402_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_value_405_);
lean_inc(v_key_404_);
lean_inc(v_index_403_);
lean_dec(v___x_402_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_index_403_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_key_404_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_value_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
else
{
lean_object* v___x_413_; 
lean_dec(v___x_402_);
v___x_413_ = lean_box(1);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg___boxed(lean_object* v_m_414_, lean_object* v_query_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_m_414_, v_query_415_);
lean_dec_ref(v_query_415_);
lean_dec_ref(v_m_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(lean_object* v_m_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_m_417_, v_a_418_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_value_420_; lean_object* v___x_421_; 
v_value_420_ = lean_ctor_get(v___x_419_, 2);
lean_inc(v_value_420_);
lean_dec_ref_known(v___x_419_, 3);
v___x_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_421_, 0, v_value_420_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; 
v___x_422_ = lean_box(0);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg___boxed(lean_object* v_m_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v_m_423_, v_a_424_);
lean_dec_ref(v_a_424_);
lean_dec_ref(v_m_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualLink_spec__1(lean_object* v_b_426_, lean_object* v_acc_427_, lean_object* v_i_428_){
_start:
{
lean_object* v_keyArray_433_; lean_object* v_valueArray_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_keyArray_433_ = lean_ctor_get(v_b_426_, 1);
v_valueArray_434_ = lean_ctor_get(v_b_426_, 2);
v___x_435_ = lean_array_get_size(v_keyArray_433_);
v___x_436_ = lean_nat_dec_lt(v_i_428_, v___x_435_);
if (v___x_436_ == 0)
{
lean_dec(v_i_428_);
lean_inc(v_acc_427_);
return v_acc_427_;
}
else
{
lean_object* v___x_437_; uint8_t v_isSome_438_; 
v___x_437_ = lean_array_fget_borrowed(v_keyArray_433_, v_i_428_);
v_isSome_438_ = lean_noption_is_some(v___x_437_);
if (v_isSome_438_ == 0)
{
goto v___jp_429_;
}
else
{
lean_object* v___x_439_; uint8_t v_isSome_440_; 
v___x_439_ = lean_array_fget_borrowed(v_valueArray_434_, v_i_428_);
v_isSome_440_ = lean_noption_is_some(v___x_439_);
if (v_isSome_440_ == 0)
{
goto v___jp_429_;
}
else
{
lean_object* v_val_441_; lean_object* v_val_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
lean_inc(v___x_437_);
v_val_441_ = lean_noption_get(v___x_437_);
lean_inc(v___x_439_);
v_val_442_ = lean_noption_get(v___x_439_);
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_add(v_i_428_, v___x_443_);
lean_dec(v_i_428_);
v___x_445_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualLink_spec__1(v_b_426_, v_acc_427_, v___x_444_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_val_441_);
lean_ctor_set(v___x_446_, 1, v_val_442_);
v___x_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
return v___x_447_;
}
}
}
v___jp_429_:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = lean_nat_add(v_i_428_, v___x_430_);
lean_dec(v_i_428_);
v_i_428_ = v___x_431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualLink_spec__1___boxed(lean_object* v_b_448_, lean_object* v_acc_449_, lean_object* v_i_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualLink_spec__1(v_b_448_, v_acc_449_, v_i_450_);
lean_dec(v_acc_449_);
lean_dec_ref(v_b_448_);
return v_res_451_;
}
}
static lean_object* _init_l_Lean_manualLink___closed__3(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_box(0);
v___x_457_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_458_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_manualLink_spec__1(v___x_457_, v___x_456_, v___x_455_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_manualLink___closed__4(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_box(0);
v___x_460_ = lean_obj_once(&l_Lean_manualLink___closed__3, &l_Lean_manualLink___closed__3_once, _init_l_Lean_manualLink___closed__3);
v___x_461_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__2(v___x_460_, v___x_459_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_manualLink___closed__5(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_acceptableKinds_464_; 
v___x_462_ = lean_obj_once(&l_Lean_manualLink___closed__4, &l_Lean_manualLink___closed__4_once, _init_l_Lean_manualLink___closed__4);
v___x_463_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v_acceptableKinds_464_ = l_String_intercalate(v___x_463_, v___x_462_);
return v_acceptableKinds_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_manualLink(lean_object* v_kind_467_, lean_object* v_name_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_469_, v_kind_467_);
if (lean_obj_tag(v___x_470_) == 1)
{
lean_object* v_val_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_485_; 
v_val_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_485_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_485_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_val_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_485_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_475_ = l_Lean_manualRoot;
v___x_476_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_477_ = lean_string_append(v___x_476_, v_val_471_);
lean_dec(v_val_471_);
v___x_478_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_479_ = lean_string_append(v___x_477_, v___x_478_);
v___x_480_ = lean_string_append(v___x_479_, v_name_468_);
v___x_481_ = lean_string_append(v___x_475_, v___x_480_);
lean_dec_ref(v___x_480_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_481_);
v___x_483_ = v___x_473_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
else
{
lean_object* v_acceptableKinds_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v___x_470_);
v_acceptableKinds_486_ = lean_obj_once(&l_Lean_manualLink___closed__5, &l_Lean_manualLink___closed__5_once, _init_l_Lean_manualLink___closed__5);
v___x_487_ = ((lean_object*)(l_Lean_manualLink___closed__6));
v___x_488_ = lean_string_append(v___x_487_, v_kind_467_);
v___x_489_ = ((lean_object*)(l_Lean_manualLink___closed__7));
v___x_490_ = lean_string_append(v___x_488_, v___x_489_);
v___x_491_ = lean_string_append(v___x_490_, v_acceptableKinds_486_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_manualLink___boxed(lean_object* v_kind_493_, lean_object* v_name_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_manualLink(v_kind_493_, v_name_494_);
lean_dec_ref(v_name_494_);
lean_dec_ref(v_kind_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(lean_object* v_00_u03b2_496_, lean_object* v_m_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v_m_497_, v_a_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___boxed(lean_object* v_00_u03b2_500_, lean_object* v_m_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(v_00_u03b2_500_, v_m_501_, v_a_502_);
lean_dec_ref(v_a_502_);
lean_dec_ref(v_m_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(lean_object* v_00_u03b2_504_, lean_object* v_m_505_, lean_object* v_query_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_m_505_, v_query_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___boxed(lean_object* v_00_u03b2_508_, lean_object* v_m_509_, lean_object* v_query_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(v_00_u03b2_508_, v_m_509_, v_query_510_);
lean_dec_ref(v_query_510_);
lean_dec_ref(v_m_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(lean_object* v_s_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0));
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___boxed(lean_object* v_s_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(v_s_516_);
lean_dec_ref(v_s_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(lean_object* v_path_518_, lean_object* v___x_519_, lean_object* v___x_520_, lean_object* v_a_521_, lean_object* v_b_522_){
_start:
{
lean_object* v_it_524_; lean_object* v_startInclusive_525_; lean_object* v_endExclusive_526_; 
if (lean_obj_tag(v_a_521_) == 0)
{
lean_object* v_currPos_531_; lean_object* v_searcher_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_558_; 
v_currPos_531_ = lean_ctor_get(v_a_521_, 0);
v_searcher_532_ = lean_ctor_get(v_a_521_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_a_521_);
if (v_isSharedCheck_558_ == 0)
{
v___x_534_ = v_a_521_;
v_isShared_535_ = v_isSharedCheck_558_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_searcher_532_);
lean_inc(v_currPos_531_);
lean_dec(v_a_521_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_558_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_startInclusive_536_; lean_object* v_endExclusive_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_startInclusive_536_ = lean_ctor_get(v___x_519_, 1);
v_endExclusive_537_ = lean_ctor_get(v___x_519_, 2);
v___x_538_ = lean_nat_sub(v_endExclusive_537_, v_startInclusive_536_);
v___x_539_ = lean_nat_dec_eq(v_searcher_532_, v___x_538_);
lean_dec(v___x_538_);
if (v___x_539_ == 0)
{
uint32_t v___x_540_; uint32_t v___x_541_; uint8_t v___x_542_; 
v___x_540_ = 47;
v___x_541_ = lean_string_utf8_get_fast(v_path_518_, v_searcher_532_);
v___x_542_ = lean_uint32_dec_eq(v___x_541_, v___x_540_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = lean_string_utf8_next_fast(v_path_518_, v_searcher_532_);
lean_dec(v_searcher_532_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___x_543_);
v___x_545_ = v___x_534_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_currPos_531_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_547_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
v_a_521_ = v___x_545_;
goto _start;
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v_slice_551_; lean_object* v_nextIt_553_; 
v___x_548_ = lean_string_utf8_next_fast(v_path_518_, v_searcher_532_);
v___x_549_ = lean_nat_sub(v___x_548_, v_searcher_532_);
v___x_550_ = lean_nat_add(v_searcher_532_, v___x_549_);
lean_dec(v___x_549_);
v_slice_551_ = l_String_Slice_subslice_x21(v___x_519_, v_currPos_531_, v_searcher_532_);
lean_inc(v___x_550_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___x_550_);
lean_ctor_set(v___x_534_, 0, v___x_550_);
v_nextIt_553_ = v___x_534_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_550_);
v_nextIt_553_ = v_reuseFailAlloc_556_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v_startInclusive_554_; lean_object* v_endExclusive_555_; 
v_startInclusive_554_ = lean_ctor_get(v_slice_551_, 0);
lean_inc(v_startInclusive_554_);
v_endExclusive_555_ = lean_ctor_get(v_slice_551_, 1);
lean_inc(v_endExclusive_555_);
lean_dec_ref(v_slice_551_);
v_it_524_ = v_nextIt_553_;
v_startInclusive_525_ = v_startInclusive_554_;
v_endExclusive_526_ = v_endExclusive_555_;
goto v___jp_523_;
}
}
}
else
{
lean_object* v___x_557_; 
lean_del_object(v___x_534_);
lean_dec(v_searcher_532_);
v___x_557_ = lean_box(1);
lean_inc(v___x_520_);
v_it_524_ = v___x_557_;
v_startInclusive_525_ = v_currPos_531_;
v_endExclusive_526_ = v___x_520_;
goto v___jp_523_;
}
}
}
else
{
lean_dec(v___x_520_);
lean_dec_ref(v_path_518_);
return v_b_522_;
}
v___jp_523_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
lean_inc_ref(v_path_518_);
v___x_527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_527_, 0, v_path_518_);
lean_ctor_set(v___x_527_, 1, v_startInclusive_525_);
lean_ctor_set(v___x_527_, 2, v_endExclusive_526_);
v___x_528_ = l_String_Slice_toString(v___x_527_);
lean_dec_ref_known(v___x_527_, 3);
v___x_529_ = lean_array_push(v_b_522_, v___x_528_);
v_a_521_ = v_it_524_;
v_b_522_ = v___x_529_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg___boxed(lean_object* v_path_559_, lean_object* v___x_560_, lean_object* v___x_561_, lean_object* v_a_562_, lean_object* v_b_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_559_, v___x_560_, v___x_561_, v_a_562_, v_b_563_);
lean_dec_ref(v___x_560_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
return v_x_565_;
}
else
{
lean_object* v_head_567_; lean_object* v_tail_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_head_567_ = lean_ctor_get(v_x_566_, 0);
v_tail_568_ = lean_ctor_get(v_x_566_, 1);
v___x_569_ = ((lean_object*)(l_Lean_manualLink___closed__2));
v___x_570_ = lean_string_append(v_x_565_, v___x_569_);
v___x_571_ = lean_string_append(v___x_570_, v_head_567_);
v_x_565_ = v___x_571_;
v_x_566_ = v_tail_568_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0___boxed(lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v_x_573_, v_x_574_);
lean_dec(v_x_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(lean_object* v_x_579_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
lean_object* v___x_580_; 
v___x_580_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0));
return v___x_580_;
}
else
{
lean_object* v_tail_581_; 
v_tail_581_ = lean_ctor_get(v_x_579_, 1);
if (lean_obj_tag(v_tail_581_) == 0)
{
lean_object* v_head_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_head_582_ = lean_ctor_get(v_x_579_, 0);
v___x_583_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_584_ = lean_string_append(v___x_583_, v_head_582_);
v___x_585_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2));
v___x_586_ = lean_string_append(v___x_584_, v___x_585_);
return v___x_586_;
}
else
{
lean_object* v_head_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint32_t v___x_591_; lean_object* v___x_592_; 
v_head_587_ = lean_ctor_get(v_x_579_, 0);
v___x_588_ = ((lean_object*)(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1));
v___x_589_ = lean_string_append(v___x_588_, v_head_587_);
v___x_590_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v___x_589_, v_tail_581_);
v___x_591_ = 93;
v___x_592_ = lean_string_push(v___x_590_, v___x_591_);
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___boxed(lean_object* v_x_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v_x_593_);
lean_dec(v_x_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rw(lean_object* v_path_605_){
_start:
{
lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_string_utf8_byte_size(v_path_605_);
lean_inc_ref(v_path_605_);
v___x_620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_620_, 0, v_path_605_);
lean_ctor_set(v___x_620_, 1, v___x_618_);
lean_ctor_set(v___x_620_, 2, v___x_619_);
v___x_621_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(v___x_620_);
v___x_622_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__4));
v___x_623_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_605_, v___x_620_, v___x_619_, v___x_621_, v___x_622_);
lean_dec_ref_known(v___x_620_, 3);
v___x_624_ = lean_array_to_list(v___x_623_);
if (lean_obj_tag(v___x_624_) == 0)
{
goto v___jp_616_;
}
else
{
lean_object* v_head_625_; lean_object* v_tail_626_; lean_object* v_kind_628_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_head_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_head_625_);
v_tail_626_ = lean_ctor_get(v___x_624_, 1);
lean_inc(v_tail_626_);
lean_dec_ref_known(v___x_624_, 2);
v___x_662_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_663_ = lean_string_dec_eq(v_head_625_, v___x_662_);
if (v___x_663_ == 0)
{
v_kind_628_ = v_head_625_;
goto v___jp_627_;
}
else
{
lean_dec(v_head_625_);
if (lean_obj_tag(v_tail_626_) == 0)
{
goto v___jp_616_;
}
else
{
v_kind_628_ = v___x_662_;
goto v___jp_627_;
}
}
v___jp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
v___x_630_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_629_, v_kind_628_);
if (lean_obj_tag(v___x_630_) == 1)
{
if (lean_obj_tag(v_tail_626_) == 1)
{
lean_object* v_tail_631_; 
v_tail_631_ = lean_ctor_get(v_tail_626_, 1);
if (lean_obj_tag(v_tail_631_) == 0)
{
lean_object* v_val_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_654_; 
v_val_632_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_654_ == 0)
{
v___x_634_ = v___x_630_;
v_isShared_635_ = v_isSharedCheck_654_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_val_632_);
lean_dec(v___x_630_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_654_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v_head_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_head_636_ = lean_ctor_get(v_tail_626_, 0);
lean_inc(v_head_636_);
lean_dec_ref_known(v_tail_626_, 2);
v___x_637_ = lean_string_utf8_byte_size(v_head_636_);
v___x_638_ = lean_nat_dec_eq(v___x_637_, v___x_618_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
lean_dec_ref(v_kind_628_);
v___x_639_ = ((lean_object*)(l_Lean_manualLink___closed__0));
v___x_640_ = lean_string_append(v___x_639_, v_val_632_);
lean_dec(v_val_632_);
v___x_641_ = ((lean_object*)(l_Lean_manualLink___closed__1));
v___x_642_ = lean_string_append(v___x_640_, v___x_641_);
v___x_643_ = lean_string_append(v___x_642_, v_head_636_);
lean_dec(v_head_636_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_643_);
v___x_645_ = v___x_634_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
lean_dec(v_head_636_);
lean_dec(v_val_632_);
v___x_647_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__5));
v___x_648_ = lean_string_append(v___x_647_, v_kind_628_);
lean_dec_ref(v_kind_628_);
v___x_649_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__6));
v___x_650_ = lean_string_append(v___x_648_, v___x_649_);
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 0);
lean_ctor_set(v___x_634_, 0, v___x_650_);
v___x_652_ = v___x_634_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_630_, 1);
v___y_607_ = v_tail_626_;
v___y_608_ = v_kind_628_;
goto v___jp_606_;
}
}
else
{
lean_dec_ref_known(v___x_630_, 1);
v___y_607_ = v_tail_626_;
v___y_608_ = v_kind_628_;
goto v___jp_606_;
}
}
else
{
lean_object* v_acceptableKinds_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec(v___x_630_);
lean_dec(v_tail_626_);
v_acceptableKinds_655_ = lean_obj_once(&l_Lean_manualLink___closed__5, &l_Lean_manualLink___closed__5_once, _init_l_Lean_manualLink___closed__5);
v___x_656_ = ((lean_object*)(l_Lean_manualLink___closed__6));
v___x_657_ = lean_string_append(v___x_656_, v_kind_628_);
lean_dec_ref(v_kind_628_);
v___x_658_ = ((lean_object*)(l_Lean_manualLink___closed__7));
v___x_659_ = lean_string_append(v___x_657_, v___x_658_);
v___x_660_ = lean_string_append(v___x_659_, v_acceptableKinds_655_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
}
v___jp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_609_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__0));
v___x_610_ = lean_string_append(v___x_609_, v___y_608_);
lean_dec_ref(v___y_608_);
v___x_611_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__1));
v___x_612_ = lean_string_append(v___x_610_, v___x_611_);
v___x_613_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v___y_607_);
lean_dec(v___y_607_);
v___x_614_ = lean_string_append(v___x_612_, v___x_613_);
lean_dec_ref(v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
v___jp_616_:
{
lean_object* v___x_617_; 
v___x_617_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__3));
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(lean_object* v_path_664_, lean_object* v___x_665_, lean_object* v___x_666_, lean_object* v_inst_667_, lean_object* v_R_668_, lean_object* v_a_669_, lean_object* v_b_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_664_, v___x_665_, v___x_666_, v_a_669_, v_b_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___boxed(lean_object* v_path_672_, lean_object* v___x_673_, lean_object* v___x_674_, lean_object* v_inst_675_, lean_object* v_R_676_, lean_object* v_a_677_, lean_object* v_b_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(v_path_672_, v___x_673_, v___x_674_, v_inst_675_, v_R_676_, v_a_677_, v_b_678_);
lean_dec_ref(v___x_673_);
return v_res_679_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(uint32_t v_c_680_){
_start:
{
uint8_t v___y_682_; uint8_t v___y_724_; uint32_t v___x_734_; uint8_t v___x_735_; 
v___x_734_ = 65;
v___x_735_ = lean_uint32_dec_le(v___x_734_, v_c_680_);
if (v___x_735_ == 0)
{
goto v___jp_729_;
}
else
{
uint32_t v___x_736_; uint8_t v___x_737_; 
v___x_736_ = 90;
v___x_737_ = lean_uint32_dec_le(v_c_680_, v___x_736_);
if (v___x_737_ == 0)
{
goto v___jp_729_;
}
else
{
return v___x_737_;
}
}
v___jp_681_:
{
if (v___y_682_ == 0)
{
uint32_t v___x_683_; uint8_t v___x_684_; 
v___x_683_ = 45;
v___x_684_ = lean_uint32_dec_eq(v_c_680_, v___x_683_);
if (v___x_684_ == 0)
{
uint32_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = 46;
v___x_686_ = lean_uint32_dec_eq(v_c_680_, v___x_685_);
if (v___x_686_ == 0)
{
uint32_t v___x_687_; uint8_t v___x_688_; 
v___x_687_ = 95;
v___x_688_ = lean_uint32_dec_eq(v_c_680_, v___x_687_);
if (v___x_688_ == 0)
{
uint32_t v___x_689_; uint8_t v___x_690_; 
v___x_689_ = 126;
v___x_690_ = lean_uint32_dec_eq(v_c_680_, v___x_689_);
if (v___x_690_ == 0)
{
uint32_t v___x_691_; uint8_t v___x_692_; 
v___x_691_ = 58;
v___x_692_ = lean_uint32_dec_eq(v_c_680_, v___x_691_);
if (v___x_692_ == 0)
{
uint32_t v___x_693_; uint8_t v___x_694_; 
v___x_693_ = 47;
v___x_694_ = lean_uint32_dec_eq(v_c_680_, v___x_693_);
if (v___x_694_ == 0)
{
uint32_t v___x_695_; uint8_t v___x_696_; 
v___x_695_ = 63;
v___x_696_ = lean_uint32_dec_eq(v_c_680_, v___x_695_);
if (v___x_696_ == 0)
{
uint32_t v___x_697_; uint8_t v___x_698_; 
v___x_697_ = 35;
v___x_698_ = lean_uint32_dec_eq(v_c_680_, v___x_697_);
if (v___x_698_ == 0)
{
uint32_t v___x_699_; uint8_t v___x_700_; 
v___x_699_ = 91;
v___x_700_ = lean_uint32_dec_eq(v_c_680_, v___x_699_);
if (v___x_700_ == 0)
{
uint32_t v___x_701_; uint8_t v___x_702_; 
v___x_701_ = 93;
v___x_702_ = lean_uint32_dec_eq(v_c_680_, v___x_701_);
if (v___x_702_ == 0)
{
uint32_t v___x_703_; uint8_t v___x_704_; 
v___x_703_ = 64;
v___x_704_ = lean_uint32_dec_eq(v_c_680_, v___x_703_);
if (v___x_704_ == 0)
{
uint32_t v___x_705_; uint8_t v___x_706_; 
v___x_705_ = 33;
v___x_706_ = lean_uint32_dec_eq(v_c_680_, v___x_705_);
if (v___x_706_ == 0)
{
uint32_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = 36;
v___x_708_ = lean_uint32_dec_eq(v_c_680_, v___x_707_);
if (v___x_708_ == 0)
{
uint32_t v___x_709_; uint8_t v___x_710_; 
v___x_709_ = 38;
v___x_710_ = lean_uint32_dec_eq(v_c_680_, v___x_709_);
if (v___x_710_ == 0)
{
uint32_t v___x_711_; uint8_t v___x_712_; 
v___x_711_ = 39;
v___x_712_ = lean_uint32_dec_eq(v_c_680_, v___x_711_);
if (v___x_712_ == 0)
{
uint32_t v___x_713_; uint8_t v___x_714_; 
v___x_713_ = 42;
v___x_714_ = lean_uint32_dec_eq(v_c_680_, v___x_713_);
if (v___x_714_ == 0)
{
uint32_t v___x_715_; uint8_t v___x_716_; 
v___x_715_ = 43;
v___x_716_ = lean_uint32_dec_eq(v_c_680_, v___x_715_);
if (v___x_716_ == 0)
{
uint32_t v___x_717_; uint8_t v___x_718_; 
v___x_717_ = 44;
v___x_718_ = lean_uint32_dec_eq(v_c_680_, v___x_717_);
if (v___x_718_ == 0)
{
uint32_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = 59;
v___x_720_ = lean_uint32_dec_eq(v_c_680_, v___x_719_);
if (v___x_720_ == 0)
{
uint32_t v___x_721_; uint8_t v___x_722_; 
v___x_721_ = 61;
v___x_722_ = lean_uint32_dec_eq(v_c_680_, v___x_721_);
return v___x_722_;
}
else
{
return v___x_720_;
}
}
else
{
return v___x_718_;
}
}
else
{
return v___x_716_;
}
}
else
{
return v___x_714_;
}
}
else
{
return v___x_712_;
}
}
else
{
return v___x_710_;
}
}
else
{
return v___x_708_;
}
}
else
{
return v___x_706_;
}
}
else
{
return v___x_704_;
}
}
else
{
return v___x_702_;
}
}
else
{
return v___x_700_;
}
}
else
{
return v___x_698_;
}
}
else
{
return v___x_696_;
}
}
else
{
return v___x_694_;
}
}
else
{
return v___x_692_;
}
}
else
{
return v___x_690_;
}
}
else
{
return v___x_688_;
}
}
else
{
return v___x_686_;
}
}
else
{
return v___x_684_;
}
}
else
{
return v___y_682_;
}
}
v___jp_723_:
{
if (v___y_724_ == 0)
{
uint32_t v___x_725_; uint8_t v___x_726_; 
v___x_725_ = 48;
v___x_726_ = lean_uint32_dec_le(v___x_725_, v_c_680_);
if (v___x_726_ == 0)
{
v___y_682_ = v___x_726_;
goto v___jp_681_;
}
else
{
uint32_t v___x_727_; uint8_t v___x_728_; 
v___x_727_ = 57;
v___x_728_ = lean_uint32_dec_le(v_c_680_, v___x_727_);
v___y_682_ = v___x_728_;
goto v___jp_681_;
}
}
else
{
return v___y_724_;
}
}
v___jp_729_:
{
uint32_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = 97;
v___x_731_ = lean_uint32_dec_le(v___x_730_, v_c_680_);
if (v___x_731_ == 0)
{
v___y_724_ = v___x_731_;
goto v___jp_723_;
}
else
{
uint32_t v___x_732_; uint8_t v___x_733_; 
v___x_732_ = 122;
v___x_733_ = lean_uint32_dec_le(v_c_680_, v___x_732_);
v___y_724_ = v___x_733_;
goto v___jp_723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar___boxed(lean_object* v_c_738_){
_start:
{
uint32_t v_c_boxed_739_; uint8_t v_res_740_; lean_object* v_r_741_; 
v_c_boxed_739_ = lean_unbox_uint32(v_c_738_);
lean_dec(v_c_738_);
v_res_740_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v_c_boxed_739_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(lean_object* v_s_742_, lean_object* v___x_743_, lean_object* v___x_744_, uint32_t v___x_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_snd_747_; lean_object* v_snd_748_; lean_object* v_fst_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_817_; 
v_snd_747_ = lean_ctor_get(v_a_746_, 1);
lean_inc(v_snd_747_);
v_snd_748_ = lean_ctor_get(v_snd_747_, 1);
lean_inc(v_snd_748_);
v_fst_749_ = lean_ctor_get(v_a_746_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v_a_746_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_a_746_, 1);
lean_dec(v_unused_818_);
v___x_751_ = v_a_746_;
v_isShared_752_ = v_isSharedCheck_817_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_fst_749_);
lean_dec(v_a_746_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_817_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_fst_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_815_; 
v_fst_753_ = lean_ctor_get(v_snd_747_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v_snd_747_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v_snd_747_, 1);
lean_dec(v_unused_816_);
v___x_755_ = v_snd_747_;
v_isShared_756_ = v_isSharedCheck_815_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_fst_753_);
lean_dec(v_snd_747_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_815_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_fst_757_; lean_object* v_snd_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_814_; 
v_fst_757_ = lean_ctor_get(v_snd_748_, 0);
v_snd_758_ = lean_ctor_get(v_snd_748_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v_snd_748_);
if (v_isSharedCheck_814_ == 0)
{
v___x_760_ = v_snd_748_;
v_isShared_761_ = v_isSharedCheck_814_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_snd_758_);
lean_inc(v_fst_757_);
lean_dec(v_snd_748_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_814_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_762_ = lean_string_utf8_byte_size(v_s_742_);
v___x_763_ = lean_nat_dec_eq(v_snd_758_, v___x_762_);
if (v___x_763_ == 0)
{
uint32_t v___x_764_; lean_object* v___x_765_; uint8_t v___y_798_; uint8_t v___x_803_; 
v___x_764_ = lean_string_utf8_get_fast(v_s_742_, v_snd_758_);
v___x_765_ = lean_string_utf8_next_fast(v_s_742_, v_snd_758_);
v___x_803_ = l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v___x_764_);
if (v___x_803_ == 0)
{
v___y_798_ = v___x_803_;
goto v___jp_797_;
}
else
{
uint8_t v___x_804_; 
v___x_804_ = lean_nat_dec_eq(v___x_765_, v___x_762_);
if (v___x_804_ == 0)
{
v___y_798_ = v___x_803_;
goto v___jp_797_;
}
else
{
goto v___jp_766_;
}
}
v___jp_766_:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_string_utf8_extract_fast(v_s_742_, v___x_743_, v_snd_758_);
v___x_768_ = l___private_Lean_DocString_Links_0__Lean_rw(v___x_767_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_744_);
lean_ctor_set(v___x_770_, 1, v_snd_758_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v_a_769_);
lean_ctor_set(v___x_760_, 0, v___x_770_);
v___x_772_ = v___x_760_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_a_769_);
v___x_772_ = v_reuseFailAlloc_782_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_773_ = lean_array_push(v_fst_753_, v___x_772_);
v___x_774_ = lean_string_push(v_fst_749_, v___x_745_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v___x_765_);
lean_ctor_set(v___x_755_, 0, v_fst_757_);
v___x_776_ = v___x_755_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_fst_757_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_765_);
v___x_776_ = v_reuseFailAlloc_781_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v___x_776_);
lean_ctor_set(v___x_751_, 0, v___x_773_);
v___x_778_ = v___x_751_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_780_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; 
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_774_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
return v___x_779_;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
lean_dec(v_snd_758_);
lean_dec(v_fst_757_);
lean_dec(v___x_744_);
v_a_783_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_768_, 1);
v___x_784_ = l_Lean_manualRoot;
v___x_785_ = lean_string_append(v_fst_749_, v___x_784_);
v___x_786_ = lean_string_append(v___x_785_, v_a_783_);
lean_dec(v_a_783_);
v___x_787_ = lean_string_push(v___x_786_, v___x_764_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v___x_765_);
lean_ctor_set(v___x_760_, 0, v___x_765_);
v___x_789_ = v___x_760_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_765_);
v___x_789_ = v_reuseFailAlloc_796_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_791_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v___x_789_);
v___x_791_ = v___x_755_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_fst_753_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_789_);
v___x_791_ = v_reuseFailAlloc_795_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_793_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v___x_791_);
lean_ctor_set(v___x_751_, 0, v___x_787_);
v___x_793_ = v___x_751_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
v___jp_797_:
{
if (v___y_798_ == 0)
{
goto v___jp_766_;
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_del_object(v___x_760_);
lean_dec(v_snd_758_);
lean_del_object(v___x_755_);
lean_del_object(v___x_751_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_fst_757_);
lean_ctor_set(v___x_799_, 1, v___x_765_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_fst_753_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_fst_749_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v_a_746_ = v___x_801_;
goto _start;
}
}
}
else
{
lean_object* v___x_806_; 
lean_dec(v___x_744_);
if (v_isShared_761_ == 0)
{
v___x_806_ = v___x_760_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_fst_757_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_snd_758_);
v___x_806_ = v_reuseFailAlloc_813_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v___x_806_);
v___x_808_ = v___x_755_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_fst_753_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_806_);
v___x_808_ = v_reuseFailAlloc_812_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v___x_808_);
v___x_810_ = v___x_751_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_fst_749_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg___boxed(lean_object* v_s_819_, lean_object* v___x_820_, lean_object* v___x_821_, lean_object* v___x_822_, lean_object* v_a_823_){
_start:
{
uint32_t v___x_2150__boxed_824_; lean_object* v_res_825_; 
v___x_2150__boxed_824_ = lean_unbox_uint32(v___x_822_);
lean_dec(v___x_822_);
v_res_825_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_819_, v___x_820_, v___x_821_, v___x_2150__boxed_824_, v_a_823_);
lean_dec(v___x_820_);
lean_dec_ref(v_s_819_);
return v_res_825_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v_scheme_827_; lean_object* v___x_828_; 
v_scheme_827_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0));
v___x_828_ = lean_string_utf8_byte_size(v_scheme_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(lean_object* v_s_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_snd_831_; lean_object* v_fst_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_896_; 
v_snd_831_ = lean_ctor_get(v_a_830_, 1);
v_fst_832_ = lean_ctor_get(v_a_830_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v_a_830_);
if (v_isSharedCheck_896_ == 0)
{
v___x_834_ = v_a_830_;
v_isShared_835_ = v_isSharedCheck_896_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_snd_831_);
lean_inc(v_fst_832_);
lean_dec(v_a_830_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_896_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_fst_836_; lean_object* v_snd_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_895_; 
v_fst_836_ = lean_ctor_get(v_snd_831_, 0);
v_snd_837_ = lean_ctor_get(v_snd_831_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_snd_831_);
if (v_isSharedCheck_895_ == 0)
{
v___x_839_ = v_snd_831_;
v_isShared_840_ = v_isSharedCheck_895_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_snd_837_);
lean_inc(v_fst_836_);
lean_dec(v_snd_831_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_895_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = lean_string_utf8_byte_size(v_s_829_);
v___x_842_ = lean_nat_dec_eq(v_snd_837_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v_scheme_843_; uint32_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_scheme_843_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0));
v___x_844_ = lean_string_utf8_get_fast(v_s_829_, v_snd_837_);
v___x_845_ = lean_string_utf8_next_fast(v_s_829_, v_snd_837_);
v___x_855_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1);
v___x_856_ = lean_nat_sub(v___x_841_, v_snd_837_);
v___x_857_ = lean_nat_dec_le(v___x_855_, v___x_856_);
lean_dec(v___x_856_);
if (v___x_857_ == 0)
{
lean_dec(v_snd_837_);
goto v___jp_846_;
}
else
{
lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_string_memcmp(v_s_829_, v_scheme_843_, v_snd_837_, v___x_858_, v___x_855_);
if (v___x_859_ == 0)
{
lean_dec(v_snd_837_);
goto v___jp_846_;
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v_snd_867_; lean_object* v_snd_868_; lean_object* v_fst_869_; lean_object* v_fst_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_887_; 
lean_del_object(v___x_839_);
lean_del_object(v___x_834_);
lean_inc(v_snd_837_);
lean_inc_ref(v_s_829_);
v___x_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_860_, 0, v_s_829_);
lean_ctor_set(v___x_860_, 1, v_snd_837_);
lean_ctor_set(v___x_860_, 2, v___x_841_);
v___x_861_ = l_String_Slice_pos_x21(v___x_860_, v___x_855_);
lean_dec_ref_known(v___x_860_, 3);
v___x_862_ = lean_nat_add(v_snd_837_, v___x_861_);
lean_dec(v___x_861_);
lean_inc(v___x_862_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_845_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v_fst_836_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v_fst_832_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_829_, v___x_862_, v_snd_837_, v___x_844_, v___x_865_);
lean_dec(v___x_862_);
v_snd_867_ = lean_ctor_get(v___x_866_, 1);
lean_inc(v_snd_867_);
v_snd_868_ = lean_ctor_get(v_snd_867_, 1);
lean_inc(v_snd_868_);
v_fst_869_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_fst_869_);
lean_dec_ref(v___x_866_);
v_fst_870_ = lean_ctor_get(v_snd_867_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v_snd_867_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; 
v_unused_888_ = lean_ctor_get(v_snd_867_, 1);
lean_dec(v_unused_888_);
v___x_872_ = v_snd_867_;
v_isShared_873_ = v_isSharedCheck_887_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_fst_870_);
lean_dec(v_snd_867_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_887_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v_fst_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_885_; 
v_fst_874_ = lean_ctor_get(v_snd_868_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v_snd_868_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v_snd_868_, 1);
lean_dec(v_unused_886_);
v___x_876_ = v_snd_868_;
v_isShared_877_ = v_isSharedCheck_885_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_fst_874_);
lean_dec(v_snd_868_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_885_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v_fst_874_);
lean_ctor_set(v___x_876_, 0, v_fst_870_);
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_fst_870_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_fst_874_);
v___x_879_ = v_reuseFailAlloc_884_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_881_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___x_879_);
lean_ctor_set(v___x_872_, 0, v_fst_869_);
v___x_881_ = v___x_872_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_fst_869_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_879_);
v___x_881_ = v_reuseFailAlloc_883_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
v_a_830_ = v___x_881_;
goto _start;
}
}
}
}
}
}
v___jp_846_:
{
lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_847_ = lean_string_push(v_fst_832_, v___x_844_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_845_);
v___x_849_ = v___x_839_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_fst_836_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v___x_845_);
v___x_849_ = v_reuseFailAlloc_854_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_851_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_849_);
lean_ctor_set(v___x_834_, 0, v___x_847_);
v___x_851_ = v___x_834_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_849_);
v___x_851_ = v_reuseFailAlloc_853_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
v_a_830_ = v___x_851_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_890_; 
lean_dec_ref(v_s_829_);
if (v_isShared_840_ == 0)
{
v___x_890_ = v___x_839_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_fst_836_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_snd_837_);
v___x_890_ = v_reuseFailAlloc_894_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_892_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_890_);
v___x_892_ = v___x_834_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_fst_832_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore(lean_object* v_s_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v_snd_908_; lean_object* v_fst_909_; lean_object* v_fst_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
v___x_906_ = ((lean_object*)(l_Lean_rewriteManualLinksCore___closed__2));
v___x_907_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(v_s_905_, v___x_906_);
v_snd_908_ = lean_ctor_get(v___x_907_, 1);
lean_inc(v_snd_908_);
v_fst_909_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_fst_909_);
lean_dec_ref(v___x_907_);
v_fst_910_ = lean_ctor_get(v_snd_908_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_snd_908_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; 
v_unused_918_ = lean_ctor_get(v_snd_908_, 1);
lean_dec(v_unused_918_);
v___x_912_ = v_snd_908_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_fst_910_);
lean_dec(v_snd_908_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v_fst_909_);
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_fst_910_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_fst_909_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0(lean_object* v_s_919_, lean_object* v___x_920_, lean_object* v___x_921_, uint32_t v___x_922_, lean_object* v_inst_923_, lean_object* v_a_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_919_, v___x_920_, v___x_921_, v___x_922_, v_a_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0___boxed(lean_object* v_s_926_, lean_object* v___x_927_, lean_object* v___x_928_, lean_object* v___x_929_, lean_object* v_inst_930_, lean_object* v_a_931_){
_start:
{
uint32_t v___x_2435__boxed_932_; lean_object* v_res_933_; 
v___x_2435__boxed_932_ = lean_unbox_uint32(v___x_929_);
lean_dec(v___x_929_);
v_res_933_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__0(v_s_926_, v___x_927_, v___x_928_, v___x_2435__boxed_932_, v_inst_930_, v_a_931_);
lean_dec(v___x_927_);
lean_dec_ref(v_s_926_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1(lean_object* v_s_934_, lean_object* v_inst_935_, lean_object* v_a_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l___private_Init_While_0__repeatM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(v_s_934_, v_a_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(lean_object* v_docString_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
if (lean_obj_tag(v_a_942_) == 0)
{
lean_object* v___x_944_; 
v___x_944_ = l_List_reverse___redArg(v_a_943_);
return v___x_944_;
}
else
{
lean_object* v_head_945_; lean_object* v_fst_946_; lean_object* v_tail_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_966_; 
v_head_945_ = lean_ctor_get(v_a_942_, 0);
lean_inc(v_head_945_);
v_fst_946_ = lean_ctor_get(v_head_945_, 0);
lean_inc(v_fst_946_);
v_tail_947_ = lean_ctor_get(v_a_942_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v_a_942_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v_a_942_, 0);
lean_dec(v_unused_967_);
v___x_949_ = v_a_942_;
v_isShared_950_ = v_isSharedCheck_966_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_tail_947_);
lean_dec(v_a_942_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_966_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v_snd_951_; lean_object* v_start_952_; lean_object* v_stop_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v_snd_951_ = lean_ctor_get(v_head_945_, 1);
lean_inc(v_snd_951_);
lean_dec(v_head_945_);
v_start_952_ = lean_ctor_get(v_fst_946_, 0);
lean_inc(v_start_952_);
v_stop_953_ = lean_ctor_get(v_fst_946_, 1);
lean_inc(v_stop_953_);
lean_dec(v_fst_946_);
v___x_954_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0));
v___x_955_ = lean_string_utf8_extract(v_docString_941_, v_start_952_, v_stop_953_);
lean_dec(v_stop_953_);
lean_dec(v_start_952_);
v___x_956_ = lean_string_append(v___x_954_, v___x_955_);
lean_dec_ref(v___x_955_);
v___x_957_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1));
v___x_958_ = lean_string_append(v___x_956_, v___x_957_);
v___x_959_ = lean_string_append(v___x_958_, v_snd_951_);
lean_dec(v_snd_951_);
v___x_960_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_961_ = lean_string_append(v___x_959_, v___x_960_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v_a_943_);
lean_ctor_set(v___x_949_, 0, v___x_961_);
v___x_963_ = v___x_949_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_a_943_);
v___x_963_ = v_reuseFailAlloc_965_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
v_a_942_ = v_tail_947_;
v_a_943_ = v___x_963_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___boxed(lean_object* v_docString_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_968_, v_a_969_, v_a_970_);
lean_dec_ref(v_docString_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(lean_object* v_x_972_, lean_object* v_x_973_){
_start:
{
if (lean_obj_tag(v_x_973_) == 0)
{
return v_x_972_;
}
else
{
lean_object* v_head_974_; lean_object* v_tail_975_; lean_object* v___x_976_; 
v_head_974_ = lean_ctor_get(v_x_973_, 0);
v_tail_975_ = lean_ctor_get(v_x_973_, 1);
v___x_976_ = lean_string_append(v_x_972_, v_head_974_);
v_x_972_ = v___x_976_;
v_x_973_ = v_tail_975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rewriteManualLinks_spec__1___boxed(lean_object* v_x_978_, lean_object* v_x_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v_x_978_, v_x_979_);
lean_dec(v_x_979_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks(lean_object* v_docString_982_){
_start:
{
lean_object* v___x_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
lean_inc_ref(v_docString_982_);
v___x_984_ = l_Lean_rewriteManualLinksCore(v_docString_982_);
v_fst_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_fst_985_);
v_snd_986_ = lean_ctor_get(v___x_984_, 1);
lean_inc(v_snd_986_);
lean_dec_ref(v___x_984_);
v___x_987_ = lean_array_get_size(v_fst_985_);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_nat_dec_eq(v___x_987_, v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_990_ = ((lean_object*)(l_Lean_rewriteManualLinks___closed__0));
v___x_991_ = lean_array_to_list(v_fst_985_);
v___x_992_ = lean_box(0);
v___x_993_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(v_docString_982_, v___x_991_, v___x_992_);
lean_dec_ref(v_docString_982_);
v___x_994_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_995_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_994_, v___x_993_);
lean_dec(v___x_993_);
v___x_996_ = lean_string_append(v___x_990_, v___x_995_);
lean_dec_ref(v___x_995_);
v___x_997_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2));
v___x_998_ = lean_string_append(v_snd_986_, v___x_997_);
v___x_999_ = lean_string_append(v___x_998_, v___x_996_);
lean_dec_ref(v___x_996_);
return v___x_999_;
}
else
{
lean_dec(v_fst_985_);
lean_dec_ref(v_docString_982_);
return v_snd_986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks___boxed(lean_object* v_docString_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_rewriteManualLinks(v_docString_1000_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(lean_object* v_docString_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
if (lean_obj_tag(v_a_1007_) == 0)
{
lean_object* v___x_1009_; 
v___x_1009_ = l_List_reverse___redArg(v_a_1008_);
return v___x_1009_;
}
else
{
lean_object* v_head_1010_; lean_object* v_fst_1011_; lean_object* v_tail_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1036_; 
v_head_1010_ = lean_ctor_get(v_a_1007_, 0);
lean_inc(v_head_1010_);
v_fst_1011_ = lean_ctor_get(v_head_1010_, 0);
lean_inc(v_fst_1011_);
v_tail_1012_ = lean_ctor_get(v_a_1007_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_a_1007_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v_a_1007_, 0);
lean_dec(v_unused_1037_);
v___x_1014_ = v_a_1007_;
v_isShared_1015_ = v_isSharedCheck_1036_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_tail_1012_);
lean_dec(v_a_1007_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1036_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v_snd_1016_; lean_object* v_start_1017_; lean_object* v_stop_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
v_snd_1016_ = lean_ctor_get(v_head_1010_, 1);
lean_inc(v_snd_1016_);
lean_dec(v_head_1010_);
v_start_1017_ = lean_ctor_get(v_fst_1011_, 0);
lean_inc(v_start_1017_);
v_stop_1018_ = lean_ctor_get(v_fst_1011_, 1);
lean_inc(v_stop_1018_);
lean_dec(v_fst_1011_);
v___x_1019_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0));
v___x_1020_ = lean_string_utf8_extract(v_docString_1006_, v_start_1017_, v_stop_1018_);
lean_dec(v_stop_1018_);
lean_dec(v_start_1017_);
v___x_1021_ = l_String_quote(v___x_1020_);
v___x_1022_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
v___x_1023_ = l_Std_Format_defWidth;
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = l_Std_Format_pretty(v___x_1022_, v___x_1023_, v___x_1024_, v___x_1024_);
v___x_1026_ = lean_string_append(v___x_1019_, v___x_1025_);
lean_dec_ref(v___x_1025_);
v___x_1027_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1));
v___x_1028_ = lean_string_append(v___x_1026_, v___x_1027_);
v___x_1029_ = lean_string_append(v___x_1028_, v_snd_1016_);
lean_dec(v_snd_1016_);
v___x_1030_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2));
v___x_1031_ = lean_string_append(v___x_1029_, v___x_1030_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v_a_1008_);
lean_ctor_set(v___x_1014_, 0, v___x_1031_);
v___x_1033_ = v___x_1014_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_a_1008_);
v___x_1033_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
v_a_1007_ = v_tail_1012_;
v_a_1008_ = v___x_1033_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___boxed(lean_object* v_docString_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_1038_, v_a_1039_, v_a_1040_);
lean_dec_ref(v_docString_1038_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString(lean_object* v_docString_1043_){
_start:
{
lean_object* v___x_1045_; lean_object* v_fst_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
lean_inc_ref(v_docString_1043_);
v___x_1045_ = l_Lean_rewriteManualLinksCore(v_docString_1043_);
v_fst_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_fst_1046_);
lean_dec_ref(v___x_1045_);
v___x_1047_ = lean_array_get_size(v_fst_1046_);
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = lean_nat_dec_eq(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1050_ = ((lean_object*)(l_Lean_validateBuiltinDocString___closed__0));
v___x_1051_ = lean_array_to_list(v_fst_1046_);
v___x_1052_ = lean_box(0);
v___x_1053_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(v_docString_1043_, v___x_1051_, v___x_1052_);
lean_dec_ref(v_docString_1043_);
v___x_1054_ = ((lean_object*)(l___private_Lean_DocString_Links_0__Lean_rw___closed__7));
v___x_1055_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_1054_, v___x_1053_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_string_append(v___x_1050_, v___x_1055_);
lean_dec_ref(v___x_1055_);
v___x_1057_ = lean_mk_io_user_error(v___x_1056_);
v___x_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec(v_fst_1046_);
lean_dec_ref(v_docString_1043_);
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString___boxed(lean_object* v_docString_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_validateBuiltinDocString(v_docString_1061_);
return v_res_1063_;
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
