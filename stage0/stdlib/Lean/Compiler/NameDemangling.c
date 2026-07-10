// Lean compiler output
// Module: Lean.Compiler.NameDemangling
// Imports: import Init.While import Init.Data.String.TakeDrop import Init.Data.String.Search import Init.Data.String.Iterate import Lean.Data.NameTrie public import Lean.Compiler.NameMangling
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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_instInhabitedNamePart_default;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t l_Lean_instBEqNamePart_beq(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_Lean_Name_demangle(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_demangle_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName___boxed(lean_object*);
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___boxed(lean_object*);
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "λ"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_elam_"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__2 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_elam"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_jp"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_closed"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_lam_"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "closed"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7_value)}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "jp"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9_value)}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_redArg"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_impl"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_lam"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_lambda"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "impl"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__16 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__16_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__16_value)}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__17 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__17_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "boxed"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__18 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__18_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__18_value)}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__19 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__19_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 6, .m_data = "arity↓"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__20 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__20_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__20_value)}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__21 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(lean_object*);
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "spec_"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__1_value)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__1 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__1_value)}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0_value),((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_at_"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__0_value)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_spec"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0_value)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0_value)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " spec at "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0_value;
static const lean_array_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody___boxed(lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".cold"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lp_"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "l_"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "initialize_"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "[module_init] "};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "initialize_lp_"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "initialize_l_"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "_init_lp_"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "[init] "};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_init_l_"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(lean_object*);
static const lean_string_object l_Lean_Name_Demangle_demangleSymbol___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_lean_main"};
static const lean_object* l_Lean_Name_Demangle_demangleSymbol___closed__0 = (const lean_object*)&l_Lean_Name_Demangle_demangleSymbol___closed__0_value;
static const lean_string_object l_Lean_Name_Demangle_demangleSymbol___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Name_Demangle_demangleSymbol___closed__1 = (const lean_object*)&l_Lean_Name_Demangle_demangleSymbol___closed__1_value;
static const lean_string_object l_Lean_Name_Demangle_demangleSymbol___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "[lean] main "};
static const lean_object* l_Lean_Name_Demangle_demangleSymbol___closed__2 = (const lean_object*)&l_Lean_Name_Demangle_demangleSymbol___closed__2_value;
static const lean_string_object l_Lean_Name_Demangle_demangleSymbol___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[lean] main"};
static const lean_object* l_Lean_Name_Demangle_demangleSymbol___closed__3 = (const lean_object*)&l_Lean_Name_Demangle_demangleSymbol___closed__3_value;
static const lean_ctor_object l_Lean_Name_Demangle_demangleSymbol___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Name_Demangle_demangleSymbol___closed__3_value)}};
static const lean_object* l_Lean_Name_Demangle_demangleSymbol___closed__4 = (const lean_object*)&l_Lean_Name_Demangle_demangleSymbol___closed__4_value;
static const lean_string_object l_Lean_Name_Demangle_demangleSymbol___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "lean_apply_"};
static const lean_object* l_Lean_Name_Demangle_demangleSymbol___closed__5 = (const lean_object*)&l_Lean_Name_Demangle_demangleSymbol___closed__5_value;
static const lean_string_object l_Lean_Name_Demangle_demangleSymbol___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<apply/"};
static const lean_object* l_Lean_Name_Demangle_demangleSymbol___closed__6 = (const lean_object*)&l_Lean_Name_Demangle_demangleSymbol___closed__6_value;
static const lean_string_object l_Lean_Name_Demangle_demangleSymbol___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ">"};
static const lean_object* l_Lean_Name_Demangle_demangleSymbol___closed__7 = (const lean_object*)&l_Lean_Name_Demangle_demangleSymbol___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleSymbol(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "0x"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " + "};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleBtLine(lean_object*);
LEAN_EXPORT lean_object* lean_demangle_bt_line_cstr(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___redArg(lean_object* v_pre_1_, lean_object* v_s_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_3_ = lean_string_utf8_byte_size(v_s_2_);
v___x_4_ = lean_string_utf8_byte_size(v_pre_1_);
v___x_5_ = lean_nat_dec_le(v___x_4_, v___x_3_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; 
lean_dec_ref(v_s_2_);
v___x_6_ = lean_box(0);
return v___x_6_;
}
else
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_string_memcmp(v_s_2_, v_pre_1_, v___x_7_, v___x_7_, v___x_4_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
lean_dec_ref(v_s_2_);
v___x_9_ = lean_box(0);
return v___x_9_;
}
else
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
lean_inc_ref(v_s_2_);
v___x_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_10_, 0, v_s_2_);
lean_ctor_set(v___x_10_, 1, v___x_7_);
lean_ctor_set(v___x_10_, 2, v___x_3_);
v___x_11_ = l_String_Slice_pos_x21(v___x_10_, v___x_4_);
lean_dec_ref_known(v___x_10_, 3);
v___x_12_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_12_, 0, v_s_2_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
lean_ctor_set(v___x_12_, 2, v___x_3_);
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___redArg___boxed(lean_object* v_pre_14_, lean_object* v_s_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___redArg(v_pre_14_, v_s_15_);
lean_dec_ref(v_pre_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0(lean_object* v_pre_17_, lean_object* v_s_18_, lean_object* v_pat_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___redArg(v_pre_17_, v_s_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___boxed(lean_object* v_pre_21_, lean_object* v_s_22_, lean_object* v_pat_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0(v_pre_21_, v_s_22_, v_pat_23_);
lean_dec_ref(v_pat_23_);
lean_dec_ref(v_pre_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(lean_object* v_s_25_, lean_object* v_pre_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_String_dropPrefix_x3f___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f_spec__0___redArg(v_pre_26_, v_s_25_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v___x_28_; 
v___x_28_ = lean_box(0);
return v___x_28_;
}
else
{
lean_object* v_val_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_37_; 
v_val_29_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_37_ == 0)
{
v___x_31_ = v___x_27_;
v_isShared_32_ = v_isSharedCheck_37_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_val_29_);
lean_dec(v___x_27_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_37_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_33_ = l_String_Slice_toString(v_val_29_);
lean_dec(v_val_29_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 0, v___x_33_);
v___x_35_ = v___x_31_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_33_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f___boxed(lean_object* v_s_38_, lean_object* v_pre_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_38_, v_pre_39_);
lean_dec_ref(v_pre_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(lean_object* v_s_41_, lean_object* v_pos_42_){
_start:
{
lean_object* v_str_43_; lean_object* v_startInclusive_44_; lean_object* v_endExclusive_45_; lean_object* v___x_46_; uint8_t v___y_48_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v_str_43_ = lean_ctor_get(v_s_41_, 0);
v_startInclusive_44_ = lean_ctor_get(v_s_41_, 1);
v_endExclusive_45_ = lean_ctor_get(v_s_41_, 2);
v___x_46_ = lean_nat_add(v_startInclusive_44_, v_pos_42_);
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = lean_nat_sub(v_endExclusive_45_, v___x_46_);
v___x_56_ = lean_nat_dec_eq(v___x_54_, v___x_55_);
lean_dec(v___x_55_);
if (v___x_56_ == 0)
{
uint32_t v___x_57_; uint32_t v___x_58_; uint8_t v___x_59_; 
v___x_57_ = lean_string_utf8_get_fast(v_str_43_, v___x_46_);
v___x_58_ = 48;
v___x_59_ = lean_uint32_dec_le(v___x_58_, v___x_57_);
if (v___x_59_ == 0)
{
v___y_48_ = v___x_59_;
goto v___jp_47_;
}
else
{
uint32_t v___x_60_; uint8_t v___x_61_; 
v___x_60_ = 57;
v___x_61_ = lean_uint32_dec_le(v___x_57_, v___x_60_);
v___y_48_ = v___x_61_;
goto v___jp_47_;
}
}
else
{
lean_dec(v___x_46_);
return v_pos_42_;
}
v___jp_47_:
{
if (v___y_48_ == 0)
{
lean_dec(v___x_46_);
return v_pos_42_;
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_49_ = lean_string_utf8_next_fast(v_str_43_, v___x_46_);
v___x_50_ = lean_nat_sub(v___x_49_, v___x_46_);
lean_dec(v___x_46_);
v___x_51_ = lean_nat_add(v_pos_42_, v___x_50_);
lean_dec(v___x_50_);
v___x_52_ = lean_nat_dec_lt(v_pos_42_, v___x_51_);
if (v___x_52_ == 0)
{
lean_dec(v___x_51_);
return v_pos_42_;
}
else
{
lean_dec(v_pos_42_);
v_pos_42_ = v___x_51_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0___boxed(lean_object* v_s_62_, lean_object* v_pos_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(v_s_62_, v_pos_63_);
lean_dec_ref(v_s_62_);
return v_res_64_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(lean_object* v_s_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; uint8_t v___x_69_; 
v___x_66_ = lean_string_utf8_byte_size(v_s_65_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
v___x_69_ = lean_bool_not(v___x_68_);
if (v___x_69_ == 0)
{
lean_dec_ref(v_s_65_);
return v___x_69_;
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_70_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_70_, 0, v_s_65_);
lean_ctor_set(v___x_70_, 1, v___x_67_);
lean_ctor_set(v___x_70_, 2, v___x_66_);
v___x_71_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(v___x_70_, v___x_67_);
lean_dec_ref_known(v___x_70_, 3);
v___x_72_ = lean_nat_dec_eq(v___x_71_, v___x_66_);
lean_dec(v___x_71_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits___boxed(lean_object* v_s_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_s_73_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go(lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
switch(lean_obj_tag(v_a_76_))
{
case 0:
{
return v_a_77_;
}
case 1:
{
lean_object* v_pre_78_; lean_object* v_str_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_pre_78_ = lean_ctor_get(v_a_76_, 0);
v_str_79_ = lean_ctor_get(v_a_76_, 1);
lean_inc_ref(v_str_79_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v_str_79_);
v___x_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v_a_77_);
v_a_76_ = v_pre_78_;
v_a_77_ = v___x_81_;
goto _start;
}
default: 
{
lean_object* v_pre_83_; lean_object* v_i_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_pre_83_ = lean_ctor_get(v_a_76_, 0);
v_i_84_ = lean_ctor_get(v_a_76_, 1);
lean_inc(v_i_84_);
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v_i_84_);
v___x_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v_a_77_);
v_a_76_ = v_pre_83_;
v_a_77_ = v___x_86_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go___boxed(lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go(v_a_88_, v_a_89_);
lean_dec(v_a_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(lean_object* v_n_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_box(0);
v___x_93_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go(v_n_91_, v___x_92_);
v___x_94_ = lean_array_mk(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts___boxed(lean_object* v_n_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(v_n_95_);
lean_dec(v_n_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(lean_object* v_as_97_, size_t v_i_98_, size_t v_stop_99_, lean_object* v_b_100_){
_start:
{
lean_object* v___y_102_; uint8_t v___x_106_; 
v___x_106_ = lean_usize_dec_eq(v_i_98_, v_stop_99_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_array_uget_borrowed(v_as_97_, v_i_98_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_s_108_; lean_object* v___x_109_; 
v_s_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_s_108_);
v___x_109_ = l_Lean_Name_str___override(v_b_100_, v_s_108_);
v___y_102_ = v___x_109_;
goto v___jp_101_;
}
else
{
lean_object* v_n_110_; lean_object* v___x_111_; 
v_n_110_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_n_110_);
v___x_111_ = l_Lean_Name_num___override(v_b_100_, v_n_110_);
v___y_102_ = v___x_111_;
goto v___jp_101_;
}
}
else
{
return v_b_100_;
}
v___jp_101_:
{
size_t v___x_103_; size_t v___x_104_; 
v___x_103_ = ((size_t)1ULL);
v___x_104_ = lean_usize_add(v_i_98_, v___x_103_);
v_i_98_ = v___x_104_;
v_b_100_ = v___y_102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0___boxed(lean_object* v_as_112_, lean_object* v_i_113_, lean_object* v_stop_114_, lean_object* v_b_115_){
_start:
{
size_t v_i_boxed_116_; size_t v_stop_boxed_117_; lean_object* v_res_118_; 
v_i_boxed_116_ = lean_unbox_usize(v_i_113_);
lean_dec(v_i_113_);
v_stop_boxed_117_ = lean_unbox_usize(v_stop_114_);
lean_dec(v_stop_114_);
v_res_118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_as_112_, v_i_boxed_116_, v_stop_boxed_117_, v_b_115_);
lean_dec_ref(v_as_112_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(lean_object* v_parts_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_120_ = lean_box(0);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_array_get_size(v_parts_119_);
v___x_123_ = lean_nat_dec_lt(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
return v___x_120_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = lean_nat_dec_le(v___x_122_, v___x_122_);
if (v___x_124_ == 0)
{
if (v___x_123_ == 0)
{
return v___x_120_;
}
else
{
size_t v___x_125_; size_t v___x_126_; lean_object* v___x_127_; 
v___x_125_ = ((size_t)0ULL);
v___x_126_ = lean_usize_of_nat(v___x_122_);
v___x_127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_parts_119_, v___x_125_, v___x_126_, v___x_120_);
return v___x_127_;
}
}
else
{
size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; 
v___x_128_ = ((size_t)0ULL);
v___x_129_ = lean_usize_of_nat(v___x_122_);
v___x_130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_parts_119_, v___x_128_, v___x_129_, v___x_120_);
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName___boxed(lean_object* v_parts_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(v_parts_131_);
lean_dec_ref(v_parts_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(lean_object* v_comps_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_135_ = lean_array_get_size(v_comps_134_);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_nat_dec_eq(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = 1;
v___x_139_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(v_comps_134_);
v___x_140_ = l_Lean_Name_toString(v___x_139_, v___x_138_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___boxed(lean_object* v_comps_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_comps_142_);
lean_dec_ref(v_comps_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(lean_object* v_c_172_){
_start:
{
if (lean_obj_tag(v_c_172_) == 0)
{
lean_object* v_s_175_; uint8_t v___y_177_; uint8_t v___y_186_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_s_175_ = lean_ctor_get(v_c_172_, 0);
lean_inc_ref(v_s_175_);
lean_dec_ref_known(v_c_172_, 1);
v___x_199_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11));
v___x_200_ = lean_string_dec_eq(v_s_175_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12));
v___x_202_ = lean_string_dec_eq(v_s_175_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13));
v___x_204_ = lean_string_dec_eq(v_s_175_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14));
v___x_206_ = lean_string_dec_eq(v_s_175_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15));
v___x_208_ = lean_string_dec_eq(v_s_175_, v___x_207_);
v___y_186_ = v___x_208_;
goto v___jp_185_;
}
else
{
v___y_186_ = v___x_206_;
goto v___jp_185_;
}
}
else
{
lean_object* v___x_209_; 
lean_dec_ref(v_s_175_);
v___x_209_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__17));
return v___x_209_;
}
}
else
{
lean_object* v___x_210_; 
lean_dec_ref(v_s_175_);
v___x_210_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__19));
return v___x_210_;
}
}
else
{
lean_object* v___x_211_; 
lean_dec_ref(v_s_175_);
v___x_211_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__21));
return v___x_211_;
}
v___jp_176_:
{
if (v___y_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__2));
v___x_179_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_175_, v___x_178_);
if (lean_obj_tag(v___x_179_) == 0)
{
return v___x_179_;
}
else
{
lean_object* v_val_180_; uint8_t v___x_181_; 
v_val_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_val_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_181_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_box(0);
return v___x_182_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_183_;
}
}
}
else
{
lean_object* v___x_184_; 
lean_dec_ref(v_s_175_);
v___x_184_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_184_;
}
}
v___jp_185_:
{
if (v___y_186_ == 0)
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3));
v___x_188_ = lean_string_dec_eq(v_s_175_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4));
v___x_190_ = lean_string_dec_eq(v_s_175_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5));
v___x_192_ = lean_string_dec_eq(v_s_175_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6));
lean_inc_ref(v_s_175_);
v___x_194_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_175_, v___x_193_);
if (lean_obj_tag(v___x_194_) == 0)
{
v___y_177_ = v___x_192_;
goto v___jp_176_;
}
else
{
lean_object* v_val_195_; uint8_t v___x_196_; 
v_val_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_val_195_);
lean_dec_ref_known(v___x_194_, 1);
v___x_196_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_195_);
v___y_177_ = v___x_196_;
goto v___jp_176_;
}
}
else
{
lean_object* v___x_197_; 
lean_dec_ref(v_s_175_);
v___x_197_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8));
return v___x_197_;
}
}
else
{
lean_object* v___x_198_; 
lean_dec_ref(v_s_175_);
v___x_198_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10));
return v___x_198_;
}
}
else
{
lean_dec_ref(v_s_175_);
goto v___jp_173_;
}
}
else
{
lean_dec_ref(v_s_175_);
goto v___jp_173_;
}
}
}
else
{
lean_object* v___x_212_; 
lean_dec_ref(v_c_172_);
v___x_212_ = lean_box(0);
return v___x_212_;
}
v___jp_173_:
{
lean_object* v___x_174_; 
v___x_174_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_174_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(lean_object* v_c_214_){
_start:
{
if (lean_obj_tag(v_c_214_) == 0)
{
lean_object* v_s_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_s_215_ = lean_ctor_get(v_c_214_, 0);
lean_inc_ref(v_s_215_);
lean_dec_ref_known(v_c_214_, 1);
v___x_216_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___closed__0));
v___x_217_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_215_, v___x_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
uint8_t v___x_218_; 
v___x_218_ = 0;
return v___x_218_;
}
else
{
lean_object* v_val_219_; uint8_t v___x_220_; 
v_val_219_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_val_219_);
lean_dec_ref_known(v___x_217_, 1);
v___x_220_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_219_);
return v___x_220_;
}
}
else
{
uint8_t v___x_221_; 
lean_dec_ref(v_c_214_);
v___x_221_ = 0;
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___boxed(lean_object* v_c_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(v_c_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
if (lean_obj_tag(v_x_226_) == 0)
{
uint8_t v___x_227_; 
v___x_227_ = 1;
return v___x_227_;
}
else
{
uint8_t v___x_228_; 
v___x_228_ = 0;
return v___x_228_;
}
}
else
{
if (lean_obj_tag(v_x_226_) == 0)
{
uint8_t v___x_229_; 
v___x_229_ = 0;
return v___x_229_;
}
else
{
lean_object* v_val_230_; lean_object* v_val_231_; uint8_t v___x_232_; 
v_val_230_ = lean_ctor_get(v_x_225_, 0);
v_val_231_ = lean_ctor_get(v_x_226_, 0);
v___x_232_ = l_Lean_instBEqNamePart_beq(v_val_230_, v_val_231_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0___boxed(lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
uint8_t v_res_235_; lean_object* v_r_236_; 
v_res_235_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v_x_233_, v_x_234_);
lean_dec(v_x_234_);
lean_dec(v_x_233_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(lean_object* v_stop_244_, lean_object* v_start_245_, uint8_t v___y_246_, lean_object* v_comps_247_, lean_object* v_range_248_, lean_object* v_b_249_, lean_object* v_i_250_){
_start:
{
lean_object* v_stop_251_; lean_object* v_step_252_; uint8_t v___x_253_; 
v_stop_251_ = lean_ctor_get(v_range_248_, 1);
v_step_252_ = lean_ctor_get(v_range_248_, 2);
v___x_253_ = lean_nat_dec_lt(v_i_250_, v_stop_251_);
if (v___x_253_ == 0)
{
lean_dec(v_i_250_);
lean_dec(v_start_245_);
lean_inc_ref(v_b_249_);
return v_b_249_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___y_259_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_254_ = lean_box(0);
v___x_255_ = lean_box(0);
v___x_256_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0));
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_array_get_size(v_comps_247_);
v___x_275_ = lean_nat_dec_lt(v_i_250_, v___x_274_);
if (v___x_275_ == 0)
{
v___y_259_ = v___x_254_;
goto v___jp_258_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_array_fget_borrowed(v_comps_247_, v_i_250_);
lean_inc(v___x_276_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
v___y_259_ = v___x_277_;
goto v___jp_258_;
}
v___jp_258_:
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2));
v___x_261_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_259_, v___x_260_);
lean_dec(v___y_259_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
v___x_262_ = lean_nat_add(v_i_250_, v_step_252_);
lean_dec(v_i_250_);
v_b_249_ = v___x_256_;
v_i_250_ = v___x_262_;
goto _start;
}
else
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_nat_add(v_i_250_, v___x_257_);
lean_dec(v_i_250_);
v___x_265_ = lean_nat_dec_lt(v___x_264_, v_stop_244_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v___x_264_);
v___x_266_ = lean_box(v___x_265_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v_start_245_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_255_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec(v_start_245_);
v___x_270_ = lean_box(v___y_246_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_264_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_255_);
return v___x_273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___boxed(lean_object* v_stop_278_, lean_object* v_start_279_, lean_object* v___y_280_, lean_object* v_comps_281_, lean_object* v_range_282_, lean_object* v_b_283_, lean_object* v_i_284_){
_start:
{
uint8_t v___y_946__boxed_285_; lean_object* v_res_286_; 
v___y_946__boxed_285_ = lean_unbox(v___y_280_);
v_res_286_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_278_, v_start_279_, v___y_946__boxed_285_, v_comps_281_, v_range_282_, v_b_283_, v_i_284_);
lean_dec_ref(v_b_283_);
lean_dec_ref(v_range_282_);
lean_dec_ref(v_comps_281_);
lean_dec(v_stop_278_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(lean_object* v_comps_292_, lean_object* v_start_293_, lean_object* v_stop_294_){
_start:
{
uint8_t v___y_296_; lean_object* v___y_317_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_320_ = lean_unsigned_to_nat(3u);
v___x_321_ = lean_nat_sub(v_stop_294_, v_start_293_);
v___x_322_ = lean_nat_dec_le(v___x_320_, v___x_321_);
lean_dec(v___x_321_);
if (v___x_322_ == 0)
{
v___y_296_ = v___x_322_;
goto v___jp_295_;
}
else
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_array_get_size(v_comps_292_);
v___x_324_ = lean_nat_dec_lt(v_start_293_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
v___x_325_ = lean_box(0);
v___y_317_ = v___x_325_;
goto v___jp_316_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_array_fget_borrowed(v_comps_292_, v_start_293_);
lean_inc(v___x_326_);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___y_317_ = v___x_327_;
goto v___jp_316_;
}
}
v___jp_295_:
{
if (v___y_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v_stop_294_);
v___x_297_ = lean_box(v___y_296_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_start_293_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_fst_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_314_; 
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_add(v_start_293_, v___x_299_);
lean_inc(v_stop_294_);
lean_inc(v___x_300_);
v___x_301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_stop_294_);
lean_ctor_set(v___x_301_, 2, v___x_299_);
v___x_302_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0));
lean_inc(v_start_293_);
v___x_303_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_294_, v_start_293_, v___y_296_, v_comps_292_, v___x_301_, v___x_302_, v___x_300_);
lean_dec_ref_known(v___x_301_, 3);
lean_dec(v_stop_294_);
v_fst_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; 
v_unused_315_ = lean_ctor_get(v___x_303_, 1);
lean_dec(v_unused_315_);
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_314_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_fst_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_314_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
if (lean_obj_tag(v_fst_304_) == 0)
{
uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_308_ = 0;
v___x_309_ = lean_box(v___x_308_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v___x_309_);
lean_ctor_set(v___x_306_, 0, v_start_293_);
v___x_311_ = v___x_306_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_start_293_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
else
{
lean_object* v_val_313_; 
lean_del_object(v___x_306_);
lean_dec(v_start_293_);
v_val_313_ = lean_ctor_get(v_fst_304_, 0);
lean_inc(v_val_313_);
lean_dec_ref_known(v_fst_304_, 1);
return v_val_313_;
}
}
}
}
v___jp_316_:
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2));
v___x_319_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_317_, v___x_318_);
lean_dec(v___y_317_);
v___y_296_ = v___x_319_;
goto v___jp_295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___boxed(lean_object* v_comps_328_, lean_object* v_start_329_, lean_object* v_stop_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_comps_328_, v_start_329_, v_stop_330_);
lean_dec_ref(v_comps_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(lean_object* v_stop_332_, lean_object* v_start_333_, uint8_t v___y_334_, lean_object* v_comps_335_, lean_object* v_range_336_, lean_object* v_b_337_, lean_object* v_i_338_, lean_object* v_hs_339_, lean_object* v_hl_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_332_, v_start_333_, v___y_334_, v_comps_335_, v_range_336_, v_b_337_, v_i_338_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___boxed(lean_object* v_stop_342_, lean_object* v_start_343_, lean_object* v___y_344_, lean_object* v_comps_345_, lean_object* v_range_346_, lean_object* v_b_347_, lean_object* v_i_348_, lean_object* v_hs_349_, lean_object* v_hl_350_){
_start:
{
uint8_t v___y_1088__boxed_351_; lean_object* v_res_352_; 
v___y_1088__boxed_351_ = lean_unbox(v___y_344_);
v_res_352_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(v_stop_342_, v_start_343_, v___y_1088__boxed_351_, v_comps_345_, v_range_346_, v_b_347_, v_i_348_, v_hs_349_, v_hl_350_);
lean_dec_ref(v_b_347_);
lean_dec_ref(v_range_346_);
lean_dec_ref(v_comps_345_);
lean_dec(v_stop_342_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(lean_object* v___x_353_, lean_object* v_comps_354_, lean_object* v_range_355_, lean_object* v_b_356_, lean_object* v_i_357_){
_start:
{
lean_object* v_stop_358_; lean_object* v_step_359_; uint8_t v___x_360_; 
v_stop_358_ = lean_ctor_get(v_range_355_, 1);
v_step_359_ = lean_ctor_get(v_range_355_, 2);
v___x_360_ = lean_nat_dec_lt(v_i_357_, v_stop_358_);
if (v___x_360_ == 0)
{
lean_dec(v_i_357_);
lean_inc(v_b_356_);
return v_b_356_;
}
else
{
lean_object* v___x_361_; uint8_t v___y_363_; lean_object* v___y_368_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_373_ = lean_array_get_size(v_comps_354_);
v___x_374_ = lean_nat_dec_lt(v_i_357_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; 
v___x_375_ = lean_box(0);
v___y_368_ = v___x_375_;
goto v___jp_367_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_array_fget_borrowed(v_comps_354_, v_i_357_);
lean_inc(v___x_376_);
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
v___y_368_ = v___x_377_;
goto v___jp_367_;
}
v___jp_362_:
{
if (v___y_363_ == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_nat_add(v_i_357_, v_step_359_);
lean_dec(v_i_357_);
v_i_357_ = v___x_364_;
goto _start;
}
else
{
lean_object* v___x_366_; 
v___x_366_ = lean_nat_add(v_i_357_, v___x_361_);
lean_dec(v_i_357_);
return v___x_366_;
}
}
v___jp_367_:
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2));
v___x_370_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_368_, v___x_369_);
lean_dec(v___y_368_);
if (v___x_370_ == 0)
{
v___y_363_ = v___x_370_;
goto v___jp_362_;
}
else
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = lean_nat_add(v_i_357_, v___x_361_);
v___x_372_ = lean_nat_dec_lt(v___x_371_, v___x_353_);
lean_dec(v___x_371_);
v___y_363_ = v___x_372_;
goto v___jp_362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg___boxed(lean_object* v___x_378_, lean_object* v_comps_379_, lean_object* v_range_380_, lean_object* v_b_381_, lean_object* v_i_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_378_, v_comps_379_, v_range_380_, v_b_381_, v_i_382_);
lean_dec(v_b_381_);
lean_dec_ref(v_range_380_);
lean_dec_ref(v_comps_379_);
lean_dec(v___x_378_);
return v_res_383_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(lean_object* v_a_384_, lean_object* v_as_385_, size_t v_i_386_, size_t v_stop_387_){
_start:
{
uint8_t v___x_388_; 
v___x_388_ = lean_usize_dec_eq(v_i_386_, v_stop_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = lean_array_uget_borrowed(v_as_385_, v_i_386_);
v___x_390_ = lean_string_dec_eq(v_a_384_, v___x_389_);
if (v___x_390_ == 0)
{
size_t v___x_391_; size_t v___x_392_; 
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_386_, v___x_391_);
v_i_386_ = v___x_392_;
goto _start;
}
else
{
return v___x_390_;
}
}
else
{
uint8_t v___x_394_; 
v___x_394_ = 0;
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0___boxed(lean_object* v_a_395_, lean_object* v_as_396_, lean_object* v_i_397_, lean_object* v_stop_398_){
_start:
{
size_t v_i_boxed_399_; size_t v_stop_boxed_400_; uint8_t v_res_401_; lean_object* v_r_402_; 
v_i_boxed_399_ = lean_unbox_usize(v_i_397_);
lean_dec(v_i_397_);
v_stop_boxed_400_ = lean_unbox_usize(v_stop_398_);
lean_dec(v_stop_398_);
v_res_401_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_395_, v_as_396_, v_i_boxed_399_, v_stop_boxed_400_);
lean_dec_ref(v_as_396_);
lean_dec_ref(v_a_395_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(lean_object* v_as_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_array_get_size(v_as_403_);
v___x_407_ = lean_nat_dec_lt(v___x_405_, v___x_406_);
if (v___x_407_ == 0)
{
return v___x_407_;
}
else
{
if (v___x_407_ == 0)
{
return v___x_407_;
}
else
{
size_t v___x_408_; size_t v___x_409_; uint8_t v___x_410_; 
v___x_408_ = ((size_t)0ULL);
v___x_409_ = lean_usize_of_nat(v___x_406_);
v___x_410_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_404_, v_as_403_, v___x_408_, v___x_409_);
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0___boxed(lean_object* v_as_411_, lean_object* v_a_412_){
_start:
{
uint8_t v_res_413_; lean_object* v_r_414_; 
v_res_413_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_as_411_, v_a_412_);
lean_dec_ref(v_a_412_);
lean_dec_ref(v_as_411_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(lean_object* v_comps_415_, lean_object* v_range_416_, lean_object* v_b_417_, lean_object* v_i_418_){
_start:
{
lean_object* v_stop_419_; lean_object* v_step_420_; lean_object* v_a_422_; uint8_t v___x_425_; 
v_stop_419_ = lean_ctor_get(v_range_416_, 1);
v_step_420_ = lean_ctor_get(v_range_416_, 2);
v___x_425_ = lean_nat_dec_lt(v_i_418_, v_stop_419_);
if (v___x_425_ == 0)
{
lean_dec(v_i_418_);
return v_b_417_;
}
else
{
lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_452_; 
v_fst_426_ = lean_ctor_get(v_b_417_, 0);
v_snd_427_ = lean_ctor_get(v_b_417_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v_b_417_);
if (v_isSharedCheck_452_ == 0)
{
v___x_429_ = v_b_417_;
v_isShared_430_ = v_isSharedCheck_452_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snd_427_);
lean_inc(v_fst_426_);
lean_dec(v_b_417_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_452_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = l_Lean_instInhabitedNamePart_default;
v___x_432_ = lean_array_get_borrowed(v___x_431_, v_comps_415_, v_i_418_);
lean_inc(v___x_432_);
v___x_433_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_432_);
if (lean_obj_tag(v___x_433_) == 0)
{
uint8_t v___x_434_; 
lean_inc(v___x_432_);
v___x_434_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(v___x_432_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_437_; 
lean_inc(v___x_432_);
v___x_435_ = lean_array_push(v_fst_426_, v___x_432_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_435_);
v___x_437_ = v___x_429_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_snd_427_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
v_a_422_ = v___x_437_;
goto v___jp_421_;
}
}
else
{
lean_object* v___x_440_; 
if (v_isShared_430_ == 0)
{
v___x_440_ = v___x_429_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_fst_426_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_snd_427_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
v_a_422_ = v___x_440_;
goto v___jp_421_;
}
}
}
else
{
lean_object* v_val_442_; uint8_t v___x_443_; uint8_t v___x_444_; 
v_val_442_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_val_442_);
lean_dec_ref_known(v___x_433_, 1);
v___x_443_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_snd_427_, v_val_442_);
v___x_444_ = lean_bool_not(v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_446_; 
lean_dec(v_val_442_);
if (v_isShared_430_ == 0)
{
v___x_446_ = v___x_429_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_fst_426_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_snd_427_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
v_a_422_ = v___x_446_;
goto v___jp_421_;
}
}
else
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_array_push(v_snd_427_, v_val_442_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_448_);
v___x_450_ = v___x_429_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_fst_426_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
v_a_422_ = v___x_450_;
goto v___jp_421_;
}
}
}
}
}
v___jp_421_:
{
lean_object* v___x_423_; 
v___x_423_ = lean_nat_add(v_i_418_, v_step_420_);
lean_dec(v_i_418_);
v_b_417_ = v_a_422_;
v_i_418_ = v___x_423_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg___boxed(lean_object* v_comps_453_, lean_object* v_range_454_, lean_object* v_b_455_, lean_object* v_i_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_453_, v_range_454_, v_b_455_, v_i_456_);
lean_dec_ref(v_range_454_);
lean_dec_ref(v_comps_453_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(lean_object* v_comps_462_){
_start:
{
lean_object* v_begin___464_; lean_object* v_begin___480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___y_484_; lean_object* v___y_489_; uint8_t v___x_492_; 
v_begin___480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_unsigned_to_nat(3u);
v___x_482_ = lean_array_get_size(v_comps_462_);
v___x_492_ = lean_nat_dec_le(v___x_481_, v___x_482_);
if (v___x_492_ == 0)
{
v___y_484_ = v___x_492_;
goto v___jp_483_;
}
else
{
uint8_t v___x_493_; 
v___x_493_ = lean_nat_dec_lt(v_begin___480_, v___x_482_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
v___x_494_ = lean_box(0);
v___y_489_ = v___x_494_;
goto v___jp_488_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_array_fget_borrowed(v_comps_462_, v_begin___480_);
lean_inc(v___x_495_);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
v___y_489_ = v___x_496_;
goto v___jp_488_;
}
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_479_; 
v___x_465_ = lean_array_get_size(v_comps_462_);
v___x_466_ = lean_unsigned_to_nat(1u);
lean_inc(v_begin___464_);
v___x_467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_467_, 0, v_begin___464_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
lean_ctor_set(v___x_467_, 2, v___x_466_);
v___x_468_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1));
v___x_469_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_462_, v___x_467_, v___x_468_, v_begin___464_);
lean_dec_ref_known(v___x_467_, 3);
v_fst_470_ = lean_ctor_get(v___x_469_, 0);
v_snd_471_ = lean_ctor_get(v___x_469_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_479_ == 0)
{
v___x_473_ = v___x_469_;
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_snd_471_);
lean_inc(v_fst_470_);
lean_dec(v___x_469_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_479_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_475_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_fst_470_);
lean_dec(v_fst_470_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_475_);
v___x_477_ = v___x_473_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_snd_471_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
v___jp_483_:
{
if (v___y_484_ == 0)
{
v_begin___464_ = v_begin___480_;
goto v___jp_463_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_482_);
lean_ctor_set(v___x_486_, 2, v___x_485_);
v___x_487_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_482_, v_comps_462_, v___x_486_, v_begin___480_, v___x_485_);
lean_dec_ref_known(v___x_486_, 3);
v_begin___464_ = v___x_487_;
goto v___jp_463_;
}
}
v___jp_488_:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2));
v___x_491_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_489_, v___x_490_);
lean_dec(v___y_489_);
v___y_484_ = v___x_491_;
goto v___jp_483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___boxed(lean_object* v_comps_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(v_comps_497_);
lean_dec_ref(v_comps_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1(lean_object* v_comps_499_, lean_object* v_range_500_, lean_object* v_b_501_, lean_object* v_i_502_, lean_object* v_hs_503_, lean_object* v_hl_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_499_, v_range_500_, v_b_501_, v_i_502_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___boxed(lean_object* v_comps_506_, lean_object* v_range_507_, lean_object* v_b_508_, lean_object* v_i_509_, lean_object* v_hs_510_, lean_object* v_hl_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1(v_comps_506_, v_range_507_, v_b_508_, v_i_509_, v_hs_510_, v_hl_511_);
lean_dec_ref(v_range_507_);
lean_dec_ref(v_comps_506_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2(lean_object* v___x_513_, lean_object* v_comps_514_, lean_object* v_range_515_, lean_object* v_b_516_, lean_object* v_i_517_, lean_object* v_hs_518_, lean_object* v_hl_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_513_, v_comps_514_, v_range_515_, v_b_516_, v_i_517_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___boxed(lean_object* v___x_521_, lean_object* v_comps_522_, lean_object* v_range_523_, lean_object* v_b_524_, lean_object* v_i_525_, lean_object* v_hs_526_, lean_object* v_hl_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2(v___x_521_, v_comps_522_, v_range_523_, v_b_524_, v_i_525_, v_hs_526_, v_hl_527_);
lean_dec(v_b_524_);
lean_dec_ref(v_range_523_);
lean_dec_ref(v_comps_522_);
lean_dec(v___x_521_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(lean_object* v___x_532_, lean_object* v_range_533_, lean_object* v_b_534_, lean_object* v_i_535_){
_start:
{
lean_object* v_stop_536_; lean_object* v_step_537_; uint8_t v___x_538_; 
v_stop_536_ = lean_ctor_get(v_range_533_, 1);
v_step_537_ = lean_ctor_get(v_range_533_, 2);
v___x_538_ = lean_nat_dec_lt(v_i_535_, v_stop_536_);
if (v___x_538_ == 0)
{
lean_dec(v_i_535_);
lean_inc(v_b_534_);
return v_b_534_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_539_ = l_Lean_instInhabitedNamePart_default;
v___x_540_ = lean_array_get_borrowed(v___x_539_, v___x_532_, v_i_535_);
v___x_541_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1));
v___x_542_ = l_Lean_instBEqNamePart_beq(v___x_540_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; 
v___x_543_ = lean_nat_add(v_i_535_, v_step_537_);
lean_dec(v_i_535_);
v_i_535_ = v___x_543_;
goto _start;
}
else
{
lean_object* v___x_545_; 
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v_i_535_);
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___boxed(lean_object* v___x_546_, lean_object* v_range_547_, lean_object* v_b_548_, lean_object* v_i_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_546_, v_range_547_, v_b_548_, v_i_549_);
lean_dec(v_b_548_);
lean_dec_ref(v_range_547_);
lean_dec_ref(v___x_546_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(lean_object* v_as_551_, size_t v_sz_552_, size_t v_i_553_, lean_object* v_b_554_){
_start:
{
lean_object* v_a_556_; uint8_t v___x_560_; 
v___x_560_ = lean_usize_dec_lt(v_i_553_, v_sz_552_);
if (v___x_560_ == 0)
{
return v_b_554_;
}
else
{
lean_object* v_a_561_; lean_object* v___x_562_; lean_object* v_name_565_; lean_object* v_flags_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; uint8_t v___x_570_; 
v_a_561_ = lean_array_uget_borrowed(v_as_551_, v_i_553_);
v___x_562_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(v_a_561_);
v_name_565_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_name_565_);
v_flags_566_ = lean_ctor_get(v___x_562_, 1);
lean_inc_ref(v_flags_566_);
v___x_567_ = lean_string_utf8_byte_size(v_name_565_);
lean_dec_ref(v_name_565_);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_nat_dec_eq(v___x_567_, v___x_568_);
v___x_570_ = lean_bool_not(v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; uint8_t v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_array_get_size(v_flags_566_);
lean_dec_ref(v_flags_566_);
v___x_572_ = lean_nat_dec_eq(v___x_571_, v___x_568_);
v___x_573_ = lean_bool_not(v___x_572_);
if (v___x_573_ == 0)
{
lean_dec_ref(v___x_562_);
v_a_556_ = v_b_554_;
goto v___jp_555_;
}
else
{
goto v___jp_563_;
}
}
else
{
lean_dec_ref(v_flags_566_);
goto v___jp_563_;
}
v___jp_563_:
{
lean_object* v___x_564_; 
v___x_564_ = lean_array_push(v_b_554_, v___x_562_);
v_a_556_ = v___x_564_;
goto v___jp_555_;
}
}
v___jp_555_:
{
size_t v___x_557_; size_t v___x_558_; 
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_i_553_, v___x_557_);
v_i_553_ = v___x_558_;
v_b_554_ = v_a_556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5___boxed(lean_object* v_as_574_, lean_object* v_sz_575_, lean_object* v_i_576_, lean_object* v_b_577_){
_start:
{
size_t v_sz_boxed_578_; size_t v_i_boxed_579_; lean_object* v_res_580_; 
v_sz_boxed_578_ = lean_unbox_usize(v_sz_575_);
lean_dec(v_sz_575_);
v_i_boxed_579_ = lean_unbox_usize(v_i_576_);
lean_dec(v_i_576_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v_as_574_, v_sz_boxed_578_, v_i_boxed_579_, v_b_577_);
lean_dec_ref(v_as_574_);
return v_res_580_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0));
v___x_583_ = lean_string_utf8_byte_size(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(lean_object* v___x_584_, lean_object* v_range_585_, lean_object* v_b_586_, lean_object* v_i_587_){
_start:
{
lean_object* v_stop_588_; lean_object* v_step_589_; lean_object* v_a_591_; uint8_t v___x_594_; 
v_stop_588_ = lean_ctor_get(v_range_585_, 1);
v_step_589_ = lean_ctor_get(v_range_585_, 2);
v___x_594_ = lean_nat_dec_lt(v_i_587_, v_stop_588_);
if (v___x_594_ == 0)
{
lean_dec(v_i_587_);
lean_inc_ref(v_b_586_);
return v_b_586_;
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = l_Lean_instInhabitedNamePart_default;
v___x_596_ = lean_array_get_borrowed(v___x_595_, v_b_586_, v_i_587_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_s_597_; lean_object* v___x_598_; uint8_t v___y_600_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_s_597_ = lean_ctor_get(v___x_596_, 0);
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_602_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0));
v___x_603_ = lean_string_utf8_byte_size(v_s_597_);
v___x_604_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1);
v___x_605_ = lean_nat_dec_le(v___x_604_, v___x_603_);
if (v___x_605_ == 0)
{
uint8_t v___x_606_; 
v___x_606_ = lean_nat_dec_eq(v___x_584_, v___x_598_);
v___y_600_ = v___x_606_;
goto v___jp_599_;
}
else
{
uint8_t v___x_607_; 
v___x_607_ = lean_string_memcmp(v_s_597_, v___x_602_, v___x_598_, v___x_598_, v___x_604_);
v___y_600_ = v___x_607_;
goto v___jp_599_;
}
v___jp_599_:
{
if (v___y_600_ == 0)
{
v_a_591_ = v_b_586_;
goto v___jp_590_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = l_Array_extract___redArg(v_b_586_, v___x_598_, v_i_587_);
return v___x_601_;
}
}
}
else
{
v_a_591_ = v_b_586_;
goto v___jp_590_;
}
}
v___jp_590_:
{
lean_object* v___x_592_; 
v___x_592_ = lean_nat_add(v_i_587_, v_step_589_);
lean_dec(v_i_587_);
v_b_586_ = v_a_591_;
v_i_587_ = v___x_592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___boxed(lean_object* v___x_608_, lean_object* v_range_609_, lean_object* v_b_610_, lean_object* v_i_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_608_, v_range_609_, v_b_610_, v_i_611_);
lean_dec_ref(v_b_610_);
lean_dec_ref(v_range_609_);
lean_dec(v___x_608_);
return v_res_612_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0));
v___x_617_ = lean_string_utf8_byte_size(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(lean_object* v___x_620_, lean_object* v___x_621_, lean_object* v_range_622_, lean_object* v_b_623_, lean_object* v_i_624_){
_start:
{
lean_object* v_stop_625_; lean_object* v_step_626_; lean_object* v_a_628_; uint8_t v___x_631_; 
v_stop_625_ = lean_ctor_get(v_range_622_, 1);
v_step_626_ = lean_ctor_get(v_range_622_, 2);
v___x_631_ = lean_nat_dec_lt(v_i_624_, v_stop_625_);
if (v___x_631_ == 0)
{
lean_dec(v_i_624_);
return v_b_623_;
}
else
{
lean_object* v_snd_632_; lean_object* v_snd_633_; lean_object* v_fst_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_749_; 
v_snd_632_ = lean_ctor_get(v_b_623_, 1);
lean_inc(v_snd_632_);
v_snd_633_ = lean_ctor_get(v_snd_632_, 1);
lean_inc(v_snd_633_);
v_fst_634_ = lean_ctor_get(v_b_623_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v_b_623_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v_b_623_, 1);
lean_dec(v_unused_750_);
v___x_636_ = v_b_623_;
v_isShared_637_ = v_isSharedCheck_749_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_fst_634_);
lean_dec(v_b_623_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_749_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_fst_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_747_; 
v_fst_638_ = lean_ctor_get(v_snd_632_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v_snd_632_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v_snd_632_, 1);
lean_dec(v_unused_748_);
v___x_640_ = v_snd_632_;
v_isShared_641_ = v_isSharedCheck_747_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_fst_638_);
lean_dec(v_snd_632_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_747_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_fst_642_; lean_object* v_snd_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_746_; 
v_fst_642_ = lean_ctor_get(v_snd_633_, 0);
v_snd_643_ = lean_ctor_get(v_snd_633_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_snd_633_);
if (v_isSharedCheck_746_ == 0)
{
v___x_645_ = v_snd_633_;
v_isShared_646_ = v_isSharedCheck_746_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_snd_643_);
lean_inc(v_fst_642_);
lean_dec(v_snd_633_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_746_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; uint8_t v___x_648_; uint8_t v___x_649_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_nat_dec_eq(v___x_621_, v___x_647_);
v___x_649_ = lean_unbox(v_snd_643_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_650_ = l_Lean_instInhabitedNamePart_default;
v___x_651_ = lean_array_get_borrowed(v___x_650_, v___x_620_, v_i_624_);
v___x_652_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1));
v___x_653_ = l_Lean_instBEqNamePart_beq(v___x_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; uint8_t v___y_656_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v_cont_707_; lean_object* v_entries_709_; lean_object* v_currentCtx_710_; 
v___x_654_ = lean_box(0);
v___x_705_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0));
v___x_706_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1));
v_cont_707_ = l_Lean_instBEqNamePart_beq(v___x_651_, v___x_706_);
if (v_cont_707_ == 0)
{
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_s_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v_s_715_ = lean_ctor_get(v___x_651_, 0);
v___x_716_ = lean_string_utf8_byte_size(v_s_715_);
v___x_717_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2);
v___x_718_ = lean_nat_dec_le(v___x_717_, v___x_716_);
if (v___x_718_ == 0)
{
v___y_656_ = v_cont_707_;
goto v___jp_655_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = lean_string_memcmp(v_s_715_, v___x_705_, v___x_647_, v___x_647_, v___x_717_);
v___y_656_ = v___x_719_;
goto v___jp_655_;
}
}
else
{
v___y_656_ = v___x_648_;
goto v___jp_655_;
}
}
else
{
lean_del_object(v___x_645_);
lean_dec(v_snd_643_);
lean_del_object(v___x_640_);
lean_del_object(v___x_636_);
if (lean_obj_tag(v_fst_638_) == 1)
{
lean_object* v_val_720_; lean_object* v___x_721_; 
v_val_720_ = lean_ctor_get(v_fst_638_, 0);
lean_inc(v_val_720_);
lean_dec_ref_known(v_fst_638_, 1);
v___x_721_ = lean_array_push(v_fst_634_, v_val_720_);
v_entries_709_ = v___x_721_;
v_currentCtx_710_ = v___x_654_;
goto v___jp_708_;
}
else
{
v_entries_709_ = v_fst_634_;
v_currentCtx_710_ = v_fst_638_;
goto v___jp_708_;
}
}
v___jp_655_:
{
if (v___y_656_ == 0)
{
if (lean_obj_tag(v_fst_638_) == 0)
{
lean_object* v___x_657_; lean_object* v___x_659_; 
lean_inc(v___x_651_);
v___x_657_ = lean_array_push(v_fst_642_, v___x_651_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_657_);
v___x_659_ = v___x_645_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_snd_643_);
v___x_659_ = v_reuseFailAlloc_666_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_661_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_659_);
v___x_661_ = v___x_640_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_fst_638_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_659_);
v___x_661_ = v_reuseFailAlloc_665_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_661_);
v___x_663_ = v___x_636_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_fst_634_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
v_a_628_ = v___x_663_;
goto v___jp_627_;
}
}
}
}
else
{
lean_object* v_val_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_684_; 
v_val_667_ = lean_ctor_get(v_fst_638_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v_fst_638_);
if (v_isSharedCheck_684_ == 0)
{
v___x_669_ = v_fst_638_;
v_isShared_670_ = v_isSharedCheck_684_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_val_667_);
lean_dec(v_fst_638_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_684_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
lean_inc(v___x_651_);
v___x_671_ = lean_array_push(v_val_667_, v___x_651_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_683_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_675_; 
if (v_isShared_646_ == 0)
{
v___x_675_ = v___x_645_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_fst_642_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_snd_643_);
v___x_675_ = v_reuseFailAlloc_682_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_675_);
lean_ctor_set(v___x_640_, 0, v___x_673_);
v___x_677_ = v___x_640_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_675_);
v___x_677_ = v_reuseFailAlloc_681_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_679_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_677_);
v___x_679_ = v___x_636_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_fst_634_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
v_a_628_ = v___x_679_;
goto v___jp_627_;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_fst_638_) == 1)
{
lean_object* v_val_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v_val_685_ = lean_ctor_get(v_fst_638_, 0);
lean_inc(v_val_685_);
lean_dec_ref_known(v_fst_638_, 1);
v___x_686_ = lean_array_push(v_fst_634_, v_val_685_);
if (v_isShared_646_ == 0)
{
v___x_688_ = v___x_645_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_fst_642_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_snd_643_);
v___x_688_ = v_reuseFailAlloc_695_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_690_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_688_);
lean_ctor_set(v___x_640_, 0, v___x_654_);
v___x_690_ = v___x_640_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_690_);
lean_ctor_set(v___x_636_, 0, v___x_686_);
v___x_692_ = v___x_636_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
v_a_628_ = v___x_692_;
goto v___jp_627_;
}
}
}
}
else
{
lean_object* v___x_697_; 
if (v_isShared_646_ == 0)
{
v___x_697_ = v___x_645_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_fst_642_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_snd_643_);
v___x_697_ = v_reuseFailAlloc_704_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_697_);
v___x_699_ = v___x_640_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_fst_638_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_697_);
v___x_699_ = v_reuseFailAlloc_703_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_699_);
v___x_701_ = v___x_636_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_fst_634_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
v_a_628_ = v___x_701_;
goto v___jp_627_;
}
}
}
}
}
}
v___jp_708_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_711_ = lean_box(v_cont_707_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_fst_642_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_currentCtx_710_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v_entries_709_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v_a_628_ = v___x_714_;
goto v___jp_627_;
}
}
else
{
lean_object* v_entries_723_; 
if (lean_obj_tag(v_fst_638_) == 1)
{
lean_object* v_val_734_; lean_object* v___x_735_; 
v_val_734_ = lean_ctor_get(v_fst_638_, 0);
lean_inc(v_val_734_);
lean_dec_ref_known(v_fst_638_, 1);
v___x_735_ = lean_array_push(v_fst_634_, v_val_734_);
v_entries_723_ = v___x_735_;
goto v___jp_722_;
}
else
{
lean_dec(v_fst_638_);
v_entries_723_ = v_fst_634_;
goto v___jp_722_;
}
v___jp_722_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__3));
if (v_isShared_646_ == 0)
{
v___x_726_ = v___x_645_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_fst_642_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_snd_643_);
v___x_726_ = v_reuseFailAlloc_733_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_726_);
lean_ctor_set(v___x_640_, 0, v___x_724_);
v___x_728_ = v___x_640_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_728_);
lean_ctor_set(v___x_636_, 0, v_entries_723_);
v___x_730_ = v___x_636_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_entries_723_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
v_a_628_ = v___x_730_;
goto v___jp_627_;
}
}
}
}
}
}
else
{
lean_object* v___x_736_; lean_object* v___x_738_; 
lean_dec(v_snd_643_);
v___x_736_ = lean_box(v___x_648_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_736_);
v___x_738_ = v___x_645_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_fst_642_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_736_);
v___x_738_ = v_reuseFailAlloc_745_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_740_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_738_);
v___x_740_ = v___x_640_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_fst_638_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___x_738_);
v___x_740_ = v_reuseFailAlloc_744_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_742_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_740_);
v___x_742_ = v___x_636_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_fst_634_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
v_a_628_ = v___x_742_;
goto v___jp_627_;
}
}
}
}
}
}
}
}
v___jp_627_:
{
lean_object* v___x_629_; 
v___x_629_ = lean_nat_add(v_i_624_, v_step_626_);
lean_dec(v_i_624_);
v_b_623_ = v_a_628_;
v_i_624_ = v___x_629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___boxed(lean_object* v___x_751_, lean_object* v___x_752_, lean_object* v_range_753_, lean_object* v_b_754_, lean_object* v_i_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_751_, v___x_752_, v_range_753_, v_b_754_, v_i_755_);
lean_dec_ref(v_range_753_);
lean_dec(v___x_752_);
lean_dec_ref(v___x_751_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(lean_object* v___x_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_snd_759_; lean_object* v_fst_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_818_; 
v_snd_759_ = lean_ctor_get(v_a_758_, 1);
v_fst_760_ = lean_ctor_get(v_a_758_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v_a_758_);
if (v_isSharedCheck_818_ == 0)
{
v___x_762_ = v_a_758_;
v_isShared_763_ = v_isSharedCheck_818_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_snd_759_);
lean_inc(v_fst_760_);
lean_dec(v_a_758_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_818_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_fst_764_; lean_object* v_snd_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_817_; 
v_fst_764_ = lean_ctor_get(v_snd_759_, 0);
v_snd_765_ = lean_ctor_get(v_snd_759_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_snd_759_);
if (v_isSharedCheck_817_ == 0)
{
v___x_767_ = v_snd_759_;
v_isShared_768_ = v_isSharedCheck_817_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_snd_765_);
lean_inc(v_fst_764_);
lean_dec(v_snd_759_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_817_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
uint8_t v___x_776_; 
v___x_776_ = lean_unbox(v_snd_765_);
if (v___x_776_ == 0)
{
goto v___jp_769_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; uint8_t v___x_780_; 
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_array_get_size(v_fst_760_);
v___x_779_ = lean_nat_dec_eq(v___x_778_, v___x_777_);
v___x_780_ = lean_bool_not(v___x_779_);
if (v___x_780_ == 0)
{
goto v___jp_769_;
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_del_object(v___x_767_);
lean_del_object(v___x_762_);
v___x_781_ = l_Lean_instInhabitedNamePart_default;
v___x_782_ = lean_unsigned_to_nat(1u);
v___x_783_ = lean_nat_sub(v___x_778_, v___x_782_);
v___x_784_ = lean_array_get_borrowed(v___x_781_, v_fst_760_, v___x_783_);
lean_dec(v___x_783_);
lean_inc(v___x_784_);
v___x_785_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_784_);
if (lean_obj_tag(v___x_785_) == 0)
{
uint8_t v___x_786_; 
v___x_786_ = lean_nat_dec_eq(v___x_757_, v___x_777_);
if (lean_obj_tag(v___x_784_) == 1)
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = lean_unsigned_to_nat(2u);
v___x_788_ = lean_nat_dec_le(v___x_787_, v___x_778_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_dec(v_snd_765_);
v___x_789_ = lean_box(v___x_786_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_fst_764_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_fst_760_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v_a_758_ = v___x_791_;
goto _start;
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_793_ = lean_nat_sub(v___x_778_, v___x_787_);
v___x_794_ = lean_array_get_borrowed(v___x_781_, v_fst_760_, v___x_793_);
lean_dec(v___x_793_);
lean_inc(v___x_794_);
v___x_795_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_794_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec(v_snd_765_);
v___x_796_ = lean_box(v___x_786_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_fst_764_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v_fst_760_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v_a_758_ = v___x_798_;
goto _start;
}
else
{
lean_object* v_val_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_val_800_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_val_800_);
lean_dec_ref_known(v___x_795_, 1);
v___x_801_ = lean_array_push(v_fst_764_, v_val_800_);
v___x_802_ = lean_array_pop(v_fst_760_);
v___x_803_ = lean_array_pop(v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_801_);
lean_ctor_set(v___x_804_, 1, v_snd_765_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v_a_758_ = v___x_805_;
goto _start;
}
}
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v_snd_765_);
v___x_807_ = lean_box(v___x_786_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v_fst_764_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v_fst_760_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v_a_758_ = v___x_809_;
goto _start;
}
}
else
{
lean_object* v_val_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_val_811_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v___x_785_, 1);
v___x_812_ = lean_array_push(v_fst_764_, v_val_811_);
v___x_813_ = lean_array_pop(v_fst_760_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v_snd_765_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v_a_758_ = v___x_815_;
goto _start;
}
}
}
v___jp_769_:
{
lean_object* v___x_771_; 
if (v_isShared_768_ == 0)
{
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_fst_764_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_snd_765_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v___x_771_);
v___x_773_ = v___x_762_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_fst_760_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg___boxed(lean_object* v___x_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_819_, v_a_820_);
lean_dec(v___x_819_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(lean_object* v_as_827_, size_t v_sz_828_, size_t v_i_829_, lean_object* v_b_830_){
_start:
{
lean_object* v_a_832_; uint8_t v___x_836_; 
v___x_836_ = lean_usize_dec_lt(v_i_829_, v_sz_828_);
if (v___x_836_ == 0)
{
return v_b_830_;
}
else
{
lean_object* v_a_837_; lean_object* v___y_839_; lean_object* v_name_859_; lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v_a_837_ = lean_array_uget_borrowed(v_as_827_, v_i_829_);
v_name_859_ = lean_ctor_get(v_a_837_, 0);
v___x_860_ = lean_string_utf8_byte_size(v_name_859_);
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_nat_dec_eq(v___x_860_, v___x_861_);
if (v___x_862_ == 0)
{
lean_inc_ref(v_name_859_);
v___y_839_ = v_name_859_;
goto v___jp_838_;
}
else
{
lean_object* v___x_863_; 
v___x_863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_839_ = v___x_863_;
goto v___jp_838_;
}
v___jp_838_:
{
lean_object* v_flags_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; uint8_t v___x_844_; 
v_flags_840_ = lean_ctor_get(v_a_837_, 1);
v___x_841_ = lean_array_get_size(v_flags_840_);
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = lean_nat_dec_eq(v___x_841_, v___x_842_);
v___x_844_ = lean_bool_not(v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_846_ = lean_string_append(v_b_830_, v___x_845_);
v___x_847_ = lean_string_append(v___x_846_, v___y_839_);
lean_dec_ref(v___y_839_);
v_a_832_ = v___x_847_;
goto v___jp_831_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_849_ = lean_string_append(v_b_830_, v___x_848_);
v___x_850_ = lean_string_append(v___x_849_, v___y_839_);
lean_dec_ref(v___y_839_);
v___x_851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1));
v___x_852_ = lean_string_append(v___x_850_, v___x_851_);
v___x_853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
lean_inc_ref(v_flags_840_);
v___x_854_ = lean_array_to_list(v_flags_840_);
v___x_855_ = l_String_intercalate(v___x_853_, v___x_854_);
v___x_856_ = lean_string_append(v___x_852_, v___x_855_);
lean_dec_ref(v___x_855_);
v___x_857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_858_ = lean_string_append(v___x_856_, v___x_857_);
v_a_832_ = v___x_858_;
goto v___jp_831_;
}
}
}
v___jp_831_:
{
size_t v___x_833_; size_t v___x_834_; 
v___x_833_ = ((size_t)1ULL);
v___x_834_ = lean_usize_add(v_i_829_, v___x_833_);
v_i_829_ = v___x_834_;
v_b_830_ = v_a_832_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___boxed(lean_object* v_as_864_, lean_object* v_sz_865_, lean_object* v_i_866_, lean_object* v_b_867_){
_start:
{
size_t v_sz_boxed_868_; size_t v_i_boxed_869_; lean_object* v_res_870_; 
v_sz_boxed_868_ = lean_unbox_usize(v_sz_865_);
lean_dec(v_sz_865_);
v_i_boxed_869_ = lean_unbox_usize(v_i_866_);
lean_dec(v_i_866_);
v_res_870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v_as_864_, v_sz_boxed_868_, v_i_boxed_869_, v_b_867_);
lean_dec_ref(v_as_864_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(lean_object* v_components_879_){
_start:
{
lean_object* v___y_881_; lean_object* v_result_882_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_904_; lean_object* v_parts_905_; lean_object* v_specEntries_906_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v_entries_916_; uint8_t v___x_921_; 
v___x_886_ = lean_array_get_size(v_components_879_);
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_nat_dec_eq(v___x_886_, v___x_887_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v_fst_923_; lean_object* v_snd_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_980_; 
v___x_922_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_components_879_, v___x_887_, v___x_886_);
v_fst_923_ = lean_ctor_get(v___x_922_, 0);
v_snd_924_ = lean_ctor_get(v___x_922_, 1);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_980_ == 0)
{
v___x_926_ = v___x_922_;
v_isShared_927_ = v_isSharedCheck_980_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_snd_924_);
lean_inc(v_fst_923_);
lean_dec(v___x_922_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_980_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_parts_928_; lean_object* v_flags_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v_parts_928_ = l_Array_extract___redArg(v_components_879_, v_fst_923_, v___x_886_);
v_flags_929_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1));
v___x_930_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2));
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_930_);
lean_ctor_set(v___x_926_, 0, v_parts_928_);
v___x_932_ = v___x_926_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_parts_928_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v___x_930_);
v___x_932_ = v_reuseFailAlloc_979_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; lean_object* v_fst_934_; lean_object* v_snd_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_978_; 
v___x_933_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_886_, v___x_932_);
v_fst_934_ = lean_ctor_get(v___x_933_, 0);
v_snd_935_ = lean_ctor_get(v___x_933_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_978_ == 0)
{
v___x_937_ = v___x_933_;
v_isShared_938_ = v_isSharedCheck_978_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_snd_935_);
lean_inc(v_fst_934_);
lean_dec(v___x_933_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_978_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v_flags_940_; uint8_t v___x_973_; 
v___x_973_ = lean_unbox(v_snd_924_);
lean_dec(v_snd_924_);
if (v___x_973_ == 0)
{
lean_object* v_fst_974_; 
v_fst_974_ = lean_ctor_get(v_snd_935_, 0);
lean_inc(v_fst_974_);
lean_dec(v_snd_935_);
v_flags_940_ = v_fst_974_;
goto v___jp_939_;
}
else
{
lean_object* v_fst_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_fst_975_ = lean_ctor_get(v_snd_935_, 0);
lean_inc(v_fst_975_);
lean_dec(v_snd_935_);
v___x_976_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3));
v___x_977_ = lean_array_push(v_fst_975_, v___x_976_);
v_flags_940_ = v___x_977_;
goto v___jp_939_;
}
v___jp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_941_ = lean_array_get_size(v_fst_934_);
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_943_, 0, v___x_887_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
lean_ctor_set(v___x_943_, 2, v___x_942_);
v___x_944_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_886_, v___x_943_, v_fst_934_, v___x_887_);
lean_dec(v_fst_934_);
lean_dec_ref_known(v___x_943_, 3);
v___x_945_ = lean_box(0);
v___x_946_ = lean_array_get_size(v___x_944_);
v___x_947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_947_, 0, v___x_887_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
lean_ctor_set(v___x_947_, 2, v___x_942_);
v___x_948_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_944_, v___x_947_, v___x_945_, v___x_887_);
lean_dec_ref_known(v___x_947_, 3);
if (lean_obj_tag(v___x_948_) == 1)
{
lean_object* v_val_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_956_; 
v_val_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc_n(v_val_949_, 2);
lean_dec_ref_known(v___x_948_, 1);
v___x_950_ = l_Array_extract___redArg(v___x_944_, v___x_887_, v_val_949_);
v___x_951_ = l_Array_extract___redArg(v___x_944_, v_val_949_, v___x_946_);
lean_dec_ref(v___x_944_);
v___x_952_ = lean_array_get_size(v___x_951_);
v___x_953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_953_, 0, v___x_887_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
lean_ctor_set(v___x_953_, 2, v___x_942_);
v___x_954_ = lean_box(v___x_921_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 1, v___x_954_);
lean_ctor_set(v___x_937_, 0, v_flags_929_);
v___x_956_ = v___x_937_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_flags_929_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_954_);
v___x_956_ = v_reuseFailAlloc_972_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v_snd_960_; lean_object* v_snd_961_; lean_object* v_fst_962_; 
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_945_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v_flags_929_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_951_, v___x_886_, v___x_953_, v___x_958_, v___x_887_);
lean_dec_ref_known(v___x_953_, 3);
lean_dec_ref(v___x_951_);
v_snd_960_ = lean_ctor_get(v___x_959_, 1);
lean_inc(v_snd_960_);
v_snd_961_ = lean_ctor_get(v_snd_960_, 1);
lean_inc(v_snd_961_);
v_fst_962_ = lean_ctor_get(v_snd_960_, 0);
lean_inc(v_fst_962_);
lean_dec(v_snd_960_);
if (lean_obj_tag(v_fst_962_) == 1)
{
lean_object* v_fst_963_; lean_object* v_fst_964_; lean_object* v_val_965_; lean_object* v___x_966_; uint8_t v___x_967_; uint8_t v___x_968_; 
v_fst_963_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_fst_963_);
lean_dec_ref(v___x_959_);
v_fst_964_ = lean_ctor_get(v_snd_961_, 0);
lean_inc(v_fst_964_);
lean_dec(v_snd_961_);
v_val_965_ = lean_ctor_get(v_fst_962_, 0);
lean_inc(v_val_965_);
lean_dec_ref_known(v_fst_962_, 1);
v___x_966_ = lean_array_get_size(v_val_965_);
v___x_967_ = lean_nat_dec_eq(v___x_966_, v___x_887_);
v___x_968_ = lean_bool_not(v___x_967_);
if (v___x_968_ == 0)
{
lean_dec(v_val_965_);
v___y_912_ = v___x_950_;
v___y_913_ = v_fst_964_;
v___y_914_ = v_flags_929_;
v___y_915_ = v_flags_940_;
v_entries_916_ = v_fst_963_;
goto v___jp_911_;
}
else
{
lean_object* v___x_969_; 
v___x_969_ = lean_array_push(v_fst_963_, v_val_965_);
v___y_912_ = v___x_950_;
v___y_913_ = v_fst_964_;
v___y_914_ = v_flags_929_;
v___y_915_ = v_flags_940_;
v_entries_916_ = v___x_969_;
goto v___jp_911_;
}
}
else
{
lean_object* v_fst_970_; lean_object* v_fst_971_; 
lean_dec(v_fst_962_);
v_fst_970_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_fst_970_);
lean_dec_ref(v___x_959_);
v_fst_971_ = lean_ctor_get(v_snd_961_, 0);
lean_inc(v_fst_971_);
lean_dec(v_snd_961_);
v___y_912_ = v___x_950_;
v___y_913_ = v_fst_971_;
v___y_914_ = v_flags_929_;
v___y_915_ = v_flags_940_;
v_entries_916_ = v_fst_970_;
goto v___jp_911_;
}
}
}
else
{
lean_dec(v___x_948_);
lean_del_object(v___x_937_);
v___y_904_ = v_flags_940_;
v_parts_905_ = v___x_944_;
v_specEntries_906_ = v_flags_929_;
goto v___jp_903_;
}
}
}
}
}
}
else
{
lean_object* v___x_981_; 
v___x_981_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_981_;
}
v___jp_880_:
{
size_t v_sz_883_; size_t v___x_884_; lean_object* v___x_885_; 
v_sz_883_ = lean_array_size(v___y_881_);
v___x_884_ = ((size_t)0ULL);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v___y_881_, v_sz_883_, v___x_884_, v_result_882_);
lean_dec_ref(v___y_881_);
return v___x_885_;
}
v___jp_888_:
{
lean_object* v___x_892_; uint8_t v___x_893_; uint8_t v___x_894_; 
v___x_892_ = lean_array_get_size(v___y_889_);
v___x_893_ = lean_nat_dec_eq(v___x_892_, v___x_887_);
v___x_894_ = lean_bool_not(v___x_893_);
if (v___x_894_ == 0)
{
lean_dec_ref(v___y_889_);
v___y_881_ = v___y_890_;
v_result_882_ = v___y_891_;
goto v___jp_880_;
}
else
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_895_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0));
v___x_896_ = lean_string_append(v___y_891_, v___x_895_);
v___x_897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
v___x_898_ = lean_array_to_list(v___y_889_);
v___x_899_ = l_String_intercalate(v___x_897_, v___x_898_);
v___x_900_ = lean_string_append(v___x_896_, v___x_899_);
lean_dec_ref(v___x_899_);
v___x_901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_902_ = lean_string_append(v___x_900_, v___x_901_);
v___y_881_ = v___y_890_;
v_result_882_ = v___x_902_;
goto v___jp_880_;
}
}
v___jp_903_:
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = lean_array_get_size(v_parts_905_);
v___x_908_ = lean_nat_dec_eq(v___x_907_, v___x_887_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_parts_905_);
lean_dec_ref(v_parts_905_);
v___y_889_ = v___y_904_;
v___y_890_ = v_specEntries_906_;
v___y_891_ = v___x_909_;
goto v___jp_888_;
}
else
{
lean_object* v___x_910_; 
lean_dec_ref(v_parts_905_);
v___x_910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_889_ = v___y_904_;
v___y_890_ = v_specEntries_906_;
v___y_891_ = v___x_910_;
goto v___jp_888_;
}
}
v___jp_911_:
{
size_t v_sz_917_; size_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_sz_917_ = lean_array_size(v_entries_916_);
v___x_918_ = ((size_t)0ULL);
v___x_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v_entries_916_, v_sz_917_, v___x_918_, v___y_914_);
lean_dec_ref(v_entries_916_);
v___x_920_ = l_Array_append___redArg(v___y_912_, v___y_913_);
lean_dec(v___y_913_);
v___y_904_ = v___y_915_;
v_parts_905_ = v___x_920_;
v_specEntries_906_ = v___x_919_;
goto v___jp_903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___boxed(lean_object* v_components_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v_components_982_);
lean_dec_ref(v_components_982_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(lean_object* v___x_984_, lean_object* v_inst_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_984_, v_a_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___boxed(lean_object* v___x_988_, lean_object* v_inst_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(v___x_988_, v_inst_989_, v_a_990_);
lean_dec(v___x_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(lean_object* v___x_992_, lean_object* v_range_993_, lean_object* v_b_994_, lean_object* v_i_995_, lean_object* v_hs_996_, lean_object* v_hl_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_992_, v_range_993_, v_b_994_, v_i_995_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___boxed(lean_object* v___x_999_, lean_object* v_range_1000_, lean_object* v_b_1001_, lean_object* v_i_1002_, lean_object* v_hs_1003_, lean_object* v_hl_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(v___x_999_, v_range_1000_, v_b_1001_, v_i_1002_, v_hs_1003_, v_hl_1004_);
lean_dec_ref(v_b_1001_);
lean_dec_ref(v_range_1000_);
lean_dec(v___x_999_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(lean_object* v___x_1006_, lean_object* v_range_1007_, lean_object* v_b_1008_, lean_object* v_i_1009_, lean_object* v_hs_1010_, lean_object* v_hl_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_1006_, v_range_1007_, v_b_1008_, v_i_1009_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___boxed(lean_object* v___x_1013_, lean_object* v_range_1014_, lean_object* v_b_1015_, lean_object* v_i_1016_, lean_object* v_hs_1017_, lean_object* v_hl_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(v___x_1013_, v_range_1014_, v_b_1015_, v_i_1016_, v_hs_1017_, v_hl_1018_);
lean_dec(v_b_1015_);
lean_dec_ref(v_range_1014_);
lean_dec_ref(v___x_1013_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(lean_object* v___x_1020_, lean_object* v___x_1021_, lean_object* v_range_1022_, lean_object* v_b_1023_, lean_object* v_i_1024_, lean_object* v_hs_1025_, lean_object* v_hl_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_1020_, v___x_1021_, v_range_1022_, v_b_1023_, v_i_1024_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___boxed(lean_object* v___x_1028_, lean_object* v___x_1029_, lean_object* v_range_1030_, lean_object* v_b_1031_, lean_object* v_i_1032_, lean_object* v_hs_1033_, lean_object* v_hl_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(v___x_1028_, v___x_1029_, v_range_1030_, v_b_1031_, v_i_1032_, v_hs_1033_, v_hl_1034_);
lean_dec_ref(v_range_1030_);
lean_dec(v___x_1029_);
lean_dec_ref(v___x_1028_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(lean_object* v_body_1036_){
_start:
{
lean_object* v_name_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_name_1037_ = l_Lean_Name_demangle(v_body_1036_);
v___x_1038_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(v_name_1037_);
lean_dec(v_name_1037_);
v___x_1039_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v___x_1038_);
lean_dec_ref(v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody___boxed(lean_object* v_body_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_body_1040_);
lean_dec_ref(v_body_1040_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(lean_object* v_s_1045_, lean_object* v___x_1046_, lean_object* v_a_1047_, lean_object* v_b_1048_){
_start:
{
lean_object* v_startInclusive_1049_; lean_object* v_endExclusive_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_startInclusive_1049_ = lean_ctor_get(v___x_1046_, 1);
v_endExclusive_1050_ = lean_ctor_get(v___x_1046_, 2);
v___x_1051_ = lean_nat_sub(v_endExclusive_1050_, v_startInclusive_1049_);
v___x_1052_ = lean_nat_dec_eq(v_a_1047_, v___x_1051_);
lean_dec(v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___y_1071_; uint8_t v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1077_; uint8_t v___y_1078_; lean_object* v___y_1079_; uint8_t v___y_1080_; uint8_t v___y_1083_; uint32_t v___x_1094_; uint32_t v___x_1095_; uint8_t v___x_1096_; 
lean_dec_ref(v_b_1048_);
v___x_1053_ = lean_box(0);
v___x_1068_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1069_ = lean_string_utf8_next_fast(v_s_1045_, v_a_1047_);
v___x_1094_ = lean_string_utf8_get_fast(v_s_1045_, v_a_1047_);
v___x_1095_ = 95;
v___x_1096_ = lean_uint32_dec_eq(v___x_1094_, v___x_1095_);
if (v___x_1096_ == 0)
{
v___y_1083_ = v___x_1096_;
goto v___jp_1082_;
}
else
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = lean_nat_dec_eq(v_a_1047_, v___x_1097_);
if (v___x_1098_ == 0)
{
v___y_1083_ = v___x_1096_;
goto v___jp_1082_;
}
else
{
lean_dec(v_a_1047_);
v_a_1047_ = v___x_1069_;
v_b_1048_ = v___x_1068_;
goto _start;
}
}
v___jp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1057_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v___y_1055_);
lean_dec_ref(v___y_1055_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___y_1056_);
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v___x_1053_);
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
v___jp_1062_:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_Name_demangle(v___y_1063_);
if (lean_obj_tag(v___x_1065_) == 1)
{
lean_object* v_pre_1066_; 
v_pre_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_pre_1066_);
if (lean_obj_tag(v_pre_1066_) == 0)
{
lean_object* v_str_1067_; 
lean_dec_ref(v___y_1063_);
v_str_1067_ = lean_ctor_get(v___x_1065_, 1);
lean_inc_ref(v_str_1067_);
lean_dec_ref_known(v___x_1065_, 2);
v___y_1055_ = v___y_1064_;
v___y_1056_ = v_str_1067_;
goto v___jp_1054_;
}
else
{
lean_dec(v_pre_1066_);
lean_dec_ref_known(v___x_1065_, 2);
v___y_1055_ = v___y_1064_;
v___y_1056_ = v___y_1063_;
goto v___jp_1054_;
}
}
else
{
lean_dec(v___x_1065_);
v___y_1055_ = v___y_1064_;
v___y_1056_ = v___y_1063_;
goto v___jp_1054_;
}
}
v___jp_1070_:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_Name_demangle_x3f(v___y_1073_);
if (lean_obj_tag(v___x_1074_) == 0)
{
if (v___y_1072_ == 0)
{
lean_dec_ref(v___y_1073_);
lean_dec_ref(v___y_1071_);
v_a_1047_ = v___x_1069_;
v_b_1048_ = v___x_1068_;
goto _start;
}
else
{
v___y_1063_ = v___y_1071_;
v___y_1064_ = v___y_1073_;
goto v___jp_1062_;
}
}
else
{
lean_dec_ref_known(v___x_1074_, 1);
v___y_1063_ = v___y_1071_;
v___y_1064_ = v___y_1073_;
goto v___jp_1062_;
}
}
v___jp_1076_:
{
if (v___y_1080_ == 0)
{
lean_dec_ref(v___y_1079_);
lean_dec_ref(v___y_1077_);
v_a_1047_ = v___x_1069_;
v_b_1048_ = v___x_1068_;
goto _start;
}
else
{
v___y_1071_ = v___y_1077_;
v___y_1072_ = v___y_1078_;
v___y_1073_ = v___y_1079_;
goto v___jp_1070_;
}
}
v___jp_1082_:
{
if (v___y_1083_ == 0)
{
lean_dec(v_a_1047_);
v_a_1047_ = v___x_1069_;
v_b_1048_ = v___x_1068_;
goto _start;
}
else
{
lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1085_ = lean_string_utf8_byte_size(v_s_1045_);
v___x_1086_ = lean_nat_dec_eq(v___x_1069_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_string_utf8_extract(v_s_1045_, v___x_1087_, v_a_1047_);
lean_dec(v_a_1047_);
v___x_1089_ = lean_string_utf8_extract(v_s_1045_, v___x_1069_, v___x_1085_);
v___x_1090_ = l_Lean_Name_demangle_x3f(v___x_1088_);
if (lean_obj_tag(v___x_1090_) == 1)
{
lean_object* v_val_1091_; 
v_val_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_val_1091_);
lean_dec_ref_known(v___x_1090_, 1);
if (lean_obj_tag(v_val_1091_) == 1)
{
lean_object* v_pre_1092_; 
v_pre_1092_ = lean_ctor_get(v_val_1091_, 0);
lean_inc(v_pre_1092_);
lean_dec_ref_known(v_val_1091_, 2);
if (lean_obj_tag(v_pre_1092_) == 0)
{
v___y_1071_ = v___x_1088_;
v___y_1072_ = v___x_1086_;
v___y_1073_ = v___x_1089_;
goto v___jp_1070_;
}
else
{
lean_dec(v_pre_1092_);
v___y_1077_ = v___x_1088_;
v___y_1078_ = v___x_1086_;
v___y_1079_ = v___x_1089_;
v___y_1080_ = v___x_1086_;
goto v___jp_1076_;
}
}
else
{
lean_dec(v_val_1091_);
v___y_1077_ = v___x_1088_;
v___y_1078_ = v___x_1086_;
v___y_1079_ = v___x_1089_;
v___y_1080_ = v___x_1086_;
goto v___jp_1076_;
}
}
else
{
lean_dec(v___x_1090_);
v___y_1077_ = v___x_1088_;
v___y_1078_ = v___x_1086_;
v___y_1079_ = v___x_1089_;
v___y_1080_ = v___x_1086_;
goto v___jp_1076_;
}
}
else
{
lean_dec(v_a_1047_);
v_a_1047_ = v___x_1069_;
v_b_1048_ = v___x_1068_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1100_; 
lean_dec(v_a_1047_);
v___x_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_b_1048_);
return v___x_1100_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___boxed(lean_object* v_s_1101_, lean_object* v___x_1102_, lean_object* v_a_1103_, lean_object* v_b_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1101_, v___x_1102_, v_a_1103_, v_b_1104_);
lean_dec_ref(v___x_1102_);
lean_dec_ref(v_s_1101_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(lean_object* v_s_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_string_utf8_byte_size(v_s_1106_);
lean_inc_ref(v_s_1106_);
v___x_1109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1109_, 0, v_s_1106_);
lean_ctor_set(v___x_1109_, 1, v___x_1107_);
lean_ctor_set(v___x_1109_, 2, v___x_1108_);
v___x_1110_ = lean_box(0);
v___x_1111_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1112_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1106_, v___x_1109_, v___x_1107_, v___x_1111_);
lean_dec_ref_known(v___x_1109_, 3);
lean_dec_ref(v_s_1106_);
if (lean_obj_tag(v___x_1112_) == 0)
{
return v___x_1110_;
}
else
{
lean_object* v_val_1113_; lean_object* v_fst_1114_; 
v_val_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_val_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v_fst_1114_ = lean_ctor_get(v_val_1113_, 0);
lean_inc(v_fst_1114_);
lean_dec(v_val_1113_);
if (lean_obj_tag(v_fst_1114_) == 0)
{
return v___x_1110_;
}
else
{
return v_fst_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(lean_object* v_s_1115_, lean_object* v___x_1116_, lean_object* v_inst_1117_, lean_object* v_R_1118_, lean_object* v_a_1119_, lean_object* v_b_1120_, lean_object* v_c_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1115_, v___x_1116_, v_a_1119_, v_b_1120_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___boxed(lean_object* v_s_1123_, lean_object* v___x_1124_, lean_object* v_inst_1125_, lean_object* v_R_1126_, lean_object* v_a_1127_, lean_object* v_b_1128_, lean_object* v_c_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(v_s_1123_, v___x_1124_, v_inst_1125_, v_R_1126_, v_a_1127_, v_b_1128_, v_c_1129_);
lean_dec_ref(v___x_1124_);
lean_dec_ref(v_s_1123_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(lean_object* v_s_1131_, lean_object* v___x_1132_, lean_object* v___x_1133_, lean_object* v_a_1134_, lean_object* v_b_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_box(0);
switch(lean_obj_tag(v_a_1134_))
{
case 0:
{
lean_object* v_pos_1137_; lean_object* v___x_1138_; 
v_pos_1137_ = lean_ctor_get(v_a_1134_, 0);
lean_inc(v_pos_1137_);
lean_dec_ref_known(v_a_1134_, 1);
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_pos_1137_);
return v___x_1138_;
}
case 1:
{
lean_object* v_pos_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1148_; 
v_pos_1139_ = lean_ctor_get(v_a_1134_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_a_1134_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1141_ = v_a_1134_;
v_isShared_1142_ = v_isSharedCheck_1148_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_pos_1139_);
lean_dec(v_a_1134_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1148_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_string_utf8_next_fast(v_s_1131_, v_pos_1139_);
lean_dec(v_pos_1139_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1143_);
v___x_1145_ = v___x_1141_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
v_a_1134_ = v___x_1145_;
v_b_1135_ = v___x_1136_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1149_; lean_object* v_table_1150_; lean_object* v_stackPos_1151_; lean_object* v_needlePos_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1203_; 
v_needle_1149_ = lean_ctor_get(v_a_1134_, 0);
v_table_1150_ = lean_ctor_get(v_a_1134_, 1);
v_stackPos_1151_ = lean_ctor_get(v_a_1134_, 2);
v_needlePos_1152_ = lean_ctor_get(v_a_1134_, 3);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_a_1134_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1154_ = v_a_1134_;
v_isShared_1155_ = v_isSharedCheck_1203_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_needlePos_1152_);
lean_inc(v_stackPos_1151_);
lean_inc(v_table_1150_);
lean_inc(v_needle_1149_);
lean_dec(v_a_1134_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1203_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_str_1156_; lean_object* v_startInclusive_1157_; lean_object* v_endExclusive_1158_; lean_object* v_basePos_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v_str_1156_ = lean_ctor_get(v_needle_1149_, 0);
v_startInclusive_1157_ = lean_ctor_get(v_needle_1149_, 1);
v_endExclusive_1158_ = lean_ctor_get(v_needle_1149_, 2);
v_basePos_1159_ = lean_nat_sub(v_stackPos_1151_, v_needlePos_1152_);
v___x_1160_ = lean_nat_sub(v_endExclusive_1158_, v_startInclusive_1157_);
v___x_1161_ = lean_nat_add(v_basePos_1159_, v___x_1160_);
v___x_1162_ = lean_nat_dec_le(v___x_1161_, v___x_1133_);
lean_dec(v___x_1161_);
if (v___x_1162_ == 0)
{
uint8_t v___x_1163_; 
lean_dec(v___x_1160_);
lean_del_object(v___x_1154_);
lean_dec(v_needlePos_1152_);
lean_dec(v_stackPos_1151_);
lean_dec_ref(v_table_1150_);
lean_dec_ref(v_needle_1149_);
v___x_1163_ = lean_nat_dec_lt(v_basePos_1159_, v___x_1133_);
lean_dec(v_basePos_1159_);
if (v___x_1163_ == 0)
{
lean_inc(v_b_1135_);
return v_b_1135_;
}
else
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_box(3);
v_a_1134_ = v___x_1164_;
v_b_1135_ = v___x_1136_;
goto _start;
}
}
else
{
uint8_t v_stackByte_1166_; lean_object* v___x_1167_; uint8_t v_patByte_1168_; uint8_t v___x_1169_; 
lean_dec(v_basePos_1159_);
lean_inc(v_stackPos_1151_);
v_stackByte_1166_ = lean_string_get_byte_fast(v_s_1131_, v_stackPos_1151_);
v___x_1167_ = lean_nat_add(v_startInclusive_1157_, v_needlePos_1152_);
v_patByte_1168_ = lean_string_get_byte_fast(v_str_1156_, v___x_1167_);
v___x_1169_ = lean_uint8_dec_eq(v_stackByte_1166_, v_patByte_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
lean_dec(v___x_1160_);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_nat_dec_eq(v_needlePos_1152_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v_newNeedlePos_1174_; uint8_t v___x_1175_; 
v___x_1172_ = lean_unsigned_to_nat(1u);
v___x_1173_ = lean_nat_sub(v_needlePos_1152_, v___x_1172_);
lean_dec(v_needlePos_1152_);
v_newNeedlePos_1174_ = lean_array_fget_borrowed(v_table_1150_, v___x_1173_);
lean_dec(v___x_1173_);
v___x_1175_ = lean_nat_dec_eq(v_newNeedlePos_1174_, v___x_1170_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1177_; 
lean_inc(v_newNeedlePos_1174_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 3, v_newNeedlePos_1174_);
v___x_1177_ = v___x_1154_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_needle_1149_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_table_1150_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_stackPos_1151_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_newNeedlePos_1174_);
v___x_1177_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
v_a_1134_ = v___x_1177_;
v_b_1135_ = v___x_1136_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1180_; lean_object* v___x_1182_; 
v_nextStackPos_1180_ = l_String_Slice_posGE___redArg(v___x_1132_, v_stackPos_1151_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 3, v___x_1170_);
lean_ctor_set(v___x_1154_, 2, v_nextStackPos_1180_);
v___x_1182_ = v___x_1154_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_needle_1149_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_table_1150_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_nextStackPos_1180_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v___x_1170_);
v___x_1182_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
v_a_1134_ = v___x_1182_;
v_b_1135_ = v___x_1136_;
goto _start;
}
}
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v_nextStackPos_1187_; lean_object* v___x_1189_; 
lean_dec(v_needlePos_1152_);
v___x_1185_ = lean_unsigned_to_nat(1u);
v___x_1186_ = lean_nat_add(v_stackPos_1151_, v___x_1185_);
lean_dec(v_stackPos_1151_);
v_nextStackPos_1187_ = l_String_Slice_posGE___redArg(v___x_1132_, v___x_1186_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 3, v___x_1170_);
lean_ctor_set(v___x_1154_, 2, v_nextStackPos_1187_);
v___x_1189_ = v___x_1154_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_needle_1149_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_table_1150_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v_nextStackPos_1187_);
lean_ctor_set(v_reuseFailAlloc_1191_, 3, v___x_1170_);
v___x_1189_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
v_a_1134_ = v___x_1189_;
v_b_1135_ = v___x_1136_;
goto _start;
}
}
}
else
{
lean_object* v___x_1192_; lean_object* v_nextStackPos_1193_; lean_object* v_nextNeedlePos_1194_; uint8_t v___x_1195_; 
v___x_1192_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1193_ = lean_nat_add(v_stackPos_1151_, v___x_1192_);
lean_dec(v_stackPos_1151_);
v_nextNeedlePos_1194_ = lean_nat_add(v_needlePos_1152_, v___x_1192_);
lean_dec(v_needlePos_1152_);
v___x_1195_ = lean_nat_dec_eq(v_nextNeedlePos_1194_, v___x_1160_);
lean_dec(v___x_1160_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1197_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 3, v_nextNeedlePos_1194_);
lean_ctor_set(v___x_1154_, 2, v_nextStackPos_1193_);
v___x_1197_ = v___x_1154_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_needle_1149_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_table_1150_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v_nextStackPos_1193_);
lean_ctor_set(v_reuseFailAlloc_1199_, 3, v_nextNeedlePos_1194_);
v___x_1197_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
v_a_1134_ = v___x_1197_;
goto _start;
}
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_del_object(v___x_1154_);
lean_dec_ref(v_table_1150_);
lean_dec_ref(v_needle_1149_);
v___x_1200_ = lean_nat_sub(v_nextStackPos_1193_, v_nextNeedlePos_1194_);
lean_dec(v_nextNeedlePos_1194_);
lean_dec(v_nextStackPos_1193_);
v___x_1201_ = l_String_Slice_pos_x21(v___x_1132_, v___x_1200_);
lean_dec(v___x_1200_);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
}
}
}
}
default: 
{
lean_inc(v_b_1135_);
return v_b_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg___boxed(lean_object* v_s_1204_, lean_object* v___x_1205_, lean_object* v___x_1206_, lean_object* v_a_1207_, lean_object* v_b_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1204_, v___x_1205_, v___x_1206_, v_a_1207_, v_b_1208_);
lean_dec(v_b_1208_);
lean_dec(v___x_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v_s_1204_);
return v_res_1209_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0));
v___x_1212_ = lean_string_utf8_byte_size(v___x_1211_);
return v___x_1212_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1);
v___x_1215_ = lean_nat_dec_eq(v___x_1214_, v___x_1213_);
return v___x_1215_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1216_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1);
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0));
v___x_1219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___x_1217_);
lean_ctor_set(v___x_1219_, 2, v___x_1216_);
return v___x_1219_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
v___x_1221_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1220_);
return v___x_1221_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4);
v___x_1224_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
v___x_1225_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v___x_1223_);
lean_ctor_set(v___x_1225_, 2, v___x_1222_);
lean_ctor_set(v___x_1225_, 3, v___x_1222_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(lean_object* v_s_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___y_1233_; uint8_t v___x_1242_; 
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_string_utf8_byte_size(v_s_1228_);
lean_inc_ref(v_s_1228_);
v___x_1231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1231_, 0, v_s_1228_);
lean_ctor_set(v___x_1231_, 1, v___x_1229_);
lean_ctor_set(v___x_1231_, 2, v___x_1230_);
v___x_1242_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5);
v___y_1233_ = v___x_1243_;
goto v___jp_1232_;
}
else
{
lean_object* v___x_1244_; 
v___x_1244_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1233_ = v___x_1244_;
goto v___jp_1232_;
}
v___jp_1232_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_box(0);
lean_inc(v___y_1233_);
v___x_1235_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1228_, v___x_1231_, v___x_1230_, v___y_1233_, v___x_1234_);
lean_dec_ref_known(v___x_1231_, 3);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_s_1228_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
return v___x_1237_;
}
else
{
lean_object* v_val_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_val_1238_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1239_ = lean_string_utf8_extract(v_s_1228_, v___x_1229_, v_val_1238_);
v___x_1240_ = lean_string_utf8_extract(v_s_1228_, v_val_1238_, v___x_1230_);
lean_dec(v_val_1238_);
lean_dec_ref(v_s_1228_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
return v___x_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(lean_object* v_s_1245_, lean_object* v___x_1246_, lean_object* v___x_1247_, lean_object* v_inst_1248_, lean_object* v_R_1249_, lean_object* v_a_1250_, lean_object* v_b_1251_, lean_object* v_c_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1245_, v___x_1246_, v___x_1247_, v_a_1250_, v_b_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___boxed(lean_object* v_s_1254_, lean_object* v___x_1255_, lean_object* v___x_1256_, lean_object* v_inst_1257_, lean_object* v_R_1258_, lean_object* v_a_1259_, lean_object* v_b_1260_, lean_object* v_c_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(v_s_1254_, v___x_1255_, v___x_1256_, v_inst_1257_, v_R_1258_, v_a_1259_, v_b_1260_, v_c_1261_);
lean_dec(v_b_1260_);
lean_dec(v___x_1256_);
lean_dec_ref(v___x_1255_);
lean_dec_ref(v_s_1254_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(lean_object* v_s_1274_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10));
lean_inc_ref(v_s_1274_);
v___x_1394_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1274_, v___x_1393_);
if (lean_obj_tag(v___x_1394_) == 1)
{
lean_object* v_val_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1409_; 
v_val_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1409_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_val_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1409_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; uint8_t v___x_1402_; 
v___x_1399_ = lean_string_utf8_byte_size(v_val_1395_);
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = lean_nat_dec_eq(v___x_1399_, v___x_1400_);
v___x_1402_ = lean_bool_not(v___x_1401_);
if (v___x_1402_ == 0)
{
lean_del_object(v___x_1397_);
lean_dec(v_val_1395_);
goto v___jp_1371_;
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_dec_ref(v_s_1274_);
v___x_1403_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1404_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1395_);
lean_dec(v_val_1395_);
v___x_1405_ = lean_string_append(v___x_1403_, v___x_1404_);
lean_dec_ref(v___x_1404_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1405_);
v___x_1407_ = v___x_1397_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
else
{
lean_dec(v___x_1394_);
goto v___jp_1371_;
}
v___jp_1275_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0));
v___x_1277_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1274_, v___x_1276_);
if (lean_obj_tag(v___x_1277_) == 1)
{
lean_object* v_val_1278_; lean_object* v___x_1279_; 
v_val_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_val_1278_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1279_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1278_);
if (lean_obj_tag(v___x_1279_) == 1)
{
lean_object* v_val_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1294_; 
v_val_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1294_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_val_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1294_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v_fst_1284_; lean_object* v_snd_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v_fst_1284_ = lean_ctor_get(v_val_1280_, 0);
lean_inc(v_fst_1284_);
v_snd_1285_ = lean_ctor_get(v_val_1280_, 1);
lean_inc(v_snd_1285_);
lean_dec(v_val_1280_);
v___x_1286_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1287_ = lean_string_append(v_fst_1284_, v___x_1286_);
v___x_1288_ = lean_string_append(v___x_1287_, v_snd_1285_);
lean_dec(v_snd_1285_);
v___x_1289_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1290_ = lean_string_append(v___x_1288_, v___x_1289_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1290_);
v___x_1292_ = v___x_1282_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
else
{
lean_object* v___x_1295_; 
lean_dec(v___x_1279_);
v___x_1295_ = lean_box(0);
return v___x_1295_;
}
}
else
{
lean_object* v___x_1296_; 
lean_dec(v___x_1277_);
v___x_1296_ = lean_box(0);
return v___x_1296_;
}
}
v___jp_1297_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3));
lean_inc_ref(v_s_1274_);
v___x_1299_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1274_, v___x_1298_);
if (lean_obj_tag(v___x_1299_) == 1)
{
lean_object* v_val_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1312_; 
v_val_1300_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1302_ = v___x_1299_;
v_isShared_1303_ = v_isSharedCheck_1312_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_val_1300_);
lean_dec(v___x_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1312_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; uint8_t v___x_1307_; 
v___x_1304_ = lean_string_utf8_byte_size(v_val_1300_);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_nat_dec_eq(v___x_1304_, v___x_1305_);
v___x_1307_ = lean_bool_not(v___x_1306_);
if (v___x_1307_ == 0)
{
lean_del_object(v___x_1302_);
lean_dec(v_val_1300_);
goto v___jp_1275_;
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
lean_dec_ref(v_s_1274_);
v___x_1308_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1300_);
lean_dec(v_val_1300_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1308_);
v___x_1310_ = v___x_1302_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_dec(v___x_1299_);
goto v___jp_1275_;
}
}
v___jp_1313_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4));
lean_inc_ref(v_s_1274_);
v___x_1315_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1274_, v___x_1314_);
if (lean_obj_tag(v___x_1315_) == 1)
{
lean_object* v_val_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1330_; 
v_val_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1330_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_val_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1330_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; uint8_t v___x_1323_; 
v___x_1320_ = lean_string_utf8_byte_size(v_val_1316_);
v___x_1321_ = lean_unsigned_to_nat(0u);
v___x_1322_ = lean_nat_dec_eq(v___x_1320_, v___x_1321_);
v___x_1323_ = lean_bool_not(v___x_1322_);
if (v___x_1323_ == 0)
{
lean_del_object(v___x_1318_);
lean_dec(v_val_1316_);
goto v___jp_1297_;
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
lean_dec_ref(v_s_1274_);
v___x_1324_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1325_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1316_);
lean_dec(v_val_1316_);
v___x_1326_ = lean_string_append(v___x_1324_, v___x_1325_);
lean_dec_ref(v___x_1325_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1326_);
v___x_1328_ = v___x_1318_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
else
{
lean_dec(v___x_1315_);
goto v___jp_1297_;
}
}
v___jp_1331_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6));
lean_inc_ref(v_s_1274_);
v___x_1333_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1274_, v___x_1332_);
if (lean_obj_tag(v___x_1333_) == 1)
{
lean_object* v_val_1334_; lean_object* v___x_1335_; 
v_val_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_val_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v___x_1335_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1334_);
if (lean_obj_tag(v___x_1335_) == 1)
{
lean_object* v_val_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v_s_1274_);
v_val_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1352_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_val_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1352_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_fst_1340_; lean_object* v_snd_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v_fst_1340_ = lean_ctor_get(v_val_1336_, 0);
lean_inc(v_fst_1340_);
v_snd_1341_ = lean_ctor_get(v_val_1336_, 1);
lean_inc(v_snd_1341_);
lean_dec(v_val_1336_);
v___x_1342_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1343_ = lean_string_append(v___x_1342_, v_fst_1340_);
lean_dec(v_fst_1340_);
v___x_1344_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1345_ = lean_string_append(v___x_1343_, v___x_1344_);
v___x_1346_ = lean_string_append(v___x_1345_, v_snd_1341_);
lean_dec(v_snd_1341_);
v___x_1347_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1348_ = lean_string_append(v___x_1346_, v___x_1347_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1348_);
v___x_1350_ = v___x_1338_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
else
{
lean_dec(v___x_1335_);
goto v___jp_1313_;
}
}
else
{
lean_dec(v___x_1333_);
goto v___jp_1313_;
}
}
v___jp_1353_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7));
lean_inc_ref(v_s_1274_);
v___x_1355_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1274_, v___x_1354_);
if (lean_obj_tag(v___x_1355_) == 1)
{
lean_object* v_val_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1370_; 
v_val_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1370_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_val_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1370_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; uint8_t v___x_1363_; 
v___x_1360_ = lean_string_utf8_byte_size(v_val_1356_);
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = lean_nat_dec_eq(v___x_1360_, v___x_1361_);
v___x_1363_ = lean_bool_not(v___x_1362_);
if (v___x_1363_ == 0)
{
lean_del_object(v___x_1358_);
lean_dec(v_val_1356_);
goto v___jp_1331_;
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
lean_dec_ref(v_s_1274_);
v___x_1364_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1365_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1356_);
lean_dec(v_val_1356_);
v___x_1366_ = lean_string_append(v___x_1364_, v___x_1365_);
lean_dec_ref(v___x_1365_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1366_);
v___x_1368_ = v___x_1358_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_dec(v___x_1355_);
goto v___jp_1331_;
}
}
v___jp_1371_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8));
lean_inc_ref(v_s_1274_);
v___x_1373_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1274_, v___x_1372_);
if (lean_obj_tag(v___x_1373_) == 1)
{
lean_object* v_val_1374_; lean_object* v___x_1375_; 
v_val_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_val_1374_);
lean_dec_ref_known(v___x_1373_, 1);
v___x_1375_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1374_);
if (lean_obj_tag(v___x_1375_) == 1)
{
lean_object* v_val_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1392_; 
lean_dec_ref(v_s_1274_);
v_val_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1392_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_val_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1392_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v_fst_1380_; lean_object* v_snd_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1390_; 
v_fst_1380_ = lean_ctor_get(v_val_1376_, 0);
lean_inc(v_fst_1380_);
v_snd_1381_ = lean_ctor_get(v_val_1376_, 1);
lean_inc(v_snd_1381_);
lean_dec(v_val_1376_);
v___x_1382_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1383_ = lean_string_append(v___x_1382_, v_fst_1380_);
lean_dec(v_fst_1380_);
v___x_1384_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1385_ = lean_string_append(v___x_1383_, v___x_1384_);
v___x_1386_ = lean_string_append(v___x_1385_, v_snd_1381_);
lean_dec(v_snd_1381_);
v___x_1387_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1388_ = lean_string_append(v___x_1386_, v___x_1387_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1388_);
v___x_1390_ = v___x_1378_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_dec(v___x_1375_);
goto v___jp_1353_;
}
}
else
{
lean_dec(v___x_1373_);
goto v___jp_1353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleSymbol(lean_object* v_symbol_1419_){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1420_ = lean_string_utf8_byte_size(v_symbol_1419_);
v___x_1421_ = lean_unsigned_to_nat(0u);
v___x_1422_ = lean_nat_dec_eq(v___x_1420_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v_fst_1424_; lean_object* v_snd_1425_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1423_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(v_symbol_1419_);
v_fst_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc_n(v_fst_1424_, 2);
v_snd_1425_ = lean_ctor_get(v___x_1423_, 1);
lean_inc(v_snd_1425_);
lean_dec_ref(v___x_1423_);
v___x_1450_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__5));
v___x_1451_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_fst_1424_, v___x_1450_);
if (lean_obj_tag(v___x_1451_) == 1)
{
lean_object* v_val_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1472_; 
v_val_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1472_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_val_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1472_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
uint8_t v___x_1456_; 
lean_inc(v_val_1452_);
v___x_1456_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_1452_);
if (v___x_1456_ == 0)
{
lean_del_object(v___x_1454_);
lean_dec(v_val_1452_);
goto v___jp_1426_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_r_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
lean_dec(v_fst_1424_);
v___x_1457_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__6));
v___x_1458_ = lean_string_append(v___x_1457_, v_val_1452_);
lean_dec(v_val_1452_);
v___x_1459_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__7));
v_r_1460_ = lean_string_append(v___x_1458_, v___x_1459_);
v___x_1461_ = lean_string_utf8_byte_size(v_snd_1425_);
v___x_1462_ = lean_nat_dec_eq(v___x_1461_, v___x_1421_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1463_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1464_ = lean_string_append(v_r_1460_, v___x_1463_);
v___x_1465_ = lean_string_append(v___x_1464_, v_snd_1425_);
lean_dec(v_snd_1425_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1465_);
v___x_1467_ = v___x_1454_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
else
{
lean_object* v___x_1470_; 
lean_dec(v_snd_1425_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v_r_1460_);
v___x_1470_ = v___x_1454_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_r_1460_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
else
{
lean_dec(v___x_1451_);
goto v___jp_1426_;
}
v___jp_1426_:
{
lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__0));
v___x_1428_ = lean_string_dec_eq(v_fst_1424_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; 
v___x_1429_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(v_fst_1424_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_dec(v_snd_1425_);
return v___x_1429_;
}
else
{
lean_object* v_val_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v_val_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_val_1430_);
v___x_1431_ = lean_string_utf8_byte_size(v_snd_1425_);
v___x_1432_ = lean_nat_dec_eq(v___x_1431_, v___x_1421_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1442_; 
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; 
v_unused_1443_ = lean_ctor_get(v___x_1429_, 0);
lean_dec(v_unused_1443_);
v___x_1434_ = v___x_1429_;
v_isShared_1435_ = v_isSharedCheck_1442_;
goto v_resetjp_1433_;
}
else
{
lean_dec(v___x_1429_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1442_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1436_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1437_ = lean_string_append(v_val_1430_, v___x_1436_);
v___x_1438_ = lean_string_append(v___x_1437_, v_snd_1425_);
lean_dec(v_snd_1425_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1438_);
v___x_1440_ = v___x_1434_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
else
{
lean_dec(v_val_1430_);
lean_dec(v_snd_1425_);
return v___x_1429_;
}
}
}
else
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
lean_dec(v_fst_1424_);
v___x_1444_ = lean_string_utf8_byte_size(v_snd_1425_);
v___x_1445_ = lean_nat_dec_eq(v___x_1444_, v___x_1421_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__2));
v___x_1447_ = lean_string_append(v___x_1446_, v_snd_1425_);
lean_dec(v_snd_1425_);
v___x_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
return v___x_1448_;
}
else
{
lean_object* v___x_1449_; 
lean_dec(v_snd_1425_);
v___x_1449_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__4));
return v___x_1449_;
}
}
}
}
else
{
lean_object* v___x_1473_; 
lean_dec_ref(v_symbol_1419_);
v___x_1473_ = lean_box(0);
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(lean_object* v_s_1474_, lean_object* v_pos_1475_, lean_object* v_pred_1476_){
_start:
{
lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = lean_string_utf8_byte_size(v_s_1474_);
v___x_1478_ = lean_nat_dec_eq(v_pos_1475_, v___x_1477_);
if (v___x_1478_ == 0)
{
uint32_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1479_ = lean_string_utf8_get_fast(v_s_1474_, v_pos_1475_);
v___x_1480_ = lean_box_uint32(v___x_1479_);
lean_inc_ref(v_pred_1476_);
v___x_1481_ = lean_apply_1(v_pred_1476_, v___x_1480_);
v___x_1482_ = lean_unbox(v___x_1481_);
if (v___x_1482_ == 0)
{
lean_dec_ref(v_pred_1476_);
return v_pos_1475_;
}
else
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_string_utf8_next_fast(v_s_1474_, v_pos_1475_);
lean_dec(v_pos_1475_);
v_pos_1475_ = v___x_1483_;
goto _start;
}
}
else
{
lean_dec_ref(v_pred_1476_);
return v_pos_1475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile___boxed(lean_object* v_s_1485_, lean_object* v_pos_1486_, lean_object* v_pred_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_s_1485_, v_pos_1486_, v_pred_1487_);
lean_dec_ref(v_s_1485_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(lean_object* v_s_1489_, lean_object* v_p_u2081_1490_, lean_object* v_p_u2082_1491_){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = lean_string_utf8_extract(v_s_1489_, v___x_1492_, v_p_u2081_1490_);
v___x_1494_ = lean_string_utf8_extract(v_s_1489_, v_p_u2081_1490_, v_p_u2082_1491_);
v___x_1495_ = lean_string_utf8_byte_size(v_s_1489_);
v___x_1496_ = lean_string_utf8_extract(v_s_1489_, v_p_u2082_1491_, v___x_1495_);
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1494_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1493_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082___boxed(lean_object* v_s_1499_, lean_object* v_p_u2081_1500_, lean_object* v_p_u2082_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_s_1499_, v_p_u2081_1500_, v_p_u2082_1501_);
lean_dec(v_p_u2082_1501_);
lean_dec(v_p_u2081_1500_);
lean_dec_ref(v_s_1499_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(lean_object* v___x_1503_, lean_object* v___x_1504_, lean_object* v_line_1505_, lean_object* v_a_1506_, lean_object* v_b_1507_){
_start:
{
lean_object* v_startInclusive_1508_; lean_object* v_endExclusive_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v_startInclusive_1508_ = lean_ctor_get(v___x_1503_, 1);
v_endExclusive_1509_ = lean_ctor_get(v___x_1503_, 2);
v___x_1510_ = lean_nat_sub(v_endExclusive_1509_, v_startInclusive_1508_);
v___x_1511_ = lean_nat_dec_eq(v_a_1506_, v___x_1510_);
lean_dec(v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___y_1515_; uint32_t v___x_1520_; uint32_t v___x_1521_; uint8_t v___x_1522_; 
v___x_1512_ = lean_box(0);
v___x_1513_ = lean_nat_add(v___x_1504_, v_a_1506_);
v___x_1520_ = lean_string_utf8_get_fast(v_line_1505_, v___x_1513_);
v___x_1521_ = 43;
v___x_1522_ = lean_uint32_dec_eq(v___x_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
uint32_t v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = 41;
v___x_1524_ = lean_uint32_dec_eq(v___x_1520_, v___x_1523_);
v___y_1515_ = v___x_1524_;
goto v___jp_1514_;
}
else
{
v___y_1515_ = v___x_1522_;
goto v___jp_1514_;
}
v___jp_1514_:
{
if (v___y_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec(v_a_1506_);
v___x_1516_ = lean_string_utf8_next_fast(v_line_1505_, v___x_1513_);
lean_dec(v___x_1513_);
v___x_1517_ = lean_nat_sub(v___x_1516_, v___x_1504_);
v_a_1506_ = v___x_1517_;
v_b_1507_ = v___x_1512_;
goto _start;
}
else
{
lean_object* v___x_1519_; 
lean_dec(v___x_1513_);
v___x_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1519_, 0, v_a_1506_);
return v___x_1519_;
}
}
}
else
{
lean_dec(v_a_1506_);
lean_inc(v_b_1507_);
return v_b_1507_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg___boxed(lean_object* v___x_1525_, lean_object* v___x_1526_, lean_object* v_line_1527_, lean_object* v_a_1528_, lean_object* v_b_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1525_, v___x_1526_, v_line_1527_, v_a_1528_, v_b_1529_);
lean_dec(v_b_1529_);
lean_dec_ref(v_line_1527_);
lean_dec(v___x_1526_);
lean_dec_ref(v___x_1525_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(lean_object* v___x_1531_, lean_object* v_line_1532_, lean_object* v_a_1533_, lean_object* v_b_1534_){
_start:
{
lean_object* v_startInclusive_1535_; lean_object* v_endExclusive_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_startInclusive_1535_ = lean_ctor_get(v___x_1531_, 1);
v_endExclusive_1536_ = lean_ctor_get(v___x_1531_, 2);
v___x_1537_ = lean_nat_sub(v_endExclusive_1536_, v_startInclusive_1535_);
v___x_1538_ = lean_nat_dec_eq(v_a_1533_, v___x_1537_);
lean_dec(v___x_1537_);
if (v___x_1538_ == 0)
{
uint32_t v___x_1539_; uint32_t v___x_1540_; uint8_t v___x_1541_; 
v___x_1539_ = lean_string_utf8_get_fast(v_line_1532_, v_a_1533_);
v___x_1540_ = 40;
v___x_1541_ = lean_uint32_dec_eq(v___x_1539_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_box(0);
v___x_1543_ = lean_string_utf8_next_fast(v_line_1532_, v_a_1533_);
lean_dec(v_a_1533_);
v_a_1533_ = v___x_1543_;
v_b_1534_ = v___x_1542_;
goto _start;
}
else
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1545_, 0, v_a_1533_);
return v___x_1545_;
}
}
else
{
lean_dec(v_a_1533_);
lean_inc(v_b_1534_);
return v_b_1534_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg___boxed(lean_object* v___x_1546_, lean_object* v_line_1547_, lean_object* v_a_1548_, lean_object* v_b_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1546_, v_line_1547_, v_a_1548_, v_b_1549_);
lean_dec(v_b_1549_);
lean_dec_ref(v_line_1547_);
lean_dec_ref(v___x_1546_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(lean_object* v_line_1551_){
_start:
{
lean_object* v_searcher_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_searcher_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = lean_string_utf8_byte_size(v_line_1551_);
lean_inc_ref(v_line_1551_);
v___x_1554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1554_, 0, v_line_1551_);
lean_ctor_set(v___x_1554_, 1, v_searcher_1552_);
lean_ctor_set(v___x_1554_, 2, v___x_1553_);
v___x_1555_ = lean_box(0);
v___x_1556_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1554_, v_line_1551_, v_searcher_1552_, v___x_1555_);
lean_dec_ref_known(v___x_1554_, 3);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_dec_ref(v_line_1551_);
return v___x_1555_;
}
else
{
lean_object* v_val_1557_; uint8_t v___x_1558_; 
v_val_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_val_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v___x_1558_ = lean_nat_dec_eq(v_val_1557_, v___x_1553_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = lean_string_utf8_next_fast(v_line_1551_, v_val_1557_);
lean_dec(v_val_1557_);
lean_inc_ref(v_line_1551_);
v___x_1560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1560_, 0, v_line_1551_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
lean_ctor_set(v___x_1560_, 2, v___x_1553_);
v___x_1561_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1560_, v___x_1559_, v_line_1551_, v_searcher_1552_, v___x_1555_);
lean_dec_ref_known(v___x_1560_, 3);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_dec_ref(v_line_1551_);
return v___x_1555_;
}
else
{
lean_object* v_val_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1572_; 
v_val_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1572_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_val_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1572_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_nat_add(v___x_1559_, v_val_1562_);
lean_dec(v_val_1562_);
v___x_1567_ = lean_nat_dec_eq(v___x_1566_, v___x_1559_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1551_, v___x_1559_, v___x_1566_);
lean_dec(v___x_1566_);
lean_dec_ref(v_line_1551_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1568_);
v___x_1570_ = v___x_1564_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
else
{
lean_dec(v___x_1566_);
lean_del_object(v___x_1564_);
lean_dec_ref(v_line_1551_);
return v___x_1555_;
}
}
}
}
else
{
lean_dec(v_val_1557_);
lean_dec_ref(v_line_1551_);
return v___x_1555_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(lean_object* v___x_1573_, lean_object* v_line_1574_, lean_object* v_inst_1575_, lean_object* v_R_1576_, lean_object* v_a_1577_, lean_object* v_b_1578_, lean_object* v_c_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1573_, v_line_1574_, v_a_1577_, v_b_1578_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___boxed(lean_object* v___x_1581_, lean_object* v_line_1582_, lean_object* v_inst_1583_, lean_object* v_R_1584_, lean_object* v_a_1585_, lean_object* v_b_1586_, lean_object* v_c_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(v___x_1581_, v_line_1582_, v_inst_1583_, v_R_1584_, v_a_1585_, v_b_1586_, v_c_1587_);
lean_dec(v_b_1586_);
lean_dec_ref(v_line_1582_);
lean_dec_ref(v___x_1581_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(lean_object* v___x_1589_, lean_object* v___x_1590_, lean_object* v_line_1591_, lean_object* v_inst_1592_, lean_object* v_R_1593_, lean_object* v_a_1594_, lean_object* v_b_1595_, lean_object* v_c_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1589_, v___x_1590_, v_line_1591_, v_a_1594_, v_b_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___boxed(lean_object* v___x_1598_, lean_object* v___x_1599_, lean_object* v_line_1600_, lean_object* v_inst_1601_, lean_object* v_R_1602_, lean_object* v_a_1603_, lean_object* v_b_1604_, lean_object* v_c_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(v___x_1598_, v___x_1599_, v_line_1600_, v_inst_1601_, v_R_1602_, v_a_1603_, v_b_1604_, v_c_1605_);
lean_dec(v_b_1604_);
lean_dec_ref(v_line_1600_);
lean_dec(v___x_1599_);
lean_dec_ref(v___x_1598_);
return v_res_1606_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(uint32_t v_x_1607_){
_start:
{
uint32_t v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = 32;
v___x_1609_ = lean_uint32_dec_eq(v_x_1607_, v___x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed(lean_object* v_x_1610_){
_start:
{
uint32_t v_x_2608__boxed_1611_; uint8_t v_res_1612_; lean_object* v_r_1613_; 
v_x_2608__boxed_1611_ = lean_unbox_uint32(v_x_1610_);
lean_dec(v_x_1610_);
v_res_1612_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(v_x_2608__boxed_1611_);
v_r_1613_ = lean_box(v_res_1612_);
return v_r_1613_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(uint32_t v_x_1614_){
_start:
{
uint8_t v___y_1616_; uint8_t v___y_1622_; uint32_t v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = 48;
v___x_1628_ = lean_uint32_dec_le(v___x_1627_, v_x_1614_);
if (v___x_1628_ == 0)
{
v___y_1622_ = v___x_1628_;
goto v___jp_1621_;
}
else
{
uint32_t v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = 57;
v___x_1630_ = lean_uint32_dec_le(v_x_1614_, v___x_1629_);
v___y_1622_ = v___x_1630_;
goto v___jp_1621_;
}
v___jp_1615_:
{
if (v___y_1616_ == 0)
{
uint32_t v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = 65;
v___x_1618_ = lean_uint32_dec_le(v___x_1617_, v_x_1614_);
if (v___x_1618_ == 0)
{
return v___x_1618_;
}
else
{
uint32_t v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = 70;
v___x_1620_ = lean_uint32_dec_le(v_x_1614_, v___x_1619_);
return v___x_1620_;
}
}
else
{
return v___y_1616_;
}
}
v___jp_1621_:
{
if (v___y_1622_ == 0)
{
uint32_t v___x_1623_; uint8_t v___x_1624_; 
v___x_1623_ = 97;
v___x_1624_ = lean_uint32_dec_le(v___x_1623_, v_x_1614_);
if (v___x_1624_ == 0)
{
v___y_1616_ = v___x_1624_;
goto v___jp_1615_;
}
else
{
uint32_t v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = 102;
v___x_1626_ = lean_uint32_dec_le(v_x_1614_, v___x_1625_);
v___y_1616_ = v___x_1626_;
goto v___jp_1615_;
}
}
else
{
return v___y_1622_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed(lean_object* v_x_1631_){
_start:
{
uint32_t v_x_2615__boxed_1632_; uint8_t v_res_1633_; lean_object* v_r_1634_; 
v_x_2615__boxed_1632_ = lean_unbox_uint32(v_x_1631_);
lean_dec(v_x_1631_);
v_res_1633_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(v_x_2615__boxed_1632_);
v_r_1634_ = lean_box(v_res_1633_);
return v_r_1634_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(lean_object* v___x_1635_, lean_object* v_line_1636_, lean_object* v___x_1637_, lean_object* v___x_1638_, lean_object* v_a_1639_, lean_object* v_b_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = lean_box(0);
switch(lean_obj_tag(v_a_1639_))
{
case 0:
{
lean_object* v_pos_1642_; lean_object* v___x_1643_; 
v_pos_1642_ = lean_ctor_get(v_a_1639_, 0);
lean_inc(v_pos_1642_);
lean_dec_ref_known(v_a_1639_, 1);
v___x_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1643_, 0, v_pos_1642_);
return v___x_1643_;
}
case 1:
{
lean_object* v_pos_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1655_; 
v_pos_1644_ = lean_ctor_get(v_a_1639_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_a_1639_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1646_ = v_a_1639_;
v_isShared_1647_ = v_isSharedCheck_1655_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_pos_1644_);
lean_dec(v_a_1639_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1655_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1648_ = lean_nat_add(v___x_1635_, v_pos_1644_);
lean_dec(v_pos_1644_);
v___x_1649_ = lean_string_utf8_next_fast(v_line_1636_, v___x_1648_);
lean_dec(v___x_1648_);
v___x_1650_ = lean_nat_sub(v___x_1649_, v___x_1635_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set_tag(v___x_1646_, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1650_);
v___x_1652_ = v___x_1646_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
v_a_1639_ = v___x_1652_;
v_b_1640_ = v___x_1641_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1656_; lean_object* v_table_1657_; lean_object* v_stackPos_1658_; lean_object* v_needlePos_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1712_; 
v_needle_1656_ = lean_ctor_get(v_a_1639_, 0);
v_table_1657_ = lean_ctor_get(v_a_1639_, 1);
v_stackPos_1658_ = lean_ctor_get(v_a_1639_, 2);
v_needlePos_1659_ = lean_ctor_get(v_a_1639_, 3);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_a_1639_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1661_ = v_a_1639_;
v_isShared_1662_ = v_isSharedCheck_1712_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_needlePos_1659_);
lean_inc(v_stackPos_1658_);
lean_inc(v_table_1657_);
lean_inc(v_needle_1656_);
lean_dec(v_a_1639_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1712_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v_str_1663_; lean_object* v_startInclusive_1664_; lean_object* v_endExclusive_1665_; lean_object* v_basePos_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; 
v_str_1663_ = lean_ctor_get(v_needle_1656_, 0);
v_startInclusive_1664_ = lean_ctor_get(v_needle_1656_, 1);
v_endExclusive_1665_ = lean_ctor_get(v_needle_1656_, 2);
v_basePos_1666_ = lean_nat_sub(v_stackPos_1658_, v_needlePos_1659_);
v___x_1667_ = lean_nat_sub(v_endExclusive_1665_, v_startInclusive_1664_);
v___x_1668_ = lean_nat_add(v_basePos_1666_, v___x_1667_);
v___x_1669_ = lean_nat_sub(v___x_1638_, v___x_1635_);
v___x_1670_ = lean_nat_dec_le(v___x_1668_, v___x_1669_);
lean_dec(v___x_1668_);
if (v___x_1670_ == 0)
{
uint8_t v___x_1671_; 
lean_dec(v___x_1667_);
lean_del_object(v___x_1661_);
lean_dec(v_needlePos_1659_);
lean_dec(v_stackPos_1658_);
lean_dec_ref(v_table_1657_);
lean_dec_ref(v_needle_1656_);
v___x_1671_ = lean_nat_dec_lt(v_basePos_1666_, v___x_1669_);
lean_dec(v___x_1669_);
lean_dec(v_basePos_1666_);
if (v___x_1671_ == 0)
{
lean_inc(v_b_1640_);
return v_b_1640_;
}
else
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_box(3);
v_a_1639_ = v___x_1672_;
v_b_1640_ = v___x_1641_;
goto _start;
}
}
else
{
lean_object* v___x_1674_; uint8_t v_stackByte_1675_; lean_object* v___x_1676_; uint8_t v_patByte_1677_; uint8_t v___x_1678_; 
lean_dec(v___x_1669_);
lean_dec(v_basePos_1666_);
v___x_1674_ = lean_nat_add(v___x_1635_, v_stackPos_1658_);
v_stackByte_1675_ = lean_string_get_byte_fast(v_line_1636_, v___x_1674_);
v___x_1676_ = lean_nat_add(v_startInclusive_1664_, v_needlePos_1659_);
v_patByte_1677_ = lean_string_get_byte_fast(v_str_1663_, v___x_1676_);
v___x_1678_ = lean_uint8_dec_eq(v_stackByte_1675_, v_patByte_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; uint8_t v___x_1680_; 
lean_dec(v___x_1667_);
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1680_ = lean_nat_dec_eq(v_needlePos_1659_, v___x_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v_newNeedlePos_1683_; uint8_t v___x_1684_; 
v___x_1681_ = lean_unsigned_to_nat(1u);
v___x_1682_ = lean_nat_sub(v_needlePos_1659_, v___x_1681_);
lean_dec(v_needlePos_1659_);
v_newNeedlePos_1683_ = lean_array_fget_borrowed(v_table_1657_, v___x_1682_);
lean_dec(v___x_1682_);
v___x_1684_ = lean_nat_dec_eq(v_newNeedlePos_1683_, v___x_1679_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1686_; 
lean_inc(v_newNeedlePos_1683_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 3, v_newNeedlePos_1683_);
v___x_1686_ = v___x_1661_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_needle_1656_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_table_1657_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_stackPos_1658_);
lean_ctor_set(v_reuseFailAlloc_1688_, 3, v_newNeedlePos_1683_);
v___x_1686_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
v_a_1639_ = v___x_1686_;
v_b_1640_ = v___x_1641_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1689_; lean_object* v___x_1691_; 
v_nextStackPos_1689_ = l_String_Slice_posGE___redArg(v___x_1637_, v_stackPos_1658_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 3, v___x_1679_);
lean_ctor_set(v___x_1661_, 2, v_nextStackPos_1689_);
v___x_1691_ = v___x_1661_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_needle_1656_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_table_1657_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_nextStackPos_1689_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v___x_1679_);
v___x_1691_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
v_a_1639_ = v___x_1691_;
v_b_1640_ = v___x_1641_;
goto _start;
}
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v_nextStackPos_1696_; lean_object* v___x_1698_; 
lean_dec(v_needlePos_1659_);
v___x_1694_ = lean_unsigned_to_nat(1u);
v___x_1695_ = lean_nat_add(v_stackPos_1658_, v___x_1694_);
lean_dec(v_stackPos_1658_);
v_nextStackPos_1696_ = l_String_Slice_posGE___redArg(v___x_1637_, v___x_1695_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 3, v___x_1679_);
lean_ctor_set(v___x_1661_, 2, v_nextStackPos_1696_);
v___x_1698_ = v___x_1661_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_needle_1656_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_table_1657_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_nextStackPos_1696_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v___x_1679_);
v___x_1698_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
v_a_1639_ = v___x_1698_;
v_b_1640_ = v___x_1641_;
goto _start;
}
}
}
else
{
lean_object* v___x_1701_; lean_object* v_nextStackPos_1702_; lean_object* v_nextNeedlePos_1703_; uint8_t v___x_1704_; 
v___x_1701_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1702_ = lean_nat_add(v_stackPos_1658_, v___x_1701_);
lean_dec(v_stackPos_1658_);
v_nextNeedlePos_1703_ = lean_nat_add(v_needlePos_1659_, v___x_1701_);
lean_dec(v_needlePos_1659_);
v___x_1704_ = lean_nat_dec_eq(v_nextNeedlePos_1703_, v___x_1667_);
lean_dec(v___x_1667_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1706_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 3, v_nextNeedlePos_1703_);
lean_ctor_set(v___x_1661_, 2, v_nextStackPos_1702_);
v___x_1706_ = v___x_1661_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_needle_1656_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_table_1657_);
lean_ctor_set(v_reuseFailAlloc_1708_, 2, v_nextStackPos_1702_);
lean_ctor_set(v_reuseFailAlloc_1708_, 3, v_nextNeedlePos_1703_);
v___x_1706_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
v_a_1639_ = v___x_1706_;
goto _start;
}
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_del_object(v___x_1661_);
lean_dec_ref(v_table_1657_);
lean_dec_ref(v_needle_1656_);
v___x_1709_ = lean_nat_sub(v_nextStackPos_1702_, v_nextNeedlePos_1703_);
lean_dec(v_nextNeedlePos_1703_);
lean_dec(v_nextStackPos_1702_);
v___x_1710_ = l_String_Slice_pos_x21(v___x_1637_, v___x_1709_);
lean_dec(v___x_1709_);
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
}
}
}
}
default: 
{
lean_inc(v_b_1640_);
return v_b_1640_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg___boxed(lean_object* v___x_1713_, lean_object* v_line_1714_, lean_object* v___x_1715_, lean_object* v___x_1716_, lean_object* v_a_1717_, lean_object* v_b_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1713_, v_line_1714_, v___x_1715_, v___x_1716_, v_a_1717_, v_b_1718_);
lean_dec(v_b_1718_);
lean_dec(v___x_1716_);
lean_dec_ref(v___x_1715_);
lean_dec_ref(v_line_1714_);
lean_dec(v___x_1713_);
return v_res_1719_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3));
v___x_1725_ = lean_string_utf8_byte_size(v___x_1724_);
return v___x_1725_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1726_ = lean_unsigned_to_nat(0u);
v___x_1727_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4);
v___x_1728_ = lean_nat_dec_eq(v___x_1727_, v___x_1726_);
return v___x_1728_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1729_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4);
v___x_1730_ = lean_unsigned_to_nat(0u);
v___x_1731_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3));
v___x_1732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
lean_ctor_set(v___x_1732_, 1, v___x_1730_);
lean_ctor_set(v___x_1732_, 2, v___x_1729_);
return v___x_1732_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6);
v___x_1734_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1733_);
return v___x_1734_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1735_ = lean_unsigned_to_nat(0u);
v___x_1736_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7);
v___x_1737_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6);
v___x_1738_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
lean_ctor_set(v___x_1738_, 1, v___x_1736_);
lean_ctor_set(v___x_1738_, 2, v___x_1735_);
lean_ctor_set(v___x_1738_, 3, v___x_1735_);
return v___x_1738_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2));
v___x_1740_ = lean_string_utf8_byte_size(v___x_1739_);
return v___x_1740_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
v___x_1743_ = lean_nat_dec_eq(v___x_1742_, v___x_1741_);
return v___x_1743_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1744_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2));
v___x_1747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set(v___x_1747_, 1, v___x_1745_);
lean_ctor_set(v___x_1747_, 2, v___x_1744_);
return v___x_1747_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11);
v___x_1749_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1748_);
return v___x_1749_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12);
v___x_1752_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11);
v___x_1753_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v___x_1751_);
lean_ctor_set(v___x_1753_, 2, v___x_1750_);
lean_ctor_set(v___x_1753_, 3, v___x_1750_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(lean_object* v_line_1754_){
_start:
{
lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___f_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___x_1774_; lean_object* v___y_1776_; uint8_t v___x_1791_; 
v___f_1762_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0));
v___f_1763_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1));
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = lean_string_utf8_byte_size(v_line_1754_);
lean_inc_ref(v_line_1754_);
v___x_1774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1774_, 0, v_line_1754_);
lean_ctor_set(v___x_1774_, 1, v___x_1764_);
lean_ctor_set(v___x_1774_, 2, v___x_1765_);
v___x_1791_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13);
v___y_1776_ = v___x_1792_;
goto v___jp_1775_;
}
else
{
lean_object* v___x_1793_; 
v___x_1793_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1776_ = v___x_1793_;
goto v___jp_1775_;
}
v___jp_1755_:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_nat_dec_eq(v___y_1757_, v___y_1756_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1754_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v_line_1754_);
v___x_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; 
lean_dec(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v_line_1754_);
v___x_1761_ = lean_box(0);
return v___x_1761_;
}
}
v___jp_1766_:
{
lean_object* v___x_1771_; 
lean_inc(v___y_1770_);
v___x_1771_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___y_1769_, v_line_1754_, v___y_1768_, v___x_1765_, v___y_1770_, v___y_1767_);
lean_dec_ref(v___y_1768_);
if (lean_obj_tag(v___x_1771_) == 0)
{
v___y_1756_ = v___y_1769_;
v___y_1757_ = v___x_1765_;
goto v___jp_1755_;
}
else
{
lean_object* v_val_1772_; lean_object* v___x_1773_; 
v_val_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_val_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v___x_1773_ = lean_nat_add(v___y_1769_, v_val_1772_);
lean_dec(v_val_1772_);
v___y_1756_ = v___y_1769_;
v___y_1757_ = v___x_1773_;
goto v___jp_1755_;
}
}
v___jp_1775_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_box(0);
lean_inc(v___y_1776_);
v___x_1778_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_line_1754_, v___x_1774_, v___x_1765_, v___y_1776_, v___x_1777_);
lean_dec_ref_known(v___x_1774_, 3);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_dec_ref(v_line_1754_);
return v___x_1777_;
}
else
{
lean_object* v_val_1779_; uint8_t v___x_1780_; 
v_val_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_val_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v___x_1780_ = lean_nat_dec_eq(v_val_1779_, v___x_1765_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = lean_string_utf8_next_fast(v_line_1754_, v_val_1779_);
lean_dec(v_val_1779_);
v___x_1782_ = lean_nat_dec_eq(v___x_1781_, v___x_1765_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1783_ = lean_string_utf8_next_fast(v_line_1754_, v___x_1781_);
v___x_1784_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1754_, v___x_1783_, v___f_1763_);
v___x_1785_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1754_, v___x_1784_, v___f_1762_);
v___x_1786_ = lean_nat_dec_eq(v___x_1785_, v___x_1765_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
lean_inc(v___x_1785_);
lean_inc_ref(v_line_1754_);
v___x_1787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1787_, 0, v_line_1754_);
lean_ctor_set(v___x_1787_, 1, v___x_1785_);
lean_ctor_set(v___x_1787_, 2, v___x_1765_);
v___x_1788_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8);
v___y_1767_ = v___x_1777_;
v___y_1768_ = v___x_1787_;
v___y_1769_ = v___x_1785_;
v___y_1770_ = v___x_1789_;
goto v___jp_1766_;
}
else
{
lean_object* v___x_1790_; 
v___x_1790_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1767_ = v___x_1777_;
v___y_1768_ = v___x_1787_;
v___y_1769_ = v___x_1785_;
v___y_1770_ = v___x_1790_;
goto v___jp_1766_;
}
}
else
{
lean_dec(v___x_1785_);
lean_dec_ref(v_line_1754_);
return v___x_1777_;
}
}
else
{
lean_dec_ref(v_line_1754_);
return v___x_1777_;
}
}
else
{
lean_dec(v_val_1779_);
lean_dec_ref(v_line_1754_);
return v___x_1777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(lean_object* v___x_1794_, lean_object* v_line_1795_, lean_object* v___x_1796_, lean_object* v___x_1797_, lean_object* v_inst_1798_, lean_object* v_R_1799_, lean_object* v_a_1800_, lean_object* v_b_1801_, lean_object* v_c_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1794_, v_line_1795_, v___x_1796_, v___x_1797_, v_a_1800_, v_b_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___boxed(lean_object* v___x_1804_, lean_object* v_line_1805_, lean_object* v___x_1806_, lean_object* v___x_1807_, lean_object* v_inst_1808_, lean_object* v_R_1809_, lean_object* v_a_1810_, lean_object* v_b_1811_, lean_object* v_c_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(v___x_1804_, v_line_1805_, v___x_1806_, v___x_1807_, v_inst_1808_, v_R_1809_, v_a_1810_, v_b_1811_, v_c_1812_);
lean_dec(v_b_1811_);
lean_dec(v___x_1807_);
lean_dec_ref(v___x_1806_);
lean_dec_ref(v_line_1805_);
lean_dec(v___x_1804_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(lean_object* v_line_1814_){
_start:
{
lean_object* v___x_1815_; 
lean_inc_ref(v_line_1814_);
v___x_1815_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(v_line_1814_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v___x_1816_; 
v___x_1816_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(v_line_1814_);
return v___x_1816_;
}
else
{
lean_dec_ref(v_line_1814_);
return v___x_1815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleBtLine(lean_object* v_line_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(v_line_1817_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_box(0);
return v___x_1819_;
}
else
{
lean_object* v_val_1820_; lean_object* v_snd_1821_; lean_object* v_fst_1822_; lean_object* v_fst_1823_; lean_object* v_snd_1824_; lean_object* v___x_1825_; 
v_val_1820_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_val_1820_);
lean_dec_ref_known(v___x_1818_, 1);
v_snd_1821_ = lean_ctor_get(v_val_1820_, 1);
lean_inc(v_snd_1821_);
v_fst_1822_ = lean_ctor_get(v_val_1820_, 0);
lean_inc(v_fst_1822_);
lean_dec(v_val_1820_);
v_fst_1823_ = lean_ctor_get(v_snd_1821_, 0);
lean_inc(v_fst_1823_);
v_snd_1824_ = lean_ctor_get(v_snd_1821_, 1);
lean_inc(v_snd_1824_);
lean_dec(v_snd_1821_);
v___x_1825_ = l_Lean_Name_Demangle_demangleSymbol(v_fst_1823_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_dec(v_snd_1824_);
lean_dec(v_fst_1822_);
return v___x_1825_;
}
else
{
lean_object* v_val_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1835_; 
v_val_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_val_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1830_ = lean_string_append(v_fst_1822_, v_val_1826_);
lean_dec(v_val_1826_);
v___x_1831_ = lean_string_append(v___x_1830_, v_snd_1824_);
lean_dec(v_snd_1824_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1831_);
v___x_1833_ = v___x_1828_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_demangle_bt_line_cstr(lean_object* v_line_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_Name_Demangle_demangleBtLine(v_line_1836_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v___x_1838_; 
v___x_1838_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_1838_;
}
else
{
lean_object* v_val_1839_; 
v_val_1839_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_val_1839_);
lean_dec_ref_known(v___x_1837_, 1);
return v_val_1839_;
}
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_NameTrie(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NameMangling(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_NameDemangling(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_NameTrie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NameMangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_NameDemangling(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Lean_Data_NameTrie(uint8_t builtin);
lean_object* initialize_Lean_Compiler_NameMangling(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_NameDemangling(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameTrie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NameMangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NameDemangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_NameDemangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_NameDemangling(builtin);
}
#ifdef __cplusplus
}
#endif
