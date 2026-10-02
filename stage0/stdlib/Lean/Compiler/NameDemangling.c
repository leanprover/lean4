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
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedNamePart_default;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_instBEqNamePart_beq(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_demangle_x3f(lean_object*);
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
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_redArg"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_impl"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_lam"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_lambda"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_elam"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_jp"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_closed"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_lam_"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "closed"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12_value)}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "jp"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14_value)}};
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__1_value)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__1 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__1_value)}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_spec"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0_value)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0_value)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".cold"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "0x"};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3;
static const lean_closure_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_value;
static const lean_closure_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " + "};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7 = (const lean_object*)&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7_value;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8;
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9;
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
lean_object* v_str_43_; lean_object* v_startInclusive_44_; lean_object* v_endExclusive_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v_decide_49_; 
v_str_43_ = lean_ctor_get(v_s_41_, 0);
v_startInclusive_44_ = lean_ctor_get(v_s_41_, 1);
v_endExclusive_45_ = lean_ctor_get(v_s_41_, 2);
v___x_46_ = lean_nat_add(v_startInclusive_44_, v_pos_42_);
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = lean_nat_sub(v_endExclusive_45_, v___x_46_);
v_decide_49_ = lean_nat_dec_eq(v___x_47_, v___x_48_);
lean_dec(v___x_48_);
if (v_decide_49_ == 0)
{
uint32_t v___x_50_; uint32_t v___x_51_; uint8_t v___x_52_; 
v___x_50_ = lean_string_utf8_get_fast(v_str_43_, v___x_46_);
v___x_51_ = 48;
v___x_52_ = lean_uint32_dec_le(v___x_51_, v___x_50_);
if (v___x_52_ == 0)
{
lean_dec(v___x_46_);
return v_pos_42_;
}
else
{
uint32_t v___x_53_; uint8_t v___x_54_; 
v___x_53_ = 57;
v___x_54_ = lean_uint32_dec_le(v___x_50_, v___x_53_);
if (v___x_54_ == 0)
{
lean_dec(v___x_46_);
return v_pos_42_;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_55_ = lean_string_utf8_next_fast(v_str_43_, v___x_46_);
v___x_56_ = lean_nat_sub(v___x_55_, v___x_46_);
lean_dec(v___x_46_);
v___x_57_ = lean_nat_add(v_pos_42_, v___x_56_);
lean_dec(v___x_56_);
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_nat_add(v_pos_42_, v___x_58_);
v___x_60_ = lean_nat_dec_le(v___x_59_, v___x_57_);
lean_dec(v___x_59_);
if (v___x_60_ == 0)
{
lean_dec(v___x_57_);
return v_pos_42_;
}
else
{
lean_dec(v_pos_42_);
v_pos_42_ = v___x_57_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_46_);
return v_pos_42_;
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
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = lean_string_utf8_byte_size(v_s_65_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v_decide_71_; 
v___x_69_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_69_, 0, v_s_65_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
v___x_70_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(v___x_69_, v___x_67_);
lean_dec_ref_known(v___x_69_, 3);
v_decide_71_ = lean_nat_dec_eq(v___x_70_, v___x_66_);
lean_dec(v___x_70_);
return v_decide_71_;
}
else
{
uint8_t v___x_72_; 
lean_dec_ref(v_s_65_);
v___x_72_ = 0;
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
lean_object* v_s_175_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_s_175_ = lean_ctor_get(v_c_172_, 0);
lean_inc_ref(v_s_175_);
lean_dec_ref_known(v_c_172_, 1);
v___x_183_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3));
v___x_184_ = lean_string_dec_eq(v_s_175_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4));
v___x_186_ = lean_string_dec_eq(v_s_175_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5));
v___x_188_ = lean_string_dec_eq(v_s_175_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6));
v___x_190_ = lean_string_dec_eq(v_s_175_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7));
v___x_192_ = lean_string_dec_eq(v_s_175_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8));
v___x_194_ = lean_string_dec_eq(v_s_175_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9));
v___x_196_ = lean_string_dec_eq(v_s_175_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10));
v___x_198_ = lean_string_dec_eq(v_s_175_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11));
lean_inc_ref(v_s_175_);
v___x_200_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_175_, v___x_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
goto v___jp_176_;
}
else
{
lean_object* v_val_201_; uint8_t v___x_202_; 
v_val_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v___x_200_, 1);
v___x_202_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_201_);
if (v___x_202_ == 0)
{
goto v___jp_176_;
}
else
{
lean_object* v___x_203_; 
lean_dec_ref(v_s_175_);
v___x_203_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_203_;
}
}
}
else
{
lean_object* v___x_204_; 
lean_dec_ref(v_s_175_);
v___x_204_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13));
return v___x_204_;
}
}
else
{
lean_object* v___x_205_; 
lean_dec_ref(v_s_175_);
v___x_205_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15));
return v___x_205_;
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
else
{
lean_dec_ref(v_s_175_);
goto v___jp_173_;
}
}
else
{
lean_object* v___x_206_; 
lean_dec_ref(v_s_175_);
v___x_206_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__17));
return v___x_206_;
}
}
else
{
lean_object* v___x_207_; 
lean_dec_ref(v_s_175_);
v___x_207_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__19));
return v___x_207_;
}
}
else
{
lean_object* v___x_208_; 
lean_dec_ref(v_s_175_);
v___x_208_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__21));
return v___x_208_;
}
v___jp_176_:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__2));
v___x_178_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_175_, v___x_177_);
if (lean_obj_tag(v___x_178_) == 0)
{
return v___x_178_;
}
else
{
lean_object* v_val_179_; uint8_t v___x_180_; 
v_val_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_val_179_);
lean_dec_ref_known(v___x_178_, 1);
v___x_180_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
v___x_181_ = lean_box(0);
return v___x_181_;
}
else
{
lean_object* v___x_182_; 
v___x_182_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_182_;
}
}
}
}
else
{
lean_object* v___x_209_; 
lean_dec_ref(v_c_172_);
v___x_209_ = lean_box(0);
return v___x_209_;
}
v___jp_173_:
{
lean_object* v___x_174_; 
v___x_174_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_174_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(lean_object* v_c_211_){
_start:
{
if (lean_obj_tag(v_c_211_) == 0)
{
lean_object* v_s_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_s_212_ = lean_ctor_get(v_c_211_, 0);
lean_inc_ref(v_s_212_);
lean_dec_ref_known(v_c_211_, 1);
v___x_213_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___closed__0));
v___x_214_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_212_, v___x_213_);
if (lean_obj_tag(v___x_214_) == 0)
{
uint8_t v___x_215_; 
v___x_215_ = 0;
return v___x_215_;
}
else
{
lean_object* v_val_216_; uint8_t v___x_217_; 
v_val_216_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_val_216_);
lean_dec_ref_known(v___x_214_, 1);
v___x_217_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_216_);
return v___x_217_;
}
}
else
{
uint8_t v___x_218_; 
lean_dec_ref(v_c_211_);
v___x_218_ = 0;
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___boxed(lean_object* v_c_219_){
_start:
{
uint8_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(v_c_219_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
if (lean_obj_tag(v_x_223_) == 0)
{
uint8_t v___x_224_; 
v___x_224_ = 1;
return v___x_224_;
}
else
{
uint8_t v___x_225_; 
v___x_225_ = 0;
return v___x_225_;
}
}
else
{
if (lean_obj_tag(v_x_223_) == 0)
{
uint8_t v___x_226_; 
v___x_226_ = 0;
return v___x_226_;
}
else
{
lean_object* v_val_227_; lean_object* v_val_228_; uint8_t v___x_229_; 
v_val_227_ = lean_ctor_get(v_x_222_, 0);
v_val_228_ = lean_ctor_get(v_x_223_, 0);
v___x_229_ = l_Lean_instBEqNamePart_beq(v_val_227_, v_val_228_);
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0___boxed(lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v_x_230_, v_x_231_);
lean_dec(v_x_231_);
lean_dec(v_x_230_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(lean_object* v_stop_241_, lean_object* v_start_242_, lean_object* v___x_243_, lean_object* v_comps_244_, lean_object* v_range_245_, lean_object* v_b_246_, lean_object* v_i_247_){
_start:
{
lean_object* v_stop_248_; lean_object* v_step_249_; uint8_t v___x_250_; 
v_stop_248_ = lean_ctor_get(v_range_245_, 1);
v_step_249_ = lean_ctor_get(v_range_245_, 2);
v___x_250_ = lean_nat_dec_lt(v_i_247_, v_stop_248_);
if (v___x_250_ == 0)
{
lean_dec(v_i_247_);
lean_dec(v_start_242_);
lean_inc_ref(v_b_246_);
return v_b_246_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; lean_object* v___y_258_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_251_ = lean_box(0);
v___x_252_ = lean_box(0);
v___x_253_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0));
v___x_254_ = lean_unsigned_to_nat(1u);
v___x_255_ = lean_unsigned_to_nat(3u);
v___x_256_ = lean_nat_dec_le(v___x_255_, v___x_243_);
v___x_273_ = lean_array_get_size(v_comps_244_);
v___x_274_ = lean_nat_dec_lt(v_i_247_, v___x_273_);
if (v___x_274_ == 0)
{
v___y_258_ = v___x_251_;
goto v___jp_257_;
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_array_fget_borrowed(v_comps_244_, v_i_247_);
lean_inc(v___x_275_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
v___y_258_ = v___x_276_;
goto v___jp_257_;
}
v___jp_257_:
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2));
v___x_260_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_258_, v___x_259_);
lean_dec(v___y_258_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_nat_add(v_i_247_, v_step_249_);
lean_dec(v_i_247_);
v_b_246_ = v___x_253_;
v_i_247_ = v___x_261_;
goto _start;
}
else
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = lean_nat_add(v_i_247_, v___x_254_);
lean_dec(v_i_247_);
v___x_264_ = lean_nat_dec_lt(v___x_263_, v_stop_241_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v___x_263_);
v___x_265_ = lean_box(v___x_264_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v_start_242_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_252_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v_start_242_);
v___x_269_ = lean_box(v___x_256_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_263_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_252_);
return v___x_272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___boxed(lean_object* v_stop_277_, lean_object* v_start_278_, lean_object* v___x_279_, lean_object* v_comps_280_, lean_object* v_range_281_, lean_object* v_b_282_, lean_object* v_i_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_277_, v_start_278_, v___x_279_, v_comps_280_, v_range_281_, v_b_282_, v_i_283_);
lean_dec_ref(v_b_282_);
lean_dec_ref(v_range_281_);
lean_dec_ref(v_comps_280_);
lean_dec(v___x_279_);
lean_dec(v_stop_277_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(lean_object* v_comps_290_, lean_object* v_start_291_, lean_object* v_stop_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___y_296_; uint8_t v___x_318_; 
v___x_293_ = lean_unsigned_to_nat(3u);
v___x_294_ = lean_nat_sub(v_stop_292_, v_start_291_);
v___x_318_ = lean_nat_dec_le(v___x_293_, v___x_294_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v___x_294_);
lean_dec(v_stop_292_);
v___x_319_ = lean_box(v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v_start_291_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = lean_array_get_size(v_comps_290_);
v___x_322_ = lean_nat_dec_lt(v_start_291_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
v___x_323_ = lean_box(0);
v___y_296_ = v___x_323_;
goto v___jp_295_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_array_fget_borrowed(v_comps_290_, v_start_291_);
lean_inc(v___x_324_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
v___y_296_ = v___x_325_;
goto v___jp_295_;
}
}
v___jp_295_:
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2));
v___x_298_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_296_, v___x_297_);
lean_dec(v___y_296_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec(v___x_294_);
lean_dec(v_stop_292_);
v___x_299_ = lean_box(v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v_start_291_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_fst_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_316_; 
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_start_291_, v___x_301_);
lean_inc(v_stop_292_);
lean_inc(v___x_302_);
v___x_303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_stop_292_);
lean_ctor_set(v___x_303_, 2, v___x_301_);
v___x_304_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0));
lean_inc(v_start_291_);
v___x_305_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_292_, v_start_291_, v___x_294_, v_comps_290_, v___x_303_, v___x_304_, v___x_302_);
lean_dec_ref_known(v___x_303_, 3);
lean_dec(v___x_294_);
lean_dec(v_stop_292_);
v_fst_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; 
v_unused_317_ = lean_ctor_get(v___x_305_, 1);
lean_dec(v_unused_317_);
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_316_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_fst_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_316_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
if (lean_obj_tag(v_fst_306_) == 0)
{
uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_310_ = 0;
v___x_311_ = lean_box(v___x_310_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_311_);
lean_ctor_set(v___x_308_, 0, v_start_291_);
v___x_313_ = v___x_308_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_start_291_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
else
{
lean_object* v_val_315_; 
lean_del_object(v___x_308_);
lean_dec(v_start_291_);
v_val_315_ = lean_ctor_get(v_fst_306_, 0);
lean_inc(v_val_315_);
lean_dec_ref_known(v_fst_306_, 1);
return v_val_315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___boxed(lean_object* v_comps_326_, lean_object* v_start_327_, lean_object* v_stop_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_comps_326_, v_start_327_, v_stop_328_);
lean_dec_ref(v_comps_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(lean_object* v_stop_330_, lean_object* v_start_331_, lean_object* v___x_332_, lean_object* v_comps_333_, lean_object* v_range_334_, lean_object* v_b_335_, lean_object* v_i_336_, lean_object* v_hs_337_, lean_object* v_hl_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_330_, v_start_331_, v___x_332_, v_comps_333_, v_range_334_, v_b_335_, v_i_336_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___boxed(lean_object* v_stop_340_, lean_object* v_start_341_, lean_object* v___x_342_, lean_object* v_comps_343_, lean_object* v_range_344_, lean_object* v_b_345_, lean_object* v_i_346_, lean_object* v_hs_347_, lean_object* v_hl_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(v_stop_340_, v_start_341_, v___x_342_, v_comps_343_, v_range_344_, v_b_345_, v_i_346_, v_hs_347_, v_hl_348_);
lean_dec_ref(v_b_345_);
lean_dec_ref(v_range_344_);
lean_dec_ref(v_comps_343_);
lean_dec(v___x_342_);
lean_dec(v_stop_340_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(lean_object* v___x_350_, lean_object* v_comps_351_, lean_object* v_range_352_, lean_object* v_b_353_, lean_object* v_i_354_){
_start:
{
lean_object* v_stop_355_; lean_object* v_step_356_; uint8_t v___x_357_; 
v_stop_355_ = lean_ctor_get(v_range_352_, 1);
v_step_356_ = lean_ctor_get(v_range_352_, 2);
v___x_357_ = lean_nat_dec_lt(v_i_354_, v_stop_355_);
if (v___x_357_ == 0)
{
lean_dec(v_i_354_);
lean_inc(v_b_353_);
return v_b_353_;
}
else
{
lean_object* v___x_358_; uint8_t v___y_360_; lean_object* v___y_365_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_array_get_size(v_comps_351_);
v___x_371_ = lean_nat_dec_lt(v_i_354_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
v___x_372_ = lean_box(0);
v___y_365_ = v___x_372_;
goto v___jp_364_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_array_fget_borrowed(v_comps_351_, v_i_354_);
lean_inc(v___x_373_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
v___y_365_ = v___x_374_;
goto v___jp_364_;
}
v___jp_359_:
{
if (v___y_360_ == 0)
{
lean_object* v___x_361_; 
v___x_361_ = lean_nat_add(v_i_354_, v_step_356_);
lean_dec(v_i_354_);
v_i_354_ = v___x_361_;
goto _start;
}
else
{
lean_object* v___x_363_; 
v___x_363_ = lean_nat_add(v_i_354_, v___x_358_);
lean_dec(v_i_354_);
return v___x_363_;
}
}
v___jp_364_:
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2));
v___x_367_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_365_, v___x_366_);
lean_dec(v___y_365_);
if (v___x_367_ == 0)
{
v___y_360_ = v___x_367_;
goto v___jp_359_;
}
else
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_nat_add(v_i_354_, v___x_358_);
v___x_369_ = lean_nat_dec_lt(v___x_368_, v___x_350_);
lean_dec(v___x_368_);
v___y_360_ = v___x_369_;
goto v___jp_359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg___boxed(lean_object* v___x_375_, lean_object* v_comps_376_, lean_object* v_range_377_, lean_object* v_b_378_, lean_object* v_i_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_375_, v_comps_376_, v_range_377_, v_b_378_, v_i_379_);
lean_dec(v_b_378_);
lean_dec_ref(v_range_377_);
lean_dec_ref(v_comps_376_);
lean_dec(v___x_375_);
return v_res_380_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(lean_object* v_a_381_, lean_object* v_as_382_, size_t v_i_383_, size_t v_stop_384_){
_start:
{
uint8_t v___x_385_; 
v___x_385_ = lean_usize_dec_eq(v_i_383_, v_stop_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = lean_array_uget_borrowed(v_as_382_, v_i_383_);
v___x_387_ = lean_string_dec_eq(v_a_381_, v___x_386_);
if (v___x_387_ == 0)
{
size_t v___x_388_; size_t v___x_389_; 
v___x_388_ = ((size_t)1ULL);
v___x_389_ = lean_usize_add(v_i_383_, v___x_388_);
v_i_383_ = v___x_389_;
goto _start;
}
else
{
return v___x_387_;
}
}
else
{
uint8_t v___x_391_; 
v___x_391_ = 0;
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0___boxed(lean_object* v_a_392_, lean_object* v_as_393_, lean_object* v_i_394_, lean_object* v_stop_395_){
_start:
{
size_t v_i_boxed_396_; size_t v_stop_boxed_397_; uint8_t v_res_398_; lean_object* v_r_399_; 
v_i_boxed_396_ = lean_unbox_usize(v_i_394_);
lean_dec(v_i_394_);
v_stop_boxed_397_ = lean_unbox_usize(v_stop_395_);
lean_dec(v_stop_395_);
v_res_398_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_392_, v_as_393_, v_i_boxed_396_, v_stop_boxed_397_);
lean_dec_ref(v_as_393_);
lean_dec_ref(v_a_392_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(lean_object* v_as_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = lean_array_get_size(v_as_400_);
v___x_404_ = lean_nat_dec_lt(v___x_402_, v___x_403_);
if (v___x_404_ == 0)
{
return v___x_404_;
}
else
{
if (v___x_404_ == 0)
{
return v___x_404_;
}
else
{
size_t v___x_405_; size_t v___x_406_; uint8_t v___x_407_; 
v___x_405_ = ((size_t)0ULL);
v___x_406_ = lean_usize_of_nat(v___x_403_);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_401_, v_as_400_, v___x_405_, v___x_406_);
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0___boxed(lean_object* v_as_408_, lean_object* v_a_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_as_408_, v_a_409_);
lean_dec_ref(v_a_409_);
lean_dec_ref(v_as_408_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(lean_object* v_comps_412_, lean_object* v_range_413_, lean_object* v_b_414_, lean_object* v_i_415_){
_start:
{
lean_object* v_stop_416_; lean_object* v_step_417_; lean_object* v_a_419_; uint8_t v___x_422_; 
v_stop_416_ = lean_ctor_get(v_range_413_, 1);
v_step_417_ = lean_ctor_get(v_range_413_, 2);
v___x_422_ = lean_nat_dec_lt(v_i_415_, v_stop_416_);
if (v___x_422_ == 0)
{
lean_dec(v_i_415_);
return v_b_414_;
}
else
{
lean_object* v_fst_423_; lean_object* v_snd_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_448_; 
v_fst_423_ = lean_ctor_get(v_b_414_, 0);
v_snd_424_ = lean_ctor_get(v_b_414_, 1);
v_isSharedCheck_448_ = !lean_is_exclusive(v_b_414_);
if (v_isSharedCheck_448_ == 0)
{
v___x_426_ = v_b_414_;
v_isShared_427_ = v_isSharedCheck_448_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snd_424_);
lean_inc(v_fst_423_);
lean_dec(v_b_414_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_448_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = l_Lean_instInhabitedNamePart_default;
v___x_429_ = lean_array_get_borrowed(v___x_428_, v_comps_412_, v_i_415_);
lean_inc(v___x_429_);
v___x_430_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_429_);
if (lean_obj_tag(v___x_430_) == 0)
{
uint8_t v___x_431_; 
lean_inc(v___x_429_);
v___x_431_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(v___x_429_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_434_; 
lean_inc(v___x_429_);
v___x_432_ = lean_array_push(v_fst_423_, v___x_429_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_432_);
v___x_434_ = v___x_426_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_snd_424_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
v_a_419_ = v___x_434_;
goto v___jp_418_;
}
}
else
{
lean_object* v___x_437_; 
if (v_isShared_427_ == 0)
{
v___x_437_ = v___x_426_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_fst_423_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_snd_424_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
v_a_419_ = v___x_437_;
goto v___jp_418_;
}
}
}
else
{
lean_object* v_val_439_; uint8_t v___x_440_; 
v_val_439_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_val_439_);
lean_dec_ref_known(v___x_430_, 1);
v___x_440_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_snd_424_, v_val_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = lean_array_push(v_snd_424_, v_val_439_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_441_);
v___x_443_ = v___x_426_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_fst_423_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
v_a_419_ = v___x_443_;
goto v___jp_418_;
}
}
else
{
lean_object* v___x_446_; 
lean_dec(v_val_439_);
if (v_isShared_427_ == 0)
{
v___x_446_ = v___x_426_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_fst_423_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_snd_424_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
v_a_419_ = v___x_446_;
goto v___jp_418_;
}
}
}
}
}
v___jp_418_:
{
lean_object* v___x_420_; 
v___x_420_ = lean_nat_add(v_i_415_, v_step_417_);
lean_dec(v_i_415_);
v_b_414_ = v_a_419_;
v_i_415_ = v___x_420_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg___boxed(lean_object* v_comps_449_, lean_object* v_range_450_, lean_object* v_b_451_, lean_object* v_i_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_449_, v_range_450_, v_b_451_, v_i_452_);
lean_dec_ref(v_range_450_);
lean_dec_ref(v_comps_449_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(lean_object* v_comps_458_){
_start:
{
lean_object* v_begin___460_; lean_object* v_begin___476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___y_480_; uint8_t v___x_486_; 
v_begin___476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_unsigned_to_nat(3u);
v___x_478_ = lean_array_get_size(v_comps_458_);
v___x_486_ = lean_nat_dec_le(v___x_477_, v___x_478_);
if (v___x_486_ == 0)
{
v_begin___460_ = v_begin___476_;
goto v___jp_459_;
}
else
{
uint8_t v___x_487_; 
v___x_487_ = lean_nat_dec_lt(v_begin___476_, v___x_478_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
v___x_488_ = lean_box(0);
v___y_480_ = v___x_488_;
goto v___jp_479_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_array_fget_borrowed(v_comps_458_, v_begin___476_);
lean_inc(v___x_489_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
v___y_480_ = v___x_490_;
goto v___jp_479_;
}
}
v___jp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_475_; 
v___x_461_ = lean_array_get_size(v_comps_458_);
v___x_462_ = lean_unsigned_to_nat(1u);
lean_inc(v_begin___460_);
v___x_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_463_, 0, v_begin___460_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
lean_ctor_set(v___x_463_, 2, v___x_462_);
v___x_464_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1));
v___x_465_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_458_, v___x_463_, v___x_464_, v_begin___460_);
lean_dec_ref_known(v___x_463_, 3);
v_fst_466_ = lean_ctor_get(v___x_465_, 0);
v_snd_467_ = lean_ctor_get(v___x_465_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_475_ == 0)
{
v___x_469_ = v___x_465_;
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_snd_467_);
lean_inc(v_fst_466_);
lean_dec(v___x_465_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_fst_466_);
lean_dec(v_fst_466_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_snd_467_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
v___jp_479_:
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2));
v___x_482_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_480_, v___x_481_);
lean_dec(v___y_480_);
if (v___x_482_ == 0)
{
v_begin___460_ = v_begin___476_;
goto v___jp_459_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v___x_478_);
lean_ctor_set(v___x_484_, 2, v___x_483_);
v___x_485_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_478_, v_comps_458_, v___x_484_, v_begin___476_, v___x_483_);
lean_dec_ref_known(v___x_484_, 3);
v_begin___460_ = v___x_485_;
goto v___jp_459_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___boxed(lean_object* v_comps_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(v_comps_491_);
lean_dec_ref(v_comps_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1(lean_object* v_comps_493_, lean_object* v_range_494_, lean_object* v_b_495_, lean_object* v_i_496_, lean_object* v_hs_497_, lean_object* v_hl_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_493_, v_range_494_, v_b_495_, v_i_496_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___boxed(lean_object* v_comps_500_, lean_object* v_range_501_, lean_object* v_b_502_, lean_object* v_i_503_, lean_object* v_hs_504_, lean_object* v_hl_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1(v_comps_500_, v_range_501_, v_b_502_, v_i_503_, v_hs_504_, v_hl_505_);
lean_dec_ref(v_range_501_);
lean_dec_ref(v_comps_500_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2(lean_object* v___x_507_, lean_object* v_comps_508_, lean_object* v_range_509_, lean_object* v_b_510_, lean_object* v_i_511_, lean_object* v_hs_512_, lean_object* v_hl_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_507_, v_comps_508_, v_range_509_, v_b_510_, v_i_511_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___boxed(lean_object* v___x_515_, lean_object* v_comps_516_, lean_object* v_range_517_, lean_object* v_b_518_, lean_object* v_i_519_, lean_object* v_hs_520_, lean_object* v_hl_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2(v___x_515_, v_comps_516_, v_range_517_, v_b_518_, v_i_519_, v_hs_520_, v_hl_521_);
lean_dec(v_b_518_);
lean_dec_ref(v_range_517_);
lean_dec_ref(v_comps_516_);
lean_dec(v___x_515_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(lean_object* v___x_526_, lean_object* v_range_527_, lean_object* v_b_528_, lean_object* v_i_529_){
_start:
{
lean_object* v_stop_530_; lean_object* v_step_531_; uint8_t v___x_532_; 
v_stop_530_ = lean_ctor_get(v_range_527_, 1);
v_step_531_ = lean_ctor_get(v_range_527_, 2);
v___x_532_ = lean_nat_dec_lt(v_i_529_, v_stop_530_);
if (v___x_532_ == 0)
{
lean_dec(v_i_529_);
lean_inc(v_b_528_);
return v_b_528_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_533_ = l_Lean_instInhabitedNamePart_default;
v___x_534_ = lean_array_get_borrowed(v___x_533_, v___x_526_, v_i_529_);
v___x_535_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1));
v___x_536_ = l_Lean_instBEqNamePart_beq(v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
v___x_537_ = lean_nat_add(v_i_529_, v_step_531_);
lean_dec(v_i_529_);
v_i_529_ = v___x_537_;
goto _start;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v_i_529_);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___boxed(lean_object* v___x_540_, lean_object* v_range_541_, lean_object* v_b_542_, lean_object* v_i_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_540_, v_range_541_, v_b_542_, v_i_543_);
lean_dec(v_b_542_);
lean_dec_ref(v_range_541_);
lean_dec_ref(v___x_540_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(lean_object* v___x_545_, lean_object* v_as_546_, size_t v_sz_547_, size_t v_i_548_, lean_object* v_b_549_){
_start:
{
lean_object* v_a_551_; uint8_t v___x_555_; 
v___x_555_ = lean_usize_dec_lt(v_i_548_, v_sz_547_);
if (v___x_555_ == 0)
{
return v_b_549_;
}
else
{
lean_object* v_a_556_; lean_object* v___x_557_; lean_object* v_name_560_; lean_object* v_flags_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_a_556_ = lean_array_uget_borrowed(v_as_546_, v_i_548_);
v___x_557_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(v_a_556_);
v_name_560_ = lean_ctor_get(v___x_557_, 0);
v_flags_561_ = lean_ctor_get(v___x_557_, 1);
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = lean_string_utf8_byte_size(v_name_560_);
v___x_564_ = lean_nat_dec_eq(v___x_563_, v___x_562_);
if (v___x_564_ == 0)
{
goto v___jp_558_;
}
else
{
uint8_t v_skipNext_565_; 
v_skipNext_565_ = lean_nat_dec_eq(v___x_545_, v___x_562_);
if (v_skipNext_565_ == 0)
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_array_get_size(v_flags_561_);
v___x_567_ = lean_nat_dec_eq(v___x_566_, v___x_562_);
if (v___x_567_ == 0)
{
goto v___jp_558_;
}
else
{
lean_dec_ref(v___x_557_);
v_a_551_ = v_b_549_;
goto v___jp_550_;
}
}
else
{
goto v___jp_558_;
}
}
v___jp_558_:
{
lean_object* v___x_559_; 
v___x_559_ = lean_array_push(v_b_549_, v___x_557_);
v_a_551_ = v___x_559_;
goto v___jp_550_;
}
}
v___jp_550_:
{
size_t v___x_552_; size_t v___x_553_; 
v___x_552_ = ((size_t)1ULL);
v___x_553_ = lean_usize_add(v_i_548_, v___x_552_);
v_i_548_ = v___x_553_;
v_b_549_ = v_a_551_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5___boxed(lean_object* v___x_568_, lean_object* v_as_569_, lean_object* v_sz_570_, lean_object* v_i_571_, lean_object* v_b_572_){
_start:
{
size_t v_sz_boxed_573_; size_t v_i_boxed_574_; lean_object* v_res_575_; 
v_sz_boxed_573_ = lean_unbox_usize(v_sz_570_);
lean_dec(v_sz_570_);
v_i_boxed_574_ = lean_unbox_usize(v_i_571_);
lean_dec(v_i_571_);
v_res_575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_568_, v_as_569_, v_sz_boxed_573_, v_i_boxed_574_, v_b_572_);
lean_dec_ref(v_as_569_);
lean_dec(v___x_568_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(lean_object* v_range_577_, lean_object* v_b_578_, lean_object* v_i_579_){
_start:
{
lean_object* v_stop_580_; lean_object* v_step_581_; lean_object* v_a_583_; uint8_t v___x_586_; 
v_stop_580_ = lean_ctor_get(v_range_577_, 1);
v_step_581_ = lean_ctor_get(v_range_577_, 2);
v___x_586_ = lean_nat_dec_lt(v_i_579_, v_stop_580_);
if (v___x_586_ == 0)
{
lean_dec(v_i_579_);
lean_inc_ref(v_b_578_);
return v_b_578_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = l_Lean_instInhabitedNamePart_default;
v___x_588_ = lean_array_get_borrowed(v___x_587_, v_b_578_, v_i_579_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_s_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_s_589_ = lean_ctor_get(v___x_588_, 0);
v___x_590_ = lean_string_utf8_byte_size(v_s_589_);
v___x_591_ = lean_unsigned_to_nat(2u);
v___x_592_ = lean_nat_dec_le(v___x_591_, v___x_590_);
if (v___x_592_ == 0)
{
v_a_583_ = v_b_578_;
goto v___jp_582_;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0));
v___x_595_ = lean_string_memcmp(v_s_589_, v___x_594_, v___x_593_, v___x_593_, v___x_591_);
if (v___x_595_ == 0)
{
v_a_583_ = v_b_578_;
goto v___jp_582_;
}
else
{
lean_object* v___x_596_; 
v___x_596_ = l_Array_extract___redArg(v_b_578_, v___x_593_, v_i_579_);
return v___x_596_;
}
}
}
else
{
v_a_583_ = v_b_578_;
goto v___jp_582_;
}
}
v___jp_582_:
{
lean_object* v___x_584_; 
v___x_584_ = lean_nat_add(v_i_579_, v_step_581_);
lean_dec(v_i_579_);
v_b_578_ = v_a_583_;
v_i_579_ = v___x_584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___boxed(lean_object* v_range_597_, lean_object* v_b_598_, lean_object* v_i_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v_range_597_, v_b_598_, v_i_599_);
lean_dec_ref(v_b_598_);
lean_dec_ref(v_range_597_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(lean_object* v___x_606_, lean_object* v___x_607_, lean_object* v_range_608_, lean_object* v_b_609_, lean_object* v_i_610_){
_start:
{
lean_object* v_stop_611_; lean_object* v_step_612_; lean_object* v_a_614_; uint8_t v___x_617_; 
v_stop_611_ = lean_ctor_get(v_range_608_, 1);
v_step_612_ = lean_ctor_get(v_range_608_, 2);
v___x_617_ = lean_nat_dec_lt(v_i_610_, v_stop_611_);
if (v___x_617_ == 0)
{
lean_dec(v_i_610_);
return v_b_609_;
}
else
{
lean_object* v_snd_618_; lean_object* v_snd_619_; lean_object* v_fst_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_716_; 
v_snd_618_ = lean_ctor_get(v_b_609_, 1);
lean_inc(v_snd_618_);
v_snd_619_ = lean_ctor_get(v_snd_618_, 1);
lean_inc(v_snd_619_);
v_fst_620_ = lean_ctor_get(v_b_609_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v_b_609_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v_b_609_, 1);
lean_dec(v_unused_717_);
v___x_622_ = v_b_609_;
v_isShared_623_ = v_isSharedCheck_716_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_fst_620_);
lean_dec(v_b_609_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_716_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_fst_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_714_; 
v_fst_624_ = lean_ctor_get(v_snd_618_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v_snd_618_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v_snd_618_, 1);
lean_dec(v_unused_715_);
v___x_626_ = v_snd_618_;
v_isShared_627_ = v_isSharedCheck_714_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_fst_624_);
lean_dec(v_snd_618_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_714_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_fst_628_; lean_object* v_snd_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_713_; 
v_fst_628_ = lean_ctor_get(v_snd_619_, 0);
v_snd_629_ = lean_ctor_get(v_snd_619_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_snd_619_);
if (v_isSharedCheck_713_ == 0)
{
v___x_631_ = v_snd_619_;
v_isShared_632_ = v_isSharedCheck_713_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_snd_629_);
lean_inc(v_fst_628_);
lean_dec(v_snd_619_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_713_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_unbox(v_snd_629_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_635_ = l_Lean_instInhabitedNamePart_default;
v___x_636_ = lean_array_get_borrowed(v___x_635_, v___x_606_, v_i_610_);
v___x_666_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1));
v___x_667_ = l_Lean_instBEqNamePart_beq(v___x_636_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v_cont_671_; lean_object* v_entries_673_; lean_object* v_currentCtx_674_; 
v___x_668_ = lean_box(0);
v___x_669_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0));
v___x_670_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1));
v_cont_671_ = l_Lean_instBEqNamePart_beq(v___x_636_, v___x_670_);
if (v_cont_671_ == 0)
{
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_s_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_s_679_ = lean_ctor_get(v___x_636_, 0);
v___x_680_ = lean_string_utf8_byte_size(v_s_679_);
v___x_681_ = lean_unsigned_to_nat(5u);
v___x_682_ = lean_nat_dec_le(v___x_681_, v___x_680_);
if (v___x_682_ == 0)
{
goto v___jp_637_;
}
else
{
uint8_t v___x_683_; 
v___x_683_ = lean_string_memcmp(v_s_679_, v___x_669_, v___x_633_, v___x_633_, v___x_681_);
if (v___x_683_ == 0)
{
goto v___jp_637_;
}
else
{
lean_del_object(v___x_631_);
lean_del_object(v___x_626_);
lean_del_object(v___x_622_);
if (lean_obj_tag(v_fst_624_) == 1)
{
lean_object* v_val_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_val_684_ = lean_ctor_get(v_fst_624_, 0);
lean_inc(v_val_684_);
lean_dec_ref_known(v_fst_624_, 1);
v___x_685_ = lean_array_push(v_fst_620_, v_val_684_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v_fst_628_);
lean_ctor_set(v___x_686_, 1, v_snd_629_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_668_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_685_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v_a_614_ = v___x_688_;
goto v___jp_613_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_fst_628_);
lean_ctor_set(v___x_689_, 1, v_snd_629_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_fst_624_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v_fst_620_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v_a_614_ = v___x_691_;
goto v___jp_613_;
}
}
}
}
else
{
goto v___jp_637_;
}
}
else
{
lean_del_object(v___x_631_);
lean_dec(v_snd_629_);
lean_del_object(v___x_626_);
lean_del_object(v___x_622_);
if (lean_obj_tag(v_fst_624_) == 1)
{
lean_object* v_val_692_; lean_object* v___x_693_; 
v_val_692_ = lean_ctor_get(v_fst_624_, 0);
lean_inc(v_val_692_);
lean_dec_ref_known(v_fst_624_, 1);
v___x_693_ = lean_array_push(v_fst_620_, v_val_692_);
v_entries_673_ = v___x_693_;
v_currentCtx_674_ = v___x_668_;
goto v___jp_672_;
}
else
{
v_entries_673_ = v_fst_620_;
v_currentCtx_674_ = v_fst_624_;
goto v___jp_672_;
}
}
v___jp_672_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = lean_box(v_cont_671_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_fst_628_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v_currentCtx_674_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v_entries_673_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v_a_614_ = v___x_678_;
goto v___jp_613_;
}
}
else
{
lean_object* v_entries_695_; 
lean_del_object(v___x_631_);
lean_del_object(v___x_626_);
lean_del_object(v___x_622_);
if (lean_obj_tag(v_fst_624_) == 1)
{
lean_object* v_val_700_; lean_object* v___x_701_; 
v_val_700_ = lean_ctor_get(v_fst_624_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v_fst_624_, 1);
v___x_701_ = lean_array_push(v_fst_620_, v_val_700_);
v_entries_695_ = v___x_701_;
goto v___jp_694_;
}
else
{
lean_dec(v_fst_624_);
v_entries_695_ = v_fst_620_;
goto v___jp_694_;
}
v___jp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_696_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2));
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v_fst_628_);
lean_ctor_set(v___x_697_, 1, v_snd_629_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v_entries_695_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v_a_614_ = v___x_699_;
goto v___jp_613_;
}
}
v___jp_637_:
{
if (lean_obj_tag(v_fst_624_) == 0)
{
lean_object* v___x_638_; lean_object* v___x_640_; 
lean_inc(v___x_636_);
v___x_638_ = lean_array_push(v_fst_628_, v___x_636_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_638_);
v___x_640_ = v___x_631_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_snd_629_);
v___x_640_ = v_reuseFailAlloc_647_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_640_);
v___x_642_ = v___x_626_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_fst_624_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_640_);
v___x_642_ = v_reuseFailAlloc_646_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_644_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_642_);
v___x_644_ = v___x_622_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_fst_620_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
v_a_614_ = v___x_644_;
goto v___jp_613_;
}
}
}
}
else
{
lean_object* v_val_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_665_; 
v_val_648_ = lean_ctor_get(v_fst_624_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_fst_624_);
if (v_isSharedCheck_665_ == 0)
{
v___x_650_ = v_fst_624_;
v_isShared_651_ = v_isSharedCheck_665_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_val_648_);
lean_dec(v_fst_624_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_665_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_654_; 
lean_inc(v___x_636_);
v___x_652_ = lean_array_push(v_val_648_, v___x_636_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_652_);
v___x_654_ = v___x_650_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_664_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_656_; 
if (v_isShared_632_ == 0)
{
v___x_656_ = v___x_631_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_fst_628_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_snd_629_);
v___x_656_ = v_reuseFailAlloc_663_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_658_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_656_);
lean_ctor_set(v___x_626_, 0, v___x_654_);
v___x_658_ = v___x_626_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v___x_656_);
v___x_658_ = v_reuseFailAlloc_662_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_660_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_658_);
v___x_660_ = v___x_622_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_fst_620_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
v_a_614_ = v___x_660_;
goto v___jp_613_;
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
uint8_t v_skipNext_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
lean_dec(v_snd_629_);
v_skipNext_702_ = lean_nat_dec_eq(v___x_607_, v___x_633_);
v___x_703_ = lean_box(v_skipNext_702_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v___x_703_);
v___x_705_ = v___x_631_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_fst_628_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_703_);
v___x_705_ = v_reuseFailAlloc_712_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_707_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_705_);
v___x_707_ = v___x_626_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_fst_624_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_705_);
v___x_707_ = v_reuseFailAlloc_711_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_707_);
v___x_709_ = v___x_622_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_fst_620_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
v_a_614_ = v___x_709_;
goto v___jp_613_;
}
}
}
}
}
}
}
}
v___jp_613_:
{
lean_object* v___x_615_; 
v___x_615_ = lean_nat_add(v_i_610_, v_step_612_);
lean_dec(v_i_610_);
v_b_609_ = v_a_614_;
v_i_610_ = v___x_615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___boxed(lean_object* v___x_718_, lean_object* v___x_719_, lean_object* v_range_720_, lean_object* v_b_721_, lean_object* v_i_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_718_, v___x_719_, v_range_720_, v_b_721_, v_i_722_);
lean_dec_ref(v_range_720_);
lean_dec(v___x_719_);
lean_dec_ref(v___x_718_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(lean_object* v___x_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_snd_726_; lean_object* v_fst_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_784_; 
v_snd_726_ = lean_ctor_get(v_a_725_, 1);
v_fst_727_ = lean_ctor_get(v_a_725_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v_a_725_);
if (v_isSharedCheck_784_ == 0)
{
v___x_729_ = v_a_725_;
v_isShared_730_ = v_isSharedCheck_784_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_snd_726_);
lean_inc(v_fst_727_);
lean_dec(v_a_725_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_784_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v_fst_731_; lean_object* v_snd_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_783_; 
v_fst_731_ = lean_ctor_get(v_snd_726_, 0);
v_snd_732_ = lean_ctor_get(v_snd_726_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_snd_726_);
if (v_isSharedCheck_783_ == 0)
{
v___x_734_ = v_snd_726_;
v_isShared_735_ = v_isSharedCheck_783_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_snd_732_);
lean_inc(v_fst_731_);
lean_dec(v_snd_726_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_783_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
uint8_t v___x_743_; 
v___x_743_ = lean_unbox(v_snd_732_);
if (v___x_743_ == 0)
{
goto v___jp_736_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_array_get_size(v_fst_727_);
v___x_746_ = lean_nat_dec_eq(v___x_745_, v___x_744_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_del_object(v___x_734_);
lean_del_object(v___x_729_);
v___x_747_ = l_Lean_instInhabitedNamePart_default;
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_nat_sub(v___x_745_, v___x_748_);
v___x_750_ = lean_array_get_borrowed(v___x_747_, v_fst_727_, v___x_749_);
lean_dec(v___x_749_);
lean_inc(v___x_750_);
v___x_751_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_750_);
if (lean_obj_tag(v___x_751_) == 0)
{
uint8_t v_skipNext_752_; 
v_skipNext_752_ = lean_nat_dec_eq(v___x_724_, v___x_744_);
if (lean_obj_tag(v___x_750_) == 1)
{
lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_753_ = lean_unsigned_to_nat(2u);
v___x_754_ = lean_nat_dec_le(v___x_753_, v___x_745_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec(v_snd_732_);
v___x_755_ = lean_box(v___x_754_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v_fst_731_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_fst_727_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v_a_725_ = v___x_757_;
goto _start;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = lean_nat_sub(v___x_745_, v___x_753_);
v___x_760_ = lean_array_get_borrowed(v___x_747_, v_fst_727_, v___x_759_);
lean_dec(v___x_759_);
lean_inc(v___x_760_);
v___x_761_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_760_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec(v_snd_732_);
v___x_762_ = lean_box(v_skipNext_752_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v_fst_731_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v_fst_727_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v_a_725_ = v___x_764_;
goto _start;
}
else
{
lean_object* v_val_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_val_766_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v___x_761_, 1);
v___x_767_ = lean_array_push(v_fst_731_, v_val_766_);
v___x_768_ = lean_array_pop(v_fst_727_);
v___x_769_ = lean_array_pop(v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_767_);
lean_ctor_set(v___x_770_, 1, v_snd_732_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v_a_725_ = v___x_771_;
goto _start;
}
}
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v_snd_732_);
v___x_773_ = lean_box(v_skipNext_752_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_fst_731_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_fst_727_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v_a_725_ = v___x_775_;
goto _start;
}
}
else
{
lean_object* v_val_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_val_777_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_val_777_);
lean_dec_ref_known(v___x_751_, 1);
v___x_778_ = lean_array_push(v_fst_731_, v_val_777_);
v___x_779_ = lean_array_pop(v_fst_727_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v_snd_732_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v_a_725_ = v___x_781_;
goto _start;
}
}
else
{
goto v___jp_736_;
}
}
v___jp_736_:
{
lean_object* v___x_738_; 
if (v_isShared_735_ == 0)
{
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_fst_731_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_snd_732_);
v___x_738_ = v_reuseFailAlloc_742_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_740_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___x_738_);
v___x_740_ = v___x_729_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_fst_727_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg___boxed(lean_object* v___x_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_785_, v_a_786_);
lean_dec(v___x_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(lean_object* v_as_793_, size_t v_sz_794_, size_t v_i_795_, lean_object* v_b_796_){
_start:
{
lean_object* v_a_798_; uint8_t v___x_802_; 
v___x_802_ = lean_usize_dec_lt(v_i_795_, v_sz_794_);
if (v___x_802_ == 0)
{
return v_b_796_;
}
else
{
lean_object* v_a_803_; lean_object* v___y_805_; lean_object* v_name_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_a_803_ = lean_array_uget_borrowed(v_as_793_, v_i_795_);
v_name_824_ = lean_ctor_get(v_a_803_, 0);
v___x_825_ = lean_string_utf8_byte_size(v_name_824_);
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_nat_dec_eq(v___x_825_, v___x_826_);
if (v___x_827_ == 0)
{
lean_inc_ref(v_name_824_);
v___y_805_ = v_name_824_;
goto v___jp_804_;
}
else
{
lean_object* v___x_828_; 
v___x_828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_805_ = v___x_828_;
goto v___jp_804_;
}
v___jp_804_:
{
lean_object* v_flags_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_flags_806_ = lean_ctor_get(v_a_803_, 1);
v___x_807_ = lean_array_get_size(v_flags_806_);
v___x_808_ = lean_unsigned_to_nat(0u);
v___x_809_ = lean_nat_dec_eq(v___x_807_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_811_ = lean_string_append(v_b_796_, v___x_810_);
v___x_812_ = lean_string_append(v___x_811_, v___y_805_);
lean_dec_ref(v___y_805_);
v___x_813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1));
v___x_814_ = lean_string_append(v___x_812_, v___x_813_);
v___x_815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
lean_inc_ref(v_flags_806_);
v___x_816_ = lean_array_to_list(v_flags_806_);
v___x_817_ = l_String_intercalate(v___x_815_, v___x_816_);
v___x_818_ = lean_string_append(v___x_814_, v___x_817_);
lean_dec_ref(v___x_817_);
v___x_819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_820_ = lean_string_append(v___x_818_, v___x_819_);
v_a_798_ = v___x_820_;
goto v___jp_797_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_822_ = lean_string_append(v_b_796_, v___x_821_);
v___x_823_ = lean_string_append(v___x_822_, v___y_805_);
lean_dec_ref(v___y_805_);
v_a_798_ = v___x_823_;
goto v___jp_797_;
}
}
}
v___jp_797_:
{
size_t v___x_799_; size_t v___x_800_; 
v___x_799_ = ((size_t)1ULL);
v___x_800_ = lean_usize_add(v_i_795_, v___x_799_);
v_i_795_ = v___x_800_;
v_b_796_ = v_a_798_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___boxed(lean_object* v_as_829_, lean_object* v_sz_830_, lean_object* v_i_831_, lean_object* v_b_832_){
_start:
{
size_t v_sz_boxed_833_; size_t v_i_boxed_834_; lean_object* v_res_835_; 
v_sz_boxed_833_ = lean_unbox_usize(v_sz_830_);
lean_dec(v_sz_830_);
v_i_boxed_834_ = lean_unbox_usize(v_i_831_);
lean_dec(v_i_831_);
v_res_835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v_as_829_, v_sz_boxed_833_, v_i_boxed_834_, v_b_832_);
lean_dec_ref(v_as_829_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(lean_object* v_components_844_){
_start:
{
lean_object* v___y_846_; lean_object* v_result_847_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_868_; lean_object* v_parts_869_; lean_object* v_specEntries_870_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v_entries_880_; uint8_t v_skipNext_885_; 
v___x_851_ = lean_array_get_size(v_components_844_);
v___x_852_ = lean_unsigned_to_nat(0u);
v_skipNext_885_ = lean_nat_dec_eq(v___x_851_, v___x_852_);
if (v_skipNext_885_ == 0)
{
lean_object* v___x_886_; lean_object* v_fst_887_; lean_object* v_snd_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_943_; 
v___x_886_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_components_844_, v___x_852_, v___x_851_);
v_fst_887_ = lean_ctor_get(v___x_886_, 0);
v_snd_888_ = lean_ctor_get(v___x_886_, 1);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_943_ == 0)
{
v___x_890_ = v___x_886_;
v_isShared_891_ = v_isSharedCheck_943_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_snd_888_);
lean_inc(v_fst_887_);
lean_dec(v___x_886_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_943_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_parts_892_; lean_object* v_flags_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v_parts_892_ = l_Array_extract___redArg(v_components_844_, v_fst_887_, v___x_851_);
v_flags_893_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1));
v___x_894_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2));
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 1, v___x_894_);
lean_ctor_set(v___x_890_, 0, v_parts_892_);
v___x_896_ = v___x_890_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_parts_892_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v___x_894_);
v___x_896_ = v_reuseFailAlloc_942_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v_fst_898_; lean_object* v_snd_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_941_; 
v___x_897_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_851_, v___x_896_);
v_fst_898_ = lean_ctor_get(v___x_897_, 0);
v_snd_899_ = lean_ctor_get(v___x_897_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_941_ == 0)
{
v___x_901_ = v___x_897_;
v_isShared_902_ = v_isSharedCheck_941_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_snd_899_);
lean_inc(v_fst_898_);
lean_dec(v___x_897_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_941_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v_flags_904_; uint8_t v___x_936_; 
v___x_936_ = lean_unbox(v_snd_888_);
lean_dec(v_snd_888_);
if (v___x_936_ == 0)
{
lean_object* v_fst_937_; 
v_fst_937_ = lean_ctor_get(v_snd_899_, 0);
lean_inc(v_fst_937_);
lean_dec(v_snd_899_);
v_flags_904_ = v_fst_937_;
goto v___jp_903_;
}
else
{
lean_object* v_fst_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_fst_938_ = lean_ctor_get(v_snd_899_, 0);
lean_inc(v_fst_938_);
lean_dec(v_snd_899_);
v___x_939_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3));
v___x_940_ = lean_array_push(v_fst_938_, v___x_939_);
v_flags_904_ = v___x_940_;
goto v___jp_903_;
}
v___jp_903_:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_905_ = lean_array_get_size(v_fst_898_);
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_907_, 0, v___x_852_);
lean_ctor_set(v___x_907_, 1, v___x_905_);
lean_ctor_set(v___x_907_, 2, v___x_906_);
v___x_908_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_907_, v_fst_898_, v___x_852_);
lean_dec(v_fst_898_);
lean_dec_ref_known(v___x_907_, 3);
v___x_909_ = lean_box(0);
v___x_910_ = lean_array_get_size(v___x_908_);
v___x_911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_911_, 0, v___x_852_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
lean_ctor_set(v___x_911_, 2, v___x_906_);
v___x_912_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_908_, v___x_911_, v___x_909_, v___x_852_);
lean_dec_ref_known(v___x_911_, 3);
if (lean_obj_tag(v___x_912_) == 1)
{
lean_object* v_val_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v_val_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc_n(v_val_913_, 2);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = l_Array_extract___redArg(v___x_908_, v___x_852_, v_val_913_);
v___x_915_ = l_Array_extract___redArg(v___x_908_, v_val_913_, v___x_910_);
lean_dec_ref(v___x_908_);
v___x_916_ = lean_array_get_size(v___x_915_);
v___x_917_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_917_, 0, v___x_852_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
lean_ctor_set(v___x_917_, 2, v___x_906_);
v___x_918_ = lean_box(v_skipNext_885_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v___x_918_);
lean_ctor_set(v___x_901_, 0, v_flags_893_);
v___x_920_ = v___x_901_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_flags_893_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v___x_918_);
v___x_920_ = v_reuseFailAlloc_935_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_snd_924_; lean_object* v_snd_925_; lean_object* v_fst_926_; 
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_909_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_flags_893_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_915_, v___x_851_, v___x_917_, v___x_922_, v___x_852_);
lean_dec_ref_known(v___x_917_, 3);
lean_dec_ref(v___x_915_);
v_snd_924_ = lean_ctor_get(v___x_923_, 1);
v_snd_925_ = lean_ctor_get(v_snd_924_, 1);
lean_inc(v_snd_925_);
v_fst_926_ = lean_ctor_get(v_snd_924_, 0);
if (lean_obj_tag(v_fst_926_) == 1)
{
lean_object* v_fst_927_; lean_object* v_fst_928_; lean_object* v_val_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
lean_inc_ref(v_fst_926_);
v_fst_927_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_fst_927_);
lean_dec_ref(v___x_923_);
v_fst_928_ = lean_ctor_get(v_snd_925_, 0);
lean_inc(v_fst_928_);
lean_dec(v_snd_925_);
v_val_929_ = lean_ctor_get(v_fst_926_, 0);
lean_inc(v_val_929_);
lean_dec_ref_known(v_fst_926_, 1);
v___x_930_ = lean_array_get_size(v_val_929_);
v___x_931_ = lean_nat_dec_eq(v___x_930_, v___x_852_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
v___x_932_ = lean_array_push(v_fst_927_, v_val_929_);
v___y_876_ = v_flags_904_;
v___y_877_ = v___x_914_;
v___y_878_ = v_flags_893_;
v___y_879_ = v_fst_928_;
v_entries_880_ = v___x_932_;
goto v___jp_875_;
}
else
{
lean_dec(v_val_929_);
v___y_876_ = v_flags_904_;
v___y_877_ = v___x_914_;
v___y_878_ = v_flags_893_;
v___y_879_ = v_fst_928_;
v_entries_880_ = v_fst_927_;
goto v___jp_875_;
}
}
else
{
lean_object* v_fst_933_; lean_object* v_fst_934_; 
v_fst_933_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_fst_933_);
lean_dec_ref(v___x_923_);
v_fst_934_ = lean_ctor_get(v_snd_925_, 0);
lean_inc(v_fst_934_);
lean_dec(v_snd_925_);
v___y_876_ = v_flags_904_;
v___y_877_ = v___x_914_;
v___y_878_ = v_flags_893_;
v___y_879_ = v_fst_934_;
v_entries_880_ = v_fst_933_;
goto v___jp_875_;
}
}
}
else
{
lean_dec(v___x_912_);
lean_del_object(v___x_901_);
v___y_868_ = v_flags_904_;
v_parts_869_ = v___x_908_;
v_specEntries_870_ = v_flags_893_;
goto v___jp_867_;
}
}
}
}
}
}
else
{
lean_object* v___x_944_; 
v___x_944_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_944_;
}
v___jp_845_:
{
size_t v_sz_848_; size_t v___x_849_; lean_object* v___x_850_; 
v_sz_848_ = lean_array_size(v___y_846_);
v___x_849_ = ((size_t)0ULL);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v___y_846_, v_sz_848_, v___x_849_, v_result_847_);
lean_dec_ref(v___y_846_);
return v___x_850_;
}
v___jp_853_:
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = lean_array_get_size(v___y_855_);
v___x_858_ = lean_nat_dec_eq(v___x_857_, v___x_852_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_859_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0));
v___x_860_ = lean_string_append(v___y_856_, v___x_859_);
v___x_861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
v___x_862_ = lean_array_to_list(v___y_855_);
v___x_863_ = l_String_intercalate(v___x_861_, v___x_862_);
v___x_864_ = lean_string_append(v___x_860_, v___x_863_);
lean_dec_ref(v___x_863_);
v___x_865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_866_ = lean_string_append(v___x_864_, v___x_865_);
v___y_846_ = v___y_854_;
v_result_847_ = v___x_866_;
goto v___jp_845_;
}
else
{
lean_dec_ref(v___y_855_);
v___y_846_ = v___y_854_;
v_result_847_ = v___y_856_;
goto v___jp_845_;
}
}
v___jp_867_:
{
lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_871_ = lean_array_get_size(v_parts_869_);
v___x_872_ = lean_nat_dec_eq(v___x_871_, v___x_852_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_parts_869_);
lean_dec_ref(v_parts_869_);
v___y_854_ = v_specEntries_870_;
v___y_855_ = v___y_868_;
v___y_856_ = v___x_873_;
goto v___jp_853_;
}
else
{
lean_object* v___x_874_; 
lean_dec_ref(v_parts_869_);
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_854_ = v_specEntries_870_;
v___y_855_ = v___y_868_;
v___y_856_ = v___x_874_;
goto v___jp_853_;
}
}
v___jp_875_:
{
size_t v_sz_881_; size_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_sz_881_ = lean_array_size(v_entries_880_);
v___x_882_ = ((size_t)0ULL);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_851_, v_entries_880_, v_sz_881_, v___x_882_, v___y_878_);
lean_dec_ref(v_entries_880_);
v___x_884_ = l_Array_append___redArg(v___y_877_, v___y_879_);
lean_dec(v___y_879_);
v___y_868_ = v___y_876_;
v_parts_869_ = v___x_884_;
v_specEntries_870_ = v___x_883_;
goto v___jp_867_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___boxed(lean_object* v_components_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v_components_945_);
lean_dec_ref(v_components_945_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(lean_object* v___x_947_, lean_object* v_inst_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_947_, v_a_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___boxed(lean_object* v___x_951_, lean_object* v_inst_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(v___x_951_, v_inst_952_, v_a_953_);
lean_dec(v___x_951_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(lean_object* v_range_955_, lean_object* v_b_956_, lean_object* v_i_957_, lean_object* v_hs_958_, lean_object* v_hl_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v_range_955_, v_b_956_, v_i_957_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___boxed(lean_object* v_range_961_, lean_object* v_b_962_, lean_object* v_i_963_, lean_object* v_hs_964_, lean_object* v_hl_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(v_range_961_, v_b_962_, v_i_963_, v_hs_964_, v_hl_965_);
lean_dec_ref(v_b_962_);
lean_dec_ref(v_range_961_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(lean_object* v___x_967_, lean_object* v_range_968_, lean_object* v_b_969_, lean_object* v_i_970_, lean_object* v_hs_971_, lean_object* v_hl_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_967_, v_range_968_, v_b_969_, v_i_970_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___boxed(lean_object* v___x_974_, lean_object* v_range_975_, lean_object* v_b_976_, lean_object* v_i_977_, lean_object* v_hs_978_, lean_object* v_hl_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(v___x_974_, v_range_975_, v_b_976_, v_i_977_, v_hs_978_, v_hl_979_);
lean_dec(v_b_976_);
lean_dec_ref(v_range_975_);
lean_dec_ref(v___x_974_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(lean_object* v___x_981_, lean_object* v___x_982_, lean_object* v_range_983_, lean_object* v_b_984_, lean_object* v_i_985_, lean_object* v_hs_986_, lean_object* v_hl_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_981_, v___x_982_, v_range_983_, v_b_984_, v_i_985_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___boxed(lean_object* v___x_989_, lean_object* v___x_990_, lean_object* v_range_991_, lean_object* v_b_992_, lean_object* v_i_993_, lean_object* v_hs_994_, lean_object* v_hl_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(v___x_989_, v___x_990_, v_range_991_, v_b_992_, v_i_993_, v_hs_994_, v_hl_995_);
lean_dec_ref(v_range_991_);
lean_dec(v___x_990_);
lean_dec_ref(v___x_989_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(lean_object* v_body_997_){
_start:
{
lean_object* v_name_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_name_998_ = l_Lean_Name_demangle(v_body_997_);
v___x_999_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(v_name_998_);
lean_dec(v_name_998_);
v___x_1000_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v___x_999_);
lean_dec_ref(v___x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody___boxed(lean_object* v_body_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_body_1001_);
lean_dec_ref(v_body_1001_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(lean_object* v_s_1006_, lean_object* v___x_1007_, lean_object* v_a_1008_, lean_object* v_b_1009_){
_start:
{
uint8_t v_decide_1010_; 
v_decide_1010_ = lean_nat_dec_eq(v_a_1008_, v___x_1007_);
if (v_decide_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint32_t v___x_1014_; uint32_t v___x_1015_; uint8_t v___x_1016_; 
lean_dec_ref(v_b_1009_);
v___x_1011_ = lean_box(0);
v___x_1012_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1013_ = lean_string_utf8_next_fast(v_s_1006_, v_a_1008_);
v___x_1014_ = lean_string_utf8_get_fast(v_s_1006_, v_a_1008_);
v___x_1015_ = 95;
v___x_1016_ = lean_uint32_dec_eq(v___x_1014_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_dec(v_a_1008_);
v_a_1008_ = v___x_1013_;
v_b_1009_ = v___x_1012_;
goto _start;
}
else
{
lean_object* v___x_1018_; uint8_t v_decide_1019_; 
v___x_1018_ = lean_unsigned_to_nat(0u);
v_decide_1019_ = lean_nat_dec_eq(v_a_1008_, v___x_1018_);
if (v_decide_1019_ == 0)
{
if (v___x_1016_ == 0)
{
lean_dec(v_a_1008_);
v_a_1008_ = v___x_1013_;
v_b_1009_ = v___x_1012_;
goto _start;
}
else
{
lean_object* v___x_1021_; uint8_t v_decide_1022_; 
v___x_1021_ = lean_string_utf8_byte_size(v_s_1006_);
v_decide_1022_ = lean_nat_dec_eq(v___x_1013_, v___x_1021_);
if (v_decide_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_string_utf8_extract_fast(v_s_1006_, v___x_1018_, v_a_1008_);
lean_dec(v_a_1008_);
v___x_1024_ = l_Lean_Name_demangle_x3f(v___x_1023_);
if (lean_obj_tag(v___x_1024_) == 1)
{
lean_object* v_val_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1047_; 
v_val_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1047_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_val_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1047_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
if (lean_obj_tag(v_val_1025_) == 1)
{
lean_object* v_pre_1029_; 
v_pre_1029_ = lean_ctor_get(v_val_1025_, 0);
lean_inc(v_pre_1029_);
lean_dec_ref_known(v_val_1025_, 2);
if (lean_obj_tag(v_pre_1029_) == 0)
{
lean_object* v___x_1030_; lean_object* v___y_1032_; lean_object* v___x_1040_; 
v___x_1030_ = lean_string_utf8_extract_fast(v_s_1006_, v___x_1013_, v___x_1021_);
v___x_1040_ = l_Lean_Name_demangle_x3f(v___x_1030_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_dec_ref(v___x_1030_);
lean_del_object(v___x_1027_);
lean_dec_ref(v___x_1023_);
v_a_1008_ = v___x_1013_;
v_b_1009_ = v___x_1012_;
goto _start;
}
else
{
lean_object* v___x_1042_; 
lean_dec_ref_known(v___x_1040_, 1);
v___x_1042_ = l_Lean_Name_demangle(v___x_1023_);
if (lean_obj_tag(v___x_1042_) == 1)
{
lean_object* v_pre_1043_; 
v_pre_1043_ = lean_ctor_get(v___x_1042_, 0);
if (lean_obj_tag(v_pre_1043_) == 0)
{
lean_object* v_str_1044_; 
lean_dec_ref(v___x_1023_);
v_str_1044_ = lean_ctor_get(v___x_1042_, 1);
lean_inc_ref(v_str_1044_);
lean_dec_ref_known(v___x_1042_, 2);
v___y_1032_ = v_str_1044_;
goto v___jp_1031_;
}
else
{
lean_dec_ref_known(v___x_1042_, 2);
v___y_1032_ = v___x_1023_;
goto v___jp_1031_;
}
}
else
{
lean_dec(v___x_1042_);
v___y_1032_ = v___x_1023_;
goto v___jp_1031_;
}
}
v___jp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1033_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v___x_1030_);
lean_dec_ref(v___x_1030_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v___y_1032_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1034_);
v___x_1036_ = v___x_1027_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_1011_);
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
return v___x_1038_;
}
}
}
else
{
lean_dec(v_pre_1029_);
lean_del_object(v___x_1027_);
lean_dec_ref(v___x_1023_);
v_a_1008_ = v___x_1013_;
v_b_1009_ = v___x_1012_;
goto _start;
}
}
else
{
lean_del_object(v___x_1027_);
lean_dec(v_val_1025_);
lean_dec_ref(v___x_1023_);
v_a_1008_ = v___x_1013_;
v_b_1009_ = v___x_1012_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1024_);
lean_dec_ref(v___x_1023_);
v_a_1008_ = v___x_1013_;
v_b_1009_ = v___x_1012_;
goto _start;
}
}
else
{
lean_dec(v_a_1008_);
v_a_1008_ = v___x_1013_;
v_b_1009_ = v___x_1012_;
goto _start;
}
}
}
else
{
lean_dec(v_a_1008_);
v_a_1008_ = v___x_1013_;
v_b_1009_ = v___x_1012_;
goto _start;
}
}
}
else
{
lean_object* v___x_1051_; 
lean_dec(v_a_1008_);
v___x_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1051_, 0, v_b_1009_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___boxed(lean_object* v_s_1052_, lean_object* v___x_1053_, lean_object* v_a_1054_, lean_object* v_b_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1052_, v___x_1053_, v_a_1054_, v_b_1055_);
lean_dec(v___x_1053_);
lean_dec_ref(v_s_1052_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(lean_object* v_s_1057_){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1059_ = lean_string_utf8_byte_size(v_s_1057_);
v___x_1060_ = lean_box(0);
v___x_1061_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1062_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1057_, v___x_1059_, v___x_1058_, v___x_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
return v___x_1060_;
}
else
{
lean_object* v_val_1063_; lean_object* v_fst_1064_; 
v_val_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_val_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v_fst_1064_ = lean_ctor_get(v_val_1063_, 0);
lean_inc(v_fst_1064_);
lean_dec(v_val_1063_);
if (lean_obj_tag(v_fst_1064_) == 0)
{
return v___x_1060_;
}
else
{
return v_fst_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg___boxed(lean_object* v_s_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_s_1065_);
lean_dec_ref(v_s_1065_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(lean_object* v_s_1067_, lean_object* v___x_1068_, lean_object* v___x_1069_, lean_object* v_inst_1070_, lean_object* v_R_1071_, lean_object* v_a_1072_, lean_object* v_b_1073_, lean_object* v_c_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1067_, v___x_1068_, v_a_1072_, v_b_1073_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___boxed(lean_object* v_s_1076_, lean_object* v___x_1077_, lean_object* v___x_1078_, lean_object* v_inst_1079_, lean_object* v_R_1080_, lean_object* v_a_1081_, lean_object* v_b_1082_, lean_object* v_c_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(v_s_1076_, v___x_1077_, v___x_1078_, v_inst_1079_, v_R_1080_, v_a_1081_, v_b_1082_, v_c_1083_);
lean_dec_ref(v___x_1078_);
lean_dec(v___x_1077_);
lean_dec_ref(v_s_1076_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(lean_object* v_s_1085_, lean_object* v___x_1086_, lean_object* v___x_1087_, lean_object* v_a_1088_, lean_object* v_b_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_box(0);
switch(lean_obj_tag(v_a_1088_))
{
case 0:
{
lean_object* v_pos_1091_; lean_object* v___x_1092_; 
v_pos_1091_ = lean_ctor_get(v_a_1088_, 0);
lean_inc(v_pos_1091_);
lean_dec_ref_known(v_a_1088_, 1);
v___x_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_pos_1091_);
return v___x_1092_;
}
case 1:
{
lean_object* v_pos_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1102_; 
v_pos_1093_ = lean_ctor_get(v_a_1088_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_a_1088_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1095_ = v_a_1088_;
v_isShared_1096_ = v_isSharedCheck_1102_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_pos_1093_);
lean_dec(v_a_1088_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1102_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = lean_string_utf8_next_fast(v_s_1085_, v_pos_1093_);
lean_dec(v_pos_1093_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1097_);
v___x_1099_ = v___x_1095_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
v_a_1088_ = v___x_1099_;
v_b_1089_ = v___x_1090_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1103_; lean_object* v_table_1104_; lean_object* v_stackPos_1105_; lean_object* v_needlePos_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1159_; 
v_needle_1103_ = lean_ctor_get(v_a_1088_, 0);
v_table_1104_ = lean_ctor_get(v_a_1088_, 1);
v_stackPos_1105_ = lean_ctor_get(v_a_1088_, 2);
v_needlePos_1106_ = lean_ctor_get(v_a_1088_, 3);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_a_1088_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1108_ = v_a_1088_;
v_isShared_1109_ = v_isSharedCheck_1159_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_needlePos_1106_);
lean_inc(v_stackPos_1105_);
lean_inc(v_table_1104_);
lean_inc(v_needle_1103_);
lean_dec(v_a_1088_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1159_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_str_1110_; lean_object* v_startInclusive_1111_; lean_object* v_endExclusive_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_str_1110_ = lean_ctor_get(v_needle_1103_, 0);
v_startInclusive_1111_ = lean_ctor_get(v_needle_1103_, 1);
v_endExclusive_1112_ = lean_ctor_get(v_needle_1103_, 2);
v___x_1113_ = lean_nat_sub(v_stackPos_1105_, v_needlePos_1106_);
v___x_1114_ = lean_nat_sub(v_endExclusive_1112_, v_startInclusive_1111_);
v___x_1115_ = lean_nat_add(v___x_1113_, v___x_1114_);
v___x_1116_ = lean_nat_dec_le(v___x_1115_, v___x_1087_);
lean_dec(v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
lean_dec(v___x_1114_);
lean_del_object(v___x_1108_);
lean_dec(v_needlePos_1106_);
lean_dec(v_stackPos_1105_);
lean_dec_ref(v_table_1104_);
lean_dec_ref(v_needle_1103_);
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_add(v___x_1113_, v___x_1117_);
lean_dec(v___x_1113_);
v___x_1119_ = lean_nat_dec_le(v___x_1118_, v___x_1087_);
lean_dec(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_inc(v_b_1089_);
return v_b_1089_;
}
else
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_box(3);
v_a_1088_ = v___x_1120_;
v_b_1089_ = v___x_1090_;
goto _start;
}
}
else
{
uint8_t v_stackByte_1122_; lean_object* v___x_1123_; uint8_t v_patByte_1124_; uint8_t v___x_1125_; 
lean_dec(v___x_1113_);
lean_inc(v_stackPos_1105_);
v_stackByte_1122_ = lean_string_get_byte_fast(v_s_1085_, v_stackPos_1105_);
v___x_1123_ = lean_nat_add(v_startInclusive_1111_, v_needlePos_1106_);
v_patByte_1124_ = lean_string_get_byte_fast(v_str_1110_, v___x_1123_);
v___x_1125_ = lean_uint8_dec_eq(v_stackByte_1122_, v_patByte_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; uint8_t v_decide_1127_; 
lean_dec(v___x_1114_);
v___x_1126_ = lean_unsigned_to_nat(0u);
v_decide_1127_ = lean_nat_dec_eq(v_needlePos_1106_, v___x_1126_);
if (v_decide_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v_newNeedlePos_1130_; uint8_t v___x_1131_; 
v___x_1128_ = lean_unsigned_to_nat(1u);
v___x_1129_ = lean_nat_sub(v_needlePos_1106_, v___x_1128_);
lean_dec(v_needlePos_1106_);
v_newNeedlePos_1130_ = lean_array_fget_borrowed(v_table_1104_, v___x_1129_);
lean_dec(v___x_1129_);
v___x_1131_ = lean_nat_dec_eq(v_newNeedlePos_1130_, v___x_1126_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1133_; 
lean_inc(v_newNeedlePos_1130_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 3, v_newNeedlePos_1130_);
v___x_1133_ = v___x_1108_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_needle_1103_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_table_1104_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_stackPos_1105_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_newNeedlePos_1130_);
v___x_1133_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
v_a_1088_ = v___x_1133_;
v_b_1089_ = v___x_1090_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1136_; lean_object* v___x_1138_; 
v_nextStackPos_1136_ = l_String_Slice_posGE___redArg(v___x_1086_, v_stackPos_1105_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 3, v___x_1126_);
lean_ctor_set(v___x_1108_, 2, v_nextStackPos_1136_);
v___x_1138_ = v___x_1108_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_needle_1103_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_table_1104_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_nextStackPos_1136_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v___x_1126_);
v___x_1138_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
v_a_1088_ = v___x_1138_;
v_b_1089_ = v___x_1090_;
goto _start;
}
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v_nextStackPos_1143_; lean_object* v___x_1145_; 
lean_dec(v_needlePos_1106_);
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_nat_add(v_stackPos_1105_, v___x_1141_);
lean_dec(v_stackPos_1105_);
v_nextStackPos_1143_ = l_String_Slice_posGE___redArg(v___x_1086_, v___x_1142_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 3, v___x_1126_);
lean_ctor_set(v___x_1108_, 2, v_nextStackPos_1143_);
v___x_1145_ = v___x_1108_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_needle_1103_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_table_1104_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_nextStackPos_1143_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v___x_1126_);
v___x_1145_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
v_a_1088_ = v___x_1145_;
v_b_1089_ = v___x_1090_;
goto _start;
}
}
}
else
{
lean_object* v___x_1148_; lean_object* v_nextStackPos_1149_; lean_object* v_nextNeedlePos_1150_; uint8_t v_decide_1151_; 
v___x_1148_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1149_ = lean_nat_add(v_stackPos_1105_, v___x_1148_);
lean_dec(v_stackPos_1105_);
v_nextNeedlePos_1150_ = lean_nat_add(v_needlePos_1106_, v___x_1148_);
lean_dec(v_needlePos_1106_);
v_decide_1151_ = lean_nat_dec_eq(v_nextNeedlePos_1150_, v___x_1114_);
lean_dec(v___x_1114_);
if (v_decide_1151_ == 0)
{
lean_object* v___x_1153_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 3, v_nextNeedlePos_1150_);
lean_ctor_set(v___x_1108_, 2, v_nextStackPos_1149_);
v___x_1153_ = v___x_1108_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_needle_1103_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_table_1104_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_nextStackPos_1149_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v_nextNeedlePos_1150_);
v___x_1153_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
v_a_1088_ = v___x_1153_;
goto _start;
}
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_del_object(v___x_1108_);
lean_dec_ref(v_table_1104_);
lean_dec_ref(v_needle_1103_);
v___x_1156_ = lean_nat_sub(v_nextStackPos_1149_, v_nextNeedlePos_1150_);
lean_dec(v_nextNeedlePos_1150_);
lean_dec(v_nextStackPos_1149_);
v___x_1157_ = l_String_Slice_pos_x21(v___x_1086_, v___x_1156_);
lean_dec(v___x_1156_);
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
}
}
}
default: 
{
lean_inc(v_b_1089_);
return v_b_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg___boxed(lean_object* v_s_1160_, lean_object* v___x_1161_, lean_object* v___x_1162_, lean_object* v_a_1163_, lean_object* v_b_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1160_, v___x_1161_, v___x_1162_, v_a_1163_, v_b_1164_);
lean_dec(v_b_1164_);
lean_dec(v___x_1162_);
lean_dec_ref(v___x_1161_);
lean_dec_ref(v_s_1160_);
return v_res_1165_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1));
v___x_1172_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1171_);
return v___x_1172_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2);
v___x_1175_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1));
v___x_1176_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v___x_1174_);
lean_ctor_set(v___x_1176_, 2, v___x_1173_);
lean_ctor_set(v___x_1176_, 3, v___x_1173_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(lean_object* v_s_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1178_ = lean_unsigned_to_nat(0u);
v___x_1179_ = lean_string_utf8_byte_size(v_s_1177_);
lean_inc_ref(v_s_1177_);
v___x_1180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1180_, 0, v_s_1177_);
lean_ctor_set(v___x_1180_, 1, v___x_1178_);
lean_ctor_set(v___x_1180_, 2, v___x_1179_);
v___x_1181_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
v___x_1182_ = lean_box(0);
v___x_1183_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1177_, v___x_1180_, v___x_1179_, v___x_1181_, v___x_1182_);
lean_dec_ref_known(v___x_1180_, 3);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v_s_1177_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
return v___x_1185_;
}
else
{
lean_object* v_val_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_val_1186_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_val_1186_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1187_ = lean_string_utf8_extract_fast(v_s_1177_, v___x_1178_, v_val_1186_);
v___x_1188_ = lean_string_utf8_extract_fast(v_s_1177_, v_val_1186_, v___x_1179_);
lean_dec(v_val_1186_);
lean_dec_ref(v_s_1177_);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(lean_object* v_s_1190_, lean_object* v___x_1191_, lean_object* v___x_1192_, lean_object* v_inst_1193_, lean_object* v_R_1194_, lean_object* v_a_1195_, lean_object* v_b_1196_, lean_object* v_c_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1190_, v___x_1191_, v___x_1192_, v_a_1195_, v_b_1196_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___boxed(lean_object* v_s_1199_, lean_object* v___x_1200_, lean_object* v___x_1201_, lean_object* v_inst_1202_, lean_object* v_R_1203_, lean_object* v_a_1204_, lean_object* v_b_1205_, lean_object* v_c_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(v_s_1199_, v___x_1200_, v___x_1201_, v_inst_1202_, v_R_1203_, v_a_1204_, v_b_1205_, v_c_1206_);
lean_dec(v_b_1205_);
lean_dec(v___x_1201_);
lean_dec_ref(v___x_1200_);
lean_dec_ref(v_s_1199_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(lean_object* v_s_1219_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10));
lean_inc_ref(v_s_1219_);
v___x_1336_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1219_, v___x_1335_);
if (lean_obj_tag(v___x_1336_) == 1)
{
lean_object* v_val_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1350_; 
v_val_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1350_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_val_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1350_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1341_ = lean_string_utf8_byte_size(v_val_1337_);
v___x_1342_ = lean_unsigned_to_nat(0u);
v___x_1343_ = lean_nat_dec_eq(v___x_1341_, v___x_1342_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
lean_dec_ref(v_s_1219_);
v___x_1344_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1345_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1337_);
lean_dec(v_val_1337_);
v___x_1346_ = lean_string_append(v___x_1344_, v___x_1345_);
lean_dec_ref(v___x_1345_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1346_);
v___x_1348_ = v___x_1339_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
else
{
lean_del_object(v___x_1339_);
lean_dec(v_val_1337_);
goto v___jp_1313_;
}
}
}
else
{
lean_dec(v___x_1336_);
goto v___jp_1313_;
}
v___jp_1220_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0));
v___x_1222_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1219_, v___x_1221_);
if (lean_obj_tag(v___x_1222_) == 1)
{
lean_object* v_val_1223_; lean_object* v___x_1224_; 
v_val_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_val_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v___x_1224_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1223_);
lean_dec(v_val_1223_);
if (lean_obj_tag(v___x_1224_) == 1)
{
lean_object* v_val_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1239_; 
v_val_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1239_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_val_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1239_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_fst_1229_; lean_object* v_snd_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v_fst_1229_ = lean_ctor_get(v_val_1225_, 0);
lean_inc(v_fst_1229_);
v_snd_1230_ = lean_ctor_get(v_val_1225_, 1);
lean_inc(v_snd_1230_);
lean_dec(v_val_1225_);
v___x_1231_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1232_ = lean_string_append(v_fst_1229_, v___x_1231_);
v___x_1233_ = lean_string_append(v___x_1232_, v_snd_1230_);
lean_dec(v_snd_1230_);
v___x_1234_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1235_ = lean_string_append(v___x_1233_, v___x_1234_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1235_);
v___x_1237_ = v___x_1227_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
else
{
lean_object* v___x_1240_; 
lean_dec(v___x_1224_);
v___x_1240_ = lean_box(0);
return v___x_1240_;
}
}
else
{
lean_object* v___x_1241_; 
lean_dec(v___x_1222_);
v___x_1241_ = lean_box(0);
return v___x_1241_;
}
}
v___jp_1242_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3));
lean_inc_ref(v_s_1219_);
v___x_1244_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1219_, v___x_1243_);
if (lean_obj_tag(v___x_1244_) == 1)
{
lean_object* v_val_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1256_; 
v_val_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1256_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_val_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1256_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1249_ = lean_string_utf8_byte_size(v_val_1245_);
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_nat_dec_eq(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
lean_dec_ref(v_s_1219_);
v___x_1252_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1245_);
lean_dec(v_val_1245_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1252_);
v___x_1254_ = v___x_1247_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
else
{
lean_del_object(v___x_1247_);
lean_dec(v_val_1245_);
goto v___jp_1220_;
}
}
}
else
{
lean_dec(v___x_1244_);
goto v___jp_1220_;
}
}
v___jp_1257_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4));
lean_inc_ref(v_s_1219_);
v___x_1259_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1219_, v___x_1258_);
if (lean_obj_tag(v___x_1259_) == 1)
{
lean_object* v_val_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1273_; 
v_val_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1273_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_val_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1273_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1264_ = lean_string_utf8_byte_size(v_val_1260_);
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = lean_nat_dec_eq(v___x_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
lean_dec_ref(v_s_1219_);
v___x_1267_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1268_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1260_);
lean_dec(v_val_1260_);
v___x_1269_ = lean_string_append(v___x_1267_, v___x_1268_);
lean_dec_ref(v___x_1268_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1269_);
v___x_1271_ = v___x_1262_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
else
{
lean_del_object(v___x_1262_);
lean_dec(v_val_1260_);
goto v___jp_1242_;
}
}
}
else
{
lean_dec(v___x_1259_);
goto v___jp_1242_;
}
}
v___jp_1274_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6));
lean_inc_ref(v_s_1219_);
v___x_1276_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1219_, v___x_1275_);
if (lean_obj_tag(v___x_1276_) == 1)
{
lean_object* v_val_1277_; lean_object* v___x_1278_; 
v_val_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_val_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1278_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1277_);
lean_dec(v_val_1277_);
if (lean_obj_tag(v___x_1278_) == 1)
{
lean_object* v_val_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_s_1219_);
v_val_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1295_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_val_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1295_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_fst_1283_; lean_object* v_snd_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v_fst_1283_ = lean_ctor_get(v_val_1279_, 0);
lean_inc(v_fst_1283_);
v_snd_1284_ = lean_ctor_get(v_val_1279_, 1);
lean_inc(v_snd_1284_);
lean_dec(v_val_1279_);
v___x_1285_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1286_ = lean_string_append(v___x_1285_, v_fst_1283_);
lean_dec(v_fst_1283_);
v___x_1287_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1288_ = lean_string_append(v___x_1286_, v___x_1287_);
v___x_1289_ = lean_string_append(v___x_1288_, v_snd_1284_);
lean_dec(v_snd_1284_);
v___x_1290_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1291_ = lean_string_append(v___x_1289_, v___x_1290_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1291_);
v___x_1293_ = v___x_1281_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
lean_dec(v___x_1278_);
goto v___jp_1257_;
}
}
else
{
lean_dec(v___x_1276_);
goto v___jp_1257_;
}
}
v___jp_1296_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7));
lean_inc_ref(v_s_1219_);
v___x_1298_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1219_, v___x_1297_);
if (lean_obj_tag(v___x_1298_) == 1)
{
lean_object* v_val_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1312_; 
v_val_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1312_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_val_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1312_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1303_ = lean_string_utf8_byte_size(v_val_1299_);
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_nat_dec_eq(v___x_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
lean_dec_ref(v_s_1219_);
v___x_1306_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1307_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1299_);
lean_dec(v_val_1299_);
v___x_1308_ = lean_string_append(v___x_1306_, v___x_1307_);
lean_dec_ref(v___x_1307_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1308_);
v___x_1310_ = v___x_1301_;
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
else
{
lean_del_object(v___x_1301_);
lean_dec(v_val_1299_);
goto v___jp_1274_;
}
}
}
else
{
lean_dec(v___x_1298_);
goto v___jp_1274_;
}
}
v___jp_1313_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8));
lean_inc_ref(v_s_1219_);
v___x_1315_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1219_, v___x_1314_);
if (lean_obj_tag(v___x_1315_) == 1)
{
lean_object* v_val_1316_; lean_object* v___x_1317_; 
v_val_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_val_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v___x_1317_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1316_);
lean_dec(v_val_1316_);
if (lean_obj_tag(v___x_1317_) == 1)
{
lean_object* v_val_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_s_1219_);
v_val_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1334_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_val_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1334_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v_fst_1322_; lean_object* v_snd_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v_fst_1322_ = lean_ctor_get(v_val_1318_, 0);
lean_inc(v_fst_1322_);
v_snd_1323_ = lean_ctor_get(v_val_1318_, 1);
lean_inc(v_snd_1323_);
lean_dec(v_val_1318_);
v___x_1324_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1325_ = lean_string_append(v___x_1324_, v_fst_1322_);
lean_dec(v_fst_1322_);
v___x_1326_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1327_ = lean_string_append(v___x_1325_, v___x_1326_);
v___x_1328_ = lean_string_append(v___x_1327_, v_snd_1323_);
lean_dec(v_snd_1323_);
v___x_1329_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1330_ = lean_string_append(v___x_1328_, v___x_1329_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1330_);
v___x_1332_ = v___x_1320_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
lean_dec(v___x_1317_);
goto v___jp_1296_;
}
}
else
{
lean_dec(v___x_1315_);
goto v___jp_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleSymbol(lean_object* v_symbol_1360_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1361_ = lean_string_utf8_byte_size(v_symbol_1360_);
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = lean_nat_dec_eq(v___x_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v_fst_1365_; lean_object* v_snd_1366_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1364_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(v_symbol_1360_);
v_fst_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc_n(v_fst_1365_, 2);
v_snd_1366_ = lean_ctor_get(v___x_1364_, 1);
lean_inc(v_snd_1366_);
lean_dec_ref(v___x_1364_);
v___x_1391_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__5));
v___x_1392_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_fst_1365_, v___x_1391_);
if (lean_obj_tag(v___x_1392_) == 1)
{
lean_object* v_val_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1413_; 
v_val_1393_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1395_ = v___x_1392_;
v_isShared_1396_ = v_isSharedCheck_1413_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_val_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1413_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
uint8_t v___x_1397_; 
lean_inc(v_val_1393_);
v___x_1397_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_1393_);
if (v___x_1397_ == 0)
{
lean_del_object(v___x_1395_);
lean_dec(v_val_1393_);
goto v___jp_1367_;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v_r_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
lean_dec(v_fst_1365_);
v___x_1398_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__6));
v___x_1399_ = lean_string_append(v___x_1398_, v_val_1393_);
lean_dec(v_val_1393_);
v___x_1400_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__7));
v_r_1401_ = lean_string_append(v___x_1399_, v___x_1400_);
v___x_1402_ = lean_string_utf8_byte_size(v_snd_1366_);
v___x_1403_ = lean_nat_dec_eq(v___x_1402_, v___x_1362_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1404_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1405_ = lean_string_append(v_r_1401_, v___x_1404_);
v___x_1406_ = lean_string_append(v___x_1405_, v_snd_1366_);
lean_dec(v_snd_1366_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1406_);
v___x_1408_ = v___x_1395_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
else
{
lean_object* v___x_1411_; 
lean_dec(v_snd_1366_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v_r_1401_);
v___x_1411_ = v___x_1395_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_r_1401_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
else
{
lean_dec(v___x_1392_);
goto v___jp_1367_;
}
v___jp_1367_:
{
lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__0));
v___x_1369_ = lean_string_dec_eq(v_fst_1365_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
v___x_1370_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(v_fst_1365_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_dec(v_snd_1366_);
return v___x_1370_;
}
else
{
lean_object* v_val_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_val_1371_ = lean_ctor_get(v___x_1370_, 0);
v___x_1372_ = lean_string_utf8_byte_size(v_snd_1366_);
v___x_1373_ = lean_nat_dec_eq(v___x_1372_, v___x_1362_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1383_; 
lean_inc(v_val_1371_);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; 
v_unused_1384_ = lean_ctor_get(v___x_1370_, 0);
lean_dec(v_unused_1384_);
v___x_1375_ = v___x_1370_;
v_isShared_1376_ = v_isSharedCheck_1383_;
goto v_resetjp_1374_;
}
else
{
lean_dec(v___x_1370_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1383_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1377_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1378_ = lean_string_append(v_val_1371_, v___x_1377_);
v___x_1379_ = lean_string_append(v___x_1378_, v_snd_1366_);
lean_dec(v_snd_1366_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1379_);
v___x_1381_ = v___x_1375_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
else
{
lean_dec(v_snd_1366_);
return v___x_1370_;
}
}
}
else
{
lean_object* v___x_1385_; uint8_t v___x_1386_; 
lean_dec(v_fst_1365_);
v___x_1385_ = lean_string_utf8_byte_size(v_snd_1366_);
v___x_1386_ = lean_nat_dec_eq(v___x_1385_, v___x_1362_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__2));
v___x_1388_ = lean_string_append(v___x_1387_, v_snd_1366_);
lean_dec(v_snd_1366_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
else
{
lean_object* v___x_1390_; 
lean_dec(v_snd_1366_);
v___x_1390_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__4));
return v___x_1390_;
}
}
}
}
else
{
lean_object* v___x_1414_; 
lean_dec_ref(v_symbol_1360_);
v___x_1414_ = lean_box(0);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(lean_object* v_s_1415_, lean_object* v_pos_1416_, lean_object* v_pred_1417_){
_start:
{
lean_object* v___x_1418_; uint8_t v_decide_1419_; 
v___x_1418_ = lean_string_utf8_byte_size(v_s_1415_);
v_decide_1419_ = lean_nat_dec_eq(v_pos_1416_, v___x_1418_);
if (v_decide_1419_ == 0)
{
uint32_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1420_ = lean_string_utf8_get_fast(v_s_1415_, v_pos_1416_);
v___x_1421_ = lean_box_uint32(v___x_1420_);
lean_inc_ref(v_pred_1417_);
v___x_1422_ = lean_apply_1(v_pred_1417_, v___x_1421_);
v___x_1423_ = lean_unbox(v___x_1422_);
if (v___x_1423_ == 0)
{
lean_dec_ref(v_pred_1417_);
return v_pos_1416_;
}
else
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_string_utf8_next_fast(v_s_1415_, v_pos_1416_);
lean_dec(v_pos_1416_);
v_pos_1416_ = v___x_1424_;
goto _start;
}
}
else
{
lean_dec_ref(v_pred_1417_);
return v_pos_1416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile___boxed(lean_object* v_s_1426_, lean_object* v_pos_1427_, lean_object* v_pred_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_s_1426_, v_pos_1427_, v_pred_1428_);
lean_dec_ref(v_s_1426_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(lean_object* v_s_1430_, lean_object* v_p_u2081_1431_, lean_object* v_p_u2082_1432_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1433_ = lean_unsigned_to_nat(0u);
v___x_1434_ = lean_string_utf8_extract_fast(v_s_1430_, v___x_1433_, v_p_u2081_1431_);
v___x_1435_ = lean_string_utf8_extract_fast(v_s_1430_, v_p_u2081_1431_, v_p_u2082_1432_);
v___x_1436_ = lean_string_utf8_byte_size(v_s_1430_);
v___x_1437_ = lean_string_utf8_extract_fast(v_s_1430_, v_p_u2082_1432_, v___x_1436_);
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1435_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1434_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082___boxed(lean_object* v_s_1440_, lean_object* v_p_u2081_1441_, lean_object* v_p_u2082_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_s_1440_, v_p_u2081_1441_, v_p_u2082_1442_);
lean_dec(v_p_u2082_1442_);
lean_dec(v_p_u2081_1441_);
lean_dec_ref(v_s_1440_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(lean_object* v___x_1444_, lean_object* v___x_1445_, lean_object* v_line_1446_, lean_object* v_a_1447_, lean_object* v_b_1448_){
_start:
{
lean_object* v___x_1449_; uint8_t v_decide_1450_; 
v___x_1449_ = lean_nat_sub(v___x_1444_, v___x_1445_);
v_decide_1450_ = lean_nat_dec_eq(v_a_1447_, v___x_1449_);
lean_dec(v___x_1449_);
if (v_decide_1450_ == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___y_1454_; uint32_t v___x_1459_; uint32_t v___x_1460_; uint8_t v___x_1461_; 
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_nat_add(v___x_1445_, v_a_1447_);
v___x_1459_ = lean_string_utf8_get_fast(v_line_1446_, v___x_1452_);
v___x_1460_ = 43;
v___x_1461_ = lean_uint32_dec_eq(v___x_1459_, v___x_1460_);
if (v___x_1461_ == 0)
{
uint32_t v___x_1462_; uint8_t v___x_1463_; 
v___x_1462_ = 41;
v___x_1463_ = lean_uint32_dec_eq(v___x_1459_, v___x_1462_);
v___y_1454_ = v___x_1463_;
goto v___jp_1453_;
}
else
{
v___y_1454_ = v___x_1461_;
goto v___jp_1453_;
}
v___jp_1453_:
{
if (v___y_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec(v_a_1447_);
v___x_1455_ = lean_string_utf8_next_fast(v_line_1446_, v___x_1452_);
lean_dec(v___x_1452_);
v___x_1456_ = lean_nat_sub(v___x_1455_, v___x_1445_);
v_a_1447_ = v___x_1456_;
v_b_1448_ = v___x_1451_;
goto _start;
}
else
{
lean_object* v___x_1458_; 
lean_dec(v___x_1452_);
v___x_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1458_, 0, v_a_1447_);
return v___x_1458_;
}
}
}
else
{
lean_dec(v_a_1447_);
lean_inc(v_b_1448_);
return v_b_1448_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg___boxed(lean_object* v___x_1464_, lean_object* v___x_1465_, lean_object* v_line_1466_, lean_object* v_a_1467_, lean_object* v_b_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1464_, v___x_1465_, v_line_1466_, v_a_1467_, v_b_1468_);
lean_dec(v_b_1468_);
lean_dec_ref(v_line_1466_);
lean_dec(v___x_1465_);
lean_dec(v___x_1464_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(lean_object* v___x_1470_, lean_object* v_line_1471_, lean_object* v_a_1472_, lean_object* v_b_1473_){
_start:
{
uint8_t v_decide_1474_; 
v_decide_1474_ = lean_nat_dec_eq(v_a_1472_, v___x_1470_);
if (v_decide_1474_ == 0)
{
uint32_t v___x_1475_; uint32_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1475_ = lean_string_utf8_get_fast(v_line_1471_, v_a_1472_);
v___x_1476_ = 40;
v___x_1477_ = lean_uint32_dec_eq(v___x_1475_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_box(0);
v___x_1479_ = lean_string_utf8_next_fast(v_line_1471_, v_a_1472_);
lean_dec(v_a_1472_);
v_a_1472_ = v___x_1479_;
v_b_1473_ = v___x_1478_;
goto _start;
}
else
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_a_1472_);
return v___x_1481_;
}
}
else
{
lean_dec(v_a_1472_);
lean_inc(v_b_1473_);
return v_b_1473_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg___boxed(lean_object* v___x_1482_, lean_object* v_line_1483_, lean_object* v_a_1484_, lean_object* v_b_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1482_, v_line_1483_, v_a_1484_, v_b_1485_);
lean_dec(v_b_1485_);
lean_dec_ref(v_line_1483_);
lean_dec(v___x_1482_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(lean_object* v_line_1487_){
_start:
{
lean_object* v_searcher_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_searcher_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_string_utf8_byte_size(v_line_1487_);
v___x_1490_ = lean_box(0);
v___x_1491_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1489_, v_line_1487_, v_searcher_1488_, v___x_1490_);
if (lean_obj_tag(v___x_1491_) == 0)
{
return v___x_1490_;
}
else
{
lean_object* v_val_1492_; uint8_t v_decide_1493_; 
v_val_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v_decide_1493_ = lean_nat_dec_eq(v_val_1492_, v___x_1489_);
if (v_decide_1493_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_string_utf8_next_fast(v_line_1487_, v_val_1492_);
lean_dec(v_val_1492_);
v___x_1495_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1489_, v___x_1494_, v_line_1487_, v_searcher_1488_, v___x_1490_);
if (lean_obj_tag(v___x_1495_) == 0)
{
return v___x_1490_;
}
else
{
lean_object* v_val_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1506_; 
v_val_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1506_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_val_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1506_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; uint8_t v_decide_1501_; 
v___x_1500_ = lean_nat_add(v___x_1494_, v_val_1496_);
lean_dec(v_val_1496_);
v_decide_1501_ = lean_nat_dec_eq(v___x_1500_, v___x_1494_);
if (v_decide_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1502_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1487_, v___x_1494_, v___x_1500_);
lean_dec(v___x_1500_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1502_);
v___x_1504_ = v___x_1498_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
else
{
lean_dec(v___x_1500_);
lean_del_object(v___x_1498_);
return v___x_1490_;
}
}
}
}
else
{
lean_dec(v_val_1492_);
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux___boxed(lean_object* v_line_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(v_line_1507_);
lean_dec_ref(v_line_1507_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(lean_object* v___x_1509_, lean_object* v___x_1510_, lean_object* v_line_1511_, lean_object* v_inst_1512_, lean_object* v_R_1513_, lean_object* v_a_1514_, lean_object* v_b_1515_, lean_object* v_c_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1509_, v_line_1511_, v_a_1514_, v_b_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___boxed(lean_object* v___x_1518_, lean_object* v___x_1519_, lean_object* v_line_1520_, lean_object* v_inst_1521_, lean_object* v_R_1522_, lean_object* v_a_1523_, lean_object* v_b_1524_, lean_object* v_c_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(v___x_1518_, v___x_1519_, v_line_1520_, v_inst_1521_, v_R_1522_, v_a_1523_, v_b_1524_, v_c_1525_);
lean_dec(v_b_1524_);
lean_dec_ref(v_line_1520_);
lean_dec_ref(v___x_1519_);
lean_dec(v___x_1518_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(lean_object* v___x_1527_, lean_object* v___x_1528_, lean_object* v___x_1529_, lean_object* v_line_1530_, lean_object* v_inst_1531_, lean_object* v_R_1532_, lean_object* v_a_1533_, lean_object* v_b_1534_, lean_object* v_c_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1527_, v___x_1528_, v_line_1530_, v_a_1533_, v_b_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___boxed(lean_object* v___x_1537_, lean_object* v___x_1538_, lean_object* v___x_1539_, lean_object* v_line_1540_, lean_object* v_inst_1541_, lean_object* v_R_1542_, lean_object* v_a_1543_, lean_object* v_b_1544_, lean_object* v_c_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(v___x_1537_, v___x_1538_, v___x_1539_, v_line_1540_, v_inst_1541_, v_R_1542_, v_a_1543_, v_b_1544_, v_c_1545_);
lean_dec(v_b_1544_);
lean_dec_ref(v_line_1540_);
lean_dec_ref(v___x_1539_);
lean_dec(v___x_1538_);
lean_dec(v___x_1537_);
return v_res_1546_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(uint32_t v_x_1547_){
_start:
{
uint32_t v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = 48;
v___x_1559_ = lean_uint32_dec_le(v___x_1558_, v_x_1547_);
if (v___x_1559_ == 0)
{
goto v___jp_1553_;
}
else
{
uint32_t v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = 57;
v___x_1561_ = lean_uint32_dec_le(v_x_1547_, v___x_1560_);
if (v___x_1561_ == 0)
{
goto v___jp_1553_;
}
else
{
return v___x_1561_;
}
}
v___jp_1548_:
{
uint32_t v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = 65;
v___x_1550_ = lean_uint32_dec_le(v___x_1549_, v_x_1547_);
if (v___x_1550_ == 0)
{
return v___x_1550_;
}
else
{
uint32_t v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = 70;
v___x_1552_ = lean_uint32_dec_le(v_x_1547_, v___x_1551_);
return v___x_1552_;
}
}
v___jp_1553_:
{
uint32_t v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = 97;
v___x_1555_ = lean_uint32_dec_le(v___x_1554_, v_x_1547_);
if (v___x_1555_ == 0)
{
goto v___jp_1548_;
}
else
{
uint32_t v___x_1556_; uint8_t v___x_1557_; 
v___x_1556_ = 102;
v___x_1557_ = lean_uint32_dec_le(v_x_1547_, v___x_1556_);
if (v___x_1557_ == 0)
{
goto v___jp_1548_;
}
else
{
return v___x_1557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed(lean_object* v_x_1562_){
_start:
{
uint32_t v_x_2757__boxed_1563_; uint8_t v_res_1564_; lean_object* v_r_1565_; 
v_x_2757__boxed_1563_ = lean_unbox_uint32(v_x_1562_);
lean_dec(v_x_1562_);
v_res_1564_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(v_x_2757__boxed_1563_);
v_r_1565_ = lean_box(v_res_1564_);
return v_r_1565_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(uint32_t v_x_1566_){
_start:
{
uint32_t v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = 32;
v___x_1568_ = lean_uint32_dec_eq(v_x_1566_, v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed(lean_object* v_x_1569_){
_start:
{
uint32_t v_x_2788__boxed_1570_; uint8_t v_res_1571_; lean_object* v_r_1572_; 
v_x_2788__boxed_1570_ = lean_unbox_uint32(v_x_1569_);
lean_dec(v_x_1569_);
v_res_1571_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(v_x_2788__boxed_1570_);
v_r_1572_ = lean_box(v_res_1571_);
return v_r_1572_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(lean_object* v___x_1573_, lean_object* v_line_1574_, lean_object* v___x_1575_, lean_object* v___x_1576_, lean_object* v_a_1577_, lean_object* v_b_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_box(0);
switch(lean_obj_tag(v_a_1577_))
{
case 0:
{
lean_object* v_pos_1580_; lean_object* v___x_1581_; 
v_pos_1580_ = lean_ctor_get(v_a_1577_, 0);
lean_inc(v_pos_1580_);
lean_dec_ref_known(v_a_1577_, 1);
v___x_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1581_, 0, v_pos_1580_);
return v___x_1581_;
}
case 1:
{
lean_object* v_pos_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1593_; 
v_pos_1582_ = lean_ctor_get(v_a_1577_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_a_1577_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1584_ = v_a_1577_;
v_isShared_1585_ = v_isSharedCheck_1593_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_pos_1582_);
lean_dec(v_a_1577_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1593_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1586_ = lean_nat_add(v___x_1573_, v_pos_1582_);
lean_dec(v_pos_1582_);
v___x_1587_ = lean_string_utf8_next_fast(v_line_1574_, v___x_1586_);
lean_dec(v___x_1586_);
v___x_1588_ = lean_nat_sub(v___x_1587_, v___x_1573_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1588_);
v___x_1590_ = v___x_1584_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
v_a_1577_ = v___x_1590_;
v_b_1578_ = v___x_1579_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1594_; lean_object* v_table_1595_; lean_object* v_stackPos_1596_; lean_object* v_needlePos_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1652_; 
v_needle_1594_ = lean_ctor_get(v_a_1577_, 0);
v_table_1595_ = lean_ctor_get(v_a_1577_, 1);
v_stackPos_1596_ = lean_ctor_get(v_a_1577_, 2);
v_needlePos_1597_ = lean_ctor_get(v_a_1577_, 3);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_a_1577_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1599_ = v_a_1577_;
v_isShared_1600_ = v_isSharedCheck_1652_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_needlePos_1597_);
lean_inc(v_stackPos_1596_);
lean_inc(v_table_1595_);
lean_inc(v_needle_1594_);
lean_dec(v_a_1577_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1652_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_str_1601_; lean_object* v_startInclusive_1602_; lean_object* v_endExclusive_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v_str_1601_ = lean_ctor_get(v_needle_1594_, 0);
v_startInclusive_1602_ = lean_ctor_get(v_needle_1594_, 1);
v_endExclusive_1603_ = lean_ctor_get(v_needle_1594_, 2);
v___x_1604_ = lean_nat_sub(v_stackPos_1596_, v_needlePos_1597_);
v___x_1605_ = lean_nat_sub(v_endExclusive_1603_, v_startInclusive_1602_);
v___x_1606_ = lean_nat_add(v___x_1604_, v___x_1605_);
v___x_1607_ = lean_nat_sub(v___x_1576_, v___x_1573_);
v___x_1608_ = lean_nat_dec_le(v___x_1606_, v___x_1607_);
lean_dec(v___x_1606_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
lean_dec(v___x_1605_);
lean_del_object(v___x_1599_);
lean_dec(v_needlePos_1597_);
lean_dec(v_stackPos_1596_);
lean_dec_ref(v_table_1595_);
lean_dec_ref(v_needle_1594_);
v___x_1609_ = lean_unsigned_to_nat(1u);
v___x_1610_ = lean_nat_add(v___x_1604_, v___x_1609_);
lean_dec(v___x_1604_);
v___x_1611_ = lean_nat_dec_le(v___x_1610_, v___x_1607_);
lean_dec(v___x_1607_);
lean_dec(v___x_1610_);
if (v___x_1611_ == 0)
{
lean_inc(v_b_1578_);
return v_b_1578_;
}
else
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_box(3);
v_a_1577_ = v___x_1612_;
v_b_1578_ = v___x_1579_;
goto _start;
}
}
else
{
lean_object* v___x_1614_; uint8_t v_stackByte_1615_; lean_object* v___x_1616_; uint8_t v_patByte_1617_; uint8_t v___x_1618_; 
lean_dec(v___x_1607_);
lean_dec(v___x_1604_);
v___x_1614_ = lean_nat_add(v___x_1573_, v_stackPos_1596_);
v_stackByte_1615_ = lean_string_get_byte_fast(v_line_1574_, v___x_1614_);
v___x_1616_ = lean_nat_add(v_startInclusive_1602_, v_needlePos_1597_);
v_patByte_1617_ = lean_string_get_byte_fast(v_str_1601_, v___x_1616_);
v___x_1618_ = lean_uint8_dec_eq(v_stackByte_1615_, v_patByte_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; uint8_t v_decide_1620_; 
lean_dec(v___x_1605_);
v___x_1619_ = lean_unsigned_to_nat(0u);
v_decide_1620_ = lean_nat_dec_eq(v_needlePos_1597_, v___x_1619_);
if (v_decide_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v_newNeedlePos_1623_; uint8_t v___x_1624_; 
v___x_1621_ = lean_unsigned_to_nat(1u);
v___x_1622_ = lean_nat_sub(v_needlePos_1597_, v___x_1621_);
lean_dec(v_needlePos_1597_);
v_newNeedlePos_1623_ = lean_array_fget_borrowed(v_table_1595_, v___x_1622_);
lean_dec(v___x_1622_);
v___x_1624_ = lean_nat_dec_eq(v_newNeedlePos_1623_, v___x_1619_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1626_; 
lean_inc(v_newNeedlePos_1623_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 3, v_newNeedlePos_1623_);
v___x_1626_ = v___x_1599_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_needle_1594_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_table_1595_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_stackPos_1596_);
lean_ctor_set(v_reuseFailAlloc_1628_, 3, v_newNeedlePos_1623_);
v___x_1626_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
v_a_1577_ = v___x_1626_;
v_b_1578_ = v___x_1579_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1629_; lean_object* v___x_1631_; 
v_nextStackPos_1629_ = l_String_Slice_posGE___redArg(v___x_1575_, v_stackPos_1596_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 3, v___x_1619_);
lean_ctor_set(v___x_1599_, 2, v_nextStackPos_1629_);
v___x_1631_ = v___x_1599_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_needle_1594_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_table_1595_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_nextStackPos_1629_);
lean_ctor_set(v_reuseFailAlloc_1633_, 3, v___x_1619_);
v___x_1631_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
v_a_1577_ = v___x_1631_;
v_b_1578_ = v___x_1579_;
goto _start;
}
}
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v_nextStackPos_1636_; lean_object* v___x_1638_; 
lean_dec(v_needlePos_1597_);
v___x_1634_ = lean_unsigned_to_nat(1u);
v___x_1635_ = lean_nat_add(v_stackPos_1596_, v___x_1634_);
lean_dec(v_stackPos_1596_);
v_nextStackPos_1636_ = l_String_Slice_posGE___redArg(v___x_1575_, v___x_1635_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 3, v___x_1619_);
lean_ctor_set(v___x_1599_, 2, v_nextStackPos_1636_);
v___x_1638_ = v___x_1599_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_needle_1594_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_table_1595_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_nextStackPos_1636_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v___x_1619_);
v___x_1638_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
v_a_1577_ = v___x_1638_;
v_b_1578_ = v___x_1579_;
goto _start;
}
}
}
else
{
lean_object* v___x_1641_; lean_object* v_nextStackPos_1642_; lean_object* v_nextNeedlePos_1643_; uint8_t v_decide_1644_; 
v___x_1641_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1642_ = lean_nat_add(v_stackPos_1596_, v___x_1641_);
lean_dec(v_stackPos_1596_);
v_nextNeedlePos_1643_ = lean_nat_add(v_needlePos_1597_, v___x_1641_);
lean_dec(v_needlePos_1597_);
v_decide_1644_ = lean_nat_dec_eq(v_nextNeedlePos_1643_, v___x_1605_);
lean_dec(v___x_1605_);
if (v_decide_1644_ == 0)
{
lean_object* v___x_1646_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 3, v_nextNeedlePos_1643_);
lean_ctor_set(v___x_1599_, 2, v_nextStackPos_1642_);
v___x_1646_ = v___x_1599_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_needle_1594_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_table_1595_);
lean_ctor_set(v_reuseFailAlloc_1648_, 2, v_nextStackPos_1642_);
lean_ctor_set(v_reuseFailAlloc_1648_, 3, v_nextNeedlePos_1643_);
v___x_1646_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
v_a_1577_ = v___x_1646_;
goto _start;
}
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_del_object(v___x_1599_);
lean_dec_ref(v_table_1595_);
lean_dec_ref(v_needle_1594_);
v___x_1649_ = lean_nat_sub(v_nextStackPos_1642_, v_nextNeedlePos_1643_);
lean_dec(v_nextNeedlePos_1643_);
lean_dec(v_nextStackPos_1642_);
v___x_1650_ = l_String_Slice_pos_x21(v___x_1575_, v___x_1649_);
lean_dec(v___x_1649_);
v___x_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
}
}
}
}
default: 
{
lean_inc(v_b_1578_);
return v_b_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg___boxed(lean_object* v___x_1653_, lean_object* v_line_1654_, lean_object* v___x_1655_, lean_object* v___x_1656_, lean_object* v_a_1657_, lean_object* v_b_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1653_, v_line_1654_, v___x_1655_, v___x_1656_, v_a_1657_, v_b_1658_);
lean_dec(v_b_1658_);
lean_dec(v___x_1656_);
lean_dec_ref(v___x_1655_);
lean_dec_ref(v_line_1654_);
lean_dec(v___x_1653_);
return v_res_1659_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1));
v___x_1666_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1665_);
return v___x_1666_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1667_ = lean_unsigned_to_nat(0u);
v___x_1668_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2);
v___x_1669_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1));
v___x_1670_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
lean_ctor_set(v___x_1670_, 1, v___x_1668_);
lean_ctor_set(v___x_1670_, 2, v___x_1667_);
lean_ctor_set(v___x_1670_, 3, v___x_1667_);
return v___x_1670_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7));
v___x_1679_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1678_);
return v___x_1679_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1680_ = lean_unsigned_to_nat(0u);
v___x_1681_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8);
v___x_1682_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7));
v___x_1683_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v___x_1681_);
lean_ctor_set(v___x_1683_, 2, v___x_1680_);
lean_ctor_set(v___x_1683_, 3, v___x_1680_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(lean_object* v_line_1684_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1685_ = lean_unsigned_to_nat(0u);
v___x_1686_ = lean_string_utf8_byte_size(v_line_1684_);
lean_inc_ref(v_line_1684_);
v___x_1687_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1687_, 0, v_line_1684_);
lean_ctor_set(v___x_1687_, 1, v___x_1685_);
lean_ctor_set(v___x_1687_, 2, v___x_1686_);
v___x_1688_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3);
v___x_1689_ = lean_box(0);
v___x_1690_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_line_1684_, v___x_1687_, v___x_1686_, v___x_1688_, v___x_1689_);
lean_dec_ref_known(v___x_1687_, 3);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_dec_ref(v_line_1684_);
return v___x_1689_;
}
else
{
lean_object* v_val_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1716_; 
v_val_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1716_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_val_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1716_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
uint8_t v_decide_1695_; 
v_decide_1695_ = lean_nat_dec_eq(v_val_1691_, v___x_1686_);
if (v_decide_1695_ == 0)
{
lean_object* v___x_1696_; uint8_t v_decide_1697_; 
v___x_1696_ = lean_string_utf8_next_fast(v_line_1684_, v_val_1691_);
lean_dec(v_val_1691_);
v_decide_1697_ = lean_nat_dec_eq(v___x_1696_, v___x_1686_);
if (v_decide_1697_ == 0)
{
lean_object* v___f_1698_; lean_object* v___f_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___y_1704_; uint8_t v_decide_1710_; 
v___f_1698_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4));
v___f_1699_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5));
v___x_1700_ = lean_string_utf8_next_fast(v_line_1684_, v___x_1696_);
v___x_1701_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1684_, v___x_1700_, v___f_1698_);
v___x_1702_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1684_, v___x_1701_, v___f_1699_);
v_decide_1710_ = lean_nat_dec_eq(v___x_1702_, v___x_1686_);
if (v_decide_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_inc(v___x_1702_);
lean_inc_ref(v_line_1684_);
v___x_1711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1711_, 0, v_line_1684_);
lean_ctor_set(v___x_1711_, 1, v___x_1702_);
lean_ctor_set(v___x_1711_, 2, v___x_1686_);
v___x_1712_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
v___x_1713_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1702_, v_line_1684_, v___x_1711_, v___x_1686_, v___x_1712_, v___x_1689_);
lean_dec_ref_known(v___x_1711_, 3);
if (lean_obj_tag(v___x_1713_) == 0)
{
v___y_1704_ = v___x_1686_;
goto v___jp_1703_;
}
else
{
lean_object* v_val_1714_; lean_object* v___x_1715_; 
v_val_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_val_1714_);
lean_dec_ref_known(v___x_1713_, 1);
v___x_1715_ = lean_nat_add(v___x_1702_, v_val_1714_);
lean_dec(v_val_1714_);
v___y_1704_ = v___x_1715_;
goto v___jp_1703_;
}
}
else
{
lean_dec(v___x_1702_);
lean_del_object(v___x_1693_);
lean_dec_ref(v_line_1684_);
return v___x_1689_;
}
v___jp_1703_:
{
uint8_t v_decide_1705_; 
v_decide_1705_ = lean_nat_dec_eq(v___y_1704_, v___x_1702_);
if (v_decide_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1684_, v___x_1702_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec(v___x_1702_);
lean_dec_ref(v_line_1684_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1706_);
v___x_1708_ = v___x_1693_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
else
{
lean_dec(v___y_1704_);
lean_dec(v___x_1702_);
lean_del_object(v___x_1693_);
lean_dec_ref(v_line_1684_);
return v___x_1689_;
}
}
}
else
{
lean_del_object(v___x_1693_);
lean_dec_ref(v_line_1684_);
return v___x_1689_;
}
}
else
{
lean_del_object(v___x_1693_);
lean_dec(v_val_1691_);
lean_dec_ref(v_line_1684_);
return v___x_1689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(lean_object* v___x_1717_, lean_object* v_line_1718_, lean_object* v___x_1719_, lean_object* v___x_1720_, lean_object* v_inst_1721_, lean_object* v_R_1722_, lean_object* v_a_1723_, lean_object* v_b_1724_, lean_object* v_c_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1717_, v_line_1718_, v___x_1719_, v___x_1720_, v_a_1723_, v_b_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___boxed(lean_object* v___x_1727_, lean_object* v_line_1728_, lean_object* v___x_1729_, lean_object* v___x_1730_, lean_object* v_inst_1731_, lean_object* v_R_1732_, lean_object* v_a_1733_, lean_object* v_b_1734_, lean_object* v_c_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(v___x_1727_, v_line_1728_, v___x_1729_, v___x_1730_, v_inst_1731_, v_R_1732_, v_a_1733_, v_b_1734_, v_c_1735_);
lean_dec(v_b_1734_);
lean_dec(v___x_1730_);
lean_dec_ref(v___x_1729_);
lean_dec_ref(v_line_1728_);
lean_dec(v___x_1727_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(lean_object* v_line_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(v_line_1737_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v___x_1739_; 
v___x_1739_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(v_line_1737_);
return v___x_1739_;
}
else
{
lean_dec_ref(v_line_1737_);
return v___x_1738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleBtLine(lean_object* v_line_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(v_line_1740_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_box(0);
return v___x_1742_;
}
else
{
lean_object* v_val_1743_; lean_object* v_snd_1744_; lean_object* v_fst_1745_; lean_object* v_fst_1746_; lean_object* v_snd_1747_; lean_object* v___x_1748_; 
v_val_1743_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_val_1743_);
lean_dec_ref_known(v___x_1741_, 1);
v_snd_1744_ = lean_ctor_get(v_val_1743_, 1);
lean_inc(v_snd_1744_);
v_fst_1745_ = lean_ctor_get(v_val_1743_, 0);
lean_inc(v_fst_1745_);
lean_dec(v_val_1743_);
v_fst_1746_ = lean_ctor_get(v_snd_1744_, 0);
lean_inc(v_fst_1746_);
v_snd_1747_ = lean_ctor_get(v_snd_1744_, 1);
lean_inc(v_snd_1747_);
lean_dec(v_snd_1744_);
v___x_1748_ = l_Lean_Name_Demangle_demangleSymbol(v_fst_1746_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_dec(v_snd_1747_);
lean_dec(v_fst_1745_);
return v___x_1748_;
}
else
{
lean_object* v_val_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1758_; 
v_val_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1758_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_val_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1758_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1753_ = lean_string_append(v_fst_1745_, v_val_1749_);
lean_dec(v_val_1749_);
v___x_1754_ = lean_string_append(v___x_1753_, v_snd_1747_);
lean_dec(v_snd_1747_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1754_);
v___x_1756_ = v___x_1751_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_demangle_bt_line_cstr(lean_object* v_line_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_Name_Demangle_demangleBtLine(v_line_1759_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v___x_1761_; 
v___x_1761_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_1761_;
}
else
{
lean_object* v_val_1762_; 
v_val_1762_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_val_1762_);
lean_dec_ref_known(v___x_1760_, 1);
return v_val_1762_;
}
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_NameTrie(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NameMangling(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_NameDemangling(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
