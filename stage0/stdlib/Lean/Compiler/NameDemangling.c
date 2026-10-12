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
uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(lean_object* v_s_65_){
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
LEAN_EXPORT void l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_65_ = stack[0].m_obj;
uint8_t v_res_73_;
v_res_73_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_s_65_);
stack->m_num = v_res_73_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits___boxed(lean_object* v_s_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_s_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go(lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
switch(lean_obj_tag(v_a_77_))
{
case 0:
{
return v_a_78_;
}
case 1:
{
lean_object* v_pre_79_; lean_object* v_str_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_pre_79_ = lean_ctor_get(v_a_77_, 0);
v_str_80_ = lean_ctor_get(v_a_77_, 1);
lean_inc_ref(v_str_80_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v_str_80_);
v___x_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v_a_78_);
v_a_77_ = v_pre_79_;
v_a_78_ = v___x_82_;
goto _start;
}
default: 
{
lean_object* v_pre_84_; lean_object* v_i_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_pre_84_ = lean_ctor_get(v_a_77_, 0);
v_i_85_ = lean_ctor_get(v_a_77_, 1);
lean_inc(v_i_85_);
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v_i_85_);
v___x_87_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_a_78_);
v_a_77_ = v_pre_84_;
v_a_78_ = v___x_87_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go___boxed(lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go(v_a_89_, v_a_90_);
lean_dec(v_a_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(lean_object* v_n_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_box(0);
v___x_94_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go(v_n_92_, v___x_93_);
v___x_95_ = lean_array_mk(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts___boxed(lean_object* v_n_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(v_n_96_);
lean_dec(v_n_96_);
return v_res_97_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(lean_object* v_as_98_, size_t v_i_99_, size_t v_stop_100_, lean_object* v_b_101_){
_start:
{
lean_object* v___y_103_; uint8_t v___x_107_; 
v___x_107_ = lean_usize_dec_eq(v_i_99_, v_stop_100_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_array_uget_borrowed(v_as_98_, v_i_99_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_s_109_; lean_object* v___x_110_; 
v_s_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc_ref(v_s_109_);
v___x_110_ = l_Lean_Name_str___override(v_b_101_, v_s_109_);
v___y_103_ = v___x_110_;
goto v___jp_102_;
}
else
{
lean_object* v_n_111_; lean_object* v___x_112_; 
v_n_111_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_n_111_);
v___x_112_ = l_Lean_Name_num___override(v_b_101_, v_n_111_);
v___y_103_ = v___x_112_;
goto v___jp_102_;
}
}
else
{
return v_b_101_;
}
v___jp_102_:
{
size_t v___x_104_; size_t v___x_105_; 
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_add(v_i_99_, v___x_104_);
v_i_99_ = v___x_105_;
v_b_101_ = v___y_103_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_98_ = stack[0].m_obj;
size_t v_i_99_ = stack[1].m_num;
size_t v_stop_100_ = stack[2].m_num;
lean_object* v_b_101_ = stack[3].m_obj;
lean_object* v_res_113_;
v_res_113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_as_98_, v_i_99_, v_stop_100_, v_b_101_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0___boxed(lean_object* v_as_114_, lean_object* v_i_115_, lean_object* v_stop_116_, lean_object* v_b_117_){
_start:
{
size_t v_i_boxed_118_; size_t v_stop_boxed_119_; lean_object* v_res_120_; 
v_i_boxed_118_ = lean_unbox_usize(v_i_115_);
lean_dec(v_i_115_);
v_stop_boxed_119_ = lean_unbox_usize(v_stop_116_);
lean_dec(v_stop_116_);
v_res_120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_as_114_, v_i_boxed_118_, v_stop_boxed_119_, v_b_117_);
lean_dec_ref(v_as_114_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(lean_object* v_parts_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_122_ = lean_box(0);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_array_get_size(v_parts_121_);
v___x_125_ = lean_nat_dec_lt(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
return v___x_122_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = lean_nat_dec_le(v___x_124_, v___x_124_);
if (v___x_126_ == 0)
{
if (v___x_125_ == 0)
{
return v___x_122_;
}
else
{
size_t v___x_127_; size_t v___x_128_; lean_object* v___x_129_; 
v___x_127_ = ((size_t)0ULL);
v___x_128_ = lean_usize_of_nat(v___x_124_);
v___x_129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_parts_121_, v___x_127_, v___x_128_, v___x_122_);
return v___x_129_;
}
}
else
{
size_t v___x_130_; size_t v___x_131_; lean_object* v___x_132_; 
v___x_130_ = ((size_t)0ULL);
v___x_131_ = lean_usize_of_nat(v___x_124_);
v___x_132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_parts_121_, v___x_130_, v___x_131_, v___x_122_);
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName___boxed(lean_object* v_parts_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(v_parts_133_);
lean_dec_ref(v_parts_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(lean_object* v_comps_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_137_ = lean_array_get_size(v_comps_136_);
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_nat_dec_eq(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = 1;
v___x_141_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(v_comps_136_);
v___x_142_ = l_Lean_Name_toString(v___x_141_, v___x_140_);
return v___x_142_;
}
else
{
lean_object* v___x_143_; 
v___x_143_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___boxed(lean_object* v_comps_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_comps_144_);
lean_dec_ref(v_comps_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(lean_object* v_c_174_){
_start:
{
if (lean_obj_tag(v_c_174_) == 0)
{
lean_object* v_s_177_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_s_177_ = lean_ctor_get(v_c_174_, 0);
lean_inc_ref(v_s_177_);
lean_dec_ref_known(v_c_174_, 1);
v___x_185_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3));
v___x_186_ = lean_string_dec_eq(v_s_177_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4));
v___x_188_ = lean_string_dec_eq(v_s_177_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5));
v___x_190_ = lean_string_dec_eq(v_s_177_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6));
v___x_192_ = lean_string_dec_eq(v_s_177_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7));
v___x_194_ = lean_string_dec_eq(v_s_177_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8));
v___x_196_ = lean_string_dec_eq(v_s_177_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9));
v___x_198_ = lean_string_dec_eq(v_s_177_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10));
v___x_200_ = lean_string_dec_eq(v_s_177_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11));
lean_inc_ref(v_s_177_);
v___x_202_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_177_, v___x_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
goto v___jp_178_;
}
else
{
lean_object* v_val_203_; uint8_t v___x_204_; 
v_val_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_val_203_);
lean_dec_ref_known(v___x_202_, 1);
v___x_204_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_203_);
if (v___x_204_ == 0)
{
goto v___jp_178_;
}
else
{
lean_object* v___x_205_; 
lean_dec_ref(v_s_177_);
v___x_205_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_205_;
}
}
}
else
{
lean_object* v___x_206_; 
lean_dec_ref(v_s_177_);
v___x_206_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13));
return v___x_206_;
}
}
else
{
lean_object* v___x_207_; 
lean_dec_ref(v_s_177_);
v___x_207_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15));
return v___x_207_;
}
}
else
{
lean_dec_ref(v_s_177_);
goto v___jp_175_;
}
}
else
{
lean_dec_ref(v_s_177_);
goto v___jp_175_;
}
}
else
{
lean_dec_ref(v_s_177_);
goto v___jp_175_;
}
}
else
{
lean_object* v___x_208_; 
lean_dec_ref(v_s_177_);
v___x_208_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__17));
return v___x_208_;
}
}
else
{
lean_object* v___x_209_; 
lean_dec_ref(v_s_177_);
v___x_209_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__19));
return v___x_209_;
}
}
else
{
lean_object* v___x_210_; 
lean_dec_ref(v_s_177_);
v___x_210_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__21));
return v___x_210_;
}
v___jp_178_:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__2));
v___x_180_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_177_, v___x_179_);
if (lean_obj_tag(v___x_180_) == 0)
{
return v___x_180_;
}
else
{
lean_object* v_val_181_; uint8_t v___x_182_; 
v_val_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_val_181_);
lean_dec_ref_known(v___x_180_, 1);
v___x_182_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; 
v___x_183_ = lean_box(0);
return v___x_183_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_184_;
}
}
}
}
else
{
lean_object* v___x_211_; 
lean_dec_ref(v_c_174_);
v___x_211_ = lean_box(0);
return v___x_211_;
}
v___jp_175_:
{
lean_object* v___x_176_; 
v___x_176_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_176_;
}
}
}
uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(lean_object* v_c_213_){
_start:
{
if (lean_obj_tag(v_c_213_) == 0)
{
lean_object* v_s_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_s_214_ = lean_ctor_get(v_c_213_, 0);
lean_inc_ref(v_s_214_);
lean_dec_ref_known(v_c_213_, 1);
v___x_215_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___closed__0));
v___x_216_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_214_, v___x_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
uint8_t v___x_217_; 
v___x_217_ = 0;
return v___x_217_;
}
else
{
lean_object* v_val_218_; uint8_t v___x_219_; 
v_val_218_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v___x_216_, 1);
v___x_219_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_218_);
return v___x_219_;
}
}
else
{
uint8_t v___x_220_; 
lean_dec_ref(v_c_213_);
v___x_220_ = 0;
return v___x_220_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_213_ = stack[0].m_obj;
uint8_t v_res_221_;
v_res_221_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(v_c_213_);
stack->m_num = v_res_221_;
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
uint8_t l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(lean_object* v_x_225_, lean_object* v_x_226_){
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
LEAN_EXPORT void l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_225_ = stack[0].m_obj;
lean_object* v_x_226_ = stack[1].m_obj;
uint8_t v_res_233_;
v_res_233_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v_x_225_, v_x_226_);
stack->m_num = v_res_233_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0___boxed(lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v_x_234_, v_x_235_);
lean_dec(v_x_235_);
lean_dec(v_x_234_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(lean_object* v_stop_245_, lean_object* v_start_246_, lean_object* v___x_247_, lean_object* v_comps_248_, lean_object* v_range_249_, lean_object* v_b_250_, lean_object* v_i_251_){
_start:
{
lean_object* v_stop_252_; lean_object* v_step_253_; uint8_t v___x_254_; 
v_stop_252_ = lean_ctor_get(v_range_249_, 1);
v_step_253_ = lean_ctor_get(v_range_249_, 2);
v___x_254_ = lean_nat_dec_lt(v_i_251_, v_stop_252_);
if (v___x_254_ == 0)
{
lean_dec(v_i_251_);
lean_dec(v_start_246_);
lean_inc_ref(v_b_250_);
return v_b_250_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; lean_object* v___y_262_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_255_ = lean_box(0);
v___x_256_ = lean_box(0);
v___x_257_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0));
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_unsigned_to_nat(3u);
v___x_260_ = lean_nat_dec_le(v___x_259_, v___x_247_);
v___x_277_ = lean_array_get_size(v_comps_248_);
v___x_278_ = lean_nat_dec_lt(v_i_251_, v___x_277_);
if (v___x_278_ == 0)
{
v___y_262_ = v___x_255_;
goto v___jp_261_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_array_fget_borrowed(v_comps_248_, v_i_251_);
lean_inc(v___x_279_);
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
v___y_262_ = v___x_280_;
goto v___jp_261_;
}
v___jp_261_:
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2));
v___x_264_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_262_, v___x_263_);
lean_dec(v___y_262_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_nat_add(v_i_251_, v_step_253_);
lean_dec(v_i_251_);
v_b_250_ = v___x_257_;
v_i_251_ = v___x_265_;
goto _start;
}
else
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_nat_add(v_i_251_, v___x_258_);
lean_dec(v_i_251_);
v___x_268_ = lean_nat_dec_lt(v___x_267_, v_stop_245_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v___x_267_);
v___x_269_ = lean_box(v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v_start_246_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_256_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec(v_start_246_);
v___x_273_ = lean_box(v___x_260_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_267_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_256_);
return v___x_276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___boxed(lean_object* v_stop_281_, lean_object* v_start_282_, lean_object* v___x_283_, lean_object* v_comps_284_, lean_object* v_range_285_, lean_object* v_b_286_, lean_object* v_i_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_281_, v_start_282_, v___x_283_, v_comps_284_, v_range_285_, v_b_286_, v_i_287_);
lean_dec_ref(v_b_286_);
lean_dec_ref(v_range_285_);
lean_dec_ref(v_comps_284_);
lean_dec(v___x_283_);
lean_dec(v_stop_281_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(lean_object* v_comps_294_, lean_object* v_start_295_, lean_object* v_stop_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___y_300_; uint8_t v___x_322_; 
v___x_297_ = lean_unsigned_to_nat(3u);
v___x_298_ = lean_nat_sub(v_stop_296_, v_start_295_);
v___x_322_ = lean_nat_dec_le(v___x_297_, v___x_298_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v___x_298_);
lean_dec(v_stop_296_);
v___x_323_ = lean_box(v___x_322_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v_start_295_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = lean_array_get_size(v_comps_294_);
v___x_326_ = lean_nat_dec_lt(v_start_295_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
v___x_327_ = lean_box(0);
v___y_300_ = v___x_327_;
goto v___jp_299_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_array_fget_borrowed(v_comps_294_, v_start_295_);
lean_inc(v___x_328_);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
v___y_300_ = v___x_329_;
goto v___jp_299_;
}
}
v___jp_299_:
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2));
v___x_302_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_300_, v___x_301_);
lean_dec(v___y_300_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec(v___x_298_);
lean_dec(v_stop_296_);
v___x_303_ = lean_box(v___x_302_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_start_295_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_fst_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_320_; 
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_add(v_start_295_, v___x_305_);
lean_inc(v_stop_296_);
lean_inc(v___x_306_);
v___x_307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v_stop_296_);
lean_ctor_set(v___x_307_, 2, v___x_305_);
v___x_308_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0));
lean_inc(v_start_295_);
v___x_309_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_296_, v_start_295_, v___x_298_, v_comps_294_, v___x_307_, v___x_308_, v___x_306_);
lean_dec_ref_known(v___x_307_, 3);
lean_dec(v___x_298_);
lean_dec(v_stop_296_);
v_fst_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v___x_309_, 1);
lean_dec(v_unused_321_);
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_320_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_fst_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_320_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
if (lean_obj_tag(v_fst_310_) == 0)
{
uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_314_ = 0;
v___x_315_ = lean_box(v___x_314_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v___x_315_);
lean_ctor_set(v___x_312_, 0, v_start_295_);
v___x_317_ = v___x_312_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_start_295_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
else
{
lean_object* v_val_319_; 
lean_del_object(v___x_312_);
lean_dec(v_start_295_);
v_val_319_ = lean_ctor_get(v_fst_310_, 0);
lean_inc(v_val_319_);
lean_dec_ref_known(v_fst_310_, 1);
return v_val_319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___boxed(lean_object* v_comps_330_, lean_object* v_start_331_, lean_object* v_stop_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_comps_330_, v_start_331_, v_stop_332_);
lean_dec_ref(v_comps_330_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(lean_object* v_stop_334_, lean_object* v_start_335_, lean_object* v___x_336_, lean_object* v_comps_337_, lean_object* v_range_338_, lean_object* v_b_339_, lean_object* v_i_340_, lean_object* v_hs_341_, lean_object* v_hl_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_334_, v_start_335_, v___x_336_, v_comps_337_, v_range_338_, v_b_339_, v_i_340_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___boxed(lean_object* v_stop_344_, lean_object* v_start_345_, lean_object* v___x_346_, lean_object* v_comps_347_, lean_object* v_range_348_, lean_object* v_b_349_, lean_object* v_i_350_, lean_object* v_hs_351_, lean_object* v_hl_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(v_stop_344_, v_start_345_, v___x_346_, v_comps_347_, v_range_348_, v_b_349_, v_i_350_, v_hs_351_, v_hl_352_);
lean_dec_ref(v_b_349_);
lean_dec_ref(v_range_348_);
lean_dec_ref(v_comps_347_);
lean_dec(v___x_346_);
lean_dec(v_stop_344_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(lean_object* v___x_354_, lean_object* v_comps_355_, lean_object* v_range_356_, lean_object* v_b_357_, lean_object* v_i_358_){
_start:
{
lean_object* v_stop_359_; lean_object* v_step_360_; uint8_t v___x_361_; 
v_stop_359_ = lean_ctor_get(v_range_356_, 1);
v_step_360_ = lean_ctor_get(v_range_356_, 2);
v___x_361_ = lean_nat_dec_lt(v_i_358_, v_stop_359_);
if (v___x_361_ == 0)
{
lean_dec(v_i_358_);
lean_inc(v_b_357_);
return v_b_357_;
}
else
{
lean_object* v___x_362_; uint8_t v___y_364_; lean_object* v___y_369_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_array_get_size(v_comps_355_);
v___x_375_ = lean_nat_dec_lt(v_i_358_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
v___y_369_ = v___x_376_;
goto v___jp_368_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_array_fget_borrowed(v_comps_355_, v_i_358_);
lean_inc(v___x_377_);
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
v___y_369_ = v___x_378_;
goto v___jp_368_;
}
v___jp_363_:
{
if (v___y_364_ == 0)
{
lean_object* v___x_365_; 
v___x_365_ = lean_nat_add(v_i_358_, v_step_360_);
lean_dec(v_i_358_);
v_i_358_ = v___x_365_;
goto _start;
}
else
{
lean_object* v___x_367_; 
v___x_367_ = lean_nat_add(v_i_358_, v___x_362_);
lean_dec(v_i_358_);
return v___x_367_;
}
}
v___jp_368_:
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2));
v___x_371_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_369_, v___x_370_);
lean_dec(v___y_369_);
if (v___x_371_ == 0)
{
v___y_364_ = v___x_371_;
goto v___jp_363_;
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_nat_add(v_i_358_, v___x_362_);
v___x_373_ = lean_nat_dec_lt(v___x_372_, v___x_354_);
lean_dec(v___x_372_);
v___y_364_ = v___x_373_;
goto v___jp_363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg___boxed(lean_object* v___x_379_, lean_object* v_comps_380_, lean_object* v_range_381_, lean_object* v_b_382_, lean_object* v_i_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_379_, v_comps_380_, v_range_381_, v_b_382_, v_i_383_);
lean_dec(v_b_382_);
lean_dec_ref(v_range_381_);
lean_dec_ref(v_comps_380_);
lean_dec(v___x_379_);
return v_res_384_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(lean_object* v_a_385_, lean_object* v_as_386_, size_t v_i_387_, size_t v_stop_388_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = lean_usize_dec_eq(v_i_387_, v_stop_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = lean_array_uget_borrowed(v_as_386_, v_i_387_);
v___x_391_ = lean_string_dec_eq(v_a_385_, v___x_390_);
if (v___x_391_ == 0)
{
size_t v___x_392_; size_t v___x_393_; 
v___x_392_ = ((size_t)1ULL);
v___x_393_ = lean_usize_add(v_i_387_, v___x_392_);
v_i_387_ = v___x_393_;
goto _start;
}
else
{
return v___x_391_;
}
}
else
{
uint8_t v___x_395_; 
v___x_395_ = 0;
return v___x_395_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_385_ = stack[0].m_obj;
lean_object* v_as_386_ = stack[1].m_obj;
size_t v_i_387_ = stack[2].m_num;
size_t v_stop_388_ = stack[3].m_num;
uint8_t v_res_396_;
v_res_396_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_385_, v_as_386_, v_i_387_, v_stop_388_);
stack->m_num = v_res_396_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0___boxed(lean_object* v_a_397_, lean_object* v_as_398_, lean_object* v_i_399_, lean_object* v_stop_400_){
_start:
{
size_t v_i_boxed_401_; size_t v_stop_boxed_402_; uint8_t v_res_403_; lean_object* v_r_404_; 
v_i_boxed_401_ = lean_unbox_usize(v_i_399_);
lean_dec(v_i_399_);
v_stop_boxed_402_ = lean_unbox_usize(v_stop_400_);
lean_dec(v_stop_400_);
v_res_403_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_397_, v_as_398_, v_i_boxed_401_, v_stop_boxed_402_);
lean_dec_ref(v_as_398_);
lean_dec_ref(v_a_397_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(lean_object* v_as_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_array_get_size(v_as_405_);
v___x_409_ = lean_nat_dec_lt(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
return v___x_409_;
}
else
{
if (v___x_409_ == 0)
{
return v___x_409_;
}
else
{
size_t v___x_410_; size_t v___x_411_; uint8_t v___x_412_; 
v___x_410_ = ((size_t)0ULL);
v___x_411_ = lean_usize_of_nat(v___x_408_);
v___x_412_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_406_, v_as_405_, v___x_410_, v___x_411_);
return v___x_412_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_405_ = stack[0].m_obj;
lean_object* v_a_406_ = stack[1].m_obj;
uint8_t v_res_413_;
v_res_413_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_as_405_, v_a_406_);
stack->m_num = v_res_413_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0___boxed(lean_object* v_as_414_, lean_object* v_a_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_as_414_, v_a_415_);
lean_dec_ref(v_a_415_);
lean_dec_ref(v_as_414_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(lean_object* v_comps_418_, lean_object* v_range_419_, lean_object* v_b_420_, lean_object* v_i_421_){
_start:
{
lean_object* v_stop_422_; lean_object* v_step_423_; lean_object* v_a_425_; uint8_t v___x_428_; 
v_stop_422_ = lean_ctor_get(v_range_419_, 1);
v_step_423_ = lean_ctor_get(v_range_419_, 2);
v___x_428_ = lean_nat_dec_lt(v_i_421_, v_stop_422_);
if (v___x_428_ == 0)
{
lean_dec(v_i_421_);
return v_b_420_;
}
else
{
lean_object* v_fst_429_; lean_object* v_snd_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_454_; 
v_fst_429_ = lean_ctor_get(v_b_420_, 0);
v_snd_430_ = lean_ctor_get(v_b_420_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v_b_420_);
if (v_isSharedCheck_454_ == 0)
{
v___x_432_ = v_b_420_;
v_isShared_433_ = v_isSharedCheck_454_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_snd_430_);
lean_inc(v_fst_429_);
lean_dec(v_b_420_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_454_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = l_Lean_instInhabitedNamePart_default;
v___x_435_ = lean_array_get_borrowed(v___x_434_, v_comps_418_, v_i_421_);
lean_inc(v___x_435_);
v___x_436_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_435_);
if (lean_obj_tag(v___x_436_) == 0)
{
uint8_t v___x_437_; 
lean_inc(v___x_435_);
v___x_437_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(v___x_435_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_440_; 
lean_inc(v___x_435_);
v___x_438_ = lean_array_push(v_fst_429_, v___x_435_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_438_);
v___x_440_ = v___x_432_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_snd_430_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
v_a_425_ = v___x_440_;
goto v___jp_424_;
}
}
else
{
lean_object* v___x_443_; 
if (v_isShared_433_ == 0)
{
v___x_443_ = v___x_432_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_fst_429_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_snd_430_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
v_a_425_ = v___x_443_;
goto v___jp_424_;
}
}
}
else
{
lean_object* v_val_445_; uint8_t v___x_446_; 
v_val_445_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_val_445_);
lean_dec_ref_known(v___x_436_, 1);
v___x_446_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_snd_430_, v_val_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = lean_array_push(v_snd_430_, v_val_445_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v___x_447_);
v___x_449_ = v___x_432_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_fst_429_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
v_a_425_ = v___x_449_;
goto v___jp_424_;
}
}
else
{
lean_object* v___x_452_; 
lean_dec(v_val_445_);
if (v_isShared_433_ == 0)
{
v___x_452_ = v___x_432_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_fst_429_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_snd_430_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
v_a_425_ = v___x_452_;
goto v___jp_424_;
}
}
}
}
}
v___jp_424_:
{
lean_object* v___x_426_; 
v___x_426_ = lean_nat_add(v_i_421_, v_step_423_);
lean_dec(v_i_421_);
v_b_420_ = v_a_425_;
v_i_421_ = v___x_426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg___boxed(lean_object* v_comps_455_, lean_object* v_range_456_, lean_object* v_b_457_, lean_object* v_i_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_455_, v_range_456_, v_b_457_, v_i_458_);
lean_dec_ref(v_range_456_);
lean_dec_ref(v_comps_455_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(lean_object* v_comps_464_){
_start:
{
lean_object* v_begin___466_; lean_object* v_begin___482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___y_486_; uint8_t v___x_492_; 
v_begin___482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_unsigned_to_nat(3u);
v___x_484_ = lean_array_get_size(v_comps_464_);
v___x_492_ = lean_nat_dec_le(v___x_483_, v___x_484_);
if (v___x_492_ == 0)
{
v_begin___466_ = v_begin___482_;
goto v___jp_465_;
}
else
{
uint8_t v___x_493_; 
v___x_493_ = lean_nat_dec_lt(v_begin___482_, v___x_484_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
v___x_494_ = lean_box(0);
v___y_486_ = v___x_494_;
goto v___jp_485_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_array_fget_borrowed(v_comps_464_, v_begin___482_);
lean_inc(v___x_495_);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
v___y_486_ = v___x_496_;
goto v___jp_485_;
}
}
v___jp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_fst_472_; lean_object* v_snd_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_481_; 
v___x_467_ = lean_array_get_size(v_comps_464_);
v___x_468_ = lean_unsigned_to_nat(1u);
lean_inc(v_begin___466_);
v___x_469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_469_, 0, v_begin___466_);
lean_ctor_set(v___x_469_, 1, v___x_467_);
lean_ctor_set(v___x_469_, 2, v___x_468_);
v___x_470_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1));
v___x_471_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_464_, v___x_469_, v___x_470_, v_begin___466_);
lean_dec_ref_known(v___x_469_, 3);
v_fst_472_ = lean_ctor_get(v___x_471_, 0);
v_snd_473_ = lean_ctor_get(v___x_471_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_481_ == 0)
{
v___x_475_ = v___x_471_;
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_snd_473_);
lean_inc(v_fst_472_);
lean_dec(v___x_471_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_fst_472_);
lean_dec(v_fst_472_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_snd_473_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
v___jp_485_:
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2));
v___x_488_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_486_, v___x_487_);
lean_dec(v___y_486_);
if (v___x_488_ == 0)
{
v_begin___466_ = v_begin___482_;
goto v___jp_465_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_484_);
lean_ctor_set(v___x_490_, 2, v___x_489_);
v___x_491_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_484_, v_comps_464_, v___x_490_, v_begin___482_, v___x_489_);
lean_dec_ref_known(v___x_490_, 3);
v_begin___466_ = v___x_491_;
goto v___jp_465_;
}
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(lean_object* v___x_551_, lean_object* v_as_552_, size_t v_sz_553_, size_t v_i_554_, lean_object* v_b_555_){
_start:
{
lean_object* v_a_557_; uint8_t v___x_561_; 
v___x_561_ = lean_usize_dec_lt(v_i_554_, v_sz_553_);
if (v___x_561_ == 0)
{
return v_b_555_;
}
else
{
lean_object* v_a_562_; lean_object* v___x_563_; lean_object* v_name_566_; lean_object* v_flags_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_a_562_ = lean_array_uget_borrowed(v_as_552_, v_i_554_);
v___x_563_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(v_a_562_);
v_name_566_ = lean_ctor_get(v___x_563_, 0);
v_flags_567_ = lean_ctor_get(v___x_563_, 1);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_string_utf8_byte_size(v_name_566_);
v___x_570_ = lean_nat_dec_eq(v___x_569_, v___x_568_);
if (v___x_570_ == 0)
{
goto v___jp_564_;
}
else
{
uint8_t v_skipNext_571_; 
v_skipNext_571_ = lean_nat_dec_eq(v___x_551_, v___x_568_);
if (v_skipNext_571_ == 0)
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = lean_array_get_size(v_flags_567_);
v___x_573_ = lean_nat_dec_eq(v___x_572_, v___x_568_);
if (v___x_573_ == 0)
{
goto v___jp_564_;
}
else
{
lean_dec_ref(v___x_563_);
v_a_557_ = v_b_555_;
goto v___jp_556_;
}
}
else
{
goto v___jp_564_;
}
}
v___jp_564_:
{
lean_object* v___x_565_; 
v___x_565_ = lean_array_push(v_b_555_, v___x_563_);
v_a_557_ = v___x_565_;
goto v___jp_556_;
}
}
v___jp_556_:
{
size_t v___x_558_; size_t v___x_559_; 
v___x_558_ = ((size_t)1ULL);
v___x_559_ = lean_usize_add(v_i_554_, v___x_558_);
v_i_554_ = v___x_559_;
v_b_555_ = v_a_557_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_551_ = stack[0].m_obj;
lean_object* v_as_552_ = stack[1].m_obj;
size_t v_sz_553_ = stack[2].m_num;
size_t v_i_554_ = stack[3].m_num;
lean_object* v_b_555_ = stack[4].m_obj;
lean_object* v_res_574_;
v_res_574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_551_, v_as_552_, v_sz_553_, v_i_554_, v_b_555_);
stack->m_obj
 = v_res_574_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5___boxed(lean_object* v___x_575_, lean_object* v_as_576_, lean_object* v_sz_577_, lean_object* v_i_578_, lean_object* v_b_579_){
_start:
{
size_t v_sz_boxed_580_; size_t v_i_boxed_581_; lean_object* v_res_582_; 
v_sz_boxed_580_ = lean_unbox_usize(v_sz_577_);
lean_dec(v_sz_577_);
v_i_boxed_581_ = lean_unbox_usize(v_i_578_);
lean_dec(v_i_578_);
v_res_582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_575_, v_as_576_, v_sz_boxed_580_, v_i_boxed_581_, v_b_579_);
lean_dec_ref(v_as_576_);
lean_dec(v___x_575_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(lean_object* v_range_584_, lean_object* v_b_585_, lean_object* v_i_586_){
_start:
{
lean_object* v_stop_587_; lean_object* v_step_588_; lean_object* v_a_590_; uint8_t v___x_593_; 
v_stop_587_ = lean_ctor_get(v_range_584_, 1);
v_step_588_ = lean_ctor_get(v_range_584_, 2);
v___x_593_ = lean_nat_dec_lt(v_i_586_, v_stop_587_);
if (v___x_593_ == 0)
{
lean_dec(v_i_586_);
lean_inc_ref(v_b_585_);
return v_b_585_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = l_Lean_instInhabitedNamePart_default;
v___x_595_ = lean_array_get_borrowed(v___x_594_, v_b_585_, v_i_586_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_s_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_s_596_ = lean_ctor_get(v___x_595_, 0);
v___x_597_ = lean_string_utf8_byte_size(v_s_596_);
v___x_598_ = lean_unsigned_to_nat(2u);
v___x_599_ = lean_nat_dec_le(v___x_598_, v___x_597_);
if (v___x_599_ == 0)
{
v_a_590_ = v_b_585_;
goto v___jp_589_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0));
v___x_602_ = lean_string_memcmp(v_s_596_, v___x_601_, v___x_600_, v___x_600_, v___x_598_);
if (v___x_602_ == 0)
{
v_a_590_ = v_b_585_;
goto v___jp_589_;
}
else
{
lean_object* v___x_603_; 
v___x_603_ = l_Array_extract___redArg(v_b_585_, v___x_600_, v_i_586_);
return v___x_603_;
}
}
}
else
{
v_a_590_ = v_b_585_;
goto v___jp_589_;
}
}
v___jp_589_:
{
lean_object* v___x_591_; 
v___x_591_ = lean_nat_add(v_i_586_, v_step_588_);
lean_dec(v_i_586_);
v_b_585_ = v_a_590_;
v_i_586_ = v___x_591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___boxed(lean_object* v_range_604_, lean_object* v_b_605_, lean_object* v_i_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v_range_604_, v_b_605_, v_i_606_);
lean_dec_ref(v_b_605_);
lean_dec_ref(v_range_604_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(lean_object* v___x_613_, lean_object* v___x_614_, lean_object* v_range_615_, lean_object* v_b_616_, lean_object* v_i_617_){
_start:
{
lean_object* v_stop_618_; lean_object* v_step_619_; lean_object* v_a_621_; uint8_t v___x_624_; 
v_stop_618_ = lean_ctor_get(v_range_615_, 1);
v_step_619_ = lean_ctor_get(v_range_615_, 2);
v___x_624_ = lean_nat_dec_lt(v_i_617_, v_stop_618_);
if (v___x_624_ == 0)
{
lean_dec(v_i_617_);
return v_b_616_;
}
else
{
lean_object* v_snd_625_; lean_object* v_snd_626_; lean_object* v_fst_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_723_; 
v_snd_625_ = lean_ctor_get(v_b_616_, 1);
lean_inc(v_snd_625_);
v_snd_626_ = lean_ctor_get(v_snd_625_, 1);
lean_inc(v_snd_626_);
v_fst_627_ = lean_ctor_get(v_b_616_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_b_616_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; 
v_unused_724_ = lean_ctor_get(v_b_616_, 1);
lean_dec(v_unused_724_);
v___x_629_ = v_b_616_;
v_isShared_630_ = v_isSharedCheck_723_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_fst_627_);
lean_dec(v_b_616_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_723_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v_fst_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_721_; 
v_fst_631_ = lean_ctor_get(v_snd_625_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v_snd_625_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v_snd_625_, 1);
lean_dec(v_unused_722_);
v___x_633_ = v_snd_625_;
v_isShared_634_ = v_isSharedCheck_721_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_fst_631_);
lean_dec(v_snd_625_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_721_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v_fst_635_; lean_object* v_snd_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_720_; 
v_fst_635_ = lean_ctor_get(v_snd_626_, 0);
v_snd_636_ = lean_ctor_get(v_snd_626_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_snd_626_);
if (v_isSharedCheck_720_ == 0)
{
v___x_638_ = v_snd_626_;
v_isShared_639_ = v_isSharedCheck_720_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_snd_636_);
lean_inc(v_fst_635_);
lean_dec(v_snd_626_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_720_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_unbox(v_snd_636_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_642_ = l_Lean_instInhabitedNamePart_default;
v___x_643_ = lean_array_get_borrowed(v___x_642_, v___x_613_, v_i_617_);
v___x_673_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1));
v___x_674_ = l_Lean_instBEqNamePart_beq(v___x_643_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v_cont_678_; lean_object* v_entries_680_; lean_object* v_currentCtx_681_; 
v___x_675_ = lean_box(0);
v___x_676_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0));
v___x_677_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1));
v_cont_678_ = l_Lean_instBEqNamePart_beq(v___x_643_, v___x_677_);
if (v_cont_678_ == 0)
{
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_s_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_s_686_ = lean_ctor_get(v___x_643_, 0);
v___x_687_ = lean_string_utf8_byte_size(v_s_686_);
v___x_688_ = lean_unsigned_to_nat(5u);
v___x_689_ = lean_nat_dec_le(v___x_688_, v___x_687_);
if (v___x_689_ == 0)
{
goto v___jp_644_;
}
else
{
uint8_t v___x_690_; 
v___x_690_ = lean_string_memcmp(v_s_686_, v___x_676_, v___x_640_, v___x_640_, v___x_688_);
if (v___x_690_ == 0)
{
goto v___jp_644_;
}
else
{
lean_del_object(v___x_638_);
lean_del_object(v___x_633_);
lean_del_object(v___x_629_);
if (lean_obj_tag(v_fst_631_) == 1)
{
lean_object* v_val_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_val_691_ = lean_ctor_get(v_fst_631_, 0);
lean_inc(v_val_691_);
lean_dec_ref_known(v_fst_631_, 1);
v___x_692_ = lean_array_push(v_fst_627_, v_val_691_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_fst_635_);
lean_ctor_set(v___x_693_, 1, v_snd_636_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_675_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_692_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v_a_621_ = v___x_695_;
goto v___jp_620_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_fst_635_);
lean_ctor_set(v___x_696_, 1, v_snd_636_);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v_fst_631_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v_fst_627_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v_a_621_ = v___x_698_;
goto v___jp_620_;
}
}
}
}
else
{
goto v___jp_644_;
}
}
else
{
lean_del_object(v___x_638_);
lean_dec(v_snd_636_);
lean_del_object(v___x_633_);
lean_del_object(v___x_629_);
if (lean_obj_tag(v_fst_631_) == 1)
{
lean_object* v_val_699_; lean_object* v___x_700_; 
v_val_699_ = lean_ctor_get(v_fst_631_, 0);
lean_inc(v_val_699_);
lean_dec_ref_known(v_fst_631_, 1);
v___x_700_ = lean_array_push(v_fst_627_, v_val_699_);
v_entries_680_ = v___x_700_;
v_currentCtx_681_ = v___x_675_;
goto v___jp_679_;
}
else
{
v_entries_680_ = v_fst_627_;
v_currentCtx_681_ = v_fst_631_;
goto v___jp_679_;
}
}
v___jp_679_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_682_ = lean_box(v_cont_678_);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v_fst_635_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_currentCtx_681_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v_entries_680_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v_a_621_ = v___x_685_;
goto v___jp_620_;
}
}
else
{
lean_object* v_entries_702_; 
lean_del_object(v___x_638_);
lean_del_object(v___x_633_);
lean_del_object(v___x_629_);
if (lean_obj_tag(v_fst_631_) == 1)
{
lean_object* v_val_707_; lean_object* v___x_708_; 
v_val_707_ = lean_ctor_get(v_fst_631_, 0);
lean_inc(v_val_707_);
lean_dec_ref_known(v_fst_631_, 1);
v___x_708_ = lean_array_push(v_fst_627_, v_val_707_);
v_entries_702_ = v___x_708_;
goto v___jp_701_;
}
else
{
lean_dec(v_fst_631_);
v_entries_702_ = v_fst_627_;
goto v___jp_701_;
}
v___jp_701_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_703_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2));
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_fst_635_);
lean_ctor_set(v___x_704_, 1, v_snd_636_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_entries_702_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v_a_621_ = v___x_706_;
goto v___jp_620_;
}
}
v___jp_644_:
{
if (lean_obj_tag(v_fst_631_) == 0)
{
lean_object* v___x_645_; lean_object* v___x_647_; 
lean_inc(v___x_643_);
v___x_645_ = lean_array_push(v_fst_635_, v___x_643_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_645_);
v___x_647_ = v___x_638_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_snd_636_);
v___x_647_ = v_reuseFailAlloc_654_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_647_);
v___x_649_ = v___x_633_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fst_631_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_647_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_649_);
v___x_651_ = v___x_629_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_fst_627_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
v_a_621_ = v___x_651_;
goto v___jp_620_;
}
}
}
}
else
{
lean_object* v_val_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_672_; 
v_val_655_ = lean_ctor_get(v_fst_631_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_fst_631_);
if (v_isSharedCheck_672_ == 0)
{
v___x_657_ = v_fst_631_;
v_isShared_658_ = v_isSharedCheck_672_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_val_655_);
lean_dec(v_fst_631_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_672_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
lean_inc(v___x_643_);
v___x_659_ = lean_array_push(v_val_655_, v___x_643_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_671_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
if (v_isShared_639_ == 0)
{
v___x_663_ = v___x_638_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_fst_635_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_snd_636_);
v___x_663_ = v_reuseFailAlloc_670_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_665_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_663_);
lean_ctor_set(v___x_633_, 0, v___x_661_);
v___x_665_ = v___x_633_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_663_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_667_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_665_);
v___x_667_ = v___x_629_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_fst_627_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
v_a_621_ = v___x_667_;
goto v___jp_620_;
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
uint8_t v_skipNext_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
lean_dec(v_snd_636_);
v_skipNext_709_ = lean_nat_dec_eq(v___x_614_, v___x_640_);
v___x_710_ = lean_box(v_skipNext_709_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v___x_710_);
v___x_712_ = v___x_638_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_fst_635_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_710_);
v___x_712_ = v_reuseFailAlloc_719_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_712_);
v___x_714_ = v___x_633_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_fst_631_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_712_);
v___x_714_ = v_reuseFailAlloc_718_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_714_);
v___x_716_ = v___x_629_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_fst_627_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
v_a_621_ = v___x_716_;
goto v___jp_620_;
}
}
}
}
}
}
}
}
v___jp_620_:
{
lean_object* v___x_622_; 
v___x_622_ = lean_nat_add(v_i_617_, v_step_619_);
lean_dec(v_i_617_);
v_b_616_ = v_a_621_;
v_i_617_ = v___x_622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___boxed(lean_object* v___x_725_, lean_object* v___x_726_, lean_object* v_range_727_, lean_object* v_b_728_, lean_object* v_i_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_725_, v___x_726_, v_range_727_, v_b_728_, v_i_729_);
lean_dec_ref(v_range_727_);
lean_dec(v___x_726_);
lean_dec_ref(v___x_725_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(lean_object* v___x_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_snd_733_; lean_object* v_fst_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_791_; 
v_snd_733_ = lean_ctor_get(v_a_732_, 1);
v_fst_734_ = lean_ctor_get(v_a_732_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v_a_732_);
if (v_isSharedCheck_791_ == 0)
{
v___x_736_ = v_a_732_;
v_isShared_737_ = v_isSharedCheck_791_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_snd_733_);
lean_inc(v_fst_734_);
lean_dec(v_a_732_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_791_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_fst_738_; lean_object* v_snd_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_790_; 
v_fst_738_ = lean_ctor_get(v_snd_733_, 0);
v_snd_739_ = lean_ctor_get(v_snd_733_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_snd_733_);
if (v_isSharedCheck_790_ == 0)
{
v___x_741_ = v_snd_733_;
v_isShared_742_ = v_isSharedCheck_790_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_snd_739_);
lean_inc(v_fst_738_);
lean_dec(v_snd_733_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_790_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
uint8_t v___x_750_; 
v___x_750_ = lean_unbox(v_snd_739_);
if (v___x_750_ == 0)
{
goto v___jp_743_;
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = lean_array_get_size(v_fst_734_);
v___x_753_ = lean_nat_dec_eq(v___x_752_, v___x_751_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
lean_del_object(v___x_741_);
lean_del_object(v___x_736_);
v___x_754_ = l_Lean_instInhabitedNamePart_default;
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = lean_nat_sub(v___x_752_, v___x_755_);
v___x_757_ = lean_array_get_borrowed(v___x_754_, v_fst_734_, v___x_756_);
lean_dec(v___x_756_);
lean_inc(v___x_757_);
v___x_758_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_757_);
if (lean_obj_tag(v___x_758_) == 0)
{
uint8_t v_skipNext_759_; 
v_skipNext_759_ = lean_nat_dec_eq(v___x_731_, v___x_751_);
if (lean_obj_tag(v___x_757_) == 1)
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(2u);
v___x_761_ = lean_nat_dec_le(v___x_760_, v___x_752_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec(v_snd_739_);
v___x_762_ = lean_box(v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v_fst_738_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v_fst_734_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v_a_732_ = v___x_764_;
goto _start;
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_nat_sub(v___x_752_, v___x_760_);
v___x_767_ = lean_array_get_borrowed(v___x_754_, v_fst_734_, v___x_766_);
lean_dec(v___x_766_);
lean_inc(v___x_767_);
v___x_768_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_767_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec(v_snd_739_);
v___x_769_ = lean_box(v_skipNext_759_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v_fst_738_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_fst_734_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v_a_732_ = v___x_771_;
goto _start;
}
else
{
lean_object* v_val_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_val_773_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v___x_768_, 1);
v___x_774_ = lean_array_push(v_fst_738_, v_val_773_);
v___x_775_ = lean_array_pop(v_fst_734_);
v___x_776_ = lean_array_pop(v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_774_);
lean_ctor_set(v___x_777_, 1, v_snd_739_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v_a_732_ = v___x_778_;
goto _start;
}
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec(v_snd_739_);
v___x_780_ = lean_box(v_skipNext_759_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v_fst_738_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_fst_734_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v_a_732_ = v___x_782_;
goto _start;
}
}
else
{
lean_object* v_val_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_val_784_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v___x_758_, 1);
v___x_785_ = lean_array_push(v_fst_738_, v_val_784_);
v___x_786_ = lean_array_pop(v_fst_734_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v_snd_739_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v_a_732_ = v___x_788_;
goto _start;
}
}
else
{
goto v___jp_743_;
}
}
v___jp_743_:
{
lean_object* v___x_745_; 
if (v_isShared_742_ == 0)
{
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_fst_738_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_snd_739_);
v___x_745_ = v_reuseFailAlloc_749_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_747_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v___x_745_);
v___x_747_ = v___x_736_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_fst_734_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg___boxed(lean_object* v___x_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_792_, v_a_793_);
lean_dec(v___x_792_);
return v_res_794_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(lean_object* v_as_800_, size_t v_sz_801_, size_t v_i_802_, lean_object* v_b_803_){
_start:
{
lean_object* v_a_805_; uint8_t v___x_809_; 
v___x_809_ = lean_usize_dec_lt(v_i_802_, v_sz_801_);
if (v___x_809_ == 0)
{
return v_b_803_;
}
else
{
lean_object* v_a_810_; lean_object* v___y_812_; lean_object* v_name_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_a_810_ = lean_array_uget_borrowed(v_as_800_, v_i_802_);
v_name_831_ = lean_ctor_get(v_a_810_, 0);
v___x_832_ = lean_string_utf8_byte_size(v_name_831_);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_nat_dec_eq(v___x_832_, v___x_833_);
if (v___x_834_ == 0)
{
lean_inc_ref(v_name_831_);
v___y_812_ = v_name_831_;
goto v___jp_811_;
}
else
{
lean_object* v___x_835_; 
v___x_835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_812_ = v___x_835_;
goto v___jp_811_;
}
v___jp_811_:
{
lean_object* v_flags_813_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_flags_813_ = lean_ctor_get(v_a_810_, 1);
v___x_814_ = lean_array_get_size(v_flags_813_);
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_nat_dec_eq(v___x_814_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_818_ = lean_string_append(v_b_803_, v___x_817_);
v___x_819_ = lean_string_append(v___x_818_, v___y_812_);
lean_dec_ref(v___y_812_);
v___x_820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1));
v___x_821_ = lean_string_append(v___x_819_, v___x_820_);
v___x_822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
lean_inc_ref(v_flags_813_);
v___x_823_ = lean_array_to_list(v_flags_813_);
v___x_824_ = l_String_intercalate(v___x_822_, v___x_823_);
v___x_825_ = lean_string_append(v___x_821_, v___x_824_);
lean_dec_ref(v___x_824_);
v___x_826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_827_ = lean_string_append(v___x_825_, v___x_826_);
v_a_805_ = v___x_827_;
goto v___jp_804_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_829_ = lean_string_append(v_b_803_, v___x_828_);
v___x_830_ = lean_string_append(v___x_829_, v___y_812_);
lean_dec_ref(v___y_812_);
v_a_805_ = v___x_830_;
goto v___jp_804_;
}
}
}
v___jp_804_:
{
size_t v___x_806_; size_t v___x_807_; 
v___x_806_ = ((size_t)1ULL);
v___x_807_ = lean_usize_add(v_i_802_, v___x_806_);
v_i_802_ = v___x_807_;
v_b_803_ = v_a_805_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_800_ = stack[0].m_obj;
size_t v_sz_801_ = stack[1].m_num;
size_t v_i_802_ = stack[2].m_num;
lean_object* v_b_803_ = stack[3].m_obj;
lean_object* v_res_836_;
v_res_836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v_as_800_, v_sz_801_, v_i_802_, v_b_803_);
stack->m_obj
 = v_res_836_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___boxed(lean_object* v_as_837_, lean_object* v_sz_838_, lean_object* v_i_839_, lean_object* v_b_840_){
_start:
{
size_t v_sz_boxed_841_; size_t v_i_boxed_842_; lean_object* v_res_843_; 
v_sz_boxed_841_ = lean_unbox_usize(v_sz_838_);
lean_dec(v_sz_838_);
v_i_boxed_842_ = lean_unbox_usize(v_i_839_);
lean_dec(v_i_839_);
v_res_843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v_as_837_, v_sz_boxed_841_, v_i_boxed_842_, v_b_840_);
lean_dec_ref(v_as_837_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(lean_object* v_components_852_){
_start:
{
lean_object* v___y_854_; lean_object* v_result_855_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_876_; lean_object* v_parts_877_; lean_object* v_specEntries_878_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v_entries_888_; uint8_t v_skipNext_893_; 
v___x_859_ = lean_array_get_size(v_components_852_);
v___x_860_ = lean_unsigned_to_nat(0u);
v_skipNext_893_ = lean_nat_dec_eq(v___x_859_, v___x_860_);
if (v_skipNext_893_ == 0)
{
lean_object* v___x_894_; lean_object* v_fst_895_; lean_object* v_snd_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_951_; 
v___x_894_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_components_852_, v___x_860_, v___x_859_);
v_fst_895_ = lean_ctor_get(v___x_894_, 0);
v_snd_896_ = lean_ctor_get(v___x_894_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_951_ == 0)
{
v___x_898_ = v___x_894_;
v_isShared_899_ = v_isSharedCheck_951_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_snd_896_);
lean_inc(v_fst_895_);
lean_dec(v___x_894_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_951_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_parts_900_; lean_object* v_flags_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v_parts_900_ = l_Array_extract___redArg(v_components_852_, v_fst_895_, v___x_859_);
v_flags_901_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1));
v___x_902_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2));
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___x_902_);
lean_ctor_set(v___x_898_, 0, v_parts_900_);
v___x_904_ = v___x_898_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_parts_900_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_902_);
v___x_904_ = v_reuseFailAlloc_950_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; lean_object* v_fst_906_; lean_object* v_snd_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_949_; 
v___x_905_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_859_, v___x_904_);
v_fst_906_ = lean_ctor_get(v___x_905_, 0);
v_snd_907_ = lean_ctor_get(v___x_905_, 1);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_949_ == 0)
{
v___x_909_ = v___x_905_;
v_isShared_910_ = v_isSharedCheck_949_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_snd_907_);
lean_inc(v_fst_906_);
lean_dec(v___x_905_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_949_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v_flags_912_; uint8_t v___x_944_; 
v___x_944_ = lean_unbox(v_snd_896_);
lean_dec(v_snd_896_);
if (v___x_944_ == 0)
{
lean_object* v_fst_945_; 
v_fst_945_ = lean_ctor_get(v_snd_907_, 0);
lean_inc(v_fst_945_);
lean_dec(v_snd_907_);
v_flags_912_ = v_fst_945_;
goto v___jp_911_;
}
else
{
lean_object* v_fst_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_fst_946_ = lean_ctor_get(v_snd_907_, 0);
lean_inc(v_fst_946_);
lean_dec(v_snd_907_);
v___x_947_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3));
v___x_948_ = lean_array_push(v_fst_946_, v___x_947_);
v_flags_912_ = v___x_948_;
goto v___jp_911_;
}
v___jp_911_:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_913_ = lean_array_get_size(v_fst_906_);
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_915_, 0, v___x_860_);
lean_ctor_set(v___x_915_, 1, v___x_913_);
lean_ctor_set(v___x_915_, 2, v___x_914_);
v___x_916_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_915_, v_fst_906_, v___x_860_);
lean_dec(v_fst_906_);
lean_dec_ref_known(v___x_915_, 3);
v___x_917_ = lean_box(0);
v___x_918_ = lean_array_get_size(v___x_916_);
v___x_919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_919_, 0, v___x_860_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
lean_ctor_set(v___x_919_, 2, v___x_914_);
v___x_920_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_916_, v___x_919_, v___x_917_, v___x_860_);
lean_dec_ref_known(v___x_919_, 3);
if (lean_obj_tag(v___x_920_) == 1)
{
lean_object* v_val_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v_val_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc_n(v_val_921_, 2);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = l_Array_extract___redArg(v___x_916_, v___x_860_, v_val_921_);
v___x_923_ = l_Array_extract___redArg(v___x_916_, v_val_921_, v___x_918_);
lean_dec_ref(v___x_916_);
v___x_924_ = lean_array_get_size(v___x_923_);
v___x_925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_925_, 0, v___x_860_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
lean_ctor_set(v___x_925_, 2, v___x_914_);
v___x_926_ = lean_box(v_skipNext_893_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v___x_926_);
lean_ctor_set(v___x_909_, 0, v_flags_901_);
v___x_928_ = v___x_909_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_flags_901_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___x_926_);
v___x_928_ = v_reuseFailAlloc_943_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_snd_932_; lean_object* v_snd_933_; lean_object* v_fst_934_; 
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_917_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v_flags_901_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_923_, v___x_859_, v___x_925_, v___x_930_, v___x_860_);
lean_dec_ref_known(v___x_925_, 3);
lean_dec_ref(v___x_923_);
v_snd_932_ = lean_ctor_get(v___x_931_, 1);
v_snd_933_ = lean_ctor_get(v_snd_932_, 1);
lean_inc(v_snd_933_);
v_fst_934_ = lean_ctor_get(v_snd_932_, 0);
if (lean_obj_tag(v_fst_934_) == 1)
{
lean_object* v_fst_935_; lean_object* v_fst_936_; lean_object* v_val_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
lean_inc_ref(v_fst_934_);
v_fst_935_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_fst_935_);
lean_dec_ref(v___x_931_);
v_fst_936_ = lean_ctor_get(v_snd_933_, 0);
lean_inc(v_fst_936_);
lean_dec(v_snd_933_);
v_val_937_ = lean_ctor_get(v_fst_934_, 0);
lean_inc(v_val_937_);
lean_dec_ref_known(v_fst_934_, 1);
v___x_938_ = lean_array_get_size(v_val_937_);
v___x_939_ = lean_nat_dec_eq(v___x_938_, v___x_860_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
v___x_940_ = lean_array_push(v_fst_935_, v_val_937_);
v___y_884_ = v_flags_901_;
v___y_885_ = v___x_922_;
v___y_886_ = v_fst_936_;
v___y_887_ = v_flags_912_;
v_entries_888_ = v___x_940_;
goto v___jp_883_;
}
else
{
lean_dec(v_val_937_);
v___y_884_ = v_flags_901_;
v___y_885_ = v___x_922_;
v___y_886_ = v_fst_936_;
v___y_887_ = v_flags_912_;
v_entries_888_ = v_fst_935_;
goto v___jp_883_;
}
}
else
{
lean_object* v_fst_941_; lean_object* v_fst_942_; 
v_fst_941_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_fst_941_);
lean_dec_ref(v___x_931_);
v_fst_942_ = lean_ctor_get(v_snd_933_, 0);
lean_inc(v_fst_942_);
lean_dec(v_snd_933_);
v___y_884_ = v_flags_901_;
v___y_885_ = v___x_922_;
v___y_886_ = v_fst_942_;
v___y_887_ = v_flags_912_;
v_entries_888_ = v_fst_941_;
goto v___jp_883_;
}
}
}
else
{
lean_dec(v___x_920_);
lean_del_object(v___x_909_);
v___y_876_ = v_flags_912_;
v_parts_877_ = v___x_916_;
v_specEntries_878_ = v_flags_901_;
goto v___jp_875_;
}
}
}
}
}
}
else
{
lean_object* v___x_952_; 
v___x_952_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_952_;
}
v___jp_853_:
{
size_t v_sz_856_; size_t v___x_857_; lean_object* v___x_858_; 
v_sz_856_ = lean_array_size(v___y_854_);
v___x_857_ = ((size_t)0ULL);
v___x_858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v___y_854_, v_sz_856_, v___x_857_, v_result_855_);
lean_dec_ref(v___y_854_);
return v___x_858_;
}
v___jp_861_:
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = lean_array_get_size(v___y_863_);
v___x_866_ = lean_nat_dec_eq(v___x_865_, v___x_860_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_867_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0));
v___x_868_ = lean_string_append(v___y_864_, v___x_867_);
v___x_869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
v___x_870_ = lean_array_to_list(v___y_863_);
v___x_871_ = l_String_intercalate(v___x_869_, v___x_870_);
v___x_872_ = lean_string_append(v___x_868_, v___x_871_);
lean_dec_ref(v___x_871_);
v___x_873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_874_ = lean_string_append(v___x_872_, v___x_873_);
v___y_854_ = v___y_862_;
v_result_855_ = v___x_874_;
goto v___jp_853_;
}
else
{
lean_dec_ref(v___y_863_);
v___y_854_ = v___y_862_;
v_result_855_ = v___y_864_;
goto v___jp_853_;
}
}
v___jp_875_:
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_array_get_size(v_parts_877_);
v___x_880_ = lean_nat_dec_eq(v___x_879_, v___x_860_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_parts_877_);
lean_dec_ref(v_parts_877_);
v___y_862_ = v_specEntries_878_;
v___y_863_ = v___y_876_;
v___y_864_ = v___x_881_;
goto v___jp_861_;
}
else
{
lean_object* v___x_882_; 
lean_dec_ref(v_parts_877_);
v___x_882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_862_ = v_specEntries_878_;
v___y_863_ = v___y_876_;
v___y_864_ = v___x_882_;
goto v___jp_861_;
}
}
v___jp_883_:
{
size_t v_sz_889_; size_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_sz_889_ = lean_array_size(v_entries_888_);
v___x_890_ = ((size_t)0ULL);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_859_, v_entries_888_, v_sz_889_, v___x_890_, v___y_884_);
lean_dec_ref(v_entries_888_);
v___x_892_ = l_Array_append___redArg(v___y_885_, v___y_886_);
lean_dec(v___y_886_);
v___y_876_ = v___y_887_;
v_parts_877_ = v___x_892_;
v_specEntries_878_ = v___x_891_;
goto v___jp_875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___boxed(lean_object* v_components_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v_components_953_);
lean_dec_ref(v_components_953_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(lean_object* v___x_955_, lean_object* v_inst_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_955_, v_a_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___boxed(lean_object* v___x_959_, lean_object* v_inst_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(v___x_959_, v_inst_960_, v_a_961_);
lean_dec(v___x_959_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(lean_object* v_range_963_, lean_object* v_b_964_, lean_object* v_i_965_, lean_object* v_hs_966_, lean_object* v_hl_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v_range_963_, v_b_964_, v_i_965_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___boxed(lean_object* v_range_969_, lean_object* v_b_970_, lean_object* v_i_971_, lean_object* v_hs_972_, lean_object* v_hl_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(v_range_969_, v_b_970_, v_i_971_, v_hs_972_, v_hl_973_);
lean_dec_ref(v_b_970_);
lean_dec_ref(v_range_969_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(lean_object* v___x_975_, lean_object* v_range_976_, lean_object* v_b_977_, lean_object* v_i_978_, lean_object* v_hs_979_, lean_object* v_hl_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_975_, v_range_976_, v_b_977_, v_i_978_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___boxed(lean_object* v___x_982_, lean_object* v_range_983_, lean_object* v_b_984_, lean_object* v_i_985_, lean_object* v_hs_986_, lean_object* v_hl_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(v___x_982_, v_range_983_, v_b_984_, v_i_985_, v_hs_986_, v_hl_987_);
lean_dec(v_b_984_);
lean_dec_ref(v_range_983_);
lean_dec_ref(v___x_982_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(lean_object* v___x_989_, lean_object* v___x_990_, lean_object* v_range_991_, lean_object* v_b_992_, lean_object* v_i_993_, lean_object* v_hs_994_, lean_object* v_hl_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_989_, v___x_990_, v_range_991_, v_b_992_, v_i_993_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___boxed(lean_object* v___x_997_, lean_object* v___x_998_, lean_object* v_range_999_, lean_object* v_b_1000_, lean_object* v_i_1001_, lean_object* v_hs_1002_, lean_object* v_hl_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(v___x_997_, v___x_998_, v_range_999_, v_b_1000_, v_i_1001_, v_hs_1002_, v_hl_1003_);
lean_dec_ref(v_range_999_);
lean_dec(v___x_998_);
lean_dec_ref(v___x_997_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(lean_object* v_body_1005_){
_start:
{
lean_object* v_name_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_name_1006_ = l_Lean_Name_demangle(v_body_1005_);
v___x_1007_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(v_name_1006_);
lean_dec(v_name_1006_);
v___x_1008_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v___x_1007_);
lean_dec_ref(v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody___boxed(lean_object* v_body_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_body_1009_);
lean_dec_ref(v_body_1009_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(lean_object* v_s_1014_, lean_object* v___x_1015_, lean_object* v_a_1016_, lean_object* v_b_1017_){
_start:
{
uint8_t v_decide_1018_; 
v_decide_1018_ = lean_nat_dec_eq(v_a_1016_, v___x_1015_);
if (v_decide_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; uint32_t v___x_1022_; uint32_t v___x_1023_; uint8_t v___x_1024_; 
lean_dec_ref(v_b_1017_);
v___x_1019_ = lean_box(0);
v___x_1020_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1021_ = lean_string_utf8_next_fast(v_s_1014_, v_a_1016_);
v___x_1022_ = lean_string_utf8_get_fast(v_s_1014_, v_a_1016_);
v___x_1023_ = 95;
v___x_1024_ = lean_uint32_dec_eq(v___x_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_dec(v_a_1016_);
v_a_1016_ = v___x_1021_;
v_b_1017_ = v___x_1020_;
goto _start;
}
else
{
lean_object* v___x_1026_; uint8_t v_decide_1027_; 
v___x_1026_ = lean_unsigned_to_nat(0u);
v_decide_1027_ = lean_nat_dec_eq(v_a_1016_, v___x_1026_);
if (v_decide_1027_ == 0)
{
if (v___x_1024_ == 0)
{
lean_dec(v_a_1016_);
v_a_1016_ = v___x_1021_;
v_b_1017_ = v___x_1020_;
goto _start;
}
else
{
lean_object* v___x_1029_; uint8_t v_decide_1030_; 
v___x_1029_ = lean_string_utf8_byte_size(v_s_1014_);
v_decide_1030_ = lean_nat_dec_eq(v___x_1021_, v___x_1029_);
if (v_decide_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_string_utf8_extract_fast(v_s_1014_, v___x_1026_, v_a_1016_);
lean_dec(v_a_1016_);
v___x_1032_ = l_Lean_Name_demangle_x3f(v___x_1031_);
if (lean_obj_tag(v___x_1032_) == 1)
{
lean_object* v_val_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1055_; 
v_val_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1055_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_val_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1055_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
if (lean_obj_tag(v_val_1033_) == 1)
{
lean_object* v_pre_1037_; 
v_pre_1037_ = lean_ctor_get(v_val_1033_, 0);
lean_inc(v_pre_1037_);
lean_dec_ref_known(v_val_1033_, 2);
if (lean_obj_tag(v_pre_1037_) == 0)
{
lean_object* v___x_1038_; lean_object* v___y_1040_; lean_object* v___x_1048_; 
v___x_1038_ = lean_string_utf8_extract_fast(v_s_1014_, v___x_1021_, v___x_1029_);
v___x_1048_ = l_Lean_Name_demangle_x3f(v___x_1038_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_dec_ref(v___x_1038_);
lean_del_object(v___x_1035_);
lean_dec_ref(v___x_1031_);
v_a_1016_ = v___x_1021_;
v_b_1017_ = v___x_1020_;
goto _start;
}
else
{
lean_object* v___x_1050_; 
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = l_Lean_Name_demangle(v___x_1031_);
if (lean_obj_tag(v___x_1050_) == 1)
{
lean_object* v_pre_1051_; 
v_pre_1051_ = lean_ctor_get(v___x_1050_, 0);
if (lean_obj_tag(v_pre_1051_) == 0)
{
lean_object* v_str_1052_; 
lean_dec_ref(v___x_1031_);
v_str_1052_ = lean_ctor_get(v___x_1050_, 1);
lean_inc_ref(v_str_1052_);
lean_dec_ref_known(v___x_1050_, 2);
v___y_1040_ = v_str_1052_;
goto v___jp_1039_;
}
else
{
lean_dec_ref_known(v___x_1050_, 2);
v___y_1040_ = v___x_1031_;
goto v___jp_1039_;
}
}
else
{
lean_dec(v___x_1050_);
v___y_1040_ = v___x_1031_;
goto v___jp_1039_;
}
}
v___jp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1041_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v___x_1038_);
lean_dec_ref(v___x_1038_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___y_1040_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1042_);
v___x_1044_ = v___x_1035_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v___x_1019_);
v___x_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
}
}
else
{
lean_dec(v_pre_1037_);
lean_del_object(v___x_1035_);
lean_dec_ref(v___x_1031_);
v_a_1016_ = v___x_1021_;
v_b_1017_ = v___x_1020_;
goto _start;
}
}
else
{
lean_del_object(v___x_1035_);
lean_dec(v_val_1033_);
lean_dec_ref(v___x_1031_);
v_a_1016_ = v___x_1021_;
v_b_1017_ = v___x_1020_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1032_);
lean_dec_ref(v___x_1031_);
v_a_1016_ = v___x_1021_;
v_b_1017_ = v___x_1020_;
goto _start;
}
}
else
{
lean_dec(v_a_1016_);
v_a_1016_ = v___x_1021_;
v_b_1017_ = v___x_1020_;
goto _start;
}
}
}
else
{
lean_dec(v_a_1016_);
v_a_1016_ = v___x_1021_;
v_b_1017_ = v___x_1020_;
goto _start;
}
}
}
else
{
lean_object* v___x_1059_; 
lean_dec(v_a_1016_);
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v_b_1017_);
return v___x_1059_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___boxed(lean_object* v_s_1060_, lean_object* v___x_1061_, lean_object* v_a_1062_, lean_object* v_b_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1060_, v___x_1061_, v_a_1062_, v_b_1063_);
lean_dec(v___x_1061_);
lean_dec_ref(v_s_1060_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(lean_object* v_s_1065_){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_string_utf8_byte_size(v_s_1065_);
v___x_1068_ = lean_box(0);
v___x_1069_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1070_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1065_, v___x_1067_, v___x_1066_, v___x_1069_);
if (lean_obj_tag(v___x_1070_) == 0)
{
return v___x_1068_;
}
else
{
lean_object* v_val_1071_; lean_object* v_fst_1072_; 
v_val_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_val_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v_fst_1072_ = lean_ctor_get(v_val_1071_, 0);
lean_inc(v_fst_1072_);
lean_dec(v_val_1071_);
if (lean_obj_tag(v_fst_1072_) == 0)
{
return v___x_1068_;
}
else
{
return v_fst_1072_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg___boxed(lean_object* v_s_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_s_1073_);
lean_dec_ref(v_s_1073_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(lean_object* v_s_1075_, lean_object* v___x_1076_, lean_object* v___x_1077_, lean_object* v_inst_1078_, lean_object* v_R_1079_, lean_object* v_a_1080_, lean_object* v_b_1081_, lean_object* v_c_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1075_, v___x_1076_, v_a_1080_, v_b_1081_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___boxed(lean_object* v_s_1084_, lean_object* v___x_1085_, lean_object* v___x_1086_, lean_object* v_inst_1087_, lean_object* v_R_1088_, lean_object* v_a_1089_, lean_object* v_b_1090_, lean_object* v_c_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(v_s_1084_, v___x_1085_, v___x_1086_, v_inst_1087_, v_R_1088_, v_a_1089_, v_b_1090_, v_c_1091_);
lean_dec_ref(v___x_1086_);
lean_dec(v___x_1085_);
lean_dec_ref(v_s_1084_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(lean_object* v_s_1093_, lean_object* v___x_1094_, lean_object* v___x_1095_, lean_object* v_a_1096_, lean_object* v_b_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_box(0);
switch(lean_obj_tag(v_a_1096_))
{
case 0:
{
lean_object* v_pos_1099_; lean_object* v___x_1100_; 
v_pos_1099_ = lean_ctor_get(v_a_1096_, 0);
lean_inc(v_pos_1099_);
lean_dec_ref_known(v_a_1096_, 1);
v___x_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_pos_1099_);
return v___x_1100_;
}
case 1:
{
lean_object* v_pos_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1110_; 
v_pos_1101_ = lean_ctor_get(v_a_1096_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_a_1096_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1103_ = v_a_1096_;
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_pos_1101_);
lean_dec(v_a_1096_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1105_ = lean_string_utf8_next_fast(v_s_1093_, v_pos_1101_);
lean_dec(v_pos_1101_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1105_);
v___x_1107_ = v___x_1103_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
v_a_1096_ = v___x_1107_;
v_b_1097_ = v___x_1098_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1111_; lean_object* v_table_1112_; lean_object* v_stackPos_1113_; lean_object* v_needlePos_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1167_; 
v_needle_1111_ = lean_ctor_get(v_a_1096_, 0);
v_table_1112_ = lean_ctor_get(v_a_1096_, 1);
v_stackPos_1113_ = lean_ctor_get(v_a_1096_, 2);
v_needlePos_1114_ = lean_ctor_get(v_a_1096_, 3);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_a_1096_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1116_ = v_a_1096_;
v_isShared_1117_ = v_isSharedCheck_1167_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_needlePos_1114_);
lean_inc(v_stackPos_1113_);
lean_inc(v_table_1112_);
lean_inc(v_needle_1111_);
lean_dec(v_a_1096_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1167_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_str_1118_; lean_object* v_startInclusive_1119_; lean_object* v_endExclusive_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v_str_1118_ = lean_ctor_get(v_needle_1111_, 0);
v_startInclusive_1119_ = lean_ctor_get(v_needle_1111_, 1);
v_endExclusive_1120_ = lean_ctor_get(v_needle_1111_, 2);
v___x_1121_ = lean_nat_sub(v_stackPos_1113_, v_needlePos_1114_);
v___x_1122_ = lean_nat_sub(v_endExclusive_1120_, v_startInclusive_1119_);
v___x_1123_ = lean_nat_add(v___x_1121_, v___x_1122_);
v___x_1124_ = lean_nat_dec_le(v___x_1123_, v___x_1095_);
lean_dec(v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
lean_dec(v___x_1122_);
lean_del_object(v___x_1116_);
lean_dec(v_needlePos_1114_);
lean_dec(v_stackPos_1113_);
lean_dec_ref(v_table_1112_);
lean_dec_ref(v_needle_1111_);
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_nat_add(v___x_1121_, v___x_1125_);
lean_dec(v___x_1121_);
v___x_1127_ = lean_nat_dec_le(v___x_1126_, v___x_1095_);
lean_dec(v___x_1126_);
if (v___x_1127_ == 0)
{
lean_inc(v_b_1097_);
return v_b_1097_;
}
else
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_box(3);
v_a_1096_ = v___x_1128_;
v_b_1097_ = v___x_1098_;
goto _start;
}
}
else
{
uint8_t v_stackByte_1130_; lean_object* v___x_1131_; uint8_t v_patByte_1132_; uint8_t v___x_1133_; 
lean_dec(v___x_1121_);
lean_inc(v_stackPos_1113_);
v_stackByte_1130_ = lean_string_get_byte_fast(v_s_1093_, v_stackPos_1113_);
v___x_1131_ = lean_nat_add(v_startInclusive_1119_, v_needlePos_1114_);
v_patByte_1132_ = lean_string_get_byte_fast(v_str_1118_, v___x_1131_);
v___x_1133_ = lean_uint8_dec_eq(v_stackByte_1130_, v_patByte_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; uint8_t v_decide_1135_; 
lean_dec(v___x_1122_);
v___x_1134_ = lean_unsigned_to_nat(0u);
v_decide_1135_ = lean_nat_dec_eq(v_needlePos_1114_, v___x_1134_);
if (v_decide_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v_newNeedlePos_1138_; uint8_t v___x_1139_; 
v___x_1136_ = lean_unsigned_to_nat(1u);
v___x_1137_ = lean_nat_sub(v_needlePos_1114_, v___x_1136_);
lean_dec(v_needlePos_1114_);
v_newNeedlePos_1138_ = lean_array_fget_borrowed(v_table_1112_, v___x_1137_);
lean_dec(v___x_1137_);
v___x_1139_ = lean_nat_dec_eq(v_newNeedlePos_1138_, v___x_1134_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1141_; 
lean_inc(v_newNeedlePos_1138_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 3, v_newNeedlePos_1138_);
v___x_1141_ = v___x_1116_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_needle_1111_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_table_1112_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_stackPos_1113_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_newNeedlePos_1138_);
v___x_1141_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
v_a_1096_ = v___x_1141_;
v_b_1097_ = v___x_1098_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1144_; lean_object* v___x_1146_; 
v_nextStackPos_1144_ = l_String_Slice_posGE___redArg(v___x_1094_, v_stackPos_1113_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 3, v___x_1134_);
lean_ctor_set(v___x_1116_, 2, v_nextStackPos_1144_);
v___x_1146_ = v___x_1116_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_needle_1111_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_table_1112_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_nextStackPos_1144_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v___x_1134_);
v___x_1146_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
v_a_1096_ = v___x_1146_;
v_b_1097_ = v___x_1098_;
goto _start;
}
}
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_nextStackPos_1151_; lean_object* v___x_1153_; 
lean_dec(v_needlePos_1114_);
v___x_1149_ = lean_unsigned_to_nat(1u);
v___x_1150_ = lean_nat_add(v_stackPos_1113_, v___x_1149_);
lean_dec(v_stackPos_1113_);
v_nextStackPos_1151_ = l_String_Slice_posGE___redArg(v___x_1094_, v___x_1150_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 3, v___x_1134_);
lean_ctor_set(v___x_1116_, 2, v_nextStackPos_1151_);
v___x_1153_ = v___x_1116_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_needle_1111_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_table_1112_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_nextStackPos_1151_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v___x_1134_);
v___x_1153_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
v_a_1096_ = v___x_1153_;
v_b_1097_ = v___x_1098_;
goto _start;
}
}
}
else
{
lean_object* v___x_1156_; lean_object* v_nextStackPos_1157_; lean_object* v_nextNeedlePos_1158_; uint8_t v_decide_1159_; 
v___x_1156_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1157_ = lean_nat_add(v_stackPos_1113_, v___x_1156_);
lean_dec(v_stackPos_1113_);
v_nextNeedlePos_1158_ = lean_nat_add(v_needlePos_1114_, v___x_1156_);
lean_dec(v_needlePos_1114_);
v_decide_1159_ = lean_nat_dec_eq(v_nextNeedlePos_1158_, v___x_1122_);
lean_dec(v___x_1122_);
if (v_decide_1159_ == 0)
{
lean_object* v___x_1161_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 3, v_nextNeedlePos_1158_);
lean_ctor_set(v___x_1116_, 2, v_nextStackPos_1157_);
v___x_1161_ = v___x_1116_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_needle_1111_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_table_1112_);
lean_ctor_set(v_reuseFailAlloc_1163_, 2, v_nextStackPos_1157_);
lean_ctor_set(v_reuseFailAlloc_1163_, 3, v_nextNeedlePos_1158_);
v___x_1161_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
v_a_1096_ = v___x_1161_;
goto _start;
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_del_object(v___x_1116_);
lean_dec_ref(v_table_1112_);
lean_dec_ref(v_needle_1111_);
v___x_1164_ = lean_nat_sub(v_nextStackPos_1157_, v_nextNeedlePos_1158_);
lean_dec(v_nextNeedlePos_1158_);
lean_dec(v_nextStackPos_1157_);
v___x_1165_ = l_String_Slice_pos_x21(v___x_1094_, v___x_1164_);
lean_dec(v___x_1164_);
v___x_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
}
}
}
default: 
{
lean_inc(v_b_1097_);
return v_b_1097_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg___boxed(lean_object* v_s_1168_, lean_object* v___x_1169_, lean_object* v___x_1170_, lean_object* v_a_1171_, lean_object* v_b_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1168_, v___x_1169_, v___x_1170_, v_a_1171_, v_b_1172_);
lean_dec(v_b_1172_);
lean_dec(v___x_1170_);
lean_dec_ref(v___x_1169_);
lean_dec_ref(v_s_1168_);
return v_res_1173_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1));
v___x_1180_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1179_);
return v___x_1180_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2);
v___x_1183_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1));
v___x_1184_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___x_1182_);
lean_ctor_set(v___x_1184_, 2, v___x_1181_);
lean_ctor_set(v___x_1184_, 3, v___x_1181_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(lean_object* v_s_1185_){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1187_ = lean_string_utf8_byte_size(v_s_1185_);
lean_inc_ref(v_s_1185_);
v___x_1188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1188_, 0, v_s_1185_);
lean_ctor_set(v___x_1188_, 1, v___x_1186_);
lean_ctor_set(v___x_1188_, 2, v___x_1187_);
v___x_1189_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
v___x_1190_ = lean_box(0);
v___x_1191_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1185_, v___x_1188_, v___x_1187_, v___x_1189_, v___x_1190_);
lean_dec_ref_known(v___x_1188_, 3);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v_s_1185_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
return v___x_1193_;
}
else
{
lean_object* v_val_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_val_1194_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_val_1194_);
lean_dec_ref_known(v___x_1191_, 1);
v___x_1195_ = lean_string_utf8_extract_fast(v_s_1185_, v___x_1186_, v_val_1194_);
v___x_1196_ = lean_string_utf8_extract_fast(v_s_1185_, v_val_1194_, v___x_1187_);
lean_dec(v_val_1194_);
lean_dec_ref(v_s_1185_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(lean_object* v_s_1198_, lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v_inst_1201_, lean_object* v_R_1202_, lean_object* v_a_1203_, lean_object* v_b_1204_, lean_object* v_c_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1198_, v___x_1199_, v___x_1200_, v_a_1203_, v_b_1204_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___boxed(lean_object* v_s_1207_, lean_object* v___x_1208_, lean_object* v___x_1209_, lean_object* v_inst_1210_, lean_object* v_R_1211_, lean_object* v_a_1212_, lean_object* v_b_1213_, lean_object* v_c_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(v_s_1207_, v___x_1208_, v___x_1209_, v_inst_1210_, v_R_1211_, v_a_1212_, v_b_1213_, v_c_1214_);
lean_dec(v_b_1213_);
lean_dec(v___x_1209_);
lean_dec_ref(v___x_1208_);
lean_dec_ref(v_s_1207_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(lean_object* v_s_1227_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10));
lean_inc_ref(v_s_1227_);
v___x_1344_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1227_, v___x_1343_);
if (lean_obj_tag(v___x_1344_) == 1)
{
lean_object* v_val_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1358_; 
v_val_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1358_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_val_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1358_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = lean_string_utf8_byte_size(v_val_1345_);
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_nat_dec_eq(v___x_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
lean_dec_ref(v_s_1227_);
v___x_1352_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1353_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1345_);
lean_dec(v_val_1345_);
v___x_1354_ = lean_string_append(v___x_1352_, v___x_1353_);
lean_dec_ref(v___x_1353_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1354_);
v___x_1356_ = v___x_1347_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
else
{
lean_del_object(v___x_1347_);
lean_dec(v_val_1345_);
goto v___jp_1321_;
}
}
}
else
{
lean_dec(v___x_1344_);
goto v___jp_1321_;
}
v___jp_1228_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0));
v___x_1230_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1227_, v___x_1229_);
if (lean_obj_tag(v___x_1230_) == 1)
{
lean_object* v_val_1231_; lean_object* v___x_1232_; 
v_val_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_val_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v___x_1232_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1231_);
lean_dec(v_val_1231_);
if (lean_obj_tag(v___x_1232_) == 1)
{
lean_object* v_val_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1247_; 
v_val_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1247_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_val_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1247_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_fst_1237_; lean_object* v_snd_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
v_fst_1237_ = lean_ctor_get(v_val_1233_, 0);
lean_inc(v_fst_1237_);
v_snd_1238_ = lean_ctor_get(v_val_1233_, 1);
lean_inc(v_snd_1238_);
lean_dec(v_val_1233_);
v___x_1239_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1240_ = lean_string_append(v_fst_1237_, v___x_1239_);
v___x_1241_ = lean_string_append(v___x_1240_, v_snd_1238_);
lean_dec(v_snd_1238_);
v___x_1242_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1243_ = lean_string_append(v___x_1241_, v___x_1242_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1243_);
v___x_1245_ = v___x_1235_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_object* v___x_1248_; 
lean_dec(v___x_1232_);
v___x_1248_ = lean_box(0);
return v___x_1248_;
}
}
else
{
lean_object* v___x_1249_; 
lean_dec(v___x_1230_);
v___x_1249_ = lean_box(0);
return v___x_1249_;
}
}
v___jp_1250_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3));
lean_inc_ref(v_s_1227_);
v___x_1252_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1227_, v___x_1251_);
if (lean_obj_tag(v___x_1252_) == 1)
{
lean_object* v_val_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1264_; 
v_val_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1264_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_val_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1264_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1257_ = lean_string_utf8_byte_size(v_val_1253_);
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_nat_dec_eq(v___x_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1262_; 
lean_dec_ref(v_s_1227_);
v___x_1260_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1253_);
lean_dec(v_val_1253_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1260_);
v___x_1262_ = v___x_1255_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
else
{
lean_del_object(v___x_1255_);
lean_dec(v_val_1253_);
goto v___jp_1228_;
}
}
}
else
{
lean_dec(v___x_1252_);
goto v___jp_1228_;
}
}
v___jp_1265_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4));
lean_inc_ref(v_s_1227_);
v___x_1267_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1227_, v___x_1266_);
if (lean_obj_tag(v___x_1267_) == 1)
{
lean_object* v_val_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1281_; 
v_val_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1281_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_val_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1281_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1272_ = lean_string_utf8_byte_size(v_val_1268_);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_nat_dec_eq(v___x_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
lean_dec_ref(v_s_1227_);
v___x_1275_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1276_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1268_);
lean_dec(v_val_1268_);
v___x_1277_ = lean_string_append(v___x_1275_, v___x_1276_);
lean_dec_ref(v___x_1276_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1277_);
v___x_1279_ = v___x_1270_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
else
{
lean_del_object(v___x_1270_);
lean_dec(v_val_1268_);
goto v___jp_1250_;
}
}
}
else
{
lean_dec(v___x_1267_);
goto v___jp_1250_;
}
}
v___jp_1282_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6));
lean_inc_ref(v_s_1227_);
v___x_1284_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1227_, v___x_1283_);
if (lean_obj_tag(v___x_1284_) == 1)
{
lean_object* v_val_1285_; lean_object* v___x_1286_; 
v_val_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_val_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1285_);
lean_dec(v_val_1285_);
if (lean_obj_tag(v___x_1286_) == 1)
{
lean_object* v_val_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_s_1227_);
v_val_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1303_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_val_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1303_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v_fst_1291_; lean_object* v_snd_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v_fst_1291_ = lean_ctor_get(v_val_1287_, 0);
lean_inc(v_fst_1291_);
v_snd_1292_ = lean_ctor_get(v_val_1287_, 1);
lean_inc(v_snd_1292_);
lean_dec(v_val_1287_);
v___x_1293_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1294_ = lean_string_append(v___x_1293_, v_fst_1291_);
lean_dec(v_fst_1291_);
v___x_1295_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1296_ = lean_string_append(v___x_1294_, v___x_1295_);
v___x_1297_ = lean_string_append(v___x_1296_, v_snd_1292_);
lean_dec(v_snd_1292_);
v___x_1298_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1299_ = lean_string_append(v___x_1297_, v___x_1298_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1299_);
v___x_1301_ = v___x_1289_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
else
{
lean_dec(v___x_1286_);
goto v___jp_1265_;
}
}
else
{
lean_dec(v___x_1284_);
goto v___jp_1265_;
}
}
v___jp_1304_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7));
lean_inc_ref(v_s_1227_);
v___x_1306_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1227_, v___x_1305_);
if (lean_obj_tag(v___x_1306_) == 1)
{
lean_object* v_val_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1320_; 
v_val_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1320_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_val_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1320_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1311_ = lean_string_utf8_byte_size(v_val_1307_);
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = lean_nat_dec_eq(v___x_1311_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_dec_ref(v_s_1227_);
v___x_1314_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1315_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1307_);
lean_dec(v_val_1307_);
v___x_1316_ = lean_string_append(v___x_1314_, v___x_1315_);
lean_dec_ref(v___x_1315_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1316_);
v___x_1318_ = v___x_1309_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
else
{
lean_del_object(v___x_1309_);
lean_dec(v_val_1307_);
goto v___jp_1282_;
}
}
}
else
{
lean_dec(v___x_1306_);
goto v___jp_1282_;
}
}
v___jp_1321_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8));
lean_inc_ref(v_s_1227_);
v___x_1323_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1227_, v___x_1322_);
if (lean_obj_tag(v___x_1323_) == 1)
{
lean_object* v_val_1324_; lean_object* v___x_1325_; 
v_val_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_val_1324_);
lean_dec_ref_known(v___x_1323_, 1);
v___x_1325_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1324_);
lean_dec(v_val_1324_);
if (lean_obj_tag(v___x_1325_) == 1)
{
lean_object* v_val_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref(v_s_1227_);
v_val_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1342_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_val_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1342_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v_fst_1330_; lean_object* v_snd_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v_fst_1330_ = lean_ctor_get(v_val_1326_, 0);
lean_inc(v_fst_1330_);
v_snd_1331_ = lean_ctor_get(v_val_1326_, 1);
lean_inc(v_snd_1331_);
lean_dec(v_val_1326_);
v___x_1332_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1333_ = lean_string_append(v___x_1332_, v_fst_1330_);
lean_dec(v_fst_1330_);
v___x_1334_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1335_ = lean_string_append(v___x_1333_, v___x_1334_);
v___x_1336_ = lean_string_append(v___x_1335_, v_snd_1331_);
lean_dec(v_snd_1331_);
v___x_1337_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1338_ = lean_string_append(v___x_1336_, v___x_1337_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1338_);
v___x_1340_ = v___x_1328_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
else
{
lean_dec(v___x_1325_);
goto v___jp_1304_;
}
}
else
{
lean_dec(v___x_1323_);
goto v___jp_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleSymbol(lean_object* v_symbol_1368_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1369_ = lean_string_utf8_byte_size(v_symbol_1368_);
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = lean_nat_dec_eq(v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v_fst_1373_; lean_object* v_snd_1374_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1372_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(v_symbol_1368_);
v_fst_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc_n(v_fst_1373_, 2);
v_snd_1374_ = lean_ctor_get(v___x_1372_, 1);
lean_inc(v_snd_1374_);
lean_dec_ref(v___x_1372_);
v___x_1399_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__5));
v___x_1400_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_fst_1373_, v___x_1399_);
if (lean_obj_tag(v___x_1400_) == 1)
{
lean_object* v_val_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1421_; 
v_val_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1421_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_val_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1421_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
uint8_t v___x_1405_; 
lean_inc(v_val_1401_);
v___x_1405_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_1401_);
if (v___x_1405_ == 0)
{
lean_del_object(v___x_1403_);
lean_dec(v_val_1401_);
goto v___jp_1375_;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_r_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
lean_dec(v_fst_1373_);
v___x_1406_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__6));
v___x_1407_ = lean_string_append(v___x_1406_, v_val_1401_);
lean_dec(v_val_1401_);
v___x_1408_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__7));
v_r_1409_ = lean_string_append(v___x_1407_, v___x_1408_);
v___x_1410_ = lean_string_utf8_byte_size(v_snd_1374_);
v___x_1411_ = lean_nat_dec_eq(v___x_1410_, v___x_1370_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1412_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1413_ = lean_string_append(v_r_1409_, v___x_1412_);
v___x_1414_ = lean_string_append(v___x_1413_, v_snd_1374_);
lean_dec(v_snd_1374_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1414_);
v___x_1416_ = v___x_1403_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
else
{
lean_object* v___x_1419_; 
lean_dec(v_snd_1374_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v_r_1409_);
v___x_1419_ = v___x_1403_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_r_1409_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
else
{
lean_dec(v___x_1400_);
goto v___jp_1375_;
}
v___jp_1375_:
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1376_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__0));
v___x_1377_ = lean_string_dec_eq(v_fst_1373_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
v___x_1378_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(v_fst_1373_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_dec(v_snd_1374_);
return v___x_1378_;
}
else
{
lean_object* v_val_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v_val_1379_ = lean_ctor_get(v___x_1378_, 0);
v___x_1380_ = lean_string_utf8_byte_size(v_snd_1374_);
v___x_1381_ = lean_nat_dec_eq(v___x_1380_, v___x_1370_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1391_; 
lean_inc(v_val_1379_);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; 
v_unused_1392_ = lean_ctor_get(v___x_1378_, 0);
lean_dec(v_unused_1392_);
v___x_1383_ = v___x_1378_;
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v___x_1378_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1385_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1386_ = lean_string_append(v_val_1379_, v___x_1385_);
v___x_1387_ = lean_string_append(v___x_1386_, v_snd_1374_);
lean_dec(v_snd_1374_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1387_);
v___x_1389_ = v___x_1383_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
else
{
lean_dec(v_snd_1374_);
return v___x_1378_;
}
}
}
else
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
lean_dec(v_fst_1373_);
v___x_1393_ = lean_string_utf8_byte_size(v_snd_1374_);
v___x_1394_ = lean_nat_dec_eq(v___x_1393_, v___x_1370_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__2));
v___x_1396_ = lean_string_append(v___x_1395_, v_snd_1374_);
lean_dec(v_snd_1374_);
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; 
lean_dec(v_snd_1374_);
v___x_1398_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__4));
return v___x_1398_;
}
}
}
}
else
{
lean_object* v___x_1422_; 
lean_dec_ref(v_symbol_1368_);
v___x_1422_ = lean_box(0);
return v___x_1422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(lean_object* v_s_1423_, lean_object* v_pos_1424_, lean_object* v_pred_1425_){
_start:
{
lean_object* v___x_1426_; uint8_t v_decide_1427_; 
v___x_1426_ = lean_string_utf8_byte_size(v_s_1423_);
v_decide_1427_ = lean_nat_dec_eq(v_pos_1424_, v___x_1426_);
if (v_decide_1427_ == 0)
{
uint32_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1428_ = lean_string_utf8_get_fast(v_s_1423_, v_pos_1424_);
v___x_1429_ = lean_box_uint32(v___x_1428_);
lean_inc_ref(v_pred_1425_);
v___x_1430_ = lean_apply_1(v_pred_1425_, v___x_1429_);
v___x_1431_ = lean_unbox(v___x_1430_);
if (v___x_1431_ == 0)
{
lean_dec_ref(v_pred_1425_);
return v_pos_1424_;
}
else
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_string_utf8_next_fast(v_s_1423_, v_pos_1424_);
lean_dec(v_pos_1424_);
v_pos_1424_ = v___x_1432_;
goto _start;
}
}
else
{
lean_dec_ref(v_pred_1425_);
return v_pos_1424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile___boxed(lean_object* v_s_1434_, lean_object* v_pos_1435_, lean_object* v_pred_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_s_1434_, v_pos_1435_, v_pred_1436_);
lean_dec_ref(v_s_1434_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(lean_object* v_s_1438_, lean_object* v_p_u2081_1439_, lean_object* v_p_u2082_1440_){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = lean_string_utf8_extract_fast(v_s_1438_, v___x_1441_, v_p_u2081_1439_);
v___x_1443_ = lean_string_utf8_extract_fast(v_s_1438_, v_p_u2081_1439_, v_p_u2082_1440_);
v___x_1444_ = lean_string_utf8_byte_size(v_s_1438_);
v___x_1445_ = lean_string_utf8_extract_fast(v_s_1438_, v_p_u2082_1440_, v___x_1444_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1443_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1442_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082___boxed(lean_object* v_s_1448_, lean_object* v_p_u2081_1449_, lean_object* v_p_u2082_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_s_1448_, v_p_u2081_1449_, v_p_u2082_1450_);
lean_dec(v_p_u2082_1450_);
lean_dec(v_p_u2081_1449_);
lean_dec_ref(v_s_1448_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(lean_object* v___x_1452_, lean_object* v___x_1453_, lean_object* v_line_1454_, lean_object* v_a_1455_, lean_object* v_b_1456_){
_start:
{
lean_object* v___x_1457_; uint8_t v_decide_1458_; 
v___x_1457_ = lean_nat_sub(v___x_1452_, v___x_1453_);
v_decide_1458_ = lean_nat_dec_eq(v_a_1455_, v___x_1457_);
lean_dec(v___x_1457_);
if (v_decide_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___y_1462_; uint32_t v___x_1467_; uint32_t v___x_1468_; uint8_t v___x_1469_; 
v___x_1459_ = lean_box(0);
v___x_1460_ = lean_nat_add(v___x_1453_, v_a_1455_);
v___x_1467_ = lean_string_utf8_get_fast(v_line_1454_, v___x_1460_);
v___x_1468_ = 43;
v___x_1469_ = lean_uint32_dec_eq(v___x_1467_, v___x_1468_);
if (v___x_1469_ == 0)
{
uint32_t v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = 41;
v___x_1471_ = lean_uint32_dec_eq(v___x_1467_, v___x_1470_);
v___y_1462_ = v___x_1471_;
goto v___jp_1461_;
}
else
{
v___y_1462_ = v___x_1469_;
goto v___jp_1461_;
}
v___jp_1461_:
{
if (v___y_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_dec(v_a_1455_);
v___x_1463_ = lean_string_utf8_next_fast(v_line_1454_, v___x_1460_);
lean_dec(v___x_1460_);
v___x_1464_ = lean_nat_sub(v___x_1463_, v___x_1453_);
v_a_1455_ = v___x_1464_;
v_b_1456_ = v___x_1459_;
goto _start;
}
else
{
lean_object* v___x_1466_; 
lean_dec(v___x_1460_);
v___x_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_a_1455_);
return v___x_1466_;
}
}
}
else
{
lean_dec(v_a_1455_);
lean_inc(v_b_1456_);
return v_b_1456_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg___boxed(lean_object* v___x_1472_, lean_object* v___x_1473_, lean_object* v_line_1474_, lean_object* v_a_1475_, lean_object* v_b_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1472_, v___x_1473_, v_line_1474_, v_a_1475_, v_b_1476_);
lean_dec(v_b_1476_);
lean_dec_ref(v_line_1474_);
lean_dec(v___x_1473_);
lean_dec(v___x_1472_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(lean_object* v___x_1478_, lean_object* v_line_1479_, lean_object* v_a_1480_, lean_object* v_b_1481_){
_start:
{
uint8_t v_decide_1482_; 
v_decide_1482_ = lean_nat_dec_eq(v_a_1480_, v___x_1478_);
if (v_decide_1482_ == 0)
{
uint32_t v___x_1483_; uint32_t v___x_1484_; uint8_t v___x_1485_; 
v___x_1483_ = lean_string_utf8_get_fast(v_line_1479_, v_a_1480_);
v___x_1484_ = 40;
v___x_1485_ = lean_uint32_dec_eq(v___x_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_box(0);
v___x_1487_ = lean_string_utf8_next_fast(v_line_1479_, v_a_1480_);
lean_dec(v_a_1480_);
v_a_1480_ = v___x_1487_;
v_b_1481_ = v___x_1486_;
goto _start;
}
else
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_a_1480_);
return v___x_1489_;
}
}
else
{
lean_dec(v_a_1480_);
lean_inc(v_b_1481_);
return v_b_1481_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg___boxed(lean_object* v___x_1490_, lean_object* v_line_1491_, lean_object* v_a_1492_, lean_object* v_b_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1490_, v_line_1491_, v_a_1492_, v_b_1493_);
lean_dec(v_b_1493_);
lean_dec_ref(v_line_1491_);
lean_dec(v___x_1490_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(lean_object* v_line_1495_){
_start:
{
lean_object* v_searcher_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_searcher_1496_ = lean_unsigned_to_nat(0u);
v___x_1497_ = lean_string_utf8_byte_size(v_line_1495_);
v___x_1498_ = lean_box(0);
v___x_1499_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1497_, v_line_1495_, v_searcher_1496_, v___x_1498_);
if (lean_obj_tag(v___x_1499_) == 0)
{
return v___x_1498_;
}
else
{
lean_object* v_val_1500_; uint8_t v_decide_1501_; 
v_val_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v_decide_1501_ = lean_nat_dec_eq(v_val_1500_, v___x_1497_);
if (v_decide_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_string_utf8_next_fast(v_line_1495_, v_val_1500_);
lean_dec(v_val_1500_);
v___x_1503_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1497_, v___x_1502_, v_line_1495_, v_searcher_1496_, v___x_1498_);
if (lean_obj_tag(v___x_1503_) == 0)
{
return v___x_1498_;
}
else
{
lean_object* v_val_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1514_; 
v_val_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_val_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; uint8_t v_decide_1509_; 
v___x_1508_ = lean_nat_add(v___x_1502_, v_val_1504_);
lean_dec(v_val_1504_);
v_decide_1509_ = lean_nat_dec_eq(v___x_1508_, v___x_1502_);
if (v_decide_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1510_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1495_, v___x_1502_, v___x_1508_);
lean_dec(v___x_1508_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1510_);
v___x_1512_ = v___x_1506_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
else
{
lean_dec(v___x_1508_);
lean_del_object(v___x_1506_);
return v___x_1498_;
}
}
}
}
else
{
lean_dec(v_val_1500_);
return v___x_1498_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux___boxed(lean_object* v_line_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(v_line_1515_);
lean_dec_ref(v_line_1515_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(lean_object* v___x_1517_, lean_object* v___x_1518_, lean_object* v_line_1519_, lean_object* v_inst_1520_, lean_object* v_R_1521_, lean_object* v_a_1522_, lean_object* v_b_1523_, lean_object* v_c_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1517_, v_line_1519_, v_a_1522_, v_b_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___boxed(lean_object* v___x_1526_, lean_object* v___x_1527_, lean_object* v_line_1528_, lean_object* v_inst_1529_, lean_object* v_R_1530_, lean_object* v_a_1531_, lean_object* v_b_1532_, lean_object* v_c_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(v___x_1526_, v___x_1527_, v_line_1528_, v_inst_1529_, v_R_1530_, v_a_1531_, v_b_1532_, v_c_1533_);
lean_dec(v_b_1532_);
lean_dec_ref(v_line_1528_);
lean_dec_ref(v___x_1527_);
lean_dec(v___x_1526_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(lean_object* v___x_1535_, lean_object* v___x_1536_, lean_object* v___x_1537_, lean_object* v_line_1538_, lean_object* v_inst_1539_, lean_object* v_R_1540_, lean_object* v_a_1541_, lean_object* v_b_1542_, lean_object* v_c_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1535_, v___x_1536_, v_line_1538_, v_a_1541_, v_b_1542_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___boxed(lean_object* v___x_1545_, lean_object* v___x_1546_, lean_object* v___x_1547_, lean_object* v_line_1548_, lean_object* v_inst_1549_, lean_object* v_R_1550_, lean_object* v_a_1551_, lean_object* v_b_1552_, lean_object* v_c_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(v___x_1545_, v___x_1546_, v___x_1547_, v_line_1548_, v_inst_1549_, v_R_1550_, v_a_1551_, v_b_1552_, v_c_1553_);
lean_dec(v_b_1552_);
lean_dec_ref(v_line_1548_);
lean_dec_ref(v___x_1547_);
lean_dec(v___x_1546_);
lean_dec(v___x_1545_);
return v_res_1554_;
}
}
uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(uint32_t v_x_1555_){
_start:
{
uint32_t v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = 48;
v___x_1567_ = lean_uint32_dec_le(v___x_1566_, v_x_1555_);
if (v___x_1567_ == 0)
{
goto v___jp_1561_;
}
else
{
uint32_t v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = 57;
v___x_1569_ = lean_uint32_dec_le(v_x_1555_, v___x_1568_);
if (v___x_1569_ == 0)
{
goto v___jp_1561_;
}
else
{
return v___x_1569_;
}
}
v___jp_1556_:
{
uint32_t v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = 65;
v___x_1558_ = lean_uint32_dec_le(v___x_1557_, v_x_1555_);
if (v___x_1558_ == 0)
{
return v___x_1558_;
}
else
{
uint32_t v___x_1559_; uint8_t v___x_1560_; 
v___x_1559_ = 70;
v___x_1560_ = lean_uint32_dec_le(v_x_1555_, v___x_1559_);
return v___x_1560_;
}
}
v___jp_1561_:
{
uint32_t v___x_1562_; uint8_t v___x_1563_; 
v___x_1562_ = 97;
v___x_1563_ = lean_uint32_dec_le(v___x_1562_, v_x_1555_);
if (v___x_1563_ == 0)
{
goto v___jp_1556_;
}
else
{
uint32_t v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = 102;
v___x_1565_ = lean_uint32_dec_le(v_x_1555_, v___x_1564_);
if (v___x_1565_ == 0)
{
goto v___jp_1556_;
}
else
{
return v___x_1565_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_1555_ = stack[0].m_num;
uint8_t v_res_1570_;
v_res_1570_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(v_x_1555_);
stack->m_num = v_res_1570_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed(lean_object* v_x_1571_){
_start:
{
uint32_t v_x_2757__boxed_1572_; uint8_t v_res_1573_; lean_object* v_r_1574_; 
v_x_2757__boxed_1572_ = lean_unbox_uint32(v_x_1571_);
lean_dec(v_x_1571_);
v_res_1573_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(v_x_2757__boxed_1572_);
v_r_1574_ = lean_box(v_res_1573_);
return v_r_1574_;
}
}
uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(uint32_t v_x_1575_){
_start:
{
uint32_t v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = 32;
v___x_1577_ = lean_uint32_dec_eq(v_x_1575_, v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_1575_ = stack[0].m_num;
uint8_t v_res_1578_;
v_res_1578_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(v_x_1575_);
stack->m_num = v_res_1578_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed(lean_object* v_x_1579_){
_start:
{
uint32_t v_x_2804__boxed_1580_; uint8_t v_res_1581_; lean_object* v_r_1582_; 
v_x_2804__boxed_1580_ = lean_unbox_uint32(v_x_1579_);
lean_dec(v_x_1579_);
v_res_1581_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(v_x_2804__boxed_1580_);
v_r_1582_ = lean_box(v_res_1581_);
return v_r_1582_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(lean_object* v___x_1583_, lean_object* v_line_1584_, lean_object* v___x_1585_, lean_object* v___x_1586_, lean_object* v_a_1587_, lean_object* v_b_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_box(0);
switch(lean_obj_tag(v_a_1587_))
{
case 0:
{
lean_object* v_pos_1590_; lean_object* v___x_1591_; 
v_pos_1590_ = lean_ctor_get(v_a_1587_, 0);
lean_inc(v_pos_1590_);
lean_dec_ref_known(v_a_1587_, 1);
v___x_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1591_, 0, v_pos_1590_);
return v___x_1591_;
}
case 1:
{
lean_object* v_pos_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1603_; 
v_pos_1592_ = lean_ctor_get(v_a_1587_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_a_1587_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1594_ = v_a_1587_;
v_isShared_1595_ = v_isSharedCheck_1603_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_pos_1592_);
lean_dec(v_a_1587_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1603_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1596_ = lean_nat_add(v___x_1583_, v_pos_1592_);
lean_dec(v_pos_1592_);
v___x_1597_ = lean_string_utf8_next_fast(v_line_1584_, v___x_1596_);
lean_dec(v___x_1596_);
v___x_1598_ = lean_nat_sub(v___x_1597_, v___x_1583_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set_tag(v___x_1594_, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1598_);
v___x_1600_ = v___x_1594_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
v_a_1587_ = v___x_1600_;
v_b_1588_ = v___x_1589_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1604_; lean_object* v_table_1605_; lean_object* v_stackPos_1606_; lean_object* v_needlePos_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1662_; 
v_needle_1604_ = lean_ctor_get(v_a_1587_, 0);
v_table_1605_ = lean_ctor_get(v_a_1587_, 1);
v_stackPos_1606_ = lean_ctor_get(v_a_1587_, 2);
v_needlePos_1607_ = lean_ctor_get(v_a_1587_, 3);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_a_1587_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1609_ = v_a_1587_;
v_isShared_1610_ = v_isSharedCheck_1662_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_needlePos_1607_);
lean_inc(v_stackPos_1606_);
lean_inc(v_table_1605_);
lean_inc(v_needle_1604_);
lean_dec(v_a_1587_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1662_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v_str_1611_; lean_object* v_startInclusive_1612_; lean_object* v_endExclusive_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v_str_1611_ = lean_ctor_get(v_needle_1604_, 0);
v_startInclusive_1612_ = lean_ctor_get(v_needle_1604_, 1);
v_endExclusive_1613_ = lean_ctor_get(v_needle_1604_, 2);
v___x_1614_ = lean_nat_sub(v_stackPos_1606_, v_needlePos_1607_);
v___x_1615_ = lean_nat_sub(v_endExclusive_1613_, v_startInclusive_1612_);
v___x_1616_ = lean_nat_add(v___x_1614_, v___x_1615_);
v___x_1617_ = lean_nat_sub(v___x_1586_, v___x_1583_);
v___x_1618_ = lean_nat_dec_le(v___x_1616_, v___x_1617_);
lean_dec(v___x_1616_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
lean_dec(v___x_1615_);
lean_del_object(v___x_1609_);
lean_dec(v_needlePos_1607_);
lean_dec(v_stackPos_1606_);
lean_dec_ref(v_table_1605_);
lean_dec_ref(v_needle_1604_);
v___x_1619_ = lean_unsigned_to_nat(1u);
v___x_1620_ = lean_nat_add(v___x_1614_, v___x_1619_);
lean_dec(v___x_1614_);
v___x_1621_ = lean_nat_dec_le(v___x_1620_, v___x_1617_);
lean_dec(v___x_1617_);
lean_dec(v___x_1620_);
if (v___x_1621_ == 0)
{
lean_inc(v_b_1588_);
return v_b_1588_;
}
else
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_box(3);
v_a_1587_ = v___x_1622_;
v_b_1588_ = v___x_1589_;
goto _start;
}
}
else
{
lean_object* v___x_1624_; uint8_t v_stackByte_1625_; lean_object* v___x_1626_; uint8_t v_patByte_1627_; uint8_t v___x_1628_; 
lean_dec(v___x_1617_);
lean_dec(v___x_1614_);
v___x_1624_ = lean_nat_add(v___x_1583_, v_stackPos_1606_);
v_stackByte_1625_ = lean_string_get_byte_fast(v_line_1584_, v___x_1624_);
v___x_1626_ = lean_nat_add(v_startInclusive_1612_, v_needlePos_1607_);
v_patByte_1627_ = lean_string_get_byte_fast(v_str_1611_, v___x_1626_);
v___x_1628_ = lean_uint8_dec_eq(v_stackByte_1625_, v_patByte_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; uint8_t v_decide_1630_; 
lean_dec(v___x_1615_);
v___x_1629_ = lean_unsigned_to_nat(0u);
v_decide_1630_ = lean_nat_dec_eq(v_needlePos_1607_, v___x_1629_);
if (v_decide_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_newNeedlePos_1633_; uint8_t v___x_1634_; 
v___x_1631_ = lean_unsigned_to_nat(1u);
v___x_1632_ = lean_nat_sub(v_needlePos_1607_, v___x_1631_);
lean_dec(v_needlePos_1607_);
v_newNeedlePos_1633_ = lean_array_fget_borrowed(v_table_1605_, v___x_1632_);
lean_dec(v___x_1632_);
v___x_1634_ = lean_nat_dec_eq(v_newNeedlePos_1633_, v___x_1629_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1636_; 
lean_inc(v_newNeedlePos_1633_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 3, v_newNeedlePos_1633_);
v___x_1636_ = v___x_1609_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_needle_1604_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_table_1605_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_stackPos_1606_);
lean_ctor_set(v_reuseFailAlloc_1638_, 3, v_newNeedlePos_1633_);
v___x_1636_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
v_a_1587_ = v___x_1636_;
v_b_1588_ = v___x_1589_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1639_; lean_object* v___x_1641_; 
v_nextStackPos_1639_ = l_String_Slice_posGE___redArg(v___x_1585_, v_stackPos_1606_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 3, v___x_1629_);
lean_ctor_set(v___x_1609_, 2, v_nextStackPos_1639_);
v___x_1641_ = v___x_1609_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_needle_1604_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_table_1605_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_nextStackPos_1639_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v___x_1629_);
v___x_1641_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
v_a_1587_ = v___x_1641_;
v_b_1588_ = v___x_1589_;
goto _start;
}
}
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v_nextStackPos_1646_; lean_object* v___x_1648_; 
lean_dec(v_needlePos_1607_);
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_nat_add(v_stackPos_1606_, v___x_1644_);
lean_dec(v_stackPos_1606_);
v_nextStackPos_1646_ = l_String_Slice_posGE___redArg(v___x_1585_, v___x_1645_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 3, v___x_1629_);
lean_ctor_set(v___x_1609_, 2, v_nextStackPos_1646_);
v___x_1648_ = v___x_1609_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_needle_1604_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_table_1605_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_nextStackPos_1646_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v___x_1629_);
v___x_1648_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
v_a_1587_ = v___x_1648_;
v_b_1588_ = v___x_1589_;
goto _start;
}
}
}
else
{
lean_object* v___x_1651_; lean_object* v_nextStackPos_1652_; lean_object* v_nextNeedlePos_1653_; uint8_t v_decide_1654_; 
v___x_1651_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1652_ = lean_nat_add(v_stackPos_1606_, v___x_1651_);
lean_dec(v_stackPos_1606_);
v_nextNeedlePos_1653_ = lean_nat_add(v_needlePos_1607_, v___x_1651_);
lean_dec(v_needlePos_1607_);
v_decide_1654_ = lean_nat_dec_eq(v_nextNeedlePos_1653_, v___x_1615_);
lean_dec(v___x_1615_);
if (v_decide_1654_ == 0)
{
lean_object* v___x_1656_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 3, v_nextNeedlePos_1653_);
lean_ctor_set(v___x_1609_, 2, v_nextStackPos_1652_);
v___x_1656_ = v___x_1609_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_needle_1604_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_table_1605_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_nextStackPos_1652_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v_nextNeedlePos_1653_);
v___x_1656_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
v_a_1587_ = v___x_1656_;
goto _start;
}
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_del_object(v___x_1609_);
lean_dec_ref(v_table_1605_);
lean_dec_ref(v_needle_1604_);
v___x_1659_ = lean_nat_sub(v_nextStackPos_1652_, v_nextNeedlePos_1653_);
lean_dec(v_nextNeedlePos_1653_);
lean_dec(v_nextStackPos_1652_);
v___x_1660_ = l_String_Slice_pos_x21(v___x_1585_, v___x_1659_);
lean_dec(v___x_1659_);
v___x_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
return v___x_1661_;
}
}
}
}
}
default: 
{
lean_inc(v_b_1588_);
return v_b_1588_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg___boxed(lean_object* v___x_1663_, lean_object* v_line_1664_, lean_object* v___x_1665_, lean_object* v___x_1666_, lean_object* v_a_1667_, lean_object* v_b_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1663_, v_line_1664_, v___x_1665_, v___x_1666_, v_a_1667_, v_b_1668_);
lean_dec(v_b_1668_);
lean_dec(v___x_1666_);
lean_dec_ref(v___x_1665_);
lean_dec_ref(v_line_1664_);
lean_dec(v___x_1663_);
return v_res_1669_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1));
v___x_1676_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1675_);
return v___x_1676_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2);
v___x_1679_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1));
v___x_1680_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v___x_1678_);
lean_ctor_set(v___x_1680_, 2, v___x_1677_);
lean_ctor_set(v___x_1680_, 3, v___x_1677_);
return v___x_1680_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7));
v___x_1689_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1688_);
return v___x_1689_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8);
v___x_1692_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7));
v___x_1693_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v___x_1691_);
lean_ctor_set(v___x_1693_, 2, v___x_1690_);
lean_ctor_set(v___x_1693_, 3, v___x_1690_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(lean_object* v_line_1694_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1695_ = lean_unsigned_to_nat(0u);
v___x_1696_ = lean_string_utf8_byte_size(v_line_1694_);
lean_inc_ref(v_line_1694_);
v___x_1697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1697_, 0, v_line_1694_);
lean_ctor_set(v___x_1697_, 1, v___x_1695_);
lean_ctor_set(v___x_1697_, 2, v___x_1696_);
v___x_1698_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3);
v___x_1699_ = lean_box(0);
v___x_1700_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_line_1694_, v___x_1697_, v___x_1696_, v___x_1698_, v___x_1699_);
lean_dec_ref_known(v___x_1697_, 3);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_dec_ref(v_line_1694_);
return v___x_1699_;
}
else
{
lean_object* v_val_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1726_; 
v_val_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1726_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_val_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1726_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
uint8_t v_decide_1705_; 
v_decide_1705_ = lean_nat_dec_eq(v_val_1701_, v___x_1696_);
if (v_decide_1705_ == 0)
{
lean_object* v___x_1706_; uint8_t v_decide_1707_; 
v___x_1706_ = lean_string_utf8_next_fast(v_line_1694_, v_val_1701_);
lean_dec(v_val_1701_);
v_decide_1707_ = lean_nat_dec_eq(v___x_1706_, v___x_1696_);
if (v_decide_1707_ == 0)
{
lean_object* v___f_1708_; lean_object* v___f_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___y_1714_; uint8_t v_decide_1720_; 
v___f_1708_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4));
v___f_1709_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5));
v___x_1710_ = lean_string_utf8_next_fast(v_line_1694_, v___x_1706_);
v___x_1711_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1694_, v___x_1710_, v___f_1708_);
v___x_1712_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1694_, v___x_1711_, v___f_1709_);
v_decide_1720_ = lean_nat_dec_eq(v___x_1712_, v___x_1696_);
if (v_decide_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_inc(v___x_1712_);
lean_inc_ref(v_line_1694_);
v___x_1721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1721_, 0, v_line_1694_);
lean_ctor_set(v___x_1721_, 1, v___x_1712_);
lean_ctor_set(v___x_1721_, 2, v___x_1696_);
v___x_1722_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
v___x_1723_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1712_, v_line_1694_, v___x_1721_, v___x_1696_, v___x_1722_, v___x_1699_);
lean_dec_ref_known(v___x_1721_, 3);
if (lean_obj_tag(v___x_1723_) == 0)
{
v___y_1714_ = v___x_1696_;
goto v___jp_1713_;
}
else
{
lean_object* v_val_1724_; lean_object* v___x_1725_; 
v_val_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_val_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = lean_nat_add(v___x_1712_, v_val_1724_);
lean_dec(v_val_1724_);
v___y_1714_ = v___x_1725_;
goto v___jp_1713_;
}
}
else
{
lean_dec(v___x_1712_);
lean_del_object(v___x_1703_);
lean_dec_ref(v_line_1694_);
return v___x_1699_;
}
v___jp_1713_:
{
uint8_t v_decide_1715_; 
v_decide_1715_ = lean_nat_dec_eq(v___y_1714_, v___x_1712_);
if (v_decide_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1694_, v___x_1712_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec(v___x_1712_);
lean_dec_ref(v_line_1694_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1716_);
v___x_1718_ = v___x_1703_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
else
{
lean_dec(v___y_1714_);
lean_dec(v___x_1712_);
lean_del_object(v___x_1703_);
lean_dec_ref(v_line_1694_);
return v___x_1699_;
}
}
}
else
{
lean_del_object(v___x_1703_);
lean_dec_ref(v_line_1694_);
return v___x_1699_;
}
}
else
{
lean_del_object(v___x_1703_);
lean_dec(v_val_1701_);
lean_dec_ref(v_line_1694_);
return v___x_1699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(lean_object* v___x_1727_, lean_object* v_line_1728_, lean_object* v___x_1729_, lean_object* v___x_1730_, lean_object* v_inst_1731_, lean_object* v_R_1732_, lean_object* v_a_1733_, lean_object* v_b_1734_, lean_object* v_c_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1727_, v_line_1728_, v___x_1729_, v___x_1730_, v_a_1733_, v_b_1734_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___boxed(lean_object* v___x_1737_, lean_object* v_line_1738_, lean_object* v___x_1739_, lean_object* v___x_1740_, lean_object* v_inst_1741_, lean_object* v_R_1742_, lean_object* v_a_1743_, lean_object* v_b_1744_, lean_object* v_c_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(v___x_1737_, v_line_1738_, v___x_1739_, v___x_1740_, v_inst_1741_, v_R_1742_, v_a_1743_, v_b_1744_, v_c_1745_);
lean_dec(v_b_1744_);
lean_dec(v___x_1740_);
lean_dec_ref(v___x_1739_);
lean_dec_ref(v_line_1738_);
lean_dec(v___x_1737_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(lean_object* v_line_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(v_line_1747_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v___x_1749_; 
v___x_1749_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(v_line_1747_);
return v___x_1749_;
}
else
{
lean_dec_ref(v_line_1747_);
return v___x_1748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleBtLine(lean_object* v_line_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(v_line_1750_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_box(0);
return v___x_1752_;
}
else
{
lean_object* v_val_1753_; lean_object* v_snd_1754_; lean_object* v_fst_1755_; lean_object* v_fst_1756_; lean_object* v_snd_1757_; lean_object* v___x_1758_; 
v_val_1753_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_val_1753_);
lean_dec_ref_known(v___x_1751_, 1);
v_snd_1754_ = lean_ctor_get(v_val_1753_, 1);
lean_inc(v_snd_1754_);
v_fst_1755_ = lean_ctor_get(v_val_1753_, 0);
lean_inc(v_fst_1755_);
lean_dec(v_val_1753_);
v_fst_1756_ = lean_ctor_get(v_snd_1754_, 0);
lean_inc(v_fst_1756_);
v_snd_1757_ = lean_ctor_get(v_snd_1754_, 1);
lean_inc(v_snd_1757_);
lean_dec(v_snd_1754_);
v___x_1758_ = l_Lean_Name_Demangle_demangleSymbol(v_fst_1756_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_dec(v_snd_1757_);
lean_dec(v_fst_1755_);
return v___x_1758_;
}
else
{
lean_object* v_val_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1768_; 
v_val_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1768_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_val_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1768_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1763_ = lean_string_append(v_fst_1755_, v_val_1759_);
lean_dec(v_val_1759_);
v___x_1764_ = lean_string_append(v___x_1763_, v_snd_1757_);
lean_dec(v_snd_1757_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1764_);
v___x_1766_ = v___x_1761_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_demangle_bt_line_cstr(lean_object* v_line_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_Name_Demangle_demangleBtLine(v_line_1769_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v___x_1771_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_1771_;
}
else
{
lean_object* v_val_1772_; 
v_val_1772_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_val_1772_);
lean_dec_ref_known(v___x_1770_, 1);
return v_val_1772_;
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
