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
size_t v___x_124_; size_t v___x_125_; lean_object* v___x_126_; 
v___x_124_ = ((size_t)0ULL);
v___x_125_ = lean_usize_of_nat(v___x_122_);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_parts_119_, v___x_124_, v___x_125_, v___x_120_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName___boxed(lean_object* v_parts_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(v_parts_127_);
lean_dec_ref(v_parts_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(lean_object* v_comps_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = lean_array_get_size(v_comps_130_);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_nat_dec_eq(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = 1;
v___x_135_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(v_comps_130_);
v___x_136_ = l_Lean_Name_toString(v___x_135_, v___x_134_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; 
v___x_137_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___boxed(lean_object* v_comps_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_comps_138_);
lean_dec_ref(v_comps_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(lean_object* v_c_168_){
_start:
{
if (lean_obj_tag(v_c_168_) == 0)
{
lean_object* v_s_171_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_s_171_ = lean_ctor_get(v_c_168_, 0);
lean_inc_ref(v_s_171_);
lean_dec_ref_known(v_c_168_, 1);
v___x_179_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3));
v___x_180_ = lean_string_dec_eq(v_s_171_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4));
v___x_182_ = lean_string_dec_eq(v_s_171_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5));
v___x_184_ = lean_string_dec_eq(v_s_171_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6));
v___x_186_ = lean_string_dec_eq(v_s_171_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__7));
v___x_188_ = lean_string_dec_eq(v_s_171_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8));
v___x_190_ = lean_string_dec_eq(v_s_171_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__9));
v___x_192_ = lean_string_dec_eq(v_s_171_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10));
v___x_194_ = lean_string_dec_eq(v_s_171_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11));
lean_inc_ref(v_s_171_);
v___x_196_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_171_, v___x_195_);
if (lean_obj_tag(v___x_196_) == 0)
{
goto v___jp_172_;
}
else
{
lean_object* v_val_197_; uint8_t v___x_198_; 
v_val_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_val_197_);
lean_dec_ref_known(v___x_196_, 1);
v___x_198_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_197_);
if (v___x_198_ == 0)
{
goto v___jp_172_;
}
else
{
lean_object* v___x_199_; 
lean_dec_ref(v_s_171_);
v___x_199_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_199_;
}
}
}
else
{
lean_object* v___x_200_; 
lean_dec_ref(v_s_171_);
v___x_200_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13));
return v___x_200_;
}
}
else
{
lean_object* v___x_201_; 
lean_dec_ref(v_s_171_);
v___x_201_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15));
return v___x_201_;
}
}
else
{
lean_dec_ref(v_s_171_);
goto v___jp_169_;
}
}
else
{
lean_dec_ref(v_s_171_);
goto v___jp_169_;
}
}
else
{
lean_dec_ref(v_s_171_);
goto v___jp_169_;
}
}
else
{
lean_object* v___x_202_; 
lean_dec_ref(v_s_171_);
v___x_202_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__17));
return v___x_202_;
}
}
else
{
lean_object* v___x_203_; 
lean_dec_ref(v_s_171_);
v___x_203_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__19));
return v___x_203_;
}
}
else
{
lean_object* v___x_204_; 
lean_dec_ref(v_s_171_);
v___x_204_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__21));
return v___x_204_;
}
v___jp_172_:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__2));
v___x_174_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_171_, v___x_173_);
if (lean_obj_tag(v___x_174_) == 0)
{
return v___x_174_;
}
else
{
lean_object* v_val_175_; uint8_t v___x_176_; 
v_val_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v___x_174_, 1);
v___x_176_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
v___x_177_ = lean_box(0);
return v___x_177_;
}
else
{
lean_object* v___x_178_; 
v___x_178_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_178_;
}
}
}
}
else
{
lean_object* v___x_205_; 
lean_dec_ref(v_c_168_);
v___x_205_ = lean_box(0);
return v___x_205_;
}
v___jp_169_:
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_170_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(lean_object* v_c_207_){
_start:
{
if (lean_obj_tag(v_c_207_) == 0)
{
lean_object* v_s_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_s_208_ = lean_ctor_get(v_c_207_, 0);
lean_inc_ref(v_s_208_);
lean_dec_ref_known(v_c_207_, 1);
v___x_209_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___closed__0));
v___x_210_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_208_, v___x_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
uint8_t v___x_211_; 
v___x_211_ = 0;
return v___x_211_;
}
else
{
lean_object* v_val_212_; uint8_t v___x_213_; 
v_val_212_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v___x_210_, 1);
v___x_213_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_212_);
return v___x_213_;
}
}
else
{
uint8_t v___x_214_; 
lean_dec_ref(v_c_207_);
v___x_214_ = 0;
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___boxed(lean_object* v_c_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(v_c_215_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
if (lean_obj_tag(v_x_219_) == 0)
{
uint8_t v___x_220_; 
v___x_220_ = 1;
return v___x_220_;
}
else
{
uint8_t v___x_221_; 
v___x_221_ = 0;
return v___x_221_;
}
}
else
{
if (lean_obj_tag(v_x_219_) == 0)
{
uint8_t v___x_222_; 
v___x_222_ = 0;
return v___x_222_;
}
else
{
lean_object* v_val_223_; lean_object* v_val_224_; uint8_t v___x_225_; 
v_val_223_ = lean_ctor_get(v_x_218_, 0);
v_val_224_ = lean_ctor_get(v_x_219_, 0);
v___x_225_ = l_Lean_instBEqNamePart_beq(v_val_223_, v_val_224_);
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0___boxed(lean_object* v_x_226_, lean_object* v_x_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v_x_226_, v_x_227_);
lean_dec(v_x_227_);
lean_dec(v_x_226_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(lean_object* v_stop_237_, lean_object* v_start_238_, lean_object* v___x_239_, lean_object* v_comps_240_, lean_object* v_range_241_, lean_object* v_b_242_, lean_object* v_i_243_){
_start:
{
lean_object* v_stop_244_; lean_object* v_step_245_; uint8_t v___x_246_; 
v_stop_244_ = lean_ctor_get(v_range_241_, 1);
v_step_245_ = lean_ctor_get(v_range_241_, 2);
v___x_246_ = lean_nat_dec_lt(v_i_243_, v_stop_244_);
if (v___x_246_ == 0)
{
lean_dec(v_i_243_);
lean_dec(v_start_238_);
lean_inc_ref(v_b_242_);
return v_b_242_;
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___y_254_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_box(0);
v___x_249_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0));
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = lean_unsigned_to_nat(3u);
v___x_252_ = lean_nat_dec_le(v___x_251_, v___x_239_);
v___x_269_ = lean_array_get_size(v_comps_240_);
v___x_270_ = lean_nat_dec_lt(v_i_243_, v___x_269_);
if (v___x_270_ == 0)
{
v___y_254_ = v___x_247_;
goto v___jp_253_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_array_fget_borrowed(v_comps_240_, v_i_243_);
lean_inc(v___x_271_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
v___y_254_ = v___x_272_;
goto v___jp_253_;
}
v___jp_253_:
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2));
v___x_256_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_254_, v___x_255_);
lean_dec(v___y_254_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
v___x_257_ = lean_nat_add(v_i_243_, v_step_245_);
lean_dec(v_i_243_);
v_b_242_ = v___x_249_;
v_i_243_ = v___x_257_;
goto _start;
}
else
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_nat_add(v_i_243_, v___x_250_);
lean_dec(v_i_243_);
v___x_260_ = lean_nat_dec_lt(v___x_259_, v_stop_237_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec(v___x_259_);
v___x_261_ = lean_box(v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_start_238_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_248_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v_start_238_);
v___x_265_ = lean_box(v___x_252_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_259_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_248_);
return v___x_268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___boxed(lean_object* v_stop_273_, lean_object* v_start_274_, lean_object* v___x_275_, lean_object* v_comps_276_, lean_object* v_range_277_, lean_object* v_b_278_, lean_object* v_i_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_273_, v_start_274_, v___x_275_, v_comps_276_, v_range_277_, v_b_278_, v_i_279_);
lean_dec_ref(v_b_278_);
lean_dec_ref(v_range_277_);
lean_dec_ref(v_comps_276_);
lean_dec(v___x_275_);
lean_dec(v_stop_273_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(lean_object* v_comps_286_, lean_object* v_start_287_, lean_object* v_stop_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___y_292_; uint8_t v___x_314_; 
v___x_289_ = lean_unsigned_to_nat(3u);
v___x_290_ = lean_nat_sub(v_stop_288_, v_start_287_);
v___x_314_ = lean_nat_dec_le(v___x_289_, v___x_290_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v___x_290_);
lean_dec(v_stop_288_);
v___x_315_ = lean_box(v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_start_287_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
return v___x_316_;
}
else
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_array_get_size(v_comps_286_);
v___x_318_ = lean_nat_dec_lt(v_start_287_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; 
v___x_319_ = lean_box(0);
v___y_292_ = v___x_319_;
goto v___jp_291_;
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_array_fget_borrowed(v_comps_286_, v_start_287_);
lean_inc(v___x_320_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
v___y_292_ = v___x_321_;
goto v___jp_291_;
}
}
v___jp_291_:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2));
v___x_294_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_292_, v___x_293_);
lean_dec(v___y_292_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec(v___x_290_);
lean_dec(v_stop_288_);
v___x_295_ = lean_box(v___x_294_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_start_287_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_fst_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_312_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_add(v_start_287_, v___x_297_);
lean_inc(v_stop_288_);
lean_inc(v___x_298_);
v___x_299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_stop_288_);
lean_ctor_set(v___x_299_, 2, v___x_297_);
v___x_300_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0));
lean_inc(v_start_287_);
v___x_301_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_288_, v_start_287_, v___x_290_, v_comps_286_, v___x_299_, v___x_300_, v___x_298_);
lean_dec_ref_known(v___x_299_, 3);
lean_dec(v___x_290_);
lean_dec(v_stop_288_);
v_fst_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; 
v_unused_313_ = lean_ctor_get(v___x_301_, 1);
lean_dec(v_unused_313_);
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_312_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_fst_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_312_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
if (lean_obj_tag(v_fst_302_) == 0)
{
uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_306_ = 0;
v___x_307_ = lean_box(v___x_306_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v___x_307_);
lean_ctor_set(v___x_304_, 0, v_start_287_);
v___x_309_ = v___x_304_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_start_287_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
else
{
lean_object* v_val_311_; 
lean_del_object(v___x_304_);
lean_dec(v_start_287_);
v_val_311_ = lean_ctor_get(v_fst_302_, 0);
lean_inc(v_val_311_);
lean_dec_ref_known(v_fst_302_, 1);
return v_val_311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___boxed(lean_object* v_comps_322_, lean_object* v_start_323_, lean_object* v_stop_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_comps_322_, v_start_323_, v_stop_324_);
lean_dec_ref(v_comps_322_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(lean_object* v_stop_326_, lean_object* v_start_327_, lean_object* v___x_328_, lean_object* v_comps_329_, lean_object* v_range_330_, lean_object* v_b_331_, lean_object* v_i_332_, lean_object* v_hs_333_, lean_object* v_hl_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_326_, v_start_327_, v___x_328_, v_comps_329_, v_range_330_, v_b_331_, v_i_332_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___boxed(lean_object* v_stop_336_, lean_object* v_start_337_, lean_object* v___x_338_, lean_object* v_comps_339_, lean_object* v_range_340_, lean_object* v_b_341_, lean_object* v_i_342_, lean_object* v_hs_343_, lean_object* v_hl_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(v_stop_336_, v_start_337_, v___x_338_, v_comps_339_, v_range_340_, v_b_341_, v_i_342_, v_hs_343_, v_hl_344_);
lean_dec_ref(v_b_341_);
lean_dec_ref(v_range_340_);
lean_dec_ref(v_comps_339_);
lean_dec(v___x_338_);
lean_dec(v_stop_336_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(lean_object* v___x_346_, lean_object* v_comps_347_, lean_object* v_range_348_, lean_object* v_b_349_, lean_object* v_i_350_){
_start:
{
lean_object* v_stop_351_; lean_object* v_step_352_; lean_object* v_a_354_; uint8_t v___x_357_; 
v_stop_351_ = lean_ctor_get(v_range_348_, 1);
v_step_352_ = lean_ctor_get(v_range_348_, 2);
v___x_357_ = lean_nat_dec_lt(v_i_350_, v_stop_351_);
if (v___x_357_ == 0)
{
lean_dec(v_i_350_);
lean_inc(v_b_349_);
return v_b_349_;
}
else
{
lean_object* v___x_358_; lean_object* v___y_360_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_365_ = lean_array_get_size(v_comps_347_);
v___x_366_ = lean_nat_dec_lt(v_i_350_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
v___x_367_ = lean_box(0);
v___y_360_ = v___x_367_;
goto v___jp_359_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_array_fget_borrowed(v_comps_347_, v_i_350_);
lean_inc(v___x_368_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
v___y_360_ = v___x_369_;
goto v___jp_359_;
}
v___jp_359_:
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2));
v___x_362_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_360_, v___x_361_);
lean_dec(v___y_360_);
if (v___x_362_ == 0)
{
v_a_354_ = v_b_349_;
goto v___jp_353_;
}
else
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = lean_nat_add(v_i_350_, v___x_358_);
v___x_364_ = lean_nat_dec_lt(v___x_363_, v___x_346_);
if (v___x_364_ == 0)
{
lean_dec(v___x_363_);
v_a_354_ = v_b_349_;
goto v___jp_353_;
}
else
{
lean_dec(v_i_350_);
return v___x_363_;
}
}
}
}
v___jp_353_:
{
lean_object* v___x_355_; 
v___x_355_ = lean_nat_add(v_i_350_, v_step_352_);
lean_dec(v_i_350_);
v_b_349_ = v_a_354_;
v_i_350_ = v___x_355_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg___boxed(lean_object* v___x_370_, lean_object* v_comps_371_, lean_object* v_range_372_, lean_object* v_b_373_, lean_object* v_i_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_370_, v_comps_371_, v_range_372_, v_b_373_, v_i_374_);
lean_dec(v_b_373_);
lean_dec_ref(v_range_372_);
lean_dec_ref(v_comps_371_);
lean_dec(v___x_370_);
return v_res_375_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(lean_object* v_a_376_, lean_object* v_as_377_, size_t v_i_378_, size_t v_stop_379_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = lean_usize_dec_eq(v_i_378_, v_stop_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_array_uget_borrowed(v_as_377_, v_i_378_);
v___x_382_ = lean_string_dec_eq(v_a_376_, v___x_381_);
if (v___x_382_ == 0)
{
size_t v___x_383_; size_t v___x_384_; 
v___x_383_ = ((size_t)1ULL);
v___x_384_ = lean_usize_add(v_i_378_, v___x_383_);
v_i_378_ = v___x_384_;
goto _start;
}
else
{
return v___x_382_;
}
}
else
{
uint8_t v___x_386_; 
v___x_386_ = 0;
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0___boxed(lean_object* v_a_387_, lean_object* v_as_388_, lean_object* v_i_389_, lean_object* v_stop_390_){
_start:
{
size_t v_i_boxed_391_; size_t v_stop_boxed_392_; uint8_t v_res_393_; lean_object* v_r_394_; 
v_i_boxed_391_ = lean_unbox_usize(v_i_389_);
lean_dec(v_i_389_);
v_stop_boxed_392_ = lean_unbox_usize(v_stop_390_);
lean_dec(v_stop_390_);
v_res_393_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_387_, v_as_388_, v_i_boxed_391_, v_stop_boxed_392_);
lean_dec_ref(v_as_388_);
lean_dec_ref(v_a_387_);
v_r_394_ = lean_box(v_res_393_);
return v_r_394_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(lean_object* v_as_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_array_get_size(v_as_395_);
v___x_399_ = lean_nat_dec_lt(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
return v___x_399_;
}
else
{
size_t v___x_400_; size_t v___x_401_; uint8_t v___x_402_; 
v___x_400_ = ((size_t)0ULL);
v___x_401_ = lean_usize_of_nat(v___x_398_);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_396_, v_as_395_, v___x_400_, v___x_401_);
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0___boxed(lean_object* v_as_403_, lean_object* v_a_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_as_403_, v_a_404_);
lean_dec_ref(v_a_404_);
lean_dec_ref(v_as_403_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(lean_object* v_comps_407_, lean_object* v_range_408_, lean_object* v_b_409_, lean_object* v_i_410_){
_start:
{
lean_object* v_stop_411_; lean_object* v_step_412_; lean_object* v_a_414_; uint8_t v___x_417_; 
v_stop_411_ = lean_ctor_get(v_range_408_, 1);
v_step_412_ = lean_ctor_get(v_range_408_, 2);
v___x_417_ = lean_nat_dec_lt(v_i_410_, v_stop_411_);
if (v___x_417_ == 0)
{
lean_dec(v_i_410_);
return v_b_409_;
}
else
{
lean_object* v_fst_418_; lean_object* v_snd_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_443_; 
v_fst_418_ = lean_ctor_get(v_b_409_, 0);
v_snd_419_ = lean_ctor_get(v_b_409_, 1);
v_isSharedCheck_443_ = !lean_is_exclusive(v_b_409_);
if (v_isSharedCheck_443_ == 0)
{
v___x_421_ = v_b_409_;
v_isShared_422_ = v_isSharedCheck_443_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_snd_419_);
lean_inc(v_fst_418_);
lean_dec(v_b_409_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_443_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = l_Lean_instInhabitedNamePart_default;
v___x_424_ = lean_array_get_borrowed(v___x_423_, v_comps_407_, v_i_410_);
lean_inc(v___x_424_);
v___x_425_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_424_);
if (lean_obj_tag(v___x_425_) == 0)
{
uint8_t v___x_426_; 
lean_inc(v___x_424_);
v___x_426_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(v___x_424_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_429_; 
lean_inc(v___x_424_);
v___x_427_ = lean_array_push(v_fst_418_, v___x_424_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_427_);
v___x_429_ = v___x_421_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_snd_419_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
v_a_414_ = v___x_429_;
goto v___jp_413_;
}
}
else
{
lean_object* v___x_432_; 
if (v_isShared_422_ == 0)
{
v___x_432_ = v___x_421_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_fst_418_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_snd_419_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
v_a_414_ = v___x_432_;
goto v___jp_413_;
}
}
}
else
{
lean_object* v_val_434_; uint8_t v___x_435_; 
v_val_434_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v___x_425_, 1);
v___x_435_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_snd_419_, v_val_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_array_push(v_snd_419_, v_val_434_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v___x_436_);
v___x_438_ = v___x_421_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_fst_418_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
v_a_414_ = v___x_438_;
goto v___jp_413_;
}
}
else
{
lean_object* v___x_441_; 
lean_dec(v_val_434_);
if (v_isShared_422_ == 0)
{
v___x_441_ = v___x_421_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_fst_418_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_snd_419_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
v_a_414_ = v___x_441_;
goto v___jp_413_;
}
}
}
}
}
v___jp_413_:
{
lean_object* v___x_415_; 
v___x_415_ = lean_nat_add(v_i_410_, v_step_412_);
lean_dec(v_i_410_);
v_b_409_ = v_a_414_;
v_i_410_ = v___x_415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg___boxed(lean_object* v_comps_444_, lean_object* v_range_445_, lean_object* v_b_446_, lean_object* v_i_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_444_, v_range_445_, v_b_446_, v_i_447_);
lean_dec_ref(v_range_445_);
lean_dec_ref(v_comps_444_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(lean_object* v_comps_453_){
_start:
{
lean_object* v_begin___455_; lean_object* v_begin___471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___y_475_; uint8_t v___x_481_; 
v_begin___471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_unsigned_to_nat(3u);
v___x_473_ = lean_array_get_size(v_comps_453_);
v___x_481_ = lean_nat_dec_le(v___x_472_, v___x_473_);
if (v___x_481_ == 0)
{
v_begin___455_ = v_begin___471_;
goto v___jp_454_;
}
else
{
uint8_t v___x_482_; 
v___x_482_ = lean_nat_dec_lt(v_begin___471_, v___x_473_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
v___x_483_ = lean_box(0);
v___y_475_ = v___x_483_;
goto v___jp_474_;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_array_fget_borrowed(v_comps_453_, v_begin___471_);
lean_inc(v___x_484_);
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
v___y_475_ = v___x_485_;
goto v___jp_474_;
}
}
v___jp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_470_; 
v___x_456_ = lean_array_get_size(v_comps_453_);
v___x_457_ = lean_unsigned_to_nat(1u);
lean_inc(v_begin___455_);
v___x_458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_458_, 0, v_begin___455_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_457_);
v___x_459_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1));
v___x_460_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_453_, v___x_458_, v___x_459_, v_begin___455_);
lean_dec_ref_known(v___x_458_, 3);
v_fst_461_ = lean_ctor_get(v___x_460_, 0);
v_snd_462_ = lean_ctor_get(v___x_460_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_470_ == 0)
{
v___x_464_ = v___x_460_;
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snd_462_);
lean_inc(v_fst_461_);
lean_dec(v___x_460_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_fst_461_);
lean_dec(v_fst_461_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_snd_462_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
v___jp_474_:
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2));
v___x_477_ = l_instBEqOption_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_475_, v___x_476_);
lean_dec(v___y_475_);
if (v___x_477_ == 0)
{
v_begin___455_ = v_begin___471_;
goto v___jp_454_;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___x_473_);
lean_ctor_set(v___x_479_, 2, v___x_478_);
v___x_480_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_473_, v_comps_453_, v___x_479_, v_begin___471_, v___x_478_);
lean_dec_ref_known(v___x_479_, 3);
v_begin___455_ = v___x_480_;
goto v___jp_454_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___boxed(lean_object* v_comps_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(v_comps_486_);
lean_dec_ref(v_comps_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1(lean_object* v_comps_488_, lean_object* v_range_489_, lean_object* v_b_490_, lean_object* v_i_491_, lean_object* v_hs_492_, lean_object* v_hl_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_488_, v_range_489_, v_b_490_, v_i_491_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___boxed(lean_object* v_comps_495_, lean_object* v_range_496_, lean_object* v_b_497_, lean_object* v_i_498_, lean_object* v_hs_499_, lean_object* v_hl_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1(v_comps_495_, v_range_496_, v_b_497_, v_i_498_, v_hs_499_, v_hl_500_);
lean_dec_ref(v_range_496_);
lean_dec_ref(v_comps_495_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2(lean_object* v___x_502_, lean_object* v_comps_503_, lean_object* v_range_504_, lean_object* v_b_505_, lean_object* v_i_506_, lean_object* v_hs_507_, lean_object* v_hl_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_502_, v_comps_503_, v_range_504_, v_b_505_, v_i_506_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___boxed(lean_object* v___x_510_, lean_object* v_comps_511_, lean_object* v_range_512_, lean_object* v_b_513_, lean_object* v_i_514_, lean_object* v_hs_515_, lean_object* v_hl_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2(v___x_510_, v_comps_511_, v_range_512_, v_b_513_, v_i_514_, v_hs_515_, v_hl_516_);
lean_dec(v_b_513_);
lean_dec_ref(v_range_512_);
lean_dec_ref(v_comps_511_);
lean_dec(v___x_510_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(lean_object* v___x_521_, lean_object* v_range_522_, lean_object* v_b_523_, lean_object* v_i_524_){
_start:
{
lean_object* v_stop_525_; lean_object* v_step_526_; uint8_t v___x_527_; 
v_stop_525_ = lean_ctor_get(v_range_522_, 1);
v_step_526_ = lean_ctor_get(v_range_522_, 2);
v___x_527_ = lean_nat_dec_lt(v_i_524_, v_stop_525_);
if (v___x_527_ == 0)
{
lean_dec(v_i_524_);
lean_inc(v_b_523_);
return v_b_523_;
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_528_ = l_Lean_instInhabitedNamePart_default;
v___x_529_ = lean_array_get_borrowed(v___x_528_, v___x_521_, v_i_524_);
v___x_530_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1));
v___x_531_ = l_Lean_instBEqNamePart_beq(v___x_529_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
v___x_532_ = lean_nat_add(v_i_524_, v_step_526_);
lean_dec(v_i_524_);
v_i_524_ = v___x_532_;
goto _start;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v_i_524_);
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___boxed(lean_object* v___x_535_, lean_object* v_range_536_, lean_object* v_b_537_, lean_object* v_i_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_535_, v_range_536_, v_b_537_, v_i_538_);
lean_dec(v_b_537_);
lean_dec_ref(v_range_536_);
lean_dec_ref(v___x_535_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(lean_object* v___x_540_, lean_object* v_as_541_, size_t v_sz_542_, size_t v_i_543_, lean_object* v_b_544_){
_start:
{
lean_object* v_a_546_; uint8_t v___x_550_; 
v___x_550_ = lean_usize_dec_lt(v_i_543_, v_sz_542_);
if (v___x_550_ == 0)
{
return v_b_544_;
}
else
{
lean_object* v_a_551_; lean_object* v___x_552_; lean_object* v_name_555_; lean_object* v_flags_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v_a_551_ = lean_array_uget_borrowed(v_as_541_, v_i_543_);
v___x_552_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(v_a_551_);
v_name_555_ = lean_ctor_get(v___x_552_, 0);
v_flags_556_ = lean_ctor_get(v___x_552_, 1);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_string_utf8_byte_size(v_name_555_);
v___x_559_ = lean_nat_dec_eq(v___x_558_, v___x_557_);
if (v___x_559_ == 0)
{
goto v___jp_553_;
}
else
{
uint8_t v_skipNext_560_; 
v_skipNext_560_ = lean_nat_dec_eq(v___x_540_, v___x_557_);
if (v_skipNext_560_ == 0)
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = lean_array_get_size(v_flags_556_);
v___x_562_ = lean_nat_dec_eq(v___x_561_, v___x_557_);
if (v___x_562_ == 0)
{
goto v___jp_553_;
}
else
{
lean_dec_ref(v___x_552_);
v_a_546_ = v_b_544_;
goto v___jp_545_;
}
}
else
{
goto v___jp_553_;
}
}
v___jp_553_:
{
lean_object* v___x_554_; 
v___x_554_ = lean_array_push(v_b_544_, v___x_552_);
v_a_546_ = v___x_554_;
goto v___jp_545_;
}
}
v___jp_545_:
{
size_t v___x_547_; size_t v___x_548_; 
v___x_547_ = ((size_t)1ULL);
v___x_548_ = lean_usize_add(v_i_543_, v___x_547_);
v_i_543_ = v___x_548_;
v_b_544_ = v_a_546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5___boxed(lean_object* v___x_563_, lean_object* v_as_564_, lean_object* v_sz_565_, lean_object* v_i_566_, lean_object* v_b_567_){
_start:
{
size_t v_sz_boxed_568_; size_t v_i_boxed_569_; lean_object* v_res_570_; 
v_sz_boxed_568_ = lean_unbox_usize(v_sz_565_);
lean_dec(v_sz_565_);
v_i_boxed_569_ = lean_unbox_usize(v_i_566_);
lean_dec(v_i_566_);
v_res_570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_563_, v_as_564_, v_sz_boxed_568_, v_i_boxed_569_, v_b_567_);
lean_dec_ref(v_as_564_);
lean_dec(v___x_563_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(lean_object* v_range_572_, lean_object* v_b_573_, lean_object* v_i_574_){
_start:
{
lean_object* v_stop_575_; lean_object* v_step_576_; lean_object* v_a_578_; uint8_t v___x_581_; 
v_stop_575_ = lean_ctor_get(v_range_572_, 1);
v_step_576_ = lean_ctor_get(v_range_572_, 2);
v___x_581_ = lean_nat_dec_lt(v_i_574_, v_stop_575_);
if (v___x_581_ == 0)
{
lean_dec(v_i_574_);
lean_inc_ref(v_b_573_);
return v_b_573_;
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = l_Lean_instInhabitedNamePart_default;
v___x_583_ = lean_array_get_borrowed(v___x_582_, v_b_573_, v_i_574_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_s_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_s_584_ = lean_ctor_get(v___x_583_, 0);
v___x_585_ = lean_string_utf8_byte_size(v_s_584_);
v___x_586_ = lean_unsigned_to_nat(2u);
v___x_587_ = lean_nat_dec_le(v___x_586_, v___x_585_);
if (v___x_587_ == 0)
{
v_a_578_ = v_b_573_;
goto v___jp_577_;
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0));
v___x_590_ = lean_string_memcmp(v_s_584_, v___x_589_, v___x_588_, v___x_588_, v___x_586_);
if (v___x_590_ == 0)
{
v_a_578_ = v_b_573_;
goto v___jp_577_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = l_Array_extract___redArg(v_b_573_, v___x_588_, v_i_574_);
return v___x_591_;
}
}
}
else
{
v_a_578_ = v_b_573_;
goto v___jp_577_;
}
}
v___jp_577_:
{
lean_object* v___x_579_; 
v___x_579_ = lean_nat_add(v_i_574_, v_step_576_);
lean_dec(v_i_574_);
v_b_573_ = v_a_578_;
v_i_574_ = v___x_579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___boxed(lean_object* v_range_592_, lean_object* v_b_593_, lean_object* v_i_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v_range_592_, v_b_593_, v_i_594_);
lean_dec_ref(v_b_593_);
lean_dec_ref(v_range_592_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v_range_603_, lean_object* v_b_604_, lean_object* v_i_605_){
_start:
{
lean_object* v_stop_606_; lean_object* v_step_607_; lean_object* v_a_609_; uint8_t v___x_612_; 
v_stop_606_ = lean_ctor_get(v_range_603_, 1);
v_step_607_ = lean_ctor_get(v_range_603_, 2);
v___x_612_ = lean_nat_dec_lt(v_i_605_, v_stop_606_);
if (v___x_612_ == 0)
{
lean_dec(v_i_605_);
return v_b_604_;
}
else
{
lean_object* v_snd_613_; lean_object* v_snd_614_; lean_object* v_fst_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_711_; 
v_snd_613_ = lean_ctor_get(v_b_604_, 1);
lean_inc(v_snd_613_);
v_snd_614_ = lean_ctor_get(v_snd_613_, 1);
lean_inc(v_snd_614_);
v_fst_615_ = lean_ctor_get(v_b_604_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v_b_604_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; 
v_unused_712_ = lean_ctor_get(v_b_604_, 1);
lean_dec(v_unused_712_);
v___x_617_ = v_b_604_;
v_isShared_618_ = v_isSharedCheck_711_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_fst_615_);
lean_dec(v_b_604_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_711_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_fst_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_709_; 
v_fst_619_ = lean_ctor_get(v_snd_613_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v_snd_613_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v_snd_613_, 1);
lean_dec(v_unused_710_);
v___x_621_ = v_snd_613_;
v_isShared_622_ = v_isSharedCheck_709_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_fst_619_);
lean_dec(v_snd_613_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_709_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_fst_623_; lean_object* v_snd_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_708_; 
v_fst_623_ = lean_ctor_get(v_snd_614_, 0);
v_snd_624_ = lean_ctor_get(v_snd_614_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_snd_614_);
if (v_isSharedCheck_708_ == 0)
{
v___x_626_ = v_snd_614_;
v_isShared_627_ = v_isSharedCheck_708_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_snd_624_);
lean_inc(v_fst_623_);
lean_dec(v_snd_614_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_708_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_unbox(v_snd_624_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_630_ = l_Lean_instInhabitedNamePart_default;
v___x_631_ = lean_array_get_borrowed(v___x_630_, v___x_601_, v_i_605_);
v___x_661_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1));
v___x_662_ = l_Lean_instBEqNamePart_beq(v___x_631_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v_cont_666_; lean_object* v_entries_668_; lean_object* v_currentCtx_669_; 
v___x_663_ = lean_box(0);
v___x_664_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0));
v___x_665_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1));
v_cont_666_ = l_Lean_instBEqNamePart_beq(v___x_631_, v___x_665_);
if (v_cont_666_ == 0)
{
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_s_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_s_674_ = lean_ctor_get(v___x_631_, 0);
v___x_675_ = lean_string_utf8_byte_size(v_s_674_);
v___x_676_ = lean_unsigned_to_nat(5u);
v___x_677_ = lean_nat_dec_le(v___x_676_, v___x_675_);
if (v___x_677_ == 0)
{
goto v___jp_632_;
}
else
{
uint8_t v___x_678_; 
v___x_678_ = lean_string_memcmp(v_s_674_, v___x_664_, v___x_628_, v___x_628_, v___x_676_);
if (v___x_678_ == 0)
{
goto v___jp_632_;
}
else
{
lean_del_object(v___x_626_);
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
if (lean_obj_tag(v_fst_619_) == 1)
{
lean_object* v_val_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_val_679_ = lean_ctor_get(v_fst_619_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v_fst_619_, 1);
v___x_680_ = lean_array_push(v_fst_615_, v_val_679_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_fst_623_);
lean_ctor_set(v___x_681_, 1, v_snd_624_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_663_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_680_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v_a_609_ = v___x_683_;
goto v___jp_608_;
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_fst_623_);
lean_ctor_set(v___x_684_, 1, v_snd_624_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v_fst_619_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v_fst_615_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v_a_609_ = v___x_686_;
goto v___jp_608_;
}
}
}
}
else
{
goto v___jp_632_;
}
}
else
{
lean_del_object(v___x_626_);
lean_dec(v_snd_624_);
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
if (lean_obj_tag(v_fst_619_) == 1)
{
lean_object* v_val_687_; lean_object* v___x_688_; 
v_val_687_ = lean_ctor_get(v_fst_619_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v_fst_619_, 1);
v___x_688_ = lean_array_push(v_fst_615_, v_val_687_);
v_entries_668_ = v___x_688_;
v_currentCtx_669_ = v___x_663_;
goto v___jp_667_;
}
else
{
v_entries_668_ = v_fst_615_;
v_currentCtx_669_ = v_fst_619_;
goto v___jp_667_;
}
}
v___jp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_box(v_cont_666_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v_fst_623_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v_currentCtx_669_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v_entries_668_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v_a_609_ = v___x_673_;
goto v___jp_608_;
}
}
else
{
lean_object* v_entries_690_; 
lean_del_object(v___x_626_);
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
if (lean_obj_tag(v_fst_619_) == 1)
{
lean_object* v_val_695_; lean_object* v___x_696_; 
v_val_695_ = lean_ctor_get(v_fst_619_, 0);
lean_inc(v_val_695_);
lean_dec_ref_known(v_fst_619_, 1);
v___x_696_ = lean_array_push(v_fst_615_, v_val_695_);
v_entries_690_ = v___x_696_;
goto v___jp_689_;
}
else
{
lean_dec(v_fst_619_);
v_entries_690_ = v_fst_615_;
goto v___jp_689_;
}
v___jp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_691_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2));
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_fst_623_);
lean_ctor_set(v___x_692_, 1, v_snd_624_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_entries_690_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v_a_609_ = v___x_694_;
goto v___jp_608_;
}
}
v___jp_632_:
{
if (lean_obj_tag(v_fst_619_) == 0)
{
lean_object* v___x_633_; lean_object* v___x_635_; 
lean_inc(v___x_631_);
v___x_633_ = lean_array_push(v_fst_623_, v___x_631_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_633_);
v___x_635_ = v___x_626_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_snd_624_);
v___x_635_ = v_reuseFailAlloc_642_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_637_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_635_);
v___x_637_ = v___x_621_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_fst_619_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_635_);
v___x_637_ = v_reuseFailAlloc_641_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_637_);
v___x_639_ = v___x_617_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_fst_615_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
v_a_609_ = v___x_639_;
goto v___jp_608_;
}
}
}
}
else
{
lean_object* v_val_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_660_; 
v_val_643_ = lean_ctor_get(v_fst_619_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_fst_619_);
if (v_isSharedCheck_660_ == 0)
{
v___x_645_ = v_fst_619_;
v_isShared_646_ = v_isSharedCheck_660_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_val_643_);
lean_dec(v_fst_619_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_660_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
lean_inc(v___x_631_);
v___x_647_ = lean_array_push(v_val_643_, v___x_631_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_659_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_627_ == 0)
{
v___x_651_ = v___x_626_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_fst_623_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_snd_624_);
v___x_651_ = v_reuseFailAlloc_658_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_651_);
lean_ctor_set(v___x_621_, 0, v___x_649_);
v___x_653_ = v___x_621_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_651_);
v___x_653_ = v_reuseFailAlloc_657_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_655_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_653_);
v___x_655_ = v___x_617_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_fst_615_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
v_a_609_ = v___x_655_;
goto v___jp_608_;
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
uint8_t v_skipNext_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
lean_dec(v_snd_624_);
v_skipNext_697_ = lean_nat_dec_eq(v___x_602_, v___x_628_);
v___x_698_ = lean_box(v_skipNext_697_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_698_);
v___x_700_ = v___x_626_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_fst_623_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_698_);
v___x_700_ = v_reuseFailAlloc_707_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_700_);
v___x_702_ = v___x_621_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_fst_619_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_700_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_702_);
v___x_704_ = v___x_617_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_fst_615_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
v_a_609_ = v___x_704_;
goto v___jp_608_;
}
}
}
}
}
}
}
}
v___jp_608_:
{
lean_object* v___x_610_; 
v___x_610_ = lean_nat_add(v_i_605_, v_step_607_);
lean_dec(v_i_605_);
v_b_604_ = v_a_609_;
v_i_605_ = v___x_610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___boxed(lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v_range_715_, lean_object* v_b_716_, lean_object* v_i_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_713_, v___x_714_, v_range_715_, v_b_716_, v_i_717_);
lean_dec_ref(v_range_715_);
lean_dec(v___x_714_);
lean_dec_ref(v___x_713_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(lean_object* v___x_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_snd_721_; lean_object* v_fst_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_779_; 
v_snd_721_ = lean_ctor_get(v_a_720_, 1);
v_fst_722_ = lean_ctor_get(v_a_720_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_a_720_);
if (v_isSharedCheck_779_ == 0)
{
v___x_724_ = v_a_720_;
v_isShared_725_ = v_isSharedCheck_779_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_snd_721_);
lean_inc(v_fst_722_);
lean_dec(v_a_720_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_779_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_fst_726_; lean_object* v_snd_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_778_; 
v_fst_726_ = lean_ctor_get(v_snd_721_, 0);
v_snd_727_ = lean_ctor_get(v_snd_721_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_snd_721_);
if (v_isSharedCheck_778_ == 0)
{
v___x_729_ = v_snd_721_;
v_isShared_730_ = v_isSharedCheck_778_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_snd_727_);
lean_inc(v_fst_726_);
lean_dec(v_snd_721_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_778_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
uint8_t v___x_738_; 
v___x_738_ = lean_unbox(v_snd_727_);
if (v___x_738_ == 0)
{
goto v___jp_731_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_array_get_size(v_fst_722_);
v___x_741_ = lean_nat_dec_eq(v___x_740_, v___x_739_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
lean_del_object(v___x_729_);
lean_del_object(v___x_724_);
v___x_742_ = l_Lean_instInhabitedNamePart_default;
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = lean_nat_sub(v___x_740_, v___x_743_);
v___x_745_ = lean_array_get_borrowed(v___x_742_, v_fst_722_, v___x_744_);
lean_dec(v___x_744_);
lean_inc(v___x_745_);
v___x_746_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_745_);
if (lean_obj_tag(v___x_746_) == 0)
{
uint8_t v_skipNext_747_; 
v_skipNext_747_ = lean_nat_dec_eq(v___x_719_, v___x_739_);
if (lean_obj_tag(v___x_745_) == 1)
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(2u);
v___x_749_ = lean_nat_dec_le(v___x_748_, v___x_740_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec(v_snd_727_);
v___x_750_ = lean_box(v___x_749_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_fst_726_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_fst_722_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v_a_720_ = v___x_752_;
goto _start;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_nat_sub(v___x_740_, v___x_748_);
v___x_755_ = lean_array_get_borrowed(v___x_742_, v_fst_722_, v___x_754_);
lean_dec(v___x_754_);
lean_inc(v___x_755_);
v___x_756_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_755_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v_snd_727_);
v___x_757_ = lean_box(v_skipNext_747_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_fst_726_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_fst_722_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v_a_720_ = v___x_759_;
goto _start;
}
else
{
lean_object* v_val_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_val_761_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v___x_756_, 1);
v___x_762_ = lean_array_push(v_fst_726_, v_val_761_);
v___x_763_ = lean_array_pop(v_fst_722_);
v___x_764_ = lean_array_pop(v___x_763_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_762_);
lean_ctor_set(v___x_765_, 1, v_snd_727_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v_a_720_ = v___x_766_;
goto _start;
}
}
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec(v_snd_727_);
v___x_768_ = lean_box(v_skipNext_747_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v_fst_726_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v_fst_722_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v_a_720_ = v___x_770_;
goto _start;
}
}
else
{
lean_object* v_val_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_val_772_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_val_772_);
lean_dec_ref_known(v___x_746_, 1);
v___x_773_ = lean_array_push(v_fst_726_, v_val_772_);
v___x_774_ = lean_array_pop(v_fst_722_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v_snd_727_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v_a_720_ = v___x_776_;
goto _start;
}
}
else
{
goto v___jp_731_;
}
}
v___jp_731_:
{
lean_object* v___x_733_; 
if (v_isShared_730_ == 0)
{
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_fst_726_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_snd_727_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 1, v___x_733_);
v___x_735_ = v___x_724_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_fst_722_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg___boxed(lean_object* v___x_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_780_, v_a_781_);
lean_dec(v___x_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(lean_object* v_as_788_, size_t v_sz_789_, size_t v_i_790_, lean_object* v_b_791_){
_start:
{
lean_object* v_a_793_; uint8_t v___x_797_; 
v___x_797_ = lean_usize_dec_lt(v_i_790_, v_sz_789_);
if (v___x_797_ == 0)
{
return v_b_791_;
}
else
{
lean_object* v_a_798_; lean_object* v_name_799_; lean_object* v_flags_800_; lean_object* v___y_802_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v_a_798_ = lean_array_uget_borrowed(v_as_788_, v_i_790_);
v_name_799_ = lean_ctor_get(v_a_798_, 0);
v_flags_800_ = lean_ctor_get(v_a_798_, 1);
v___x_820_ = lean_string_utf8_byte_size(v_name_799_);
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_nat_dec_eq(v___x_820_, v___x_821_);
if (v___x_822_ == 0)
{
lean_inc_ref(v_name_799_);
v___y_802_ = v_name_799_;
goto v___jp_801_;
}
else
{
lean_object* v___x_823_; 
v___x_823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_802_ = v___x_823_;
goto v___jp_801_;
}
v___jp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_803_ = lean_array_get_size(v_flags_800_);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_nat_dec_eq(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_807_ = lean_string_append(v_b_791_, v___x_806_);
v___x_808_ = lean_string_append(v___x_807_, v___y_802_);
lean_dec_ref(v___y_802_);
v___x_809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1));
v___x_810_ = lean_string_append(v___x_808_, v___x_809_);
v___x_811_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
lean_inc_ref(v_flags_800_);
v___x_812_ = lean_array_to_list(v_flags_800_);
v___x_813_ = l_String_intercalate(v___x_811_, v___x_812_);
v___x_814_ = lean_string_append(v___x_810_, v___x_813_);
lean_dec_ref(v___x_813_);
v___x_815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_816_ = lean_string_append(v___x_814_, v___x_815_);
v_a_793_ = v___x_816_;
goto v___jp_792_;
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_818_ = lean_string_append(v_b_791_, v___x_817_);
v___x_819_ = lean_string_append(v___x_818_, v___y_802_);
lean_dec_ref(v___y_802_);
v_a_793_ = v___x_819_;
goto v___jp_792_;
}
}
}
v___jp_792_:
{
size_t v___x_794_; size_t v___x_795_; 
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_add(v_i_790_, v___x_794_);
v_i_790_ = v___x_795_;
v_b_791_ = v_a_793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___boxed(lean_object* v_as_824_, lean_object* v_sz_825_, lean_object* v_i_826_, lean_object* v_b_827_){
_start:
{
size_t v_sz_boxed_828_; size_t v_i_boxed_829_; lean_object* v_res_830_; 
v_sz_boxed_828_ = lean_unbox_usize(v_sz_825_);
lean_dec(v_sz_825_);
v_i_boxed_829_ = lean_unbox_usize(v_i_826_);
lean_dec(v_i_826_);
v_res_830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v_as_824_, v_sz_boxed_828_, v_i_boxed_829_, v_b_827_);
lean_dec_ref(v_as_824_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(lean_object* v_components_839_){
_start:
{
lean_object* v___y_841_; lean_object* v_result_842_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_863_; lean_object* v_parts_864_; lean_object* v_specEntries_865_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v_entries_875_; uint8_t v_skipNext_880_; 
v___x_846_ = lean_array_get_size(v_components_839_);
v___x_847_ = lean_unsigned_to_nat(0u);
v_skipNext_880_ = lean_nat_dec_eq(v___x_846_, v___x_847_);
if (v_skipNext_880_ == 0)
{
lean_object* v___x_881_; lean_object* v_fst_882_; lean_object* v_snd_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_938_; 
v___x_881_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_components_839_, v___x_847_, v___x_846_);
v_fst_882_ = lean_ctor_get(v___x_881_, 0);
v_snd_883_ = lean_ctor_get(v___x_881_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_938_ == 0)
{
v___x_885_ = v___x_881_;
v_isShared_886_ = v_isSharedCheck_938_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_snd_883_);
lean_inc(v_fst_882_);
lean_dec(v___x_881_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_938_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v_parts_887_; lean_object* v_flags_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v_parts_887_ = l_Array_extract___redArg(v_components_839_, v_fst_882_, v___x_846_);
v_flags_888_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1));
v___x_889_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2));
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v___x_889_);
lean_ctor_set(v___x_885_, 0, v_parts_887_);
v___x_891_ = v___x_885_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_parts_887_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_889_);
v___x_891_ = v_reuseFailAlloc_937_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_892_; lean_object* v_fst_893_; lean_object* v_snd_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_936_; 
v___x_892_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_846_, v___x_891_);
v_fst_893_ = lean_ctor_get(v___x_892_, 0);
v_snd_894_ = lean_ctor_get(v___x_892_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_936_ == 0)
{
v___x_896_ = v___x_892_;
v_isShared_897_ = v_isSharedCheck_936_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_snd_894_);
lean_inc(v_fst_893_);
lean_dec(v___x_892_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_936_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_flags_899_; uint8_t v___x_931_; 
v___x_931_ = lean_unbox(v_snd_883_);
lean_dec(v_snd_883_);
if (v___x_931_ == 0)
{
lean_object* v_fst_932_; 
v_fst_932_ = lean_ctor_get(v_snd_894_, 0);
lean_inc(v_fst_932_);
lean_dec(v_snd_894_);
v_flags_899_ = v_fst_932_;
goto v___jp_898_;
}
else
{
lean_object* v_fst_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_fst_933_ = lean_ctor_get(v_snd_894_, 0);
lean_inc(v_fst_933_);
lean_dec(v_snd_894_);
v___x_934_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3));
v___x_935_ = lean_array_push(v_fst_933_, v___x_934_);
v_flags_899_ = v___x_935_;
goto v___jp_898_;
}
v___jp_898_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_900_ = lean_array_get_size(v_fst_893_);
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_902_, 0, v___x_847_);
lean_ctor_set(v___x_902_, 1, v___x_900_);
lean_ctor_set(v___x_902_, 2, v___x_901_);
v___x_903_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_902_, v_fst_893_, v___x_847_);
lean_dec(v_fst_893_);
lean_dec_ref_known(v___x_902_, 3);
v___x_904_ = lean_box(0);
v___x_905_ = lean_array_get_size(v___x_903_);
v___x_906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_906_, 0, v___x_847_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
lean_ctor_set(v___x_906_, 2, v___x_901_);
v___x_907_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_903_, v___x_906_, v___x_904_, v___x_847_);
lean_dec_ref_known(v___x_906_, 3);
if (lean_obj_tag(v___x_907_) == 1)
{
lean_object* v_val_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v_val_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc_n(v_val_908_, 2);
lean_dec_ref_known(v___x_907_, 1);
v___x_909_ = l_Array_extract___redArg(v___x_903_, v___x_847_, v_val_908_);
v___x_910_ = l_Array_extract___redArg(v___x_903_, v_val_908_, v___x_905_);
lean_dec_ref(v___x_903_);
v___x_911_ = lean_array_get_size(v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_912_, 0, v___x_847_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
lean_ctor_set(v___x_912_, 2, v___x_901_);
v___x_913_ = lean_box(v_skipNext_880_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 1, v___x_913_);
lean_ctor_set(v___x_896_, 0, v_flags_888_);
v___x_915_ = v___x_896_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_flags_888_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v___x_913_);
v___x_915_ = v_reuseFailAlloc_930_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v_snd_919_; lean_object* v_snd_920_; lean_object* v_fst_921_; 
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_904_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_flags_888_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_910_, v___x_846_, v___x_912_, v___x_917_, v___x_847_);
lean_dec_ref_known(v___x_912_, 3);
lean_dec_ref(v___x_910_);
v_snd_919_ = lean_ctor_get(v___x_918_, 1);
v_snd_920_ = lean_ctor_get(v_snd_919_, 1);
lean_inc(v_snd_920_);
v_fst_921_ = lean_ctor_get(v_snd_919_, 0);
if (lean_obj_tag(v_fst_921_) == 1)
{
lean_object* v_fst_922_; lean_object* v_fst_923_; lean_object* v_val_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
lean_inc_ref(v_fst_921_);
v_fst_922_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_fst_922_);
lean_dec_ref(v___x_918_);
v_fst_923_ = lean_ctor_get(v_snd_920_, 0);
lean_inc(v_fst_923_);
lean_dec(v_snd_920_);
v_val_924_ = lean_ctor_get(v_fst_921_, 0);
lean_inc(v_val_924_);
lean_dec_ref_known(v_fst_921_, 1);
v___x_925_ = lean_array_get_size(v_val_924_);
v___x_926_ = lean_nat_dec_eq(v___x_925_, v___x_847_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
v___x_927_ = lean_array_push(v_fst_922_, v_val_924_);
v___y_871_ = v_flags_899_;
v___y_872_ = v_fst_923_;
v___y_873_ = v_flags_888_;
v___y_874_ = v___x_909_;
v_entries_875_ = v___x_927_;
goto v___jp_870_;
}
else
{
lean_dec(v_val_924_);
v___y_871_ = v_flags_899_;
v___y_872_ = v_fst_923_;
v___y_873_ = v_flags_888_;
v___y_874_ = v___x_909_;
v_entries_875_ = v_fst_922_;
goto v___jp_870_;
}
}
else
{
lean_object* v_fst_928_; lean_object* v_fst_929_; 
v_fst_928_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_fst_928_);
lean_dec_ref(v___x_918_);
v_fst_929_ = lean_ctor_get(v_snd_920_, 0);
lean_inc(v_fst_929_);
lean_dec(v_snd_920_);
v___y_871_ = v_flags_899_;
v___y_872_ = v_fst_929_;
v___y_873_ = v_flags_888_;
v___y_874_ = v___x_909_;
v_entries_875_ = v_fst_928_;
goto v___jp_870_;
}
}
}
else
{
lean_dec(v___x_907_);
lean_del_object(v___x_896_);
v___y_863_ = v_flags_899_;
v_parts_864_ = v___x_903_;
v_specEntries_865_ = v_flags_888_;
goto v___jp_862_;
}
}
}
}
}
}
else
{
lean_object* v___x_939_; 
v___x_939_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_939_;
}
v___jp_840_:
{
size_t v_sz_843_; size_t v___x_844_; lean_object* v___x_845_; 
v_sz_843_ = lean_array_size(v___y_841_);
v___x_844_ = ((size_t)0ULL);
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v___y_841_, v_sz_843_, v___x_844_, v_result_842_);
lean_dec_ref(v___y_841_);
return v___x_845_;
}
v___jp_848_:
{
lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_852_ = lean_array_get_size(v___y_850_);
v___x_853_ = lean_nat_dec_eq(v___x_852_, v___x_847_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_854_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0));
v___x_855_ = lean_string_append(v___y_851_, v___x_854_);
v___x_856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
v___x_857_ = lean_array_to_list(v___y_850_);
v___x_858_ = l_String_intercalate(v___x_856_, v___x_857_);
v___x_859_ = lean_string_append(v___x_855_, v___x_858_);
lean_dec_ref(v___x_858_);
v___x_860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_861_ = lean_string_append(v___x_859_, v___x_860_);
v___y_841_ = v___y_849_;
v_result_842_ = v___x_861_;
goto v___jp_840_;
}
else
{
lean_dec_ref(v___y_850_);
v___y_841_ = v___y_849_;
v_result_842_ = v___y_851_;
goto v___jp_840_;
}
}
v___jp_862_:
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = lean_array_get_size(v_parts_864_);
v___x_867_ = lean_nat_dec_eq(v___x_866_, v___x_847_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_parts_864_);
lean_dec_ref(v_parts_864_);
v___y_849_ = v_specEntries_865_;
v___y_850_ = v___y_863_;
v___y_851_ = v___x_868_;
goto v___jp_848_;
}
else
{
lean_object* v___x_869_; 
lean_dec_ref(v_parts_864_);
v___x_869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_849_ = v_specEntries_865_;
v___y_850_ = v___y_863_;
v___y_851_ = v___x_869_;
goto v___jp_848_;
}
}
v___jp_870_:
{
size_t v_sz_876_; size_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_sz_876_ = lean_array_size(v_entries_875_);
v___x_877_ = ((size_t)0ULL);
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_846_, v_entries_875_, v_sz_876_, v___x_877_, v___y_873_);
lean_dec_ref(v_entries_875_);
v___x_879_ = l_Array_append___redArg(v___y_874_, v___y_872_);
lean_dec(v___y_872_);
v___y_863_ = v___y_871_;
v_parts_864_ = v___x_879_;
v_specEntries_865_ = v___x_878_;
goto v___jp_862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___boxed(lean_object* v_components_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v_components_940_);
lean_dec_ref(v_components_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(lean_object* v___x_942_, lean_object* v_inst_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_942_, v_a_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___boxed(lean_object* v___x_946_, lean_object* v_inst_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(v___x_946_, v_inst_947_, v_a_948_);
lean_dec(v___x_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(lean_object* v_range_950_, lean_object* v_b_951_, lean_object* v_i_952_, lean_object* v_hs_953_, lean_object* v_hl_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v_range_950_, v_b_951_, v_i_952_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___boxed(lean_object* v_range_956_, lean_object* v_b_957_, lean_object* v_i_958_, lean_object* v_hs_959_, lean_object* v_hl_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(v_range_956_, v_b_957_, v_i_958_, v_hs_959_, v_hl_960_);
lean_dec_ref(v_b_957_);
lean_dec_ref(v_range_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(lean_object* v___x_962_, lean_object* v_range_963_, lean_object* v_b_964_, lean_object* v_i_965_, lean_object* v_hs_966_, lean_object* v_hl_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_962_, v_range_963_, v_b_964_, v_i_965_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___boxed(lean_object* v___x_969_, lean_object* v_range_970_, lean_object* v_b_971_, lean_object* v_i_972_, lean_object* v_hs_973_, lean_object* v_hl_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(v___x_969_, v_range_970_, v_b_971_, v_i_972_, v_hs_973_, v_hl_974_);
lean_dec(v_b_971_);
lean_dec_ref(v_range_970_);
lean_dec_ref(v___x_969_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(lean_object* v___x_976_, lean_object* v___x_977_, lean_object* v_range_978_, lean_object* v_b_979_, lean_object* v_i_980_, lean_object* v_hs_981_, lean_object* v_hl_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_976_, v___x_977_, v_range_978_, v_b_979_, v_i_980_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___boxed(lean_object* v___x_984_, lean_object* v___x_985_, lean_object* v_range_986_, lean_object* v_b_987_, lean_object* v_i_988_, lean_object* v_hs_989_, lean_object* v_hl_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(v___x_984_, v___x_985_, v_range_986_, v_b_987_, v_i_988_, v_hs_989_, v_hl_990_);
lean_dec_ref(v_range_986_);
lean_dec(v___x_985_);
lean_dec_ref(v___x_984_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(lean_object* v_body_992_){
_start:
{
lean_object* v_name_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_name_993_ = l_Lean_Name_demangle(v_body_992_);
v___x_994_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(v_name_993_);
lean_dec(v_name_993_);
v___x_995_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v___x_994_);
lean_dec_ref(v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody___boxed(lean_object* v_body_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_body_996_);
lean_dec_ref(v_body_996_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(lean_object* v_s_1001_, lean_object* v___x_1002_, lean_object* v_a_1003_, lean_object* v_b_1004_){
_start:
{
uint8_t v_decide_1005_; 
v_decide_1005_ = lean_nat_dec_eq(v_a_1003_, v___x_1002_);
if (v_decide_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint32_t v___x_1009_; uint32_t v___x_1010_; uint8_t v___x_1011_; 
lean_dec_ref(v_b_1004_);
v___x_1006_ = lean_box(0);
v___x_1007_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1008_ = lean_string_utf8_next_fast(v_s_1001_, v_a_1003_);
v___x_1009_ = lean_string_utf8_get_fast(v_s_1001_, v_a_1003_);
v___x_1010_ = 95;
v___x_1011_ = lean_uint32_dec_eq(v___x_1009_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_dec(v_a_1003_);
v_a_1003_ = v___x_1008_;
v_b_1004_ = v___x_1007_;
goto _start;
}
else
{
lean_object* v___x_1013_; uint8_t v_decide_1014_; 
v___x_1013_ = lean_unsigned_to_nat(0u);
v_decide_1014_ = lean_nat_dec_eq(v_a_1003_, v___x_1013_);
if (v_decide_1014_ == 0)
{
lean_object* v___x_1015_; uint8_t v_decide_1016_; 
v___x_1015_ = lean_string_utf8_byte_size(v_s_1001_);
v_decide_1016_ = lean_nat_dec_eq(v___x_1008_, v___x_1015_);
if (v_decide_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_string_utf8_extract_fast(v_s_1001_, v___x_1013_, v_a_1003_);
lean_dec(v_a_1003_);
v___x_1018_ = l_Lean_Name_demangle_x3f(v___x_1017_);
if (lean_obj_tag(v___x_1018_) == 1)
{
lean_object* v_val_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1041_; 
v_val_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1041_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_val_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1041_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
if (lean_obj_tag(v_val_1019_) == 1)
{
lean_object* v_pre_1023_; 
v_pre_1023_ = lean_ctor_get(v_val_1019_, 0);
lean_inc(v_pre_1023_);
lean_dec_ref_known(v_val_1019_, 2);
if (lean_obj_tag(v_pre_1023_) == 0)
{
lean_object* v___x_1024_; lean_object* v___y_1026_; lean_object* v___x_1034_; 
v___x_1024_ = lean_string_utf8_extract_fast(v_s_1001_, v___x_1008_, v___x_1015_);
v___x_1034_ = l_Lean_Name_demangle_x3f(v___x_1024_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_dec_ref(v___x_1024_);
lean_del_object(v___x_1021_);
lean_dec_ref(v___x_1017_);
v_a_1003_ = v___x_1008_;
v_b_1004_ = v___x_1007_;
goto _start;
}
else
{
lean_object* v___x_1036_; 
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = l_Lean_Name_demangle(v___x_1017_);
if (lean_obj_tag(v___x_1036_) == 1)
{
lean_object* v_pre_1037_; 
v_pre_1037_ = lean_ctor_get(v___x_1036_, 0);
if (lean_obj_tag(v_pre_1037_) == 0)
{
lean_object* v_str_1038_; 
lean_dec_ref(v___x_1017_);
v_str_1038_ = lean_ctor_get(v___x_1036_, 1);
lean_inc_ref(v_str_1038_);
lean_dec_ref_known(v___x_1036_, 2);
v___y_1026_ = v_str_1038_;
goto v___jp_1025_;
}
else
{
lean_dec_ref_known(v___x_1036_, 2);
v___y_1026_ = v___x_1017_;
goto v___jp_1025_;
}
}
else
{
lean_dec(v___x_1036_);
v___y_1026_ = v___x_1017_;
goto v___jp_1025_;
}
}
v___jp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1027_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v___x_1024_);
lean_dec_ref(v___x_1024_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___y_1026_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1028_);
v___x_1030_ = v___x_1021_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_1006_);
v___x_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
return v___x_1032_;
}
}
}
else
{
lean_dec(v_pre_1023_);
lean_del_object(v___x_1021_);
lean_dec_ref(v___x_1017_);
v_a_1003_ = v___x_1008_;
v_b_1004_ = v___x_1007_;
goto _start;
}
}
else
{
lean_del_object(v___x_1021_);
lean_dec(v_val_1019_);
lean_dec_ref(v___x_1017_);
v_a_1003_ = v___x_1008_;
v_b_1004_ = v___x_1007_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1018_);
lean_dec_ref(v___x_1017_);
v_a_1003_ = v___x_1008_;
v_b_1004_ = v___x_1007_;
goto _start;
}
}
else
{
lean_dec(v_a_1003_);
v_a_1003_ = v___x_1008_;
v_b_1004_ = v___x_1007_;
goto _start;
}
}
else
{
lean_dec(v_a_1003_);
v_a_1003_ = v___x_1008_;
v_b_1004_ = v___x_1007_;
goto _start;
}
}
}
else
{
lean_object* v___x_1045_; 
lean_dec(v_a_1003_);
v___x_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1045_, 0, v_b_1004_);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___boxed(lean_object* v_s_1046_, lean_object* v___x_1047_, lean_object* v_a_1048_, lean_object* v_b_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1046_, v___x_1047_, v_a_1048_, v_b_1049_);
lean_dec(v___x_1047_);
lean_dec_ref(v_s_1046_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(lean_object* v_s_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = lean_string_utf8_byte_size(v_s_1051_);
v___x_1054_ = lean_box(0);
v___x_1055_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1056_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1051_, v___x_1053_, v___x_1052_, v___x_1055_);
if (lean_obj_tag(v___x_1056_) == 0)
{
return v___x_1054_;
}
else
{
lean_object* v_val_1057_; lean_object* v_fst_1058_; 
v_val_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_val_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v_fst_1058_ = lean_ctor_get(v_val_1057_, 0);
lean_inc(v_fst_1058_);
lean_dec(v_val_1057_);
if (lean_obj_tag(v_fst_1058_) == 0)
{
return v___x_1054_;
}
else
{
return v_fst_1058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg___boxed(lean_object* v_s_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_s_1059_);
lean_dec_ref(v_s_1059_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(lean_object* v_s_1061_, lean_object* v___x_1062_, lean_object* v___x_1063_, lean_object* v_inst_1064_, lean_object* v_R_1065_, lean_object* v_a_1066_, lean_object* v_b_1067_, lean_object* v_c_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1061_, v___x_1062_, v_a_1066_, v_b_1067_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___boxed(lean_object* v_s_1070_, lean_object* v___x_1071_, lean_object* v___x_1072_, lean_object* v_inst_1073_, lean_object* v_R_1074_, lean_object* v_a_1075_, lean_object* v_b_1076_, lean_object* v_c_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(v_s_1070_, v___x_1071_, v___x_1072_, v_inst_1073_, v_R_1074_, v_a_1075_, v_b_1076_, v_c_1077_);
lean_dec_ref(v___x_1072_);
lean_dec(v___x_1071_);
lean_dec_ref(v_s_1070_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(lean_object* v_s_1079_, lean_object* v___x_1080_, lean_object* v___x_1081_, lean_object* v_a_1082_, lean_object* v_b_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_box(0);
switch(lean_obj_tag(v_a_1082_))
{
case 0:
{
lean_object* v_pos_1085_; lean_object* v___x_1086_; 
v_pos_1085_ = lean_ctor_get(v_a_1082_, 0);
lean_inc(v_pos_1085_);
lean_dec_ref_known(v_a_1082_, 1);
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_pos_1085_);
return v___x_1086_;
}
case 1:
{
lean_object* v_pos_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1096_; 
v_pos_1087_ = lean_ctor_get(v_a_1082_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_a_1082_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1089_ = v_a_1082_;
v_isShared_1090_ = v_isSharedCheck_1096_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_pos_1087_);
lean_dec(v_a_1082_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1096_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = lean_string_utf8_next_fast(v_s_1079_, v_pos_1087_);
lean_dec(v_pos_1087_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set_tag(v___x_1089_, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1091_);
v___x_1093_ = v___x_1089_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
v_a_1082_ = v___x_1093_;
v_b_1083_ = v___x_1084_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1097_; lean_object* v_table_1098_; lean_object* v_stackPos_1099_; lean_object* v_needlePos_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1153_; 
v_needle_1097_ = lean_ctor_get(v_a_1082_, 0);
v_table_1098_ = lean_ctor_get(v_a_1082_, 1);
v_stackPos_1099_ = lean_ctor_get(v_a_1082_, 2);
v_needlePos_1100_ = lean_ctor_get(v_a_1082_, 3);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_a_1082_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1102_ = v_a_1082_;
v_isShared_1103_ = v_isSharedCheck_1153_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_needlePos_1100_);
lean_inc(v_stackPos_1099_);
lean_inc(v_table_1098_);
lean_inc(v_needle_1097_);
lean_dec(v_a_1082_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1153_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v_str_1104_; lean_object* v_startInclusive_1105_; lean_object* v_endExclusive_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v_str_1104_ = lean_ctor_get(v_needle_1097_, 0);
v_startInclusive_1105_ = lean_ctor_get(v_needle_1097_, 1);
v_endExclusive_1106_ = lean_ctor_get(v_needle_1097_, 2);
v___x_1107_ = lean_nat_sub(v_stackPos_1099_, v_needlePos_1100_);
v___x_1108_ = lean_nat_sub(v_endExclusive_1106_, v_startInclusive_1105_);
v___x_1109_ = lean_nat_add(v___x_1107_, v___x_1108_);
v___x_1110_ = lean_nat_dec_le(v___x_1109_, v___x_1081_);
lean_dec(v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
lean_dec(v___x_1108_);
lean_del_object(v___x_1102_);
lean_dec(v_needlePos_1100_);
lean_dec(v_stackPos_1099_);
lean_dec_ref(v_table_1098_);
lean_dec_ref(v_needle_1097_);
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_add(v___x_1107_, v___x_1111_);
lean_dec(v___x_1107_);
v___x_1113_ = lean_nat_dec_le(v___x_1112_, v___x_1081_);
lean_dec(v___x_1112_);
if (v___x_1113_ == 0)
{
lean_inc(v_b_1083_);
return v_b_1083_;
}
else
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_box(3);
v_a_1082_ = v___x_1114_;
v_b_1083_ = v___x_1084_;
goto _start;
}
}
else
{
uint8_t v_stackByte_1116_; lean_object* v___x_1117_; uint8_t v_patByte_1118_; uint8_t v___x_1119_; 
lean_dec(v___x_1107_);
lean_inc(v_stackPos_1099_);
v_stackByte_1116_ = lean_string_get_byte_fast(v_s_1079_, v_stackPos_1099_);
v___x_1117_ = lean_nat_add(v_startInclusive_1105_, v_needlePos_1100_);
v_patByte_1118_ = lean_string_get_byte_fast(v_str_1104_, v___x_1117_);
v___x_1119_ = lean_uint8_dec_eq(v_stackByte_1116_, v_patByte_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; uint8_t v_decide_1121_; 
lean_dec(v___x_1108_);
v___x_1120_ = lean_unsigned_to_nat(0u);
v_decide_1121_ = lean_nat_dec_eq(v_needlePos_1100_, v___x_1120_);
if (v_decide_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v_newNeedlePos_1124_; uint8_t v___x_1125_; 
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = lean_nat_sub(v_needlePos_1100_, v___x_1122_);
lean_dec(v_needlePos_1100_);
v_newNeedlePos_1124_ = lean_array_fget_borrowed(v_table_1098_, v___x_1123_);
lean_dec(v___x_1123_);
v___x_1125_ = lean_nat_dec_eq(v_newNeedlePos_1124_, v___x_1120_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1127_; 
lean_inc(v_newNeedlePos_1124_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 3, v_newNeedlePos_1124_);
v___x_1127_ = v___x_1102_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_needle_1097_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_table_1098_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v_stackPos_1099_);
lean_ctor_set(v_reuseFailAlloc_1129_, 3, v_newNeedlePos_1124_);
v___x_1127_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
v_a_1082_ = v___x_1127_;
v_b_1083_ = v___x_1084_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1130_; lean_object* v___x_1132_; 
v_nextStackPos_1130_ = l_String_Slice_posGE___redArg(v___x_1080_, v_stackPos_1099_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 3, v___x_1120_);
lean_ctor_set(v___x_1102_, 2, v_nextStackPos_1130_);
v___x_1132_ = v___x_1102_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_needle_1097_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_table_1098_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_nextStackPos_1130_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v___x_1120_);
v___x_1132_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
v_a_1082_ = v___x_1132_;
v_b_1083_ = v___x_1084_;
goto _start;
}
}
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v_nextStackPos_1137_; lean_object* v___x_1139_; 
lean_dec(v_needlePos_1100_);
v___x_1135_ = lean_unsigned_to_nat(1u);
v___x_1136_ = lean_nat_add(v_stackPos_1099_, v___x_1135_);
lean_dec(v_stackPos_1099_);
v_nextStackPos_1137_ = l_String_Slice_posGE___redArg(v___x_1080_, v___x_1136_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 3, v___x_1120_);
lean_ctor_set(v___x_1102_, 2, v_nextStackPos_1137_);
v___x_1139_ = v___x_1102_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_needle_1097_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_table_1098_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_nextStackPos_1137_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v___x_1120_);
v___x_1139_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
v_a_1082_ = v___x_1139_;
v_b_1083_ = v___x_1084_;
goto _start;
}
}
}
else
{
lean_object* v___x_1142_; lean_object* v_nextStackPos_1143_; lean_object* v_nextNeedlePos_1144_; uint8_t v_decide_1145_; 
v___x_1142_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1143_ = lean_nat_add(v_stackPos_1099_, v___x_1142_);
lean_dec(v_stackPos_1099_);
v_nextNeedlePos_1144_ = lean_nat_add(v_needlePos_1100_, v___x_1142_);
lean_dec(v_needlePos_1100_);
v_decide_1145_ = lean_nat_dec_eq(v_nextNeedlePos_1144_, v___x_1108_);
lean_dec(v___x_1108_);
if (v_decide_1145_ == 0)
{
lean_object* v___x_1147_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 3, v_nextNeedlePos_1144_);
lean_ctor_set(v___x_1102_, 2, v_nextStackPos_1143_);
v___x_1147_ = v___x_1102_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_needle_1097_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_table_1098_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_nextStackPos_1143_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_nextNeedlePos_1144_);
v___x_1147_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
v_a_1082_ = v___x_1147_;
goto _start;
}
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_del_object(v___x_1102_);
lean_dec_ref(v_table_1098_);
lean_dec_ref(v_needle_1097_);
v___x_1150_ = lean_nat_sub(v_nextStackPos_1143_, v_nextNeedlePos_1144_);
lean_dec(v_nextNeedlePos_1144_);
lean_dec(v_nextStackPos_1143_);
v___x_1151_ = l_String_Slice_pos_x21(v___x_1080_, v___x_1150_);
lean_dec(v___x_1150_);
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
}
}
}
}
default: 
{
lean_inc(v_b_1083_);
return v_b_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg___boxed(lean_object* v_s_1154_, lean_object* v___x_1155_, lean_object* v___x_1156_, lean_object* v_a_1157_, lean_object* v_b_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1154_, v___x_1155_, v___x_1156_, v_a_1157_, v_b_1158_);
lean_dec(v_b_1158_);
lean_dec(v___x_1156_);
lean_dec_ref(v___x_1155_);
lean_dec_ref(v_s_1154_);
return v_res_1159_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1));
v___x_1166_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1165_);
return v___x_1166_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2);
v___x_1169_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1));
v___x_1170_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v___x_1168_);
lean_ctor_set(v___x_1170_, 2, v___x_1167_);
lean_ctor_set(v___x_1170_, 3, v___x_1167_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(lean_object* v_s_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = lean_string_utf8_byte_size(v_s_1171_);
lean_inc_ref(v_s_1171_);
v___x_1174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1174_, 0, v_s_1171_);
lean_ctor_set(v___x_1174_, 1, v___x_1172_);
lean_ctor_set(v___x_1174_, 2, v___x_1173_);
v___x_1175_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
v___x_1176_ = lean_box(0);
v___x_1177_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1171_, v___x_1174_, v___x_1173_, v___x_1175_, v___x_1176_);
lean_dec_ref_known(v___x_1174_, 3);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v_s_1171_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
return v___x_1179_;
}
else
{
lean_object* v_val_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_val_1180_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_val_1180_);
lean_dec_ref_known(v___x_1177_, 1);
v___x_1181_ = lean_string_utf8_extract_fast(v_s_1171_, v___x_1172_, v_val_1180_);
v___x_1182_ = lean_string_utf8_extract_fast(v_s_1171_, v_val_1180_, v___x_1173_);
lean_dec(v_val_1180_);
lean_dec_ref(v_s_1171_);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(lean_object* v_s_1184_, lean_object* v___x_1185_, lean_object* v___x_1186_, lean_object* v_inst_1187_, lean_object* v_R_1188_, lean_object* v_a_1189_, lean_object* v_b_1190_, lean_object* v_c_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1184_, v___x_1185_, v___x_1186_, v_a_1189_, v_b_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___boxed(lean_object* v_s_1193_, lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v_inst_1196_, lean_object* v_R_1197_, lean_object* v_a_1198_, lean_object* v_b_1199_, lean_object* v_c_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(v_s_1193_, v___x_1194_, v___x_1195_, v_inst_1196_, v_R_1197_, v_a_1198_, v_b_1199_, v_c_1200_);
lean_dec(v_b_1199_);
lean_dec(v___x_1195_);
lean_dec_ref(v___x_1194_);
lean_dec_ref(v_s_1193_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(lean_object* v_s_1213_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10));
lean_inc_ref(v_s_1213_);
v___x_1330_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1213_, v___x_1329_);
if (lean_obj_tag(v___x_1330_) == 1)
{
lean_object* v_val_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1344_; 
v_val_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1344_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_val_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1344_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1335_ = lean_string_utf8_byte_size(v_val_1331_);
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = lean_nat_dec_eq(v___x_1335_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
lean_dec_ref(v_s_1213_);
v___x_1338_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1339_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1331_);
lean_dec(v_val_1331_);
v___x_1340_ = lean_string_append(v___x_1338_, v___x_1339_);
lean_dec_ref(v___x_1339_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1340_);
v___x_1342_ = v___x_1333_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
else
{
lean_del_object(v___x_1333_);
lean_dec(v_val_1331_);
goto v___jp_1307_;
}
}
}
else
{
lean_dec(v___x_1330_);
goto v___jp_1307_;
}
v___jp_1214_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0));
v___x_1216_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1213_, v___x_1215_);
if (lean_obj_tag(v___x_1216_) == 1)
{
lean_object* v_val_1217_; lean_object* v___x_1218_; 
v_val_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_val_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v___x_1218_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1217_);
lean_dec(v_val_1217_);
if (lean_obj_tag(v___x_1218_) == 1)
{
lean_object* v_val_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1233_; 
v_val_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1233_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_val_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1233_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_fst_1223_; lean_object* v_snd_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v_fst_1223_ = lean_ctor_get(v_val_1219_, 0);
lean_inc(v_fst_1223_);
v_snd_1224_ = lean_ctor_get(v_val_1219_, 1);
lean_inc(v_snd_1224_);
lean_dec(v_val_1219_);
v___x_1225_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1226_ = lean_string_append(v_fst_1223_, v___x_1225_);
v___x_1227_ = lean_string_append(v___x_1226_, v_snd_1224_);
lean_dec(v_snd_1224_);
v___x_1228_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1229_ = lean_string_append(v___x_1227_, v___x_1228_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1229_);
v___x_1231_ = v___x_1221_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
else
{
lean_object* v___x_1234_; 
lean_dec(v___x_1218_);
v___x_1234_ = lean_box(0);
return v___x_1234_;
}
}
else
{
lean_object* v___x_1235_; 
lean_dec(v___x_1216_);
v___x_1235_ = lean_box(0);
return v___x_1235_;
}
}
v___jp_1236_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3));
lean_inc_ref(v_s_1213_);
v___x_1238_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1213_, v___x_1237_);
if (lean_obj_tag(v___x_1238_) == 1)
{
lean_object* v_val_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1250_; 
v_val_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1250_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_val_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1250_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1243_ = lean_string_utf8_byte_size(v_val_1239_);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_nat_dec_eq(v___x_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
lean_dec_ref(v_s_1213_);
v___x_1246_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1239_);
lean_dec(v_val_1239_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1246_);
v___x_1248_ = v___x_1241_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
else
{
lean_del_object(v___x_1241_);
lean_dec(v_val_1239_);
goto v___jp_1214_;
}
}
}
else
{
lean_dec(v___x_1238_);
goto v___jp_1214_;
}
}
v___jp_1251_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4));
lean_inc_ref(v_s_1213_);
v___x_1253_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1213_, v___x_1252_);
if (lean_obj_tag(v___x_1253_) == 1)
{
lean_object* v_val_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1267_; 
v_val_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1267_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_val_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1267_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1258_ = lean_string_utf8_byte_size(v_val_1254_);
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = lean_nat_dec_eq(v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
lean_dec_ref(v_s_1213_);
v___x_1261_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1262_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1254_);
lean_dec(v_val_1254_);
v___x_1263_ = lean_string_append(v___x_1261_, v___x_1262_);
lean_dec_ref(v___x_1262_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1263_);
v___x_1265_ = v___x_1256_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
else
{
lean_del_object(v___x_1256_);
lean_dec(v_val_1254_);
goto v___jp_1236_;
}
}
}
else
{
lean_dec(v___x_1253_);
goto v___jp_1236_;
}
}
v___jp_1268_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6));
lean_inc_ref(v_s_1213_);
v___x_1270_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1213_, v___x_1269_);
if (lean_obj_tag(v___x_1270_) == 1)
{
lean_object* v_val_1271_; lean_object* v___x_1272_; 
v_val_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_val_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1271_);
lean_dec(v_val_1271_);
if (lean_obj_tag(v___x_1272_) == 1)
{
lean_object* v_val_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1289_; 
lean_dec_ref(v_s_1213_);
v_val_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1289_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_val_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1289_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v_fst_1277_; lean_object* v_snd_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v_fst_1277_ = lean_ctor_get(v_val_1273_, 0);
lean_inc(v_fst_1277_);
v_snd_1278_ = lean_ctor_get(v_val_1273_, 1);
lean_inc(v_snd_1278_);
lean_dec(v_val_1273_);
v___x_1279_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1280_ = lean_string_append(v___x_1279_, v_fst_1277_);
lean_dec(v_fst_1277_);
v___x_1281_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1282_ = lean_string_append(v___x_1280_, v___x_1281_);
v___x_1283_ = lean_string_append(v___x_1282_, v_snd_1278_);
lean_dec(v_snd_1278_);
v___x_1284_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1285_ = lean_string_append(v___x_1283_, v___x_1284_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1285_);
v___x_1287_ = v___x_1275_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
else
{
lean_dec(v___x_1272_);
goto v___jp_1251_;
}
}
else
{
lean_dec(v___x_1270_);
goto v___jp_1251_;
}
}
v___jp_1290_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7));
lean_inc_ref(v_s_1213_);
v___x_1292_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1213_, v___x_1291_);
if (lean_obj_tag(v___x_1292_) == 1)
{
lean_object* v_val_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1306_; 
v_val_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1306_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_val_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1306_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1297_ = lean_string_utf8_byte_size(v_val_1293_);
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_nat_dec_eq(v___x_1297_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
lean_dec_ref(v_s_1213_);
v___x_1300_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1301_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1293_);
lean_dec(v_val_1293_);
v___x_1302_ = lean_string_append(v___x_1300_, v___x_1301_);
lean_dec_ref(v___x_1301_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1302_);
v___x_1304_ = v___x_1295_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
else
{
lean_del_object(v___x_1295_);
lean_dec(v_val_1293_);
goto v___jp_1268_;
}
}
}
else
{
lean_dec(v___x_1292_);
goto v___jp_1268_;
}
}
v___jp_1307_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8));
lean_inc_ref(v_s_1213_);
v___x_1309_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1213_, v___x_1308_);
if (lean_obj_tag(v___x_1309_) == 1)
{
lean_object* v_val_1310_; lean_object* v___x_1311_; 
v_val_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_val_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1311_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1310_);
lean_dec(v_val_1310_);
if (lean_obj_tag(v___x_1311_) == 1)
{
lean_object* v_val_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_s_1213_);
v_val_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1328_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_val_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1328_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v_fst_1316_; lean_object* v_snd_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v_fst_1316_ = lean_ctor_get(v_val_1312_, 0);
lean_inc(v_fst_1316_);
v_snd_1317_ = lean_ctor_get(v_val_1312_, 1);
lean_inc(v_snd_1317_);
lean_dec(v_val_1312_);
v___x_1318_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1319_ = lean_string_append(v___x_1318_, v_fst_1316_);
lean_dec(v_fst_1316_);
v___x_1320_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1321_ = lean_string_append(v___x_1319_, v___x_1320_);
v___x_1322_ = lean_string_append(v___x_1321_, v_snd_1317_);
lean_dec(v_snd_1317_);
v___x_1323_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1324_ = lean_string_append(v___x_1322_, v___x_1323_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1324_);
v___x_1326_ = v___x_1314_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
else
{
lean_dec(v___x_1311_);
goto v___jp_1290_;
}
}
else
{
lean_dec(v___x_1309_);
goto v___jp_1290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleSymbol(lean_object* v_symbol_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1355_ = lean_string_utf8_byte_size(v_symbol_1354_);
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = lean_nat_dec_eq(v___x_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v_fst_1359_; lean_object* v_snd_1360_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1358_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(v_symbol_1354_);
v_fst_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc_n(v_fst_1359_, 2);
v_snd_1360_ = lean_ctor_get(v___x_1358_, 1);
lean_inc(v_snd_1360_);
lean_dec_ref(v___x_1358_);
v___x_1385_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__5));
v___x_1386_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_fst_1359_, v___x_1385_);
if (lean_obj_tag(v___x_1386_) == 1)
{
lean_object* v_val_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1407_; 
v_val_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1407_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_val_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1407_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
uint8_t v___x_1391_; 
lean_inc(v_val_1387_);
v___x_1391_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_1387_);
if (v___x_1391_ == 0)
{
lean_del_object(v___x_1389_);
lean_dec(v_val_1387_);
goto v___jp_1361_;
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v_r_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
lean_dec(v_fst_1359_);
v___x_1392_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__6));
v___x_1393_ = lean_string_append(v___x_1392_, v_val_1387_);
lean_dec(v_val_1387_);
v___x_1394_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__7));
v_r_1395_ = lean_string_append(v___x_1393_, v___x_1394_);
v___x_1396_ = lean_string_utf8_byte_size(v_snd_1360_);
v___x_1397_ = lean_nat_dec_eq(v___x_1396_, v___x_1356_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1398_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1399_ = lean_string_append(v_r_1395_, v___x_1398_);
v___x_1400_ = lean_string_append(v___x_1399_, v_snd_1360_);
lean_dec(v_snd_1360_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1400_);
v___x_1402_ = v___x_1389_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
else
{
lean_object* v___x_1405_; 
lean_dec(v_snd_1360_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v_r_1395_);
v___x_1405_ = v___x_1389_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_r_1395_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
else
{
lean_dec(v___x_1386_);
goto v___jp_1361_;
}
v___jp_1361_:
{
lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__0));
v___x_1363_ = lean_string_dec_eq(v_fst_1359_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
v___x_1364_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(v_fst_1359_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_dec(v_snd_1360_);
return v___x_1364_;
}
else
{
lean_object* v_val_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v_val_1365_ = lean_ctor_get(v___x_1364_, 0);
v___x_1366_ = lean_string_utf8_byte_size(v_snd_1360_);
v___x_1367_ = lean_nat_dec_eq(v___x_1366_, v___x_1356_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1377_; 
lean_inc(v_val_1365_);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v___x_1364_, 0);
lean_dec(v_unused_1378_);
v___x_1369_ = v___x_1364_;
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
else
{
lean_dec(v___x_1364_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1371_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1372_ = lean_string_append(v_val_1365_, v___x_1371_);
v___x_1373_ = lean_string_append(v___x_1372_, v_snd_1360_);
lean_dec(v_snd_1360_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1373_);
v___x_1375_ = v___x_1369_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
else
{
lean_dec(v_snd_1360_);
return v___x_1364_;
}
}
}
else
{
lean_object* v___x_1379_; uint8_t v___x_1380_; 
lean_dec(v_fst_1359_);
v___x_1379_ = lean_string_utf8_byte_size(v_snd_1360_);
v___x_1380_ = lean_nat_dec_eq(v___x_1379_, v___x_1356_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__2));
v___x_1382_ = lean_string_append(v___x_1381_, v_snd_1360_);
lean_dec(v_snd_1360_);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
return v___x_1383_;
}
else
{
lean_object* v___x_1384_; 
lean_dec(v_snd_1360_);
v___x_1384_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__4));
return v___x_1384_;
}
}
}
}
else
{
lean_object* v___x_1408_; 
lean_dec_ref(v_symbol_1354_);
v___x_1408_ = lean_box(0);
return v___x_1408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(lean_object* v_s_1409_, lean_object* v_pos_1410_, lean_object* v_pred_1411_){
_start:
{
lean_object* v___x_1412_; uint8_t v_decide_1413_; 
v___x_1412_ = lean_string_utf8_byte_size(v_s_1409_);
v_decide_1413_ = lean_nat_dec_eq(v_pos_1410_, v___x_1412_);
if (v_decide_1413_ == 0)
{
uint32_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1414_ = lean_string_utf8_get_fast(v_s_1409_, v_pos_1410_);
v___x_1415_ = lean_box_uint32(v___x_1414_);
lean_inc_ref(v_pred_1411_);
v___x_1416_ = lean_apply_1(v_pred_1411_, v___x_1415_);
v___x_1417_ = lean_unbox(v___x_1416_);
if (v___x_1417_ == 0)
{
lean_dec_ref(v_pred_1411_);
return v_pos_1410_;
}
else
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_string_utf8_next_fast(v_s_1409_, v_pos_1410_);
lean_dec(v_pos_1410_);
v_pos_1410_ = v___x_1418_;
goto _start;
}
}
else
{
lean_dec_ref(v_pred_1411_);
return v_pos_1410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile___boxed(lean_object* v_s_1420_, lean_object* v_pos_1421_, lean_object* v_pred_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_s_1420_, v_pos_1421_, v_pred_1422_);
lean_dec_ref(v_s_1420_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(lean_object* v_s_1424_, lean_object* v_p_u2081_1425_, lean_object* v_p_u2082_1426_){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_string_utf8_extract_fast(v_s_1424_, v___x_1427_, v_p_u2081_1425_);
v___x_1429_ = lean_string_utf8_extract_fast(v_s_1424_, v_p_u2081_1425_, v_p_u2082_1426_);
v___x_1430_ = lean_string_utf8_byte_size(v_s_1424_);
v___x_1431_ = lean_string_utf8_extract_fast(v_s_1424_, v_p_u2082_1426_, v___x_1430_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1429_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1428_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082___boxed(lean_object* v_s_1434_, lean_object* v_p_u2081_1435_, lean_object* v_p_u2082_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_s_1434_, v_p_u2081_1435_, v_p_u2082_1436_);
lean_dec(v_p_u2082_1436_);
lean_dec(v_p_u2081_1435_);
lean_dec_ref(v_s_1434_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(lean_object* v___x_1438_, lean_object* v___x_1439_, lean_object* v_line_1440_, lean_object* v_a_1441_, lean_object* v_b_1442_){
_start:
{
lean_object* v___x_1443_; uint8_t v_decide_1444_; 
v___x_1443_ = lean_nat_sub(v___x_1438_, v___x_1439_);
v_decide_1444_ = lean_nat_dec_eq(v_a_1441_, v___x_1443_);
lean_dec(v___x_1443_);
if (v_decide_1444_ == 0)
{
lean_object* v___x_1445_; uint32_t v___x_1446_; uint32_t v___x_1447_; uint8_t v___x_1448_; 
v___x_1445_ = lean_nat_add(v___x_1439_, v_a_1441_);
v___x_1446_ = lean_string_utf8_get_fast(v_line_1440_, v___x_1445_);
v___x_1447_ = 43;
v___x_1448_ = lean_uint32_dec_eq(v___x_1446_, v___x_1447_);
if (v___x_1448_ == 0)
{
uint32_t v___x_1449_; uint8_t v___x_1450_; 
v___x_1449_ = 41;
v___x_1450_ = lean_uint32_dec_eq(v___x_1446_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec(v_a_1441_);
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_string_utf8_next_fast(v_line_1440_, v___x_1445_);
lean_dec(v___x_1445_);
v___x_1453_ = lean_nat_sub(v___x_1452_, v___x_1439_);
v_a_1441_ = v___x_1453_;
v_b_1442_ = v___x_1451_;
goto _start;
}
else
{
lean_object* v___x_1455_; 
lean_dec(v___x_1445_);
v___x_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1455_, 0, v_a_1441_);
return v___x_1455_;
}
}
else
{
lean_object* v___x_1456_; 
lean_dec(v___x_1445_);
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_a_1441_);
return v___x_1456_;
}
}
else
{
lean_dec(v_a_1441_);
lean_inc(v_b_1442_);
return v_b_1442_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg___boxed(lean_object* v___x_1457_, lean_object* v___x_1458_, lean_object* v_line_1459_, lean_object* v_a_1460_, lean_object* v_b_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1457_, v___x_1458_, v_line_1459_, v_a_1460_, v_b_1461_);
lean_dec(v_b_1461_);
lean_dec_ref(v_line_1459_);
lean_dec(v___x_1458_);
lean_dec(v___x_1457_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(lean_object* v___x_1463_, lean_object* v_line_1464_, lean_object* v_a_1465_, lean_object* v_b_1466_){
_start:
{
uint8_t v_decide_1467_; 
v_decide_1467_ = lean_nat_dec_eq(v_a_1465_, v___x_1463_);
if (v_decide_1467_ == 0)
{
uint32_t v___x_1468_; uint32_t v___x_1469_; uint8_t v___x_1470_; 
v___x_1468_ = lean_string_utf8_get_fast(v_line_1464_, v_a_1465_);
v___x_1469_ = 40;
v___x_1470_ = lean_uint32_dec_eq(v___x_1468_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_string_utf8_next_fast(v_line_1464_, v_a_1465_);
lean_dec(v_a_1465_);
v_a_1465_ = v___x_1472_;
v_b_1466_ = v___x_1471_;
goto _start;
}
else
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1474_, 0, v_a_1465_);
return v___x_1474_;
}
}
else
{
lean_dec(v_a_1465_);
lean_inc(v_b_1466_);
return v_b_1466_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg___boxed(lean_object* v___x_1475_, lean_object* v_line_1476_, lean_object* v_a_1477_, lean_object* v_b_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1475_, v_line_1476_, v_a_1477_, v_b_1478_);
lean_dec(v_b_1478_);
lean_dec_ref(v_line_1476_);
lean_dec(v___x_1475_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(lean_object* v_line_1480_){
_start:
{
lean_object* v_searcher_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_searcher_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_string_utf8_byte_size(v_line_1480_);
v___x_1483_ = lean_box(0);
v___x_1484_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1482_, v_line_1480_, v_searcher_1481_, v___x_1483_);
if (lean_obj_tag(v___x_1484_) == 0)
{
return v___x_1483_;
}
else
{
lean_object* v_val_1485_; uint8_t v_decide_1486_; 
v_val_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_val_1485_);
lean_dec_ref_known(v___x_1484_, 1);
v_decide_1486_ = lean_nat_dec_eq(v_val_1485_, v___x_1482_);
if (v_decide_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_string_utf8_next_fast(v_line_1480_, v_val_1485_);
lean_dec(v_val_1485_);
v___x_1488_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1482_, v___x_1487_, v_line_1480_, v_searcher_1481_, v___x_1483_);
if (lean_obj_tag(v___x_1488_) == 0)
{
return v___x_1483_;
}
else
{
lean_object* v_val_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1499_; 
v_val_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1499_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_val_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1499_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; uint8_t v_decide_1494_; 
v___x_1493_ = lean_nat_add(v___x_1487_, v_val_1489_);
lean_dec(v_val_1489_);
v_decide_1494_ = lean_nat_dec_eq(v___x_1493_, v___x_1487_);
if (v_decide_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1480_, v___x_1487_, v___x_1493_);
lean_dec(v___x_1493_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1495_);
v___x_1497_ = v___x_1491_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
else
{
lean_dec(v___x_1493_);
lean_del_object(v___x_1491_);
return v___x_1483_;
}
}
}
}
else
{
lean_dec(v_val_1485_);
return v___x_1483_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux___boxed(lean_object* v_line_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(v_line_1500_);
lean_dec_ref(v_line_1500_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(lean_object* v___x_1502_, lean_object* v___x_1503_, lean_object* v_line_1504_, lean_object* v_inst_1505_, lean_object* v_R_1506_, lean_object* v_a_1507_, lean_object* v_b_1508_, lean_object* v_c_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1502_, v_line_1504_, v_a_1507_, v_b_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___boxed(lean_object* v___x_1511_, lean_object* v___x_1512_, lean_object* v_line_1513_, lean_object* v_inst_1514_, lean_object* v_R_1515_, lean_object* v_a_1516_, lean_object* v_b_1517_, lean_object* v_c_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(v___x_1511_, v___x_1512_, v_line_1513_, v_inst_1514_, v_R_1515_, v_a_1516_, v_b_1517_, v_c_1518_);
lean_dec(v_b_1517_);
lean_dec_ref(v_line_1513_);
lean_dec_ref(v___x_1512_);
lean_dec(v___x_1511_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(lean_object* v___x_1520_, lean_object* v___x_1521_, lean_object* v___x_1522_, lean_object* v_line_1523_, lean_object* v_inst_1524_, lean_object* v_R_1525_, lean_object* v_a_1526_, lean_object* v_b_1527_, lean_object* v_c_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1520_, v___x_1521_, v_line_1523_, v_a_1526_, v_b_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___boxed(lean_object* v___x_1530_, lean_object* v___x_1531_, lean_object* v___x_1532_, lean_object* v_line_1533_, lean_object* v_inst_1534_, lean_object* v_R_1535_, lean_object* v_a_1536_, lean_object* v_b_1537_, lean_object* v_c_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(v___x_1530_, v___x_1531_, v___x_1532_, v_line_1533_, v_inst_1534_, v_R_1535_, v_a_1536_, v_b_1537_, v_c_1538_);
lean_dec(v_b_1537_);
lean_dec_ref(v_line_1533_);
lean_dec_ref(v___x_1532_);
lean_dec(v___x_1531_);
lean_dec(v___x_1530_);
return v_res_1539_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(uint32_t v_x_1540_){
_start:
{
uint32_t v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = 48;
v___x_1552_ = lean_uint32_dec_le(v___x_1551_, v_x_1540_);
if (v___x_1552_ == 0)
{
goto v___jp_1546_;
}
else
{
uint32_t v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = 57;
v___x_1554_ = lean_uint32_dec_le(v_x_1540_, v___x_1553_);
if (v___x_1554_ == 0)
{
goto v___jp_1546_;
}
else
{
return v___x_1554_;
}
}
v___jp_1541_:
{
uint32_t v___x_1542_; uint8_t v___x_1543_; 
v___x_1542_ = 65;
v___x_1543_ = lean_uint32_dec_le(v___x_1542_, v_x_1540_);
if (v___x_1543_ == 0)
{
return v___x_1543_;
}
else
{
uint32_t v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = 70;
v___x_1545_ = lean_uint32_dec_le(v_x_1540_, v___x_1544_);
return v___x_1545_;
}
}
v___jp_1546_:
{
uint32_t v___x_1547_; uint8_t v___x_1548_; 
v___x_1547_ = 97;
v___x_1548_ = lean_uint32_dec_le(v___x_1547_, v_x_1540_);
if (v___x_1548_ == 0)
{
goto v___jp_1541_;
}
else
{
uint32_t v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = 102;
v___x_1550_ = lean_uint32_dec_le(v_x_1540_, v___x_1549_);
if (v___x_1550_ == 0)
{
goto v___jp_1541_;
}
else
{
return v___x_1550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed(lean_object* v_x_1555_){
_start:
{
uint32_t v_x_2757__boxed_1556_; uint8_t v_res_1557_; lean_object* v_r_1558_; 
v_x_2757__boxed_1556_ = lean_unbox_uint32(v_x_1555_);
lean_dec(v_x_1555_);
v_res_1557_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(v_x_2757__boxed_1556_);
v_r_1558_ = lean_box(v_res_1557_);
return v_r_1558_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(uint32_t v_x_1559_){
_start:
{
uint32_t v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = 32;
v___x_1561_ = lean_uint32_dec_eq(v_x_1559_, v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed(lean_object* v_x_1562_){
_start:
{
uint32_t v_x_2788__boxed_1563_; uint8_t v_res_1564_; lean_object* v_r_1565_; 
v_x_2788__boxed_1563_ = lean_unbox_uint32(v_x_1562_);
lean_dec(v_x_1562_);
v_res_1564_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(v_x_2788__boxed_1563_);
v_r_1565_ = lean_box(v_res_1564_);
return v_r_1565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(lean_object* v___x_1566_, lean_object* v_line_1567_, lean_object* v___x_1568_, lean_object* v___x_1569_, lean_object* v_a_1570_, lean_object* v_b_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_box(0);
switch(lean_obj_tag(v_a_1570_))
{
case 0:
{
lean_object* v_pos_1573_; lean_object* v___x_1574_; 
v_pos_1573_ = lean_ctor_get(v_a_1570_, 0);
lean_inc(v_pos_1573_);
lean_dec_ref_known(v_a_1570_, 1);
v___x_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1574_, 0, v_pos_1573_);
return v___x_1574_;
}
case 1:
{
lean_object* v_pos_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1586_; 
v_pos_1575_ = lean_ctor_get(v_a_1570_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_a_1570_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1577_ = v_a_1570_;
v_isShared_1578_ = v_isSharedCheck_1586_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_pos_1575_);
lean_dec(v_a_1570_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1586_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1579_ = lean_nat_add(v___x_1566_, v_pos_1575_);
lean_dec(v_pos_1575_);
v___x_1580_ = lean_string_utf8_next_fast(v_line_1567_, v___x_1579_);
lean_dec(v___x_1579_);
v___x_1581_ = lean_nat_sub(v___x_1580_, v___x_1566_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set_tag(v___x_1577_, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1581_);
v___x_1583_ = v___x_1577_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
v_a_1570_ = v___x_1583_;
v_b_1571_ = v___x_1572_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1587_; lean_object* v_table_1588_; lean_object* v_stackPos_1589_; lean_object* v_needlePos_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1645_; 
v_needle_1587_ = lean_ctor_get(v_a_1570_, 0);
v_table_1588_ = lean_ctor_get(v_a_1570_, 1);
v_stackPos_1589_ = lean_ctor_get(v_a_1570_, 2);
v_needlePos_1590_ = lean_ctor_get(v_a_1570_, 3);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_a_1570_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1592_ = v_a_1570_;
v_isShared_1593_ = v_isSharedCheck_1645_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_needlePos_1590_);
lean_inc(v_stackPos_1589_);
lean_inc(v_table_1588_);
lean_inc(v_needle_1587_);
lean_dec(v_a_1570_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1645_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_str_1594_; lean_object* v_startInclusive_1595_; lean_object* v_endExclusive_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v_str_1594_ = lean_ctor_get(v_needle_1587_, 0);
v_startInclusive_1595_ = lean_ctor_get(v_needle_1587_, 1);
v_endExclusive_1596_ = lean_ctor_get(v_needle_1587_, 2);
v___x_1597_ = lean_nat_sub(v_stackPos_1589_, v_needlePos_1590_);
v___x_1598_ = lean_nat_sub(v_endExclusive_1596_, v_startInclusive_1595_);
v___x_1599_ = lean_nat_add(v___x_1597_, v___x_1598_);
v___x_1600_ = lean_nat_sub(v___x_1569_, v___x_1566_);
v___x_1601_ = lean_nat_dec_le(v___x_1599_, v___x_1600_);
lean_dec(v___x_1599_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
lean_dec(v___x_1598_);
lean_del_object(v___x_1592_);
lean_dec(v_needlePos_1590_);
lean_dec(v_stackPos_1589_);
lean_dec_ref(v_table_1588_);
lean_dec_ref(v_needle_1587_);
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = lean_nat_add(v___x_1597_, v___x_1602_);
lean_dec(v___x_1597_);
v___x_1604_ = lean_nat_dec_le(v___x_1603_, v___x_1600_);
lean_dec(v___x_1600_);
lean_dec(v___x_1603_);
if (v___x_1604_ == 0)
{
lean_inc(v_b_1571_);
return v_b_1571_;
}
else
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_box(3);
v_a_1570_ = v___x_1605_;
v_b_1571_ = v___x_1572_;
goto _start;
}
}
else
{
lean_object* v___x_1607_; uint8_t v_stackByte_1608_; lean_object* v___x_1609_; uint8_t v_patByte_1610_; uint8_t v___x_1611_; 
lean_dec(v___x_1600_);
lean_dec(v___x_1597_);
v___x_1607_ = lean_nat_add(v___x_1566_, v_stackPos_1589_);
v_stackByte_1608_ = lean_string_get_byte_fast(v_line_1567_, v___x_1607_);
v___x_1609_ = lean_nat_add(v_startInclusive_1595_, v_needlePos_1590_);
v_patByte_1610_ = lean_string_get_byte_fast(v_str_1594_, v___x_1609_);
v___x_1611_ = lean_uint8_dec_eq(v_stackByte_1608_, v_patByte_1610_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; uint8_t v_decide_1613_; 
lean_dec(v___x_1598_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v_decide_1613_ = lean_nat_dec_eq(v_needlePos_1590_, v___x_1612_);
if (v_decide_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v_newNeedlePos_1616_; uint8_t v___x_1617_; 
v___x_1614_ = lean_unsigned_to_nat(1u);
v___x_1615_ = lean_nat_sub(v_needlePos_1590_, v___x_1614_);
lean_dec(v_needlePos_1590_);
v_newNeedlePos_1616_ = lean_array_fget_borrowed(v_table_1588_, v___x_1615_);
lean_dec(v___x_1615_);
v___x_1617_ = lean_nat_dec_eq(v_newNeedlePos_1616_, v___x_1612_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1619_; 
lean_inc(v_newNeedlePos_1616_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 3, v_newNeedlePos_1616_);
v___x_1619_ = v___x_1592_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_needle_1587_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_table_1588_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v_stackPos_1589_);
lean_ctor_set(v_reuseFailAlloc_1621_, 3, v_newNeedlePos_1616_);
v___x_1619_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
v_a_1570_ = v___x_1619_;
v_b_1571_ = v___x_1572_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1622_; lean_object* v___x_1624_; 
v_nextStackPos_1622_ = l_String_Slice_posGE___redArg(v___x_1568_, v_stackPos_1589_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 3, v___x_1612_);
lean_ctor_set(v___x_1592_, 2, v_nextStackPos_1622_);
v___x_1624_ = v___x_1592_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_needle_1587_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_table_1588_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_nextStackPos_1622_);
lean_ctor_set(v_reuseFailAlloc_1626_, 3, v___x_1612_);
v___x_1624_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
v_a_1570_ = v___x_1624_;
v_b_1571_ = v___x_1572_;
goto _start;
}
}
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v_nextStackPos_1629_; lean_object* v___x_1631_; 
lean_dec(v_needlePos_1590_);
v___x_1627_ = lean_unsigned_to_nat(1u);
v___x_1628_ = lean_nat_add(v_stackPos_1589_, v___x_1627_);
lean_dec(v_stackPos_1589_);
v_nextStackPos_1629_ = l_String_Slice_posGE___redArg(v___x_1568_, v___x_1628_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 3, v___x_1612_);
lean_ctor_set(v___x_1592_, 2, v_nextStackPos_1629_);
v___x_1631_ = v___x_1592_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_needle_1587_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_table_1588_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_nextStackPos_1629_);
lean_ctor_set(v_reuseFailAlloc_1633_, 3, v___x_1612_);
v___x_1631_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
v_a_1570_ = v___x_1631_;
v_b_1571_ = v___x_1572_;
goto _start;
}
}
}
else
{
lean_object* v___x_1634_; lean_object* v_nextStackPos_1635_; lean_object* v_nextNeedlePos_1636_; uint8_t v_decide_1637_; 
v___x_1634_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1635_ = lean_nat_add(v_stackPos_1589_, v___x_1634_);
lean_dec(v_stackPos_1589_);
v_nextNeedlePos_1636_ = lean_nat_add(v_needlePos_1590_, v___x_1634_);
lean_dec(v_needlePos_1590_);
v_decide_1637_ = lean_nat_dec_eq(v_nextNeedlePos_1636_, v___x_1598_);
lean_dec(v___x_1598_);
if (v_decide_1637_ == 0)
{
lean_object* v___x_1639_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 3, v_nextNeedlePos_1636_);
lean_ctor_set(v___x_1592_, 2, v_nextStackPos_1635_);
v___x_1639_ = v___x_1592_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_needle_1587_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_table_1588_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_nextStackPos_1635_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_nextNeedlePos_1636_);
v___x_1639_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
v_a_1570_ = v___x_1639_;
goto _start;
}
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_del_object(v___x_1592_);
lean_dec_ref(v_table_1588_);
lean_dec_ref(v_needle_1587_);
v___x_1642_ = lean_nat_sub(v_nextStackPos_1635_, v_nextNeedlePos_1636_);
lean_dec(v_nextNeedlePos_1636_);
lean_dec(v_nextStackPos_1635_);
v___x_1643_ = l_String_Slice_pos_x21(v___x_1568_, v___x_1642_);
lean_dec(v___x_1642_);
v___x_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
return v___x_1644_;
}
}
}
}
}
default: 
{
lean_inc(v_b_1571_);
return v_b_1571_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg___boxed(lean_object* v___x_1646_, lean_object* v_line_1647_, lean_object* v___x_1648_, lean_object* v___x_1649_, lean_object* v_a_1650_, lean_object* v_b_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1646_, v_line_1647_, v___x_1648_, v___x_1649_, v_a_1650_, v_b_1651_);
lean_dec(v_b_1651_);
lean_dec(v___x_1649_);
lean_dec_ref(v___x_1648_);
lean_dec_ref(v_line_1647_);
lean_dec(v___x_1646_);
return v_res_1652_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1));
v___x_1659_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1658_);
return v___x_1659_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1660_ = lean_unsigned_to_nat(0u);
v___x_1661_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2);
v___x_1662_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1));
v___x_1663_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
lean_ctor_set(v___x_1663_, 1, v___x_1661_);
lean_ctor_set(v___x_1663_, 2, v___x_1660_);
lean_ctor_set(v___x_1663_, 3, v___x_1660_);
return v___x_1663_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7));
v___x_1672_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1671_);
return v___x_1672_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1673_ = lean_unsigned_to_nat(0u);
v___x_1674_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8);
v___x_1675_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7));
v___x_1676_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
lean_ctor_set(v___x_1676_, 1, v___x_1674_);
lean_ctor_set(v___x_1676_, 2, v___x_1673_);
lean_ctor_set(v___x_1676_, 3, v___x_1673_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(lean_object* v_line_1677_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = lean_string_utf8_byte_size(v_line_1677_);
lean_inc_ref(v_line_1677_);
v___x_1680_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1680_, 0, v_line_1677_);
lean_ctor_set(v___x_1680_, 1, v___x_1678_);
lean_ctor_set(v___x_1680_, 2, v___x_1679_);
v___x_1681_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3);
v___x_1682_ = lean_box(0);
v___x_1683_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_line_1677_, v___x_1680_, v___x_1679_, v___x_1681_, v___x_1682_);
lean_dec_ref_known(v___x_1680_, 3);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_dec_ref(v_line_1677_);
return v___x_1682_;
}
else
{
lean_object* v_val_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1709_; 
v_val_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1709_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_val_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1709_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
uint8_t v_decide_1688_; 
v_decide_1688_ = lean_nat_dec_eq(v_val_1684_, v___x_1679_);
if (v_decide_1688_ == 0)
{
lean_object* v___x_1689_; uint8_t v_decide_1690_; 
v___x_1689_ = lean_string_utf8_next_fast(v_line_1677_, v_val_1684_);
lean_dec(v_val_1684_);
v_decide_1690_ = lean_nat_dec_eq(v___x_1689_, v___x_1679_);
if (v_decide_1690_ == 0)
{
lean_object* v___f_1691_; lean_object* v___f_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___y_1697_; uint8_t v_decide_1703_; 
v___f_1691_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4));
v___f_1692_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5));
v___x_1693_ = lean_string_utf8_next_fast(v_line_1677_, v___x_1689_);
v___x_1694_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1677_, v___x_1693_, v___f_1691_);
v___x_1695_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1677_, v___x_1694_, v___f_1692_);
v_decide_1703_ = lean_nat_dec_eq(v___x_1695_, v___x_1679_);
if (v_decide_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_inc(v___x_1695_);
lean_inc_ref(v_line_1677_);
v___x_1704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1704_, 0, v_line_1677_);
lean_ctor_set(v___x_1704_, 1, v___x_1695_);
lean_ctor_set(v___x_1704_, 2, v___x_1679_);
v___x_1705_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
v___x_1706_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1695_, v_line_1677_, v___x_1704_, v___x_1679_, v___x_1705_, v___x_1682_);
lean_dec_ref_known(v___x_1704_, 3);
if (lean_obj_tag(v___x_1706_) == 0)
{
v___y_1697_ = v___x_1679_;
goto v___jp_1696_;
}
else
{
lean_object* v_val_1707_; lean_object* v___x_1708_; 
v_val_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_val_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v___x_1708_ = lean_nat_add(v___x_1695_, v_val_1707_);
lean_dec(v_val_1707_);
v___y_1697_ = v___x_1708_;
goto v___jp_1696_;
}
}
else
{
lean_dec(v___x_1695_);
lean_del_object(v___x_1686_);
lean_dec_ref(v_line_1677_);
return v___x_1682_;
}
v___jp_1696_:
{
uint8_t v_decide_1698_; 
v_decide_1698_ = lean_nat_dec_eq(v___y_1697_, v___x_1695_);
if (v_decide_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1677_, v___x_1695_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec(v___x_1695_);
lean_dec_ref(v_line_1677_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1699_);
v___x_1701_ = v___x_1686_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
else
{
lean_dec(v___y_1697_);
lean_dec(v___x_1695_);
lean_del_object(v___x_1686_);
lean_dec_ref(v_line_1677_);
return v___x_1682_;
}
}
}
else
{
lean_del_object(v___x_1686_);
lean_dec_ref(v_line_1677_);
return v___x_1682_;
}
}
else
{
lean_del_object(v___x_1686_);
lean_dec(v_val_1684_);
lean_dec_ref(v_line_1677_);
return v___x_1682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(lean_object* v___x_1710_, lean_object* v_line_1711_, lean_object* v___x_1712_, lean_object* v___x_1713_, lean_object* v_inst_1714_, lean_object* v_R_1715_, lean_object* v_a_1716_, lean_object* v_b_1717_, lean_object* v_c_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1710_, v_line_1711_, v___x_1712_, v___x_1713_, v_a_1716_, v_b_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___boxed(lean_object* v___x_1720_, lean_object* v_line_1721_, lean_object* v___x_1722_, lean_object* v___x_1723_, lean_object* v_inst_1724_, lean_object* v_R_1725_, lean_object* v_a_1726_, lean_object* v_b_1727_, lean_object* v_c_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(v___x_1720_, v_line_1721_, v___x_1722_, v___x_1723_, v_inst_1724_, v_R_1725_, v_a_1726_, v_b_1727_, v_c_1728_);
lean_dec(v_b_1727_);
lean_dec(v___x_1723_);
lean_dec_ref(v___x_1722_);
lean_dec_ref(v_line_1721_);
lean_dec(v___x_1720_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(lean_object* v_line_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(v_line_1730_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v___x_1732_; 
v___x_1732_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(v_line_1730_);
return v___x_1732_;
}
else
{
lean_dec_ref(v_line_1730_);
return v___x_1731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleBtLine(lean_object* v_line_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(v_line_1733_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_box(0);
return v___x_1735_;
}
else
{
lean_object* v_val_1736_; lean_object* v_snd_1737_; lean_object* v_fst_1738_; lean_object* v_fst_1739_; lean_object* v_snd_1740_; lean_object* v___x_1741_; 
v_val_1736_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_val_1736_);
lean_dec_ref_known(v___x_1734_, 1);
v_snd_1737_ = lean_ctor_get(v_val_1736_, 1);
lean_inc(v_snd_1737_);
v_fst_1738_ = lean_ctor_get(v_val_1736_, 0);
lean_inc(v_fst_1738_);
lean_dec(v_val_1736_);
v_fst_1739_ = lean_ctor_get(v_snd_1737_, 0);
lean_inc(v_fst_1739_);
v_snd_1740_ = lean_ctor_get(v_snd_1737_, 1);
lean_inc(v_snd_1740_);
lean_dec(v_snd_1737_);
v___x_1741_ = l_Lean_Name_Demangle_demangleSymbol(v_fst_1739_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_dec(v_snd_1740_);
lean_dec(v_fst_1738_);
return v___x_1741_;
}
else
{
lean_object* v_val_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1751_; 
v_val_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1751_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_val_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1751_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1746_ = lean_string_append(v_fst_1738_, v_val_1742_);
lean_dec(v_val_1742_);
v___x_1747_ = lean_string_append(v___x_1746_, v_snd_1740_);
lean_dec(v_snd_1740_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1747_);
v___x_1749_ = v___x_1744_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_demangle_bt_line_cstr(lean_object* v_line_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_Name_Demangle_demangleBtLine(v_line_1752_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_1754_;
}
else
{
lean_object* v_val_1755_; 
v_val_1755_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_val_1755_);
lean_dec_ref_known(v___x_1753_, 1);
return v_val_1755_;
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
