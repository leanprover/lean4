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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_instBEqNamePart_beq(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(lean_object* v_x_222_, lean_object* v_x_223_){
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
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0___boxed(lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v_x_230_, v_x_231_);
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
v___x_260_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_258_, v___x_259_);
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
v___x_298_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_296_, v___x_297_);
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
v___x_367_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_365_, v___x_366_);
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
v___x_482_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_480_, v___x_481_);
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
lean_inc_ref(v_name_560_);
v_flags_561_ = lean_ctor_get(v___x_557_, 1);
lean_inc_ref(v_flags_561_);
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = lean_string_utf8_byte_size(v_name_560_);
lean_dec_ref(v_name_560_);
v___x_564_ = lean_nat_dec_eq(v___x_563_, v___x_562_);
if (v___x_564_ == 0)
{
lean_dec_ref(v_flags_561_);
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
lean_dec_ref(v_flags_561_);
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
lean_dec_ref(v_flags_561_);
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
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0));
v___x_578_ = lean_string_utf8_byte_size(v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(lean_object* v_range_579_, lean_object* v_b_580_, lean_object* v_i_581_){
_start:
{
lean_object* v_stop_582_; lean_object* v_step_583_; lean_object* v_a_585_; uint8_t v___x_588_; 
v_stop_582_ = lean_ctor_get(v_range_579_, 1);
v_step_583_ = lean_ctor_get(v_range_579_, 2);
v___x_588_ = lean_nat_dec_lt(v_i_581_, v_stop_582_);
if (v___x_588_ == 0)
{
lean_dec(v_i_581_);
lean_inc_ref(v_b_580_);
return v_b_580_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = l_Lean_instInhabitedNamePart_default;
v___x_590_ = lean_array_get_borrowed(v___x_589_, v_b_580_, v_i_581_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_s_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_s_591_ = lean_ctor_get(v___x_590_, 0);
v___x_592_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0));
v___x_593_ = lean_string_utf8_byte_size(v_s_591_);
v___x_594_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1);
v___x_595_ = lean_nat_dec_le(v___x_594_, v___x_593_);
if (v___x_595_ == 0)
{
v_a_585_ = v_b_580_;
goto v___jp_584_;
}
else
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_string_memcmp(v_s_591_, v___x_592_, v___x_596_, v___x_596_, v___x_594_);
if (v___x_597_ == 0)
{
v_a_585_ = v_b_580_;
goto v___jp_584_;
}
else
{
lean_object* v___x_598_; 
v___x_598_ = l_Array_extract___redArg(v_b_580_, v___x_596_, v_i_581_);
return v___x_598_;
}
}
}
else
{
v_a_585_ = v_b_580_;
goto v___jp_584_;
}
}
v___jp_584_:
{
lean_object* v___x_586_; 
v___x_586_ = lean_nat_add(v_i_581_, v_step_583_);
lean_dec(v_i_581_);
v_b_580_ = v_a_585_;
v_i_581_ = v___x_586_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___boxed(lean_object* v_range_599_, lean_object* v_b_600_, lean_object* v_i_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v_range_599_, v_b_600_, v_i_601_);
lean_dec_ref(v_b_600_);
lean_dec_ref(v_range_599_);
return v_res_602_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0));
v___x_607_ = lean_string_utf8_byte_size(v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v_range_612_, lean_object* v_b_613_, lean_object* v_i_614_){
_start:
{
lean_object* v_stop_615_; lean_object* v_step_616_; lean_object* v_a_618_; uint8_t v___x_621_; 
v_stop_615_ = lean_ctor_get(v_range_612_, 1);
v_step_616_ = lean_ctor_get(v_range_612_, 2);
v___x_621_ = lean_nat_dec_lt(v_i_614_, v_stop_615_);
if (v___x_621_ == 0)
{
lean_dec(v_i_614_);
return v_b_613_;
}
else
{
lean_object* v_snd_622_; lean_object* v_snd_623_; lean_object* v_fst_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_720_; 
v_snd_622_ = lean_ctor_get(v_b_613_, 1);
lean_inc(v_snd_622_);
v_snd_623_ = lean_ctor_get(v_snd_622_, 1);
lean_inc(v_snd_623_);
v_fst_624_ = lean_ctor_get(v_b_613_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v_b_613_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v_b_613_, 1);
lean_dec(v_unused_721_);
v___x_626_ = v_b_613_;
v_isShared_627_ = v_isSharedCheck_720_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_fst_624_);
lean_dec(v_b_613_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_720_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_fst_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_718_; 
v_fst_628_ = lean_ctor_get(v_snd_622_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v_snd_622_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v_snd_622_, 1);
lean_dec(v_unused_719_);
v___x_630_ = v_snd_622_;
v_isShared_631_ = v_isSharedCheck_718_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_fst_628_);
lean_dec(v_snd_622_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_718_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_fst_632_; lean_object* v_snd_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_717_; 
v_fst_632_ = lean_ctor_get(v_snd_623_, 0);
v_snd_633_ = lean_ctor_get(v_snd_623_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_snd_623_);
if (v_isSharedCheck_717_ == 0)
{
v___x_635_ = v_snd_623_;
v_isShared_636_ = v_isSharedCheck_717_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_snd_633_);
lean_inc(v_fst_632_);
lean_dec(v_snd_623_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_717_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_unbox(v_snd_633_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_639_ = l_Lean_instInhabitedNamePart_default;
v___x_640_ = lean_array_get_borrowed(v___x_639_, v___x_610_, v_i_614_);
v___x_670_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1));
v___x_671_ = l_Lean_instBEqNamePart_beq(v___x_640_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v_cont_675_; lean_object* v_entries_677_; lean_object* v_currentCtx_678_; 
v___x_672_ = lean_box(0);
v___x_673_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0));
v___x_674_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1));
v_cont_675_ = l_Lean_instBEqNamePart_beq(v___x_640_, v___x_674_);
if (v_cont_675_ == 0)
{
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_s_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_s_683_ = lean_ctor_get(v___x_640_, 0);
v___x_684_ = lean_string_utf8_byte_size(v_s_683_);
v___x_685_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2);
v___x_686_ = lean_nat_dec_le(v___x_685_, v___x_684_);
if (v___x_686_ == 0)
{
goto v___jp_641_;
}
else
{
uint8_t v___x_687_; 
v___x_687_ = lean_string_memcmp(v_s_683_, v___x_673_, v___x_637_, v___x_637_, v___x_685_);
if (v___x_687_ == 0)
{
goto v___jp_641_;
}
else
{
lean_del_object(v___x_635_);
lean_del_object(v___x_630_);
lean_del_object(v___x_626_);
if (lean_obj_tag(v_fst_628_) == 1)
{
lean_object* v_val_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_val_688_ = lean_ctor_get(v_fst_628_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v_fst_628_, 1);
v___x_689_ = lean_array_push(v_fst_624_, v_val_688_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_fst_632_);
lean_ctor_set(v___x_690_, 1, v_snd_633_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_672_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_689_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v_a_618_ = v___x_692_;
goto v___jp_617_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_fst_632_);
lean_ctor_set(v___x_693_, 1, v_snd_633_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_fst_628_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v_fst_624_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v_a_618_ = v___x_695_;
goto v___jp_617_;
}
}
}
}
else
{
goto v___jp_641_;
}
}
else
{
lean_del_object(v___x_635_);
lean_dec(v_snd_633_);
lean_del_object(v___x_630_);
lean_del_object(v___x_626_);
if (lean_obj_tag(v_fst_628_) == 1)
{
lean_object* v_val_696_; lean_object* v___x_697_; 
v_val_696_ = lean_ctor_get(v_fst_628_, 0);
lean_inc(v_val_696_);
lean_dec_ref_known(v_fst_628_, 1);
v___x_697_ = lean_array_push(v_fst_624_, v_val_696_);
v_entries_677_ = v___x_697_;
v_currentCtx_678_ = v___x_672_;
goto v___jp_676_;
}
else
{
v_entries_677_ = v_fst_624_;
v_currentCtx_678_ = v_fst_628_;
goto v___jp_676_;
}
}
v___jp_676_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_679_ = lean_box(v_cont_675_);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v_fst_632_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_currentCtx_678_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v_entries_677_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v_a_618_ = v___x_682_;
goto v___jp_617_;
}
}
else
{
lean_object* v_entries_699_; 
lean_del_object(v___x_635_);
lean_del_object(v___x_630_);
lean_del_object(v___x_626_);
if (lean_obj_tag(v_fst_628_) == 1)
{
lean_object* v_val_704_; lean_object* v___x_705_; 
v_val_704_ = lean_ctor_get(v_fst_628_, 0);
lean_inc(v_val_704_);
lean_dec_ref_known(v_fst_628_, 1);
v___x_705_ = lean_array_push(v_fst_624_, v_val_704_);
v_entries_699_ = v___x_705_;
goto v___jp_698_;
}
else
{
lean_dec(v_fst_628_);
v_entries_699_ = v_fst_624_;
goto v___jp_698_;
}
v___jp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_700_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__3));
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_fst_632_);
lean_ctor_set(v___x_701_, 1, v_snd_633_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_entries_699_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v_a_618_ = v___x_703_;
goto v___jp_617_;
}
}
v___jp_641_:
{
if (lean_obj_tag(v_fst_628_) == 0)
{
lean_object* v___x_642_; lean_object* v___x_644_; 
lean_inc(v___x_640_);
v___x_642_ = lean_array_push(v_fst_632_, v___x_640_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_642_);
v___x_644_ = v___x_635_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_snd_633_);
v___x_644_ = v_reuseFailAlloc_651_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_646_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_644_);
v___x_646_ = v___x_630_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_fst_628_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_644_);
v___x_646_ = v_reuseFailAlloc_650_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_648_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_646_);
v___x_648_ = v___x_626_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_fst_624_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
v_a_618_ = v___x_648_;
goto v___jp_617_;
}
}
}
}
else
{
lean_object* v_val_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_669_; 
v_val_652_ = lean_ctor_get(v_fst_628_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v_fst_628_);
if (v_isSharedCheck_669_ == 0)
{
v___x_654_ = v_fst_628_;
v_isShared_655_ = v_isSharedCheck_669_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_val_652_);
lean_dec(v_fst_628_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_669_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
lean_inc(v___x_640_);
v___x_656_ = lean_array_push(v_val_652_, v___x_640_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_668_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_660_; 
if (v_isShared_636_ == 0)
{
v___x_660_ = v___x_635_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_fst_632_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_snd_633_);
v___x_660_ = v_reuseFailAlloc_667_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_662_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_660_);
lean_ctor_set(v___x_630_, 0, v___x_658_);
v___x_662_ = v___x_630_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___x_660_);
v___x_662_ = v_reuseFailAlloc_666_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_664_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_662_);
v___x_664_ = v___x_626_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_fst_624_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
v_a_618_ = v___x_664_;
goto v___jp_617_;
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
uint8_t v_skipNext_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
lean_dec(v_snd_633_);
v_skipNext_706_ = lean_nat_dec_eq(v___x_611_, v___x_637_);
v___x_707_ = lean_box(v_skipNext_706_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v___x_707_);
v___x_709_ = v___x_635_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_fst_632_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v___x_707_);
v___x_709_ = v_reuseFailAlloc_716_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_709_);
v___x_711_ = v___x_630_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_fst_628_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_709_);
v___x_711_ = v_reuseFailAlloc_715_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_711_);
v___x_713_ = v___x_626_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_fst_624_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
v_a_618_ = v___x_713_;
goto v___jp_617_;
}
}
}
}
}
}
}
}
v___jp_617_:
{
lean_object* v___x_619_; 
v___x_619_ = lean_nat_add(v_i_614_, v_step_616_);
lean_dec(v_i_614_);
v_b_613_ = v_a_618_;
v_i_614_ = v___x_619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___boxed(lean_object* v___x_722_, lean_object* v___x_723_, lean_object* v_range_724_, lean_object* v_b_725_, lean_object* v_i_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_722_, v___x_723_, v_range_724_, v_b_725_, v_i_726_);
lean_dec_ref(v_range_724_);
lean_dec(v___x_723_);
lean_dec_ref(v___x_722_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(lean_object* v___x_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_snd_730_; lean_object* v_fst_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_788_; 
v_snd_730_ = lean_ctor_get(v_a_729_, 1);
v_fst_731_ = lean_ctor_get(v_a_729_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_a_729_);
if (v_isSharedCheck_788_ == 0)
{
v___x_733_ = v_a_729_;
v_isShared_734_ = v_isSharedCheck_788_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_snd_730_);
lean_inc(v_fst_731_);
lean_dec(v_a_729_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_788_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_fst_735_; lean_object* v_snd_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_787_; 
v_fst_735_ = lean_ctor_get(v_snd_730_, 0);
v_snd_736_ = lean_ctor_get(v_snd_730_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_snd_730_);
if (v_isSharedCheck_787_ == 0)
{
v___x_738_ = v_snd_730_;
v_isShared_739_ = v_isSharedCheck_787_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_snd_736_);
lean_inc(v_fst_735_);
lean_dec(v_snd_730_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_787_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
uint8_t v___x_747_; 
v___x_747_ = lean_unbox(v_snd_736_);
if (v___x_747_ == 0)
{
goto v___jp_740_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_array_get_size(v_fst_731_);
v___x_750_ = lean_nat_dec_eq(v___x_749_, v___x_748_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_del_object(v___x_738_);
lean_del_object(v___x_733_);
v___x_751_ = l_Lean_instInhabitedNamePart_default;
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_sub(v___x_749_, v___x_752_);
v___x_754_ = lean_array_get_borrowed(v___x_751_, v_fst_731_, v___x_753_);
lean_dec(v___x_753_);
lean_inc(v___x_754_);
v___x_755_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_754_);
if (lean_obj_tag(v___x_755_) == 0)
{
uint8_t v_skipNext_756_; 
v_skipNext_756_ = lean_nat_dec_eq(v___x_728_, v___x_748_);
if (lean_obj_tag(v___x_754_) == 1)
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(2u);
v___x_758_ = lean_nat_dec_le(v___x_757_, v___x_749_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec(v_snd_736_);
v___x_759_ = lean_box(v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v_fst_735_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v_fst_731_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v_a_729_ = v___x_761_;
goto _start;
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_nat_sub(v___x_749_, v___x_757_);
v___x_764_ = lean_array_get_borrowed(v___x_751_, v_fst_731_, v___x_763_);
lean_dec(v___x_763_);
lean_inc(v___x_764_);
v___x_765_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_764_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec(v_snd_736_);
v___x_766_ = lean_box(v_skipNext_756_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_fst_735_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v_fst_731_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v_a_729_ = v___x_768_;
goto _start;
}
else
{
lean_object* v_val_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_val_770_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v___x_765_, 1);
v___x_771_ = lean_array_push(v_fst_735_, v_val_770_);
v___x_772_ = lean_array_pop(v_fst_731_);
v___x_773_ = lean_array_pop(v___x_772_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_771_);
lean_ctor_set(v___x_774_, 1, v_snd_736_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v_a_729_ = v___x_775_;
goto _start;
}
}
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec(v_snd_736_);
v___x_777_ = lean_box(v_skipNext_756_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v_fst_735_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v_fst_731_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v_a_729_ = v___x_779_;
goto _start;
}
}
else
{
lean_object* v_val_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_val_781_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_val_781_);
lean_dec_ref_known(v___x_755_, 1);
v___x_782_ = lean_array_push(v_fst_735_, v_val_781_);
v___x_783_ = lean_array_pop(v_fst_731_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v_snd_736_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v_a_729_ = v___x_785_;
goto _start;
}
}
else
{
goto v___jp_740_;
}
}
v___jp_740_:
{
lean_object* v___x_742_; 
if (v_isShared_739_ == 0)
{
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_fst_735_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_snd_736_);
v___x_742_ = v_reuseFailAlloc_746_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_744_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v___x_742_);
v___x_744_ = v___x_733_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_fst_731_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg___boxed(lean_object* v___x_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_789_, v_a_790_);
lean_dec(v___x_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(lean_object* v_as_797_, size_t v_sz_798_, size_t v_i_799_, lean_object* v_b_800_){
_start:
{
lean_object* v_a_802_; uint8_t v___x_806_; 
v___x_806_ = lean_usize_dec_lt(v_i_799_, v_sz_798_);
if (v___x_806_ == 0)
{
return v_b_800_;
}
else
{
lean_object* v_a_807_; lean_object* v___y_809_; lean_object* v_name_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v_a_807_ = lean_array_uget_borrowed(v_as_797_, v_i_799_);
v_name_828_ = lean_ctor_get(v_a_807_, 0);
v___x_829_ = lean_string_utf8_byte_size(v_name_828_);
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = lean_nat_dec_eq(v___x_829_, v___x_830_);
if (v___x_831_ == 0)
{
lean_inc_ref(v_name_828_);
v___y_809_ = v_name_828_;
goto v___jp_808_;
}
else
{
lean_object* v___x_832_; 
v___x_832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_809_ = v___x_832_;
goto v___jp_808_;
}
v___jp_808_:
{
lean_object* v_flags_810_; lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v_flags_810_ = lean_ctor_get(v_a_807_, 1);
v___x_811_ = lean_array_get_size(v_flags_810_);
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = lean_nat_dec_eq(v___x_811_, v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_815_ = lean_string_append(v_b_800_, v___x_814_);
v___x_816_ = lean_string_append(v___x_815_, v___y_809_);
lean_dec_ref(v___y_809_);
v___x_817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1));
v___x_818_ = lean_string_append(v___x_816_, v___x_817_);
v___x_819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
lean_inc_ref(v_flags_810_);
v___x_820_ = lean_array_to_list(v_flags_810_);
v___x_821_ = l_String_intercalate(v___x_819_, v___x_820_);
v___x_822_ = lean_string_append(v___x_818_, v___x_821_);
lean_dec_ref(v___x_821_);
v___x_823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_824_ = lean_string_append(v___x_822_, v___x_823_);
v_a_802_ = v___x_824_;
goto v___jp_801_;
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_826_ = lean_string_append(v_b_800_, v___x_825_);
v___x_827_ = lean_string_append(v___x_826_, v___y_809_);
lean_dec_ref(v___y_809_);
v_a_802_ = v___x_827_;
goto v___jp_801_;
}
}
}
v___jp_801_:
{
size_t v___x_803_; size_t v___x_804_; 
v___x_803_ = ((size_t)1ULL);
v___x_804_ = lean_usize_add(v_i_799_, v___x_803_);
v_i_799_ = v___x_804_;
v_b_800_ = v_a_802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___boxed(lean_object* v_as_833_, lean_object* v_sz_834_, lean_object* v_i_835_, lean_object* v_b_836_){
_start:
{
size_t v_sz_boxed_837_; size_t v_i_boxed_838_; lean_object* v_res_839_; 
v_sz_boxed_837_ = lean_unbox_usize(v_sz_834_);
lean_dec(v_sz_834_);
v_i_boxed_838_ = lean_unbox_usize(v_i_835_);
lean_dec(v_i_835_);
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v_as_833_, v_sz_boxed_837_, v_i_boxed_838_, v_b_836_);
lean_dec_ref(v_as_833_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(lean_object* v_components_848_){
_start:
{
lean_object* v___y_850_; lean_object* v_result_851_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_872_; lean_object* v_parts_873_; lean_object* v_specEntries_874_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v_entries_884_; uint8_t v_skipNext_889_; 
v___x_855_ = lean_array_get_size(v_components_848_);
v___x_856_ = lean_unsigned_to_nat(0u);
v_skipNext_889_ = lean_nat_dec_eq(v___x_855_, v___x_856_);
if (v_skipNext_889_ == 0)
{
lean_object* v___x_890_; lean_object* v_fst_891_; lean_object* v_snd_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_947_; 
v___x_890_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_components_848_, v___x_856_, v___x_855_);
v_fst_891_ = lean_ctor_get(v___x_890_, 0);
v_snd_892_ = lean_ctor_get(v___x_890_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_947_ == 0)
{
v___x_894_ = v___x_890_;
v_isShared_895_ = v_isSharedCheck_947_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_snd_892_);
lean_inc(v_fst_891_);
lean_dec(v___x_890_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_947_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_parts_896_; lean_object* v_flags_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v_parts_896_ = l_Array_extract___redArg(v_components_848_, v_fst_891_, v___x_855_);
v_flags_897_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1));
v___x_898_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2));
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v___x_898_);
lean_ctor_set(v___x_894_, 0, v_parts_896_);
v___x_900_ = v___x_894_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_parts_896_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_898_);
v___x_900_ = v_reuseFailAlloc_946_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; lean_object* v_fst_902_; lean_object* v_snd_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_945_; 
v___x_901_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_855_, v___x_900_);
v_fst_902_ = lean_ctor_get(v___x_901_, 0);
v_snd_903_ = lean_ctor_get(v___x_901_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_945_ == 0)
{
v___x_905_ = v___x_901_;
v_isShared_906_ = v_isSharedCheck_945_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_snd_903_);
lean_inc(v_fst_902_);
lean_dec(v___x_901_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_945_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v_flags_908_; uint8_t v___x_940_; 
v___x_940_ = lean_unbox(v_snd_892_);
lean_dec(v_snd_892_);
if (v___x_940_ == 0)
{
lean_object* v_fst_941_; 
v_fst_941_ = lean_ctor_get(v_snd_903_, 0);
lean_inc(v_fst_941_);
lean_dec(v_snd_903_);
v_flags_908_ = v_fst_941_;
goto v___jp_907_;
}
else
{
lean_object* v_fst_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_fst_942_ = lean_ctor_get(v_snd_903_, 0);
lean_inc(v_fst_942_);
lean_dec(v_snd_903_);
v___x_943_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3));
v___x_944_ = lean_array_push(v_fst_942_, v___x_943_);
v_flags_908_ = v___x_944_;
goto v___jp_907_;
}
v___jp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_909_ = lean_array_get_size(v_fst_902_);
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_911_, 0, v___x_856_);
lean_ctor_set(v___x_911_, 1, v___x_909_);
lean_ctor_set(v___x_911_, 2, v___x_910_);
v___x_912_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_911_, v_fst_902_, v___x_856_);
lean_dec(v_fst_902_);
lean_dec_ref_known(v___x_911_, 3);
v___x_913_ = lean_box(0);
v___x_914_ = lean_array_get_size(v___x_912_);
v___x_915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_915_, 0, v___x_856_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
lean_ctor_set(v___x_915_, 2, v___x_910_);
v___x_916_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_912_, v___x_915_, v___x_913_, v___x_856_);
lean_dec_ref_known(v___x_915_, 3);
if (lean_obj_tag(v___x_916_) == 1)
{
lean_object* v_val_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v_val_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc_n(v_val_917_, 2);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = l_Array_extract___redArg(v___x_912_, v___x_856_, v_val_917_);
v___x_919_ = l_Array_extract___redArg(v___x_912_, v_val_917_, v___x_914_);
lean_dec_ref(v___x_912_);
v___x_920_ = lean_array_get_size(v___x_919_);
v___x_921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_921_, 0, v___x_856_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
lean_ctor_set(v___x_921_, 2, v___x_910_);
v___x_922_ = lean_box(v_skipNext_889_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 1, v___x_922_);
lean_ctor_set(v___x_905_, 0, v_flags_897_);
v___x_924_ = v___x_905_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_flags_897_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v___x_922_);
v___x_924_ = v_reuseFailAlloc_939_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_snd_928_; lean_object* v_snd_929_; lean_object* v_fst_930_; 
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_913_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_flags_897_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_919_, v___x_855_, v___x_921_, v___x_926_, v___x_856_);
lean_dec_ref_known(v___x_921_, 3);
lean_dec_ref(v___x_919_);
v_snd_928_ = lean_ctor_get(v___x_927_, 1);
lean_inc(v_snd_928_);
v_snd_929_ = lean_ctor_get(v_snd_928_, 1);
lean_inc(v_snd_929_);
v_fst_930_ = lean_ctor_get(v_snd_928_, 0);
lean_inc(v_fst_930_);
lean_dec(v_snd_928_);
if (lean_obj_tag(v_fst_930_) == 1)
{
lean_object* v_fst_931_; lean_object* v_fst_932_; lean_object* v_val_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_fst_931_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_fst_931_);
lean_dec_ref(v___x_927_);
v_fst_932_ = lean_ctor_get(v_snd_929_, 0);
lean_inc(v_fst_932_);
lean_dec(v_snd_929_);
v_val_933_ = lean_ctor_get(v_fst_930_, 0);
lean_inc(v_val_933_);
lean_dec_ref_known(v_fst_930_, 1);
v___x_934_ = lean_array_get_size(v_val_933_);
v___x_935_ = lean_nat_dec_eq(v___x_934_, v___x_856_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
v___x_936_ = lean_array_push(v_fst_931_, v_val_933_);
v___y_880_ = v___x_918_;
v___y_881_ = v_flags_897_;
v___y_882_ = v_flags_908_;
v___y_883_ = v_fst_932_;
v_entries_884_ = v___x_936_;
goto v___jp_879_;
}
else
{
lean_dec(v_val_933_);
v___y_880_ = v___x_918_;
v___y_881_ = v_flags_897_;
v___y_882_ = v_flags_908_;
v___y_883_ = v_fst_932_;
v_entries_884_ = v_fst_931_;
goto v___jp_879_;
}
}
else
{
lean_object* v_fst_937_; lean_object* v_fst_938_; 
lean_dec(v_fst_930_);
v_fst_937_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_fst_937_);
lean_dec_ref(v___x_927_);
v_fst_938_ = lean_ctor_get(v_snd_929_, 0);
lean_inc(v_fst_938_);
lean_dec(v_snd_929_);
v___y_880_ = v___x_918_;
v___y_881_ = v_flags_897_;
v___y_882_ = v_flags_908_;
v___y_883_ = v_fst_938_;
v_entries_884_ = v_fst_937_;
goto v___jp_879_;
}
}
}
else
{
lean_dec(v___x_916_);
lean_del_object(v___x_905_);
v___y_872_ = v_flags_908_;
v_parts_873_ = v___x_912_;
v_specEntries_874_ = v_flags_897_;
goto v___jp_871_;
}
}
}
}
}
}
else
{
lean_object* v___x_948_; 
v___x_948_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_948_;
}
v___jp_849_:
{
size_t v_sz_852_; size_t v___x_853_; lean_object* v___x_854_; 
v_sz_852_ = lean_array_size(v___y_850_);
v___x_853_ = ((size_t)0ULL);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v___y_850_, v_sz_852_, v___x_853_, v_result_851_);
lean_dec_ref(v___y_850_);
return v___x_854_;
}
v___jp_857_:
{
lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_861_ = lean_array_get_size(v___y_858_);
v___x_862_ = lean_nat_dec_eq(v___x_861_, v___x_856_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_863_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0));
v___x_864_ = lean_string_append(v___y_860_, v___x_863_);
v___x_865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
v___x_866_ = lean_array_to_list(v___y_858_);
v___x_867_ = l_String_intercalate(v___x_865_, v___x_866_);
v___x_868_ = lean_string_append(v___x_864_, v___x_867_);
lean_dec_ref(v___x_867_);
v___x_869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_870_ = lean_string_append(v___x_868_, v___x_869_);
v___y_850_ = v___y_859_;
v_result_851_ = v___x_870_;
goto v___jp_849_;
}
else
{
lean_dec_ref(v___y_858_);
v___y_850_ = v___y_859_;
v_result_851_ = v___y_860_;
goto v___jp_849_;
}
}
v___jp_871_:
{
lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = lean_array_get_size(v_parts_873_);
v___x_876_ = lean_nat_dec_eq(v___x_875_, v___x_856_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; 
v___x_877_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_parts_873_);
lean_dec_ref(v_parts_873_);
v___y_858_ = v___y_872_;
v___y_859_ = v_specEntries_874_;
v___y_860_ = v___x_877_;
goto v___jp_857_;
}
else
{
lean_object* v___x_878_; 
lean_dec_ref(v_parts_873_);
v___x_878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_858_ = v___y_872_;
v___y_859_ = v_specEntries_874_;
v___y_860_ = v___x_878_;
goto v___jp_857_;
}
}
v___jp_879_:
{
size_t v_sz_885_; size_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_sz_885_ = lean_array_size(v_entries_884_);
v___x_886_ = ((size_t)0ULL);
v___x_887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_855_, v_entries_884_, v_sz_885_, v___x_886_, v___y_881_);
lean_dec_ref(v_entries_884_);
v___x_888_ = l_Array_append___redArg(v___y_880_, v___y_883_);
lean_dec(v___y_883_);
v___y_872_ = v___y_882_;
v_parts_873_ = v___x_888_;
v_specEntries_874_ = v___x_887_;
goto v___jp_871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___boxed(lean_object* v_components_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v_components_949_);
lean_dec_ref(v_components_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(lean_object* v___x_951_, lean_object* v_inst_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_951_, v_a_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___boxed(lean_object* v___x_955_, lean_object* v_inst_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(v___x_955_, v_inst_956_, v_a_957_);
lean_dec(v___x_955_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(lean_object* v_range_959_, lean_object* v_b_960_, lean_object* v_i_961_, lean_object* v_hs_962_, lean_object* v_hl_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v_range_959_, v_b_960_, v_i_961_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___boxed(lean_object* v_range_965_, lean_object* v_b_966_, lean_object* v_i_967_, lean_object* v_hs_968_, lean_object* v_hl_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(v_range_965_, v_b_966_, v_i_967_, v_hs_968_, v_hl_969_);
lean_dec_ref(v_b_966_);
lean_dec_ref(v_range_965_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(lean_object* v___x_971_, lean_object* v_range_972_, lean_object* v_b_973_, lean_object* v_i_974_, lean_object* v_hs_975_, lean_object* v_hl_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_971_, v_range_972_, v_b_973_, v_i_974_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___boxed(lean_object* v___x_978_, lean_object* v_range_979_, lean_object* v_b_980_, lean_object* v_i_981_, lean_object* v_hs_982_, lean_object* v_hl_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(v___x_978_, v_range_979_, v_b_980_, v_i_981_, v_hs_982_, v_hl_983_);
lean_dec(v_b_980_);
lean_dec_ref(v_range_979_);
lean_dec_ref(v___x_978_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(lean_object* v___x_985_, lean_object* v___x_986_, lean_object* v_range_987_, lean_object* v_b_988_, lean_object* v_i_989_, lean_object* v_hs_990_, lean_object* v_hl_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_985_, v___x_986_, v_range_987_, v_b_988_, v_i_989_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___boxed(lean_object* v___x_993_, lean_object* v___x_994_, lean_object* v_range_995_, lean_object* v_b_996_, lean_object* v_i_997_, lean_object* v_hs_998_, lean_object* v_hl_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(v___x_993_, v___x_994_, v_range_995_, v_b_996_, v_i_997_, v_hs_998_, v_hl_999_);
lean_dec_ref(v_range_995_);
lean_dec(v___x_994_);
lean_dec_ref(v___x_993_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(lean_object* v_body_1001_){
_start:
{
lean_object* v_name_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_name_1002_ = l_Lean_Name_demangle(v_body_1001_);
v___x_1003_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(v_name_1002_);
lean_dec(v_name_1002_);
v___x_1004_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v___x_1003_);
lean_dec_ref(v___x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody___boxed(lean_object* v_body_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_body_1005_);
lean_dec_ref(v_body_1005_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(lean_object* v_s_1010_, lean_object* v___x_1011_, lean_object* v_a_1012_, lean_object* v_b_1013_){
_start:
{
uint8_t v_decide_1014_; 
v_decide_1014_ = lean_nat_dec_eq(v_a_1012_, v___x_1011_);
if (v_decide_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint32_t v___x_1018_; uint32_t v___x_1019_; uint8_t v___x_1020_; 
lean_dec_ref(v_b_1013_);
v___x_1015_ = lean_box(0);
v___x_1016_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1017_ = lean_string_utf8_next_fast(v_s_1010_, v_a_1012_);
v___x_1018_ = lean_string_utf8_get_fast(v_s_1010_, v_a_1012_);
v___x_1019_ = 95;
v___x_1020_ = lean_uint32_dec_eq(v___x_1018_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_dec(v_a_1012_);
v_a_1012_ = v___x_1017_;
v_b_1013_ = v___x_1016_;
goto _start;
}
else
{
lean_object* v___x_1022_; uint8_t v_decide_1023_; 
v___x_1022_ = lean_unsigned_to_nat(0u);
v_decide_1023_ = lean_nat_dec_eq(v_a_1012_, v___x_1022_);
if (v_decide_1023_ == 0)
{
if (v___x_1020_ == 0)
{
lean_dec(v_a_1012_);
v_a_1012_ = v___x_1017_;
v_b_1013_ = v___x_1016_;
goto _start;
}
else
{
lean_object* v___x_1025_; uint8_t v_decide_1026_; 
v___x_1025_ = lean_string_utf8_byte_size(v_s_1010_);
v_decide_1026_ = lean_nat_dec_eq(v___x_1017_, v___x_1025_);
if (v_decide_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_string_utf8_extract_fast(v_s_1010_, v___x_1022_, v_a_1012_);
lean_dec(v_a_1012_);
v___x_1028_ = l_Lean_Name_demangle_x3f(v___x_1027_);
if (lean_obj_tag(v___x_1028_) == 1)
{
lean_object* v_val_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1051_; 
v_val_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1051_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_val_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1051_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
if (lean_obj_tag(v_val_1029_) == 1)
{
lean_object* v_pre_1033_; 
v_pre_1033_ = lean_ctor_get(v_val_1029_, 0);
lean_inc(v_pre_1033_);
lean_dec_ref_known(v_val_1029_, 2);
if (lean_obj_tag(v_pre_1033_) == 0)
{
lean_object* v___x_1034_; lean_object* v___y_1036_; lean_object* v___x_1044_; 
v___x_1034_ = lean_string_utf8_extract_fast(v_s_1010_, v___x_1017_, v___x_1025_);
v___x_1044_ = l_Lean_Name_demangle_x3f(v___x_1034_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_dec_ref(v___x_1034_);
lean_del_object(v___x_1031_);
lean_dec_ref(v___x_1027_);
v_a_1012_ = v___x_1017_;
v_b_1013_ = v___x_1016_;
goto _start;
}
else
{
lean_object* v___x_1046_; 
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = l_Lean_Name_demangle(v___x_1027_);
if (lean_obj_tag(v___x_1046_) == 1)
{
lean_object* v_pre_1047_; 
v_pre_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_pre_1047_);
if (lean_obj_tag(v_pre_1047_) == 0)
{
lean_object* v_str_1048_; 
lean_dec_ref(v___x_1027_);
v_str_1048_ = lean_ctor_get(v___x_1046_, 1);
lean_inc_ref(v_str_1048_);
lean_dec_ref_known(v___x_1046_, 2);
v___y_1036_ = v_str_1048_;
goto v___jp_1035_;
}
else
{
lean_dec(v_pre_1047_);
lean_dec_ref_known(v___x_1046_, 2);
v___y_1036_ = v___x_1027_;
goto v___jp_1035_;
}
}
else
{
lean_dec(v___x_1046_);
v___y_1036_ = v___x_1027_;
goto v___jp_1035_;
}
}
v___jp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1037_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v___x_1034_);
lean_dec_ref(v___x_1034_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v___y_1036_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1038_);
v___x_1040_ = v___x_1031_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v___x_1015_);
v___x_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
}
else
{
lean_dec(v_pre_1033_);
lean_del_object(v___x_1031_);
lean_dec_ref(v___x_1027_);
v_a_1012_ = v___x_1017_;
v_b_1013_ = v___x_1016_;
goto _start;
}
}
else
{
lean_del_object(v___x_1031_);
lean_dec(v_val_1029_);
lean_dec_ref(v___x_1027_);
v_a_1012_ = v___x_1017_;
v_b_1013_ = v___x_1016_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1028_);
lean_dec_ref(v___x_1027_);
v_a_1012_ = v___x_1017_;
v_b_1013_ = v___x_1016_;
goto _start;
}
}
else
{
lean_dec(v_a_1012_);
v_a_1012_ = v___x_1017_;
v_b_1013_ = v___x_1016_;
goto _start;
}
}
}
else
{
lean_dec(v_a_1012_);
v_a_1012_ = v___x_1017_;
v_b_1013_ = v___x_1016_;
goto _start;
}
}
}
else
{
lean_object* v___x_1055_; 
lean_dec(v_a_1012_);
v___x_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1055_, 0, v_b_1013_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___boxed(lean_object* v_s_1056_, lean_object* v___x_1057_, lean_object* v_a_1058_, lean_object* v_b_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1056_, v___x_1057_, v_a_1058_, v_b_1059_);
lean_dec(v___x_1057_);
lean_dec_ref(v_s_1056_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(lean_object* v_s_1061_){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = lean_string_utf8_byte_size(v_s_1061_);
v___x_1064_ = lean_box(0);
v___x_1065_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1066_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1061_, v___x_1063_, v___x_1062_, v___x_1065_);
if (lean_obj_tag(v___x_1066_) == 0)
{
return v___x_1064_;
}
else
{
lean_object* v_val_1067_; lean_object* v_fst_1068_; 
v_val_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_val_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v_fst_1068_ = lean_ctor_get(v_val_1067_, 0);
lean_inc(v_fst_1068_);
lean_dec(v_val_1067_);
if (lean_obj_tag(v_fst_1068_) == 0)
{
return v___x_1064_;
}
else
{
return v_fst_1068_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg___boxed(lean_object* v_s_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_s_1069_);
lean_dec_ref(v_s_1069_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(lean_object* v_s_1071_, lean_object* v___x_1072_, lean_object* v___x_1073_, lean_object* v_inst_1074_, lean_object* v_R_1075_, lean_object* v_a_1076_, lean_object* v_b_1077_, lean_object* v_c_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1071_, v___x_1072_, v_a_1076_, v_b_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___boxed(lean_object* v_s_1080_, lean_object* v___x_1081_, lean_object* v___x_1082_, lean_object* v_inst_1083_, lean_object* v_R_1084_, lean_object* v_a_1085_, lean_object* v_b_1086_, lean_object* v_c_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(v_s_1080_, v___x_1081_, v___x_1082_, v_inst_1083_, v_R_1084_, v_a_1085_, v_b_1086_, v_c_1087_);
lean_dec_ref(v___x_1082_);
lean_dec(v___x_1081_);
lean_dec_ref(v_s_1080_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(lean_object* v_s_1089_, lean_object* v___x_1090_, lean_object* v___x_1091_, lean_object* v_a_1092_, lean_object* v_b_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_box(0);
switch(lean_obj_tag(v_a_1092_))
{
case 0:
{
lean_object* v_pos_1095_; lean_object* v___x_1096_; 
v_pos_1095_ = lean_ctor_get(v_a_1092_, 0);
lean_inc(v_pos_1095_);
lean_dec_ref_known(v_a_1092_, 1);
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_pos_1095_);
return v___x_1096_;
}
case 1:
{
lean_object* v_pos_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1106_; 
v_pos_1097_ = lean_ctor_get(v_a_1092_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_a_1092_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1099_ = v_a_1092_;
v_isShared_1100_ = v_isSharedCheck_1106_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_pos_1097_);
lean_dec(v_a_1092_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1106_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1101_ = lean_string_utf8_next_fast(v_s_1089_, v_pos_1097_);
lean_dec(v_pos_1097_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set_tag(v___x_1099_, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1101_);
v___x_1103_ = v___x_1099_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
v_a_1092_ = v___x_1103_;
v_b_1093_ = v___x_1094_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1107_; lean_object* v_table_1108_; lean_object* v_stackPos_1109_; lean_object* v_needlePos_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1163_; 
v_needle_1107_ = lean_ctor_get(v_a_1092_, 0);
v_table_1108_ = lean_ctor_get(v_a_1092_, 1);
v_stackPos_1109_ = lean_ctor_get(v_a_1092_, 2);
v_needlePos_1110_ = lean_ctor_get(v_a_1092_, 3);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_a_1092_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1112_ = v_a_1092_;
v_isShared_1113_ = v_isSharedCheck_1163_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_needlePos_1110_);
lean_inc(v_stackPos_1109_);
lean_inc(v_table_1108_);
lean_inc(v_needle_1107_);
lean_dec(v_a_1092_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1163_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_str_1114_; lean_object* v_startInclusive_1115_; lean_object* v_endExclusive_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v_str_1114_ = lean_ctor_get(v_needle_1107_, 0);
v_startInclusive_1115_ = lean_ctor_get(v_needle_1107_, 1);
v_endExclusive_1116_ = lean_ctor_get(v_needle_1107_, 2);
v___x_1117_ = lean_nat_sub(v_stackPos_1109_, v_needlePos_1110_);
v___x_1118_ = lean_nat_sub(v_endExclusive_1116_, v_startInclusive_1115_);
v___x_1119_ = lean_nat_add(v___x_1117_, v___x_1118_);
v___x_1120_ = lean_nat_dec_le(v___x_1119_, v___x_1091_);
lean_dec(v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
lean_dec(v___x_1118_);
lean_del_object(v___x_1112_);
lean_dec(v_needlePos_1110_);
lean_dec(v_stackPos_1109_);
lean_dec_ref(v_table_1108_);
lean_dec_ref(v_needle_1107_);
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_add(v___x_1117_, v___x_1121_);
lean_dec(v___x_1117_);
v___x_1123_ = lean_nat_dec_le(v___x_1122_, v___x_1091_);
lean_dec(v___x_1122_);
if (v___x_1123_ == 0)
{
lean_inc(v_b_1093_);
return v_b_1093_;
}
else
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_box(3);
v_a_1092_ = v___x_1124_;
v_b_1093_ = v___x_1094_;
goto _start;
}
}
else
{
uint8_t v_stackByte_1126_; lean_object* v___x_1127_; uint8_t v_patByte_1128_; uint8_t v___x_1129_; 
lean_dec(v___x_1117_);
lean_inc(v_stackPos_1109_);
v_stackByte_1126_ = lean_string_get_byte_fast(v_s_1089_, v_stackPos_1109_);
v___x_1127_ = lean_nat_add(v_startInclusive_1115_, v_needlePos_1110_);
v_patByte_1128_ = lean_string_get_byte_fast(v_str_1114_, v___x_1127_);
v___x_1129_ = lean_uint8_dec_eq(v_stackByte_1126_, v_patByte_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; uint8_t v_decide_1131_; 
lean_dec(v___x_1118_);
v___x_1130_ = lean_unsigned_to_nat(0u);
v_decide_1131_ = lean_nat_dec_eq(v_needlePos_1110_, v___x_1130_);
if (v_decide_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_newNeedlePos_1134_; uint8_t v___x_1135_; 
v___x_1132_ = lean_unsigned_to_nat(1u);
v___x_1133_ = lean_nat_sub(v_needlePos_1110_, v___x_1132_);
lean_dec(v_needlePos_1110_);
v_newNeedlePos_1134_ = lean_array_fget_borrowed(v_table_1108_, v___x_1133_);
lean_dec(v___x_1133_);
v___x_1135_ = lean_nat_dec_eq(v_newNeedlePos_1134_, v___x_1130_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1137_; 
lean_inc(v_newNeedlePos_1134_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 3, v_newNeedlePos_1134_);
v___x_1137_ = v___x_1112_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_needle_1107_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_table_1108_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_stackPos_1109_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v_newNeedlePos_1134_);
v___x_1137_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
v_a_1092_ = v___x_1137_;
v_b_1093_ = v___x_1094_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1140_; lean_object* v___x_1142_; 
v_nextStackPos_1140_ = l_String_Slice_posGE___redArg(v___x_1090_, v_stackPos_1109_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 3, v___x_1130_);
lean_ctor_set(v___x_1112_, 2, v_nextStackPos_1140_);
v___x_1142_ = v___x_1112_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_needle_1107_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_table_1108_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_nextStackPos_1140_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v___x_1130_);
v___x_1142_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
v_a_1092_ = v___x_1142_;
v_b_1093_ = v___x_1094_;
goto _start;
}
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v_nextStackPos_1147_; lean_object* v___x_1149_; 
lean_dec(v_needlePos_1110_);
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = lean_nat_add(v_stackPos_1109_, v___x_1145_);
lean_dec(v_stackPos_1109_);
v_nextStackPos_1147_ = l_String_Slice_posGE___redArg(v___x_1090_, v___x_1146_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 3, v___x_1130_);
lean_ctor_set(v___x_1112_, 2, v_nextStackPos_1147_);
v___x_1149_ = v___x_1112_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_needle_1107_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_table_1108_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_nextStackPos_1147_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v___x_1130_);
v___x_1149_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
v_a_1092_ = v___x_1149_;
v_b_1093_ = v___x_1094_;
goto _start;
}
}
}
else
{
lean_object* v___x_1152_; lean_object* v_nextStackPos_1153_; lean_object* v_nextNeedlePos_1154_; uint8_t v_decide_1155_; 
v___x_1152_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1153_ = lean_nat_add(v_stackPos_1109_, v___x_1152_);
lean_dec(v_stackPos_1109_);
v_nextNeedlePos_1154_ = lean_nat_add(v_needlePos_1110_, v___x_1152_);
lean_dec(v_needlePos_1110_);
v_decide_1155_ = lean_nat_dec_eq(v_nextNeedlePos_1154_, v___x_1118_);
lean_dec(v___x_1118_);
if (v_decide_1155_ == 0)
{
lean_object* v___x_1157_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 3, v_nextNeedlePos_1154_);
lean_ctor_set(v___x_1112_, 2, v_nextStackPos_1153_);
v___x_1157_ = v___x_1112_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_needle_1107_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_table_1108_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_nextStackPos_1153_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_nextNeedlePos_1154_);
v___x_1157_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
v_a_1092_ = v___x_1157_;
goto _start;
}
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_del_object(v___x_1112_);
lean_dec_ref(v_table_1108_);
lean_dec_ref(v_needle_1107_);
v___x_1160_ = lean_nat_sub(v_nextStackPos_1153_, v_nextNeedlePos_1154_);
lean_dec(v_nextNeedlePos_1154_);
lean_dec(v_nextStackPos_1153_);
v___x_1161_ = l_String_Slice_pos_x21(v___x_1090_, v___x_1160_);
lean_dec(v___x_1160_);
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
}
}
}
default: 
{
lean_inc(v_b_1093_);
return v_b_1093_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg___boxed(lean_object* v_s_1164_, lean_object* v___x_1165_, lean_object* v___x_1166_, lean_object* v_a_1167_, lean_object* v_b_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1164_, v___x_1165_, v___x_1166_, v_a_1167_, v_b_1168_);
lean_dec(v_b_1168_);
lean_dec(v___x_1166_);
lean_dec_ref(v___x_1165_);
lean_dec_ref(v_s_1164_);
return v_res_1169_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0));
v___x_1172_ = lean_string_utf8_byte_size(v___x_1171_);
return v___x_1172_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1);
v___x_1175_ = lean_nat_dec_eq(v___x_1174_, v___x_1173_);
return v___x_1175_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1176_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1);
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0));
v___x_1179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v___x_1177_);
lean_ctor_set(v___x_1179_, 2, v___x_1176_);
return v___x_1179_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
v___x_1181_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1180_);
return v___x_1181_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4);
v___x_1184_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
v___x_1185_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___x_1183_);
lean_ctor_set(v___x_1185_, 2, v___x_1182_);
lean_ctor_set(v___x_1185_, 3, v___x_1182_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(lean_object* v_s_1188_){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___y_1193_; uint8_t v___x_1202_; 
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = lean_string_utf8_byte_size(v_s_1188_);
lean_inc_ref(v_s_1188_);
v___x_1191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1191_, 0, v_s_1188_);
lean_ctor_set(v___x_1191_, 1, v___x_1189_);
lean_ctor_set(v___x_1191_, 2, v___x_1190_);
v___x_1202_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5);
v___y_1193_ = v___x_1203_;
goto v___jp_1192_;
}
else
{
lean_object* v___x_1204_; 
v___x_1204_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1193_ = v___x_1204_;
goto v___jp_1192_;
}
v___jp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_box(0);
lean_inc(v___y_1193_);
v___x_1195_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1188_, v___x_1191_, v___x_1190_, v___y_1193_, v___x_1194_);
lean_dec_ref_known(v___x_1191_, 3);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_s_1188_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
return v___x_1197_;
}
else
{
lean_object* v_val_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_val_1198_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_val_1198_);
lean_dec_ref_known(v___x_1195_, 1);
v___x_1199_ = lean_string_utf8_extract_fast(v_s_1188_, v___x_1189_, v_val_1198_);
v___x_1200_ = lean_string_utf8_extract_fast(v_s_1188_, v_val_1198_, v___x_1190_);
lean_dec(v_val_1198_);
lean_dec_ref(v_s_1188_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
return v___x_1201_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(lean_object* v_s_1205_, lean_object* v___x_1206_, lean_object* v___x_1207_, lean_object* v_inst_1208_, lean_object* v_R_1209_, lean_object* v_a_1210_, lean_object* v_b_1211_, lean_object* v_c_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1205_, v___x_1206_, v___x_1207_, v_a_1210_, v_b_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___boxed(lean_object* v_s_1214_, lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v_inst_1217_, lean_object* v_R_1218_, lean_object* v_a_1219_, lean_object* v_b_1220_, lean_object* v_c_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(v_s_1214_, v___x_1215_, v___x_1216_, v_inst_1217_, v_R_1218_, v_a_1219_, v_b_1220_, v_c_1221_);
lean_dec(v_b_1220_);
lean_dec(v___x_1216_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v_s_1214_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(lean_object* v_s_1234_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10));
lean_inc_ref(v_s_1234_);
v___x_1351_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1234_, v___x_1350_);
if (lean_obj_tag(v___x_1351_) == 1)
{
lean_object* v_val_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1365_; 
v_val_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1365_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_val_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1365_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1356_ = lean_string_utf8_byte_size(v_val_1352_);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_nat_dec_eq(v___x_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_dec_ref(v_s_1234_);
v___x_1359_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1360_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1352_);
lean_dec(v_val_1352_);
v___x_1361_ = lean_string_append(v___x_1359_, v___x_1360_);
lean_dec_ref(v___x_1360_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1361_);
v___x_1363_ = v___x_1354_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
else
{
lean_del_object(v___x_1354_);
lean_dec(v_val_1352_);
goto v___jp_1328_;
}
}
}
else
{
lean_dec(v___x_1351_);
goto v___jp_1328_;
}
v___jp_1235_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0));
v___x_1237_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1234_, v___x_1236_);
if (lean_obj_tag(v___x_1237_) == 1)
{
lean_object* v_val_1238_; lean_object* v___x_1239_; 
v_val_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v___x_1239_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1238_);
lean_dec(v_val_1238_);
if (lean_obj_tag(v___x_1239_) == 1)
{
lean_object* v_val_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1254_; 
v_val_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1254_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_val_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1254_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_fst_1244_; lean_object* v_snd_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v_fst_1244_ = lean_ctor_get(v_val_1240_, 0);
lean_inc(v_fst_1244_);
v_snd_1245_ = lean_ctor_get(v_val_1240_, 1);
lean_inc(v_snd_1245_);
lean_dec(v_val_1240_);
v___x_1246_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1247_ = lean_string_append(v_fst_1244_, v___x_1246_);
v___x_1248_ = lean_string_append(v___x_1247_, v_snd_1245_);
lean_dec(v_snd_1245_);
v___x_1249_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1250_ = lean_string_append(v___x_1248_, v___x_1249_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1250_);
v___x_1252_ = v___x_1242_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
else
{
lean_object* v___x_1255_; 
lean_dec(v___x_1239_);
v___x_1255_ = lean_box(0);
return v___x_1255_;
}
}
else
{
lean_object* v___x_1256_; 
lean_dec(v___x_1237_);
v___x_1256_ = lean_box(0);
return v___x_1256_;
}
}
v___jp_1257_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3));
lean_inc_ref(v_s_1234_);
v___x_1259_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1234_, v___x_1258_);
if (lean_obj_tag(v___x_1259_) == 1)
{
lean_object* v_val_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1271_; 
v_val_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1271_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_val_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1271_;
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
lean_object* v___x_1267_; lean_object* v___x_1269_; 
lean_dec_ref(v_s_1234_);
v___x_1267_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1260_);
lean_dec(v_val_1260_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1267_);
v___x_1269_ = v___x_1262_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
else
{
lean_del_object(v___x_1262_);
lean_dec(v_val_1260_);
goto v___jp_1235_;
}
}
}
else
{
lean_dec(v___x_1259_);
goto v___jp_1235_;
}
}
v___jp_1272_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4));
lean_inc_ref(v_s_1234_);
v___x_1274_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1234_, v___x_1273_);
if (lean_obj_tag(v___x_1274_) == 1)
{
lean_object* v_val_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1288_; 
v_val_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1288_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_val_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1288_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = lean_string_utf8_byte_size(v_val_1275_);
v___x_1280_ = lean_unsigned_to_nat(0u);
v___x_1281_ = lean_nat_dec_eq(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
lean_dec_ref(v_s_1234_);
v___x_1282_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1283_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1275_);
lean_dec(v_val_1275_);
v___x_1284_ = lean_string_append(v___x_1282_, v___x_1283_);
lean_dec_ref(v___x_1283_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1284_);
v___x_1286_ = v___x_1277_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
else
{
lean_del_object(v___x_1277_);
lean_dec(v_val_1275_);
goto v___jp_1257_;
}
}
}
else
{
lean_dec(v___x_1274_);
goto v___jp_1257_;
}
}
v___jp_1289_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6));
lean_inc_ref(v_s_1234_);
v___x_1291_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1234_, v___x_1290_);
if (lean_obj_tag(v___x_1291_) == 1)
{
lean_object* v_val_1292_; lean_object* v___x_1293_; 
v_val_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_val_1292_);
lean_dec_ref_known(v___x_1291_, 1);
v___x_1293_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1292_);
lean_dec(v_val_1292_);
if (lean_obj_tag(v___x_1293_) == 1)
{
lean_object* v_val_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref(v_s_1234_);
v_val_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1310_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_val_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1310_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_fst_1298_; lean_object* v_snd_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
v_fst_1298_ = lean_ctor_get(v_val_1294_, 0);
lean_inc(v_fst_1298_);
v_snd_1299_ = lean_ctor_get(v_val_1294_, 1);
lean_inc(v_snd_1299_);
lean_dec(v_val_1294_);
v___x_1300_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1301_ = lean_string_append(v___x_1300_, v_fst_1298_);
lean_dec(v_fst_1298_);
v___x_1302_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1303_ = lean_string_append(v___x_1301_, v___x_1302_);
v___x_1304_ = lean_string_append(v___x_1303_, v_snd_1299_);
lean_dec(v_snd_1299_);
v___x_1305_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1306_ = lean_string_append(v___x_1304_, v___x_1305_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1306_);
v___x_1308_ = v___x_1296_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
else
{
lean_dec(v___x_1293_);
goto v___jp_1272_;
}
}
else
{
lean_dec(v___x_1291_);
goto v___jp_1272_;
}
}
v___jp_1311_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7));
lean_inc_ref(v_s_1234_);
v___x_1313_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1234_, v___x_1312_);
if (lean_obj_tag(v___x_1313_) == 1)
{
lean_object* v_val_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1327_; 
v_val_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1327_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_val_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1327_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1318_ = lean_string_utf8_byte_size(v_val_1314_);
v___x_1319_ = lean_unsigned_to_nat(0u);
v___x_1320_ = lean_nat_dec_eq(v___x_1318_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
lean_dec_ref(v_s_1234_);
v___x_1321_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1322_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1314_);
lean_dec(v_val_1314_);
v___x_1323_ = lean_string_append(v___x_1321_, v___x_1322_);
lean_dec_ref(v___x_1322_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1323_);
v___x_1325_ = v___x_1316_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
else
{
lean_del_object(v___x_1316_);
lean_dec(v_val_1314_);
goto v___jp_1289_;
}
}
}
else
{
lean_dec(v___x_1313_);
goto v___jp_1289_;
}
}
v___jp_1328_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8));
lean_inc_ref(v_s_1234_);
v___x_1330_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1234_, v___x_1329_);
if (lean_obj_tag(v___x_1330_) == 1)
{
lean_object* v_val_1331_; lean_object* v___x_1332_; 
v_val_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v___x_1332_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1331_);
lean_dec(v_val_1331_);
if (lean_obj_tag(v___x_1332_) == 1)
{
lean_object* v_val_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v_s_1234_);
v_val_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1349_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_val_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1349_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_fst_1337_; lean_object* v_snd_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v_fst_1337_ = lean_ctor_get(v_val_1333_, 0);
lean_inc(v_fst_1337_);
v_snd_1338_ = lean_ctor_get(v_val_1333_, 1);
lean_inc(v_snd_1338_);
lean_dec(v_val_1333_);
v___x_1339_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1340_ = lean_string_append(v___x_1339_, v_fst_1337_);
lean_dec(v_fst_1337_);
v___x_1341_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1342_ = lean_string_append(v___x_1340_, v___x_1341_);
v___x_1343_ = lean_string_append(v___x_1342_, v_snd_1338_);
lean_dec(v_snd_1338_);
v___x_1344_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1345_ = lean_string_append(v___x_1343_, v___x_1344_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1345_);
v___x_1347_ = v___x_1335_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
else
{
lean_dec(v___x_1332_);
goto v___jp_1311_;
}
}
else
{
lean_dec(v___x_1330_);
goto v___jp_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleSymbol(lean_object* v_symbol_1375_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1376_ = lean_string_utf8_byte_size(v_symbol_1375_);
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = lean_nat_dec_eq(v___x_1376_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v_fst_1380_; lean_object* v_snd_1381_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1379_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(v_symbol_1375_);
v_fst_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_n(v_fst_1380_, 2);
v_snd_1381_ = lean_ctor_get(v___x_1379_, 1);
lean_inc(v_snd_1381_);
lean_dec_ref(v___x_1379_);
v___x_1406_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__5));
v___x_1407_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_fst_1380_, v___x_1406_);
if (lean_obj_tag(v___x_1407_) == 1)
{
lean_object* v_val_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1428_; 
v_val_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1428_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_val_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1428_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
uint8_t v___x_1412_; 
lean_inc(v_val_1408_);
v___x_1412_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_1408_);
if (v___x_1412_ == 0)
{
lean_del_object(v___x_1410_);
lean_dec(v_val_1408_);
goto v___jp_1382_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v_r_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
lean_dec(v_fst_1380_);
v___x_1413_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__6));
v___x_1414_ = lean_string_append(v___x_1413_, v_val_1408_);
lean_dec(v_val_1408_);
v___x_1415_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__7));
v_r_1416_ = lean_string_append(v___x_1414_, v___x_1415_);
v___x_1417_ = lean_string_utf8_byte_size(v_snd_1381_);
v___x_1418_ = lean_nat_dec_eq(v___x_1417_, v___x_1377_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1419_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1420_ = lean_string_append(v_r_1416_, v___x_1419_);
v___x_1421_ = lean_string_append(v___x_1420_, v_snd_1381_);
lean_dec(v_snd_1381_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1421_);
v___x_1423_ = v___x_1410_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
else
{
lean_object* v___x_1426_; 
lean_dec(v_snd_1381_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v_r_1416_);
v___x_1426_ = v___x_1410_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_r_1416_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
else
{
lean_dec(v___x_1407_);
goto v___jp_1382_;
}
v___jp_1382_:
{
lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1383_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__0));
v___x_1384_ = lean_string_dec_eq(v_fst_1380_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; 
v___x_1385_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(v_fst_1380_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_dec(v_snd_1381_);
return v___x_1385_;
}
else
{
lean_object* v_val_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_val_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_val_1386_);
v___x_1387_ = lean_string_utf8_byte_size(v_snd_1381_);
v___x_1388_ = lean_nat_dec_eq(v___x_1387_, v___x_1377_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1398_; 
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v___x_1385_, 0);
lean_dec(v_unused_1399_);
v___x_1390_ = v___x_1385_;
v_isShared_1391_ = v_isSharedCheck_1398_;
goto v_resetjp_1389_;
}
else
{
lean_dec(v___x_1385_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1398_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1392_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1393_ = lean_string_append(v_val_1386_, v___x_1392_);
v___x_1394_ = lean_string_append(v___x_1393_, v_snd_1381_);
lean_dec(v_snd_1381_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1394_);
v___x_1396_ = v___x_1390_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
else
{
lean_dec(v_val_1386_);
lean_dec(v_snd_1381_);
return v___x_1385_;
}
}
}
else
{
lean_object* v___x_1400_; uint8_t v___x_1401_; 
lean_dec(v_fst_1380_);
v___x_1400_ = lean_string_utf8_byte_size(v_snd_1381_);
v___x_1401_ = lean_nat_dec_eq(v___x_1400_, v___x_1377_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__2));
v___x_1403_ = lean_string_append(v___x_1402_, v_snd_1381_);
lean_dec(v_snd_1381_);
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
return v___x_1404_;
}
else
{
lean_object* v___x_1405_; 
lean_dec(v_snd_1381_);
v___x_1405_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__4));
return v___x_1405_;
}
}
}
}
else
{
lean_object* v___x_1429_; 
lean_dec_ref(v_symbol_1375_);
v___x_1429_ = lean_box(0);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(lean_object* v_s_1430_, lean_object* v_pos_1431_, lean_object* v_pred_1432_){
_start:
{
lean_object* v___x_1433_; uint8_t v_decide_1434_; 
v___x_1433_ = lean_string_utf8_byte_size(v_s_1430_);
v_decide_1434_ = lean_nat_dec_eq(v_pos_1431_, v___x_1433_);
if (v_decide_1434_ == 0)
{
uint32_t v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1435_ = lean_string_utf8_get_fast(v_s_1430_, v_pos_1431_);
v___x_1436_ = lean_box_uint32(v___x_1435_);
lean_inc_ref(v_pred_1432_);
v___x_1437_ = lean_apply_1(v_pred_1432_, v___x_1436_);
v___x_1438_ = lean_unbox(v___x_1437_);
if (v___x_1438_ == 0)
{
lean_dec_ref(v_pred_1432_);
return v_pos_1431_;
}
else
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_string_utf8_next_fast(v_s_1430_, v_pos_1431_);
lean_dec(v_pos_1431_);
v_pos_1431_ = v___x_1439_;
goto _start;
}
}
else
{
lean_dec_ref(v_pred_1432_);
return v_pos_1431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile___boxed(lean_object* v_s_1441_, lean_object* v_pos_1442_, lean_object* v_pred_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_s_1441_, v_pos_1442_, v_pred_1443_);
lean_dec_ref(v_s_1441_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(lean_object* v_s_1445_, lean_object* v_p_u2081_1446_, lean_object* v_p_u2082_1447_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = lean_string_utf8_extract_fast(v_s_1445_, v___x_1448_, v_p_u2081_1446_);
v___x_1450_ = lean_string_utf8_extract_fast(v_s_1445_, v_p_u2081_1446_, v_p_u2082_1447_);
v___x_1451_ = lean_string_utf8_byte_size(v_s_1445_);
v___x_1452_ = lean_string_utf8_extract_fast(v_s_1445_, v_p_u2082_1447_, v___x_1451_);
v___x_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1450_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1449_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082___boxed(lean_object* v_s_1455_, lean_object* v_p_u2081_1456_, lean_object* v_p_u2082_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_s_1455_, v_p_u2081_1456_, v_p_u2082_1457_);
lean_dec(v_p_u2082_1457_);
lean_dec(v_p_u2081_1456_);
lean_dec_ref(v_s_1455_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(lean_object* v___x_1459_, lean_object* v___x_1460_, lean_object* v_line_1461_, lean_object* v_a_1462_, lean_object* v_b_1463_){
_start:
{
lean_object* v___x_1464_; uint8_t v_decide_1465_; 
v___x_1464_ = lean_nat_sub(v___x_1459_, v___x_1460_);
v_decide_1465_ = lean_nat_dec_eq(v_a_1462_, v___x_1464_);
lean_dec(v___x_1464_);
if (v_decide_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___y_1469_; uint32_t v___x_1474_; uint32_t v___x_1475_; uint8_t v___x_1476_; 
v___x_1466_ = lean_box(0);
v___x_1467_ = lean_nat_add(v___x_1460_, v_a_1462_);
v___x_1474_ = lean_string_utf8_get_fast(v_line_1461_, v___x_1467_);
v___x_1475_ = 43;
v___x_1476_ = lean_uint32_dec_eq(v___x_1474_, v___x_1475_);
if (v___x_1476_ == 0)
{
uint32_t v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = 41;
v___x_1478_ = lean_uint32_dec_eq(v___x_1474_, v___x_1477_);
v___y_1469_ = v___x_1478_;
goto v___jp_1468_;
}
else
{
v___y_1469_ = v___x_1476_;
goto v___jp_1468_;
}
v___jp_1468_:
{
if (v___y_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec(v_a_1462_);
v___x_1470_ = lean_string_utf8_next_fast(v_line_1461_, v___x_1467_);
lean_dec(v___x_1467_);
v___x_1471_ = lean_nat_sub(v___x_1470_, v___x_1460_);
v_a_1462_ = v___x_1471_;
v_b_1463_ = v___x_1466_;
goto _start;
}
else
{
lean_object* v___x_1473_; 
lean_dec(v___x_1467_);
v___x_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1473_, 0, v_a_1462_);
return v___x_1473_;
}
}
}
else
{
lean_dec(v_a_1462_);
lean_inc(v_b_1463_);
return v_b_1463_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg___boxed(lean_object* v___x_1479_, lean_object* v___x_1480_, lean_object* v_line_1481_, lean_object* v_a_1482_, lean_object* v_b_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1479_, v___x_1480_, v_line_1481_, v_a_1482_, v_b_1483_);
lean_dec(v_b_1483_);
lean_dec_ref(v_line_1481_);
lean_dec(v___x_1480_);
lean_dec(v___x_1479_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(lean_object* v___x_1485_, lean_object* v_line_1486_, lean_object* v_a_1487_, lean_object* v_b_1488_){
_start:
{
uint8_t v_decide_1489_; 
v_decide_1489_ = lean_nat_dec_eq(v_a_1487_, v___x_1485_);
if (v_decide_1489_ == 0)
{
uint32_t v___x_1490_; uint32_t v___x_1491_; uint8_t v___x_1492_; 
v___x_1490_ = lean_string_utf8_get_fast(v_line_1486_, v_a_1487_);
v___x_1491_ = 40;
v___x_1492_ = lean_uint32_dec_eq(v___x_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_string_utf8_next_fast(v_line_1486_, v_a_1487_);
lean_dec(v_a_1487_);
v_a_1487_ = v___x_1494_;
v_b_1488_ = v___x_1493_;
goto _start;
}
else
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1496_, 0, v_a_1487_);
return v___x_1496_;
}
}
else
{
lean_dec(v_a_1487_);
lean_inc(v_b_1488_);
return v_b_1488_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg___boxed(lean_object* v___x_1497_, lean_object* v_line_1498_, lean_object* v_a_1499_, lean_object* v_b_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1497_, v_line_1498_, v_a_1499_, v_b_1500_);
lean_dec(v_b_1500_);
lean_dec_ref(v_line_1498_);
lean_dec(v___x_1497_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(lean_object* v_line_1502_){
_start:
{
lean_object* v_searcher_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v_searcher_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = lean_string_utf8_byte_size(v_line_1502_);
v___x_1505_ = lean_box(0);
v___x_1506_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1504_, v_line_1502_, v_searcher_1503_, v___x_1505_);
if (lean_obj_tag(v___x_1506_) == 0)
{
return v___x_1505_;
}
else
{
lean_object* v_val_1507_; uint8_t v_decide_1508_; 
v_val_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_val_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v_decide_1508_ = lean_nat_dec_eq(v_val_1507_, v___x_1504_);
if (v_decide_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_string_utf8_next_fast(v_line_1502_, v_val_1507_);
lean_dec(v_val_1507_);
v___x_1510_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1504_, v___x_1509_, v_line_1502_, v_searcher_1503_, v___x_1505_);
if (lean_obj_tag(v___x_1510_) == 0)
{
return v___x_1505_;
}
else
{
lean_object* v_val_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1521_; 
v_val_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1521_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_val_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1521_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; uint8_t v_decide_1516_; 
v___x_1515_ = lean_nat_add(v___x_1509_, v_val_1511_);
lean_dec(v_val_1511_);
v_decide_1516_ = lean_nat_dec_eq(v___x_1515_, v___x_1509_);
if (v_decide_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1502_, v___x_1509_, v___x_1515_);
lean_dec(v___x_1515_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1517_);
v___x_1519_ = v___x_1513_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
else
{
lean_dec(v___x_1515_);
lean_del_object(v___x_1513_);
return v___x_1505_;
}
}
}
}
else
{
lean_dec(v_val_1507_);
return v___x_1505_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux___boxed(lean_object* v_line_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(v_line_1522_);
lean_dec_ref(v_line_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(lean_object* v___x_1524_, lean_object* v___x_1525_, lean_object* v_line_1526_, lean_object* v_inst_1527_, lean_object* v_R_1528_, lean_object* v_a_1529_, lean_object* v_b_1530_, lean_object* v_c_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1524_, v_line_1526_, v_a_1529_, v_b_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___boxed(lean_object* v___x_1533_, lean_object* v___x_1534_, lean_object* v_line_1535_, lean_object* v_inst_1536_, lean_object* v_R_1537_, lean_object* v_a_1538_, lean_object* v_b_1539_, lean_object* v_c_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(v___x_1533_, v___x_1534_, v_line_1535_, v_inst_1536_, v_R_1537_, v_a_1538_, v_b_1539_, v_c_1540_);
lean_dec(v_b_1539_);
lean_dec_ref(v_line_1535_);
lean_dec_ref(v___x_1534_);
lean_dec(v___x_1533_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(lean_object* v___x_1542_, lean_object* v___x_1543_, lean_object* v___x_1544_, lean_object* v_line_1545_, lean_object* v_inst_1546_, lean_object* v_R_1547_, lean_object* v_a_1548_, lean_object* v_b_1549_, lean_object* v_c_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1542_, v___x_1543_, v_line_1545_, v_a_1548_, v_b_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___boxed(lean_object* v___x_1552_, lean_object* v___x_1553_, lean_object* v___x_1554_, lean_object* v_line_1555_, lean_object* v_inst_1556_, lean_object* v_R_1557_, lean_object* v_a_1558_, lean_object* v_b_1559_, lean_object* v_c_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(v___x_1552_, v___x_1553_, v___x_1554_, v_line_1555_, v_inst_1556_, v_R_1557_, v_a_1558_, v_b_1559_, v_c_1560_);
lean_dec(v_b_1559_);
lean_dec_ref(v_line_1555_);
lean_dec_ref(v___x_1554_);
lean_dec(v___x_1553_);
lean_dec(v___x_1552_);
return v_res_1561_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(uint32_t v_x_1562_){
_start:
{
uint32_t v___x_1563_; uint8_t v___x_1564_; 
v___x_1563_ = 32;
v___x_1564_ = lean_uint32_dec_eq(v_x_1562_, v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed(lean_object* v_x_1565_){
_start:
{
uint32_t v_x_2696__boxed_1566_; uint8_t v_res_1567_; lean_object* v_r_1568_; 
v_x_2696__boxed_1566_ = lean_unbox_uint32(v_x_1565_);
lean_dec(v_x_1565_);
v_res_1567_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(v_x_2696__boxed_1566_);
v_r_1568_ = lean_box(v_res_1567_);
return v_r_1568_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(uint32_t v_x_1569_){
_start:
{
uint32_t v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = 48;
v___x_1581_ = lean_uint32_dec_le(v___x_1580_, v_x_1569_);
if (v___x_1581_ == 0)
{
goto v___jp_1575_;
}
else
{
uint32_t v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = 57;
v___x_1583_ = lean_uint32_dec_le(v_x_1569_, v___x_1582_);
if (v___x_1583_ == 0)
{
goto v___jp_1575_;
}
else
{
return v___x_1583_;
}
}
v___jp_1570_:
{
uint32_t v___x_1571_; uint8_t v___x_1572_; 
v___x_1571_ = 65;
v___x_1572_ = lean_uint32_dec_le(v___x_1571_, v_x_1569_);
if (v___x_1572_ == 0)
{
return v___x_1572_;
}
else
{
uint32_t v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = 70;
v___x_1574_ = lean_uint32_dec_le(v_x_1569_, v___x_1573_);
return v___x_1574_;
}
}
v___jp_1575_:
{
uint32_t v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = 97;
v___x_1577_ = lean_uint32_dec_le(v___x_1576_, v_x_1569_);
if (v___x_1577_ == 0)
{
goto v___jp_1570_;
}
else
{
uint32_t v___x_1578_; uint8_t v___x_1579_; 
v___x_1578_ = 102;
v___x_1579_ = lean_uint32_dec_le(v_x_1569_, v___x_1578_);
if (v___x_1579_ == 0)
{
goto v___jp_1570_;
}
else
{
return v___x_1579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed(lean_object* v_x_1584_){
_start:
{
uint32_t v_x_2703__boxed_1585_; uint8_t v_res_1586_; lean_object* v_r_1587_; 
v_x_2703__boxed_1585_ = lean_unbox_uint32(v_x_1584_);
lean_dec(v_x_1584_);
v_res_1586_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(v_x_2703__boxed_1585_);
v_r_1587_ = lean_box(v_res_1586_);
return v_r_1587_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(lean_object* v___x_1588_, lean_object* v_line_1589_, lean_object* v___x_1590_, lean_object* v___x_1591_, lean_object* v_a_1592_, lean_object* v_b_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_box(0);
switch(lean_obj_tag(v_a_1592_))
{
case 0:
{
lean_object* v_pos_1595_; lean_object* v___x_1596_; 
v_pos_1595_ = lean_ctor_get(v_a_1592_, 0);
lean_inc(v_pos_1595_);
lean_dec_ref_known(v_a_1592_, 1);
v___x_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1596_, 0, v_pos_1595_);
return v___x_1596_;
}
case 1:
{
lean_object* v_pos_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1608_; 
v_pos_1597_ = lean_ctor_get(v_a_1592_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_a_1592_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1599_ = v_a_1592_;
v_isShared_1600_ = v_isSharedCheck_1608_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_pos_1597_);
lean_dec(v_a_1592_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1608_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1601_ = lean_nat_add(v___x_1588_, v_pos_1597_);
lean_dec(v_pos_1597_);
v___x_1602_ = lean_string_utf8_next_fast(v_line_1589_, v___x_1601_);
lean_dec(v___x_1601_);
v___x_1603_ = lean_nat_sub(v___x_1602_, v___x_1588_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1603_);
v___x_1605_ = v___x_1599_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
v_a_1592_ = v___x_1605_;
v_b_1593_ = v___x_1594_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1609_; lean_object* v_table_1610_; lean_object* v_stackPos_1611_; lean_object* v_needlePos_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1667_; 
v_needle_1609_ = lean_ctor_get(v_a_1592_, 0);
v_table_1610_ = lean_ctor_get(v_a_1592_, 1);
v_stackPos_1611_ = lean_ctor_get(v_a_1592_, 2);
v_needlePos_1612_ = lean_ctor_get(v_a_1592_, 3);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_a_1592_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1614_ = v_a_1592_;
v_isShared_1615_ = v_isSharedCheck_1667_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_needlePos_1612_);
lean_inc(v_stackPos_1611_);
lean_inc(v_table_1610_);
lean_inc(v_needle_1609_);
lean_dec(v_a_1592_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1667_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v_str_1616_; lean_object* v_startInclusive_1617_; lean_object* v_endExclusive_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v_str_1616_ = lean_ctor_get(v_needle_1609_, 0);
v_startInclusive_1617_ = lean_ctor_get(v_needle_1609_, 1);
v_endExclusive_1618_ = lean_ctor_get(v_needle_1609_, 2);
v___x_1619_ = lean_nat_sub(v_stackPos_1611_, v_needlePos_1612_);
v___x_1620_ = lean_nat_sub(v_endExclusive_1618_, v_startInclusive_1617_);
v___x_1621_ = lean_nat_add(v___x_1619_, v___x_1620_);
v___x_1622_ = lean_nat_sub(v___x_1591_, v___x_1588_);
v___x_1623_ = lean_nat_dec_le(v___x_1621_, v___x_1622_);
lean_dec(v___x_1621_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
lean_dec(v___x_1620_);
lean_del_object(v___x_1614_);
lean_dec(v_needlePos_1612_);
lean_dec(v_stackPos_1611_);
lean_dec_ref(v_table_1610_);
lean_dec_ref(v_needle_1609_);
v___x_1624_ = lean_unsigned_to_nat(1u);
v___x_1625_ = lean_nat_add(v___x_1619_, v___x_1624_);
lean_dec(v___x_1619_);
v___x_1626_ = lean_nat_dec_le(v___x_1625_, v___x_1622_);
lean_dec(v___x_1622_);
lean_dec(v___x_1625_);
if (v___x_1626_ == 0)
{
lean_inc(v_b_1593_);
return v_b_1593_;
}
else
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_box(3);
v_a_1592_ = v___x_1627_;
v_b_1593_ = v___x_1594_;
goto _start;
}
}
else
{
lean_object* v___x_1629_; uint8_t v_stackByte_1630_; lean_object* v___x_1631_; uint8_t v_patByte_1632_; uint8_t v___x_1633_; 
lean_dec(v___x_1622_);
lean_dec(v___x_1619_);
v___x_1629_ = lean_nat_add(v___x_1588_, v_stackPos_1611_);
v_stackByte_1630_ = lean_string_get_byte_fast(v_line_1589_, v___x_1629_);
v___x_1631_ = lean_nat_add(v_startInclusive_1617_, v_needlePos_1612_);
v_patByte_1632_ = lean_string_get_byte_fast(v_str_1616_, v___x_1631_);
v___x_1633_ = lean_uint8_dec_eq(v_stackByte_1630_, v_patByte_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; uint8_t v_decide_1635_; 
lean_dec(v___x_1620_);
v___x_1634_ = lean_unsigned_to_nat(0u);
v_decide_1635_ = lean_nat_dec_eq(v_needlePos_1612_, v___x_1634_);
if (v_decide_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v_newNeedlePos_1638_; uint8_t v___x_1639_; 
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = lean_nat_sub(v_needlePos_1612_, v___x_1636_);
lean_dec(v_needlePos_1612_);
v_newNeedlePos_1638_ = lean_array_fget_borrowed(v_table_1610_, v___x_1637_);
lean_dec(v___x_1637_);
v___x_1639_ = lean_nat_dec_eq(v_newNeedlePos_1638_, v___x_1634_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1641_; 
lean_inc(v_newNeedlePos_1638_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 3, v_newNeedlePos_1638_);
v___x_1641_ = v___x_1614_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_needle_1609_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_table_1610_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_stackPos_1611_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_newNeedlePos_1638_);
v___x_1641_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
v_a_1592_ = v___x_1641_;
v_b_1593_ = v___x_1594_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1644_; lean_object* v___x_1646_; 
v_nextStackPos_1644_ = l_String_Slice_posGE___redArg(v___x_1590_, v_stackPos_1611_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 3, v___x_1634_);
lean_ctor_set(v___x_1614_, 2, v_nextStackPos_1644_);
v___x_1646_ = v___x_1614_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_needle_1609_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_table_1610_);
lean_ctor_set(v_reuseFailAlloc_1648_, 2, v_nextStackPos_1644_);
lean_ctor_set(v_reuseFailAlloc_1648_, 3, v___x_1634_);
v___x_1646_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
v_a_1592_ = v___x_1646_;
v_b_1593_ = v___x_1594_;
goto _start;
}
}
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v_nextStackPos_1651_; lean_object* v___x_1653_; 
lean_dec(v_needlePos_1612_);
v___x_1649_ = lean_unsigned_to_nat(1u);
v___x_1650_ = lean_nat_add(v_stackPos_1611_, v___x_1649_);
lean_dec(v_stackPos_1611_);
v_nextStackPos_1651_ = l_String_Slice_posGE___redArg(v___x_1590_, v___x_1650_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 3, v___x_1634_);
lean_ctor_set(v___x_1614_, 2, v_nextStackPos_1651_);
v___x_1653_ = v___x_1614_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_needle_1609_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_table_1610_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_nextStackPos_1651_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v___x_1634_);
v___x_1653_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
v_a_1592_ = v___x_1653_;
v_b_1593_ = v___x_1594_;
goto _start;
}
}
}
else
{
lean_object* v___x_1656_; lean_object* v_nextStackPos_1657_; lean_object* v_nextNeedlePos_1658_; uint8_t v_decide_1659_; 
v___x_1656_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1657_ = lean_nat_add(v_stackPos_1611_, v___x_1656_);
lean_dec(v_stackPos_1611_);
v_nextNeedlePos_1658_ = lean_nat_add(v_needlePos_1612_, v___x_1656_);
lean_dec(v_needlePos_1612_);
v_decide_1659_ = lean_nat_dec_eq(v_nextNeedlePos_1658_, v___x_1620_);
lean_dec(v___x_1620_);
if (v_decide_1659_ == 0)
{
lean_object* v___x_1661_; 
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 3, v_nextNeedlePos_1658_);
lean_ctor_set(v___x_1614_, 2, v_nextStackPos_1657_);
v___x_1661_ = v___x_1614_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_needle_1609_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_table_1610_);
lean_ctor_set(v_reuseFailAlloc_1663_, 2, v_nextStackPos_1657_);
lean_ctor_set(v_reuseFailAlloc_1663_, 3, v_nextNeedlePos_1658_);
v___x_1661_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
v_a_1592_ = v___x_1661_;
goto _start;
}
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_del_object(v___x_1614_);
lean_dec_ref(v_table_1610_);
lean_dec_ref(v_needle_1609_);
v___x_1664_ = lean_nat_sub(v_nextStackPos_1657_, v_nextNeedlePos_1658_);
lean_dec(v_nextNeedlePos_1658_);
lean_dec(v_nextStackPos_1657_);
v___x_1665_ = l_String_Slice_pos_x21(v___x_1590_, v___x_1664_);
lean_dec(v___x_1664_);
v___x_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
}
}
}
default: 
{
lean_inc(v_b_1593_);
return v_b_1593_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg___boxed(lean_object* v___x_1668_, lean_object* v_line_1669_, lean_object* v___x_1670_, lean_object* v___x_1671_, lean_object* v_a_1672_, lean_object* v_b_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1668_, v_line_1669_, v___x_1670_, v___x_1671_, v_a_1672_, v_b_1673_);
lean_dec(v_b_1673_);
lean_dec(v___x_1671_);
lean_dec_ref(v___x_1670_);
lean_dec_ref(v_line_1669_);
lean_dec(v___x_1668_);
return v_res_1674_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3));
v___x_1680_ = lean_string_utf8_byte_size(v___x_1679_);
return v___x_1680_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4);
v___x_1683_ = lean_nat_dec_eq(v___x_1682_, v___x_1681_);
return v___x_1683_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1684_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4);
v___x_1685_ = lean_unsigned_to_nat(0u);
v___x_1686_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3));
v___x_1687_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v___x_1685_);
lean_ctor_set(v___x_1687_, 2, v___x_1684_);
return v___x_1687_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6);
v___x_1689_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1688_);
return v___x_1689_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7);
v___x_1692_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6);
v___x_1693_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v___x_1691_);
lean_ctor_set(v___x_1693_, 2, v___x_1690_);
lean_ctor_set(v___x_1693_, 3, v___x_1690_);
return v___x_1693_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2));
v___x_1695_ = lean_string_utf8_byte_size(v___x_1694_);
return v___x_1695_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
v___x_1698_ = lean_nat_dec_eq(v___x_1697_, v___x_1696_);
return v___x_1698_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1699_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
v___x_1700_ = lean_unsigned_to_nat(0u);
v___x_1701_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2));
v___x_1702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
lean_ctor_set(v___x_1702_, 1, v___x_1700_);
lean_ctor_set(v___x_1702_, 2, v___x_1699_);
return v___x_1702_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11);
v___x_1704_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1703_);
return v___x_1704_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1705_ = lean_unsigned_to_nat(0u);
v___x_1706_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12);
v___x_1707_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11);
v___x_1708_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v___x_1706_);
lean_ctor_set(v___x_1708_, 2, v___x_1705_);
lean_ctor_set(v___x_1708_, 3, v___x_1705_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(lean_object* v_line_1709_){
_start:
{
lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___x_1729_; lean_object* v___y_1731_; uint8_t v___x_1746_; 
v___f_1717_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0));
v___f_1718_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1));
v___x_1719_ = lean_unsigned_to_nat(0u);
v___x_1720_ = lean_string_utf8_byte_size(v_line_1709_);
lean_inc_ref(v_line_1709_);
v___x_1729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1729_, 0, v_line_1709_);
lean_ctor_set(v___x_1729_, 1, v___x_1719_);
lean_ctor_set(v___x_1729_, 2, v___x_1720_);
v___x_1746_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13);
v___y_1731_ = v___x_1747_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1748_; 
v___x_1748_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1731_ = v___x_1748_;
goto v___jp_1730_;
}
v___jp_1710_:
{
uint8_t v_decide_1713_; 
v_decide_1713_ = lean_nat_dec_eq(v___y_1712_, v___y_1711_);
if (v_decide_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1709_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v_line_1709_);
v___x_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; 
lean_dec(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v_line_1709_);
v___x_1716_ = lean_box(0);
return v___x_1716_;
}
}
v___jp_1721_:
{
lean_object* v___x_1726_; 
lean_inc(v___y_1725_);
v___x_1726_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___y_1722_, v_line_1709_, v___y_1724_, v___x_1720_, v___y_1725_, v___y_1723_);
lean_dec_ref(v___y_1724_);
if (lean_obj_tag(v___x_1726_) == 0)
{
v___y_1711_ = v___y_1722_;
v___y_1712_ = v___x_1720_;
goto v___jp_1710_;
}
else
{
lean_object* v_val_1727_; lean_object* v___x_1728_; 
v_val_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_val_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = lean_nat_add(v___y_1722_, v_val_1727_);
lean_dec(v_val_1727_);
v___y_1711_ = v___y_1722_;
v___y_1712_ = v___x_1728_;
goto v___jp_1710_;
}
}
v___jp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = lean_box(0);
lean_inc(v___y_1731_);
v___x_1733_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_line_1709_, v___x_1729_, v___x_1720_, v___y_1731_, v___x_1732_);
lean_dec_ref_known(v___x_1729_, 3);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_dec_ref(v_line_1709_);
return v___x_1732_;
}
else
{
lean_object* v_val_1734_; uint8_t v_decide_1735_; 
v_val_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_val_1734_);
lean_dec_ref_known(v___x_1733_, 1);
v_decide_1735_ = lean_nat_dec_eq(v_val_1734_, v___x_1720_);
if (v_decide_1735_ == 0)
{
lean_object* v___x_1736_; uint8_t v_decide_1737_; 
v___x_1736_ = lean_string_utf8_next_fast(v_line_1709_, v_val_1734_);
lean_dec(v_val_1734_);
v_decide_1737_ = lean_nat_dec_eq(v___x_1736_, v___x_1720_);
if (v_decide_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; uint8_t v_decide_1741_; 
v___x_1738_ = lean_string_utf8_next_fast(v_line_1709_, v___x_1736_);
v___x_1739_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1709_, v___x_1738_, v___f_1718_);
v___x_1740_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1709_, v___x_1739_, v___f_1717_);
v_decide_1741_ = lean_nat_dec_eq(v___x_1740_, v___x_1720_);
if (v_decide_1741_ == 0)
{
lean_object* v___x_1742_; uint8_t v___x_1743_; 
lean_inc(v___x_1740_);
lean_inc_ref(v_line_1709_);
v___x_1742_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1742_, 0, v_line_1709_);
lean_ctor_set(v___x_1742_, 1, v___x_1740_);
lean_ctor_set(v___x_1742_, 2, v___x_1720_);
v___x_1743_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8);
v___y_1722_ = v___x_1740_;
v___y_1723_ = v___x_1732_;
v___y_1724_ = v___x_1742_;
v___y_1725_ = v___x_1744_;
goto v___jp_1721_;
}
else
{
lean_object* v___x_1745_; 
v___x_1745_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1722_ = v___x_1740_;
v___y_1723_ = v___x_1732_;
v___y_1724_ = v___x_1742_;
v___y_1725_ = v___x_1745_;
goto v___jp_1721_;
}
}
else
{
lean_dec(v___x_1740_);
lean_dec_ref(v_line_1709_);
return v___x_1732_;
}
}
else
{
lean_dec_ref(v_line_1709_);
return v___x_1732_;
}
}
else
{
lean_dec(v_val_1734_);
lean_dec_ref(v_line_1709_);
return v___x_1732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(lean_object* v___x_1749_, lean_object* v_line_1750_, lean_object* v___x_1751_, lean_object* v___x_1752_, lean_object* v_inst_1753_, lean_object* v_R_1754_, lean_object* v_a_1755_, lean_object* v_b_1756_, lean_object* v_c_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1749_, v_line_1750_, v___x_1751_, v___x_1752_, v_a_1755_, v_b_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___boxed(lean_object* v___x_1759_, lean_object* v_line_1760_, lean_object* v___x_1761_, lean_object* v___x_1762_, lean_object* v_inst_1763_, lean_object* v_R_1764_, lean_object* v_a_1765_, lean_object* v_b_1766_, lean_object* v_c_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(v___x_1759_, v_line_1760_, v___x_1761_, v___x_1762_, v_inst_1763_, v_R_1764_, v_a_1765_, v_b_1766_, v_c_1767_);
lean_dec(v_b_1766_);
lean_dec(v___x_1762_);
lean_dec_ref(v___x_1761_);
lean_dec_ref(v_line_1760_);
lean_dec(v___x_1759_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(lean_object* v_line_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(v_line_1769_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v___x_1771_; 
v___x_1771_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(v_line_1769_);
return v___x_1771_;
}
else
{
lean_dec_ref(v_line_1769_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleBtLine(lean_object* v_line_1772_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(v_line_1772_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_box(0);
return v___x_1774_;
}
else
{
lean_object* v_val_1775_; lean_object* v_snd_1776_; lean_object* v_fst_1777_; lean_object* v_fst_1778_; lean_object* v_snd_1779_; lean_object* v___x_1780_; 
v_val_1775_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_val_1775_);
lean_dec_ref_known(v___x_1773_, 1);
v_snd_1776_ = lean_ctor_get(v_val_1775_, 1);
lean_inc(v_snd_1776_);
v_fst_1777_ = lean_ctor_get(v_val_1775_, 0);
lean_inc(v_fst_1777_);
lean_dec(v_val_1775_);
v_fst_1778_ = lean_ctor_get(v_snd_1776_, 0);
lean_inc(v_fst_1778_);
v_snd_1779_ = lean_ctor_get(v_snd_1776_, 1);
lean_inc(v_snd_1779_);
lean_dec(v_snd_1776_);
v___x_1780_ = l_Lean_Name_Demangle_demangleSymbol(v_fst_1778_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_dec(v_snd_1779_);
lean_dec(v_fst_1777_);
return v___x_1780_;
}
else
{
lean_object* v_val_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1790_; 
v_val_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1790_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_val_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1790_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1785_ = lean_string_append(v_fst_1777_, v_val_1781_);
lean_dec(v_val_1781_);
v___x_1786_ = lean_string_append(v___x_1785_, v_snd_1779_);
lean_dec(v_snd_1779_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1786_);
v___x_1788_ = v___x_1783_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_demangle_bt_line_cstr(lean_object* v_line_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_Name_Demangle_demangleBtLine(v_line_1791_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v___x_1793_; 
v___x_1793_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_1793_;
}
else
{
lean_object* v_val_1794_; 
v_val_1794_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_val_1794_);
lean_dec_ref_known(v___x_1792_, 1);
return v_val_1794_;
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
