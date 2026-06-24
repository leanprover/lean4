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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedNamePart_default;
lean_object* lean_array_get_size(lean_object*);
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = lean_string_utf8_byte_size(v_s_65_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_69_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_69_, 0, v_s_65_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
v___x_70_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(v___x_69_, v___x_67_);
lean_dec_ref_known(v___x_69_, 3);
v___x_71_ = lean_nat_dec_eq(v___x_70_, v___x_66_);
lean_dec(v___x_70_);
return v___x_71_;
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
lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_451_; 
v_fst_426_ = lean_ctor_get(v_b_417_, 0);
v_snd_427_ = lean_ctor_get(v_b_417_, 1);
v_isSharedCheck_451_ = !lean_is_exclusive(v_b_417_);
if (v_isSharedCheck_451_ == 0)
{
v___x_429_ = v_b_417_;
v_isShared_430_ = v_isSharedCheck_451_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snd_427_);
lean_inc(v_fst_426_);
lean_dec(v_b_417_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_451_;
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
lean_object* v_val_442_; uint8_t v___x_443_; 
v_val_442_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_val_442_);
lean_dec_ref_known(v___x_433_, 1);
v___x_443_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_snd_427_, v_val_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = lean_array_push(v_snd_427_, v_val_442_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_444_);
v___x_446_ = v___x_429_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_fst_426_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_444_);
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
lean_object* v___x_449_; 
lean_dec(v_val_442_);
if (v_isShared_430_ == 0)
{
v___x_449_ = v___x_429_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_fst_426_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_snd_427_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
v_a_422_ = v___x_449_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg___boxed(lean_object* v_comps_452_, lean_object* v_range_453_, lean_object* v_b_454_, lean_object* v_i_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_452_, v_range_453_, v_b_454_, v_i_455_);
lean_dec_ref(v_range_453_);
lean_dec_ref(v_comps_452_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(lean_object* v_comps_461_){
_start:
{
lean_object* v_begin___463_; lean_object* v_begin___479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___y_483_; lean_object* v___y_488_; uint8_t v___x_491_; 
v_begin___479_ = lean_unsigned_to_nat(0u);
v___x_480_ = lean_unsigned_to_nat(3u);
v___x_481_ = lean_array_get_size(v_comps_461_);
v___x_491_ = lean_nat_dec_le(v___x_480_, v___x_481_);
if (v___x_491_ == 0)
{
v___y_483_ = v___x_491_;
goto v___jp_482_;
}
else
{
uint8_t v___x_492_; 
v___x_492_ = lean_nat_dec_lt(v_begin___479_, v___x_481_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
v___x_493_ = lean_box(0);
v___y_488_ = v___x_493_;
goto v___jp_487_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_array_fget_borrowed(v_comps_461_, v_begin___479_);
lean_inc(v___x_494_);
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
v___y_488_ = v___x_495_;
goto v___jp_487_;
}
}
v___jp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v_fst_469_; lean_object* v_snd_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_478_; 
v___x_464_ = lean_array_get_size(v_comps_461_);
v___x_465_ = lean_unsigned_to_nat(1u);
lean_inc(v_begin___463_);
v___x_466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_466_, 0, v_begin___463_);
lean_ctor_set(v___x_466_, 1, v___x_464_);
lean_ctor_set(v___x_466_, 2, v___x_465_);
v___x_467_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1));
v___x_468_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_461_, v___x_466_, v___x_467_, v_begin___463_);
lean_dec_ref_known(v___x_466_, 3);
v_fst_469_ = lean_ctor_get(v___x_468_, 0);
v_snd_470_ = lean_ctor_get(v___x_468_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_478_ == 0)
{
v___x_472_ = v___x_468_;
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_snd_470_);
lean_inc(v_fst_469_);
lean_dec(v___x_468_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_fst_469_);
lean_dec(v_fst_469_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_474_);
v___x_476_ = v___x_472_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_snd_470_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
v___jp_482_:
{
if (v___y_483_ == 0)
{
v_begin___463_ = v_begin___479_;
goto v___jp_462_;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v___x_481_);
lean_ctor_set(v___x_485_, 2, v___x_484_);
v___x_486_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_481_, v_comps_461_, v___x_485_, v_begin___479_, v___x_484_);
lean_dec_ref_known(v___x_485_, 3);
v_begin___463_ = v___x_486_;
goto v___jp_462_;
}
}
v___jp_487_:
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2));
v___x_490_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_488_, v___x_489_);
lean_dec(v___y_488_);
v___y_483_ = v___x_490_;
goto v___jp_482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___boxed(lean_object* v_comps_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(v_comps_496_);
lean_dec_ref(v_comps_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1(lean_object* v_comps_498_, lean_object* v_range_499_, lean_object* v_b_500_, lean_object* v_i_501_, lean_object* v_hs_502_, lean_object* v_hl_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_498_, v_range_499_, v_b_500_, v_i_501_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___boxed(lean_object* v_comps_505_, lean_object* v_range_506_, lean_object* v_b_507_, lean_object* v_i_508_, lean_object* v_hs_509_, lean_object* v_hl_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1(v_comps_505_, v_range_506_, v_b_507_, v_i_508_, v_hs_509_, v_hl_510_);
lean_dec_ref(v_range_506_);
lean_dec_ref(v_comps_505_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2(lean_object* v___x_512_, lean_object* v_comps_513_, lean_object* v_range_514_, lean_object* v_b_515_, lean_object* v_i_516_, lean_object* v_hs_517_, lean_object* v_hl_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_512_, v_comps_513_, v_range_514_, v_b_515_, v_i_516_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___boxed(lean_object* v___x_520_, lean_object* v_comps_521_, lean_object* v_range_522_, lean_object* v_b_523_, lean_object* v_i_524_, lean_object* v_hs_525_, lean_object* v_hl_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2(v___x_520_, v_comps_521_, v_range_522_, v_b_523_, v_i_524_, v_hs_525_, v_hl_526_);
lean_dec(v_b_523_);
lean_dec_ref(v_range_522_);
lean_dec_ref(v_comps_521_);
lean_dec(v___x_520_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(lean_object* v___x_531_, lean_object* v_range_532_, lean_object* v_b_533_, lean_object* v_i_534_){
_start:
{
lean_object* v_stop_535_; lean_object* v_step_536_; uint8_t v___x_537_; 
v_stop_535_ = lean_ctor_get(v_range_532_, 1);
v_step_536_ = lean_ctor_get(v_range_532_, 2);
v___x_537_ = lean_nat_dec_lt(v_i_534_, v_stop_535_);
if (v___x_537_ == 0)
{
lean_dec(v_i_534_);
lean_inc(v_b_533_);
return v_b_533_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_538_ = l_Lean_instInhabitedNamePart_default;
v___x_539_ = lean_array_get_borrowed(v___x_538_, v___x_531_, v_i_534_);
v___x_540_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1));
v___x_541_ = l_Lean_instBEqNamePart_beq(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
v___x_542_ = lean_nat_add(v_i_534_, v_step_536_);
lean_dec(v_i_534_);
v_i_534_ = v___x_542_;
goto _start;
}
else
{
lean_object* v___x_544_; 
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v_i_534_);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___boxed(lean_object* v___x_545_, lean_object* v_range_546_, lean_object* v_b_547_, lean_object* v_i_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_545_, v_range_546_, v_b_547_, v_i_548_);
lean_dec(v_b_547_);
lean_dec_ref(v_range_546_);
lean_dec_ref(v___x_545_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(lean_object* v___x_550_, lean_object* v_as_551_, size_t v_sz_552_, size_t v_i_553_, lean_object* v_b_554_){
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
lean_object* v_a_561_; lean_object* v___x_562_; lean_object* v_name_565_; lean_object* v_flags_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_a_561_ = lean_array_uget_borrowed(v_as_551_, v_i_553_);
v___x_562_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(v_a_561_);
v_name_565_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_name_565_);
v_flags_566_ = lean_ctor_get(v___x_562_, 1);
lean_inc_ref(v_flags_566_);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_string_utf8_byte_size(v_name_565_);
lean_dec_ref(v_name_565_);
v___x_569_ = lean_nat_dec_eq(v___x_568_, v___x_567_);
if (v___x_569_ == 0)
{
lean_dec_ref(v_flags_566_);
goto v___jp_563_;
}
else
{
uint8_t v___x_570_; 
v___x_570_ = lean_nat_dec_eq(v___x_550_, v___x_567_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_array_get_size(v_flags_566_);
lean_dec_ref(v_flags_566_);
v___x_572_ = lean_nat_dec_eq(v___x_571_, v___x_567_);
if (v___x_572_ == 0)
{
goto v___jp_563_;
}
else
{
lean_dec_ref(v___x_562_);
v_a_556_ = v_b_554_;
goto v___jp_555_;
}
}
else
{
lean_dec_ref(v_flags_566_);
goto v___jp_563_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5___boxed(lean_object* v___x_573_, lean_object* v_as_574_, lean_object* v_sz_575_, lean_object* v_i_576_, lean_object* v_b_577_){
_start:
{
size_t v_sz_boxed_578_; size_t v_i_boxed_579_; lean_object* v_res_580_; 
v_sz_boxed_578_ = lean_unbox_usize(v_sz_575_);
lean_dec(v_sz_575_);
v_i_boxed_579_ = lean_unbox_usize(v_i_576_);
lean_dec(v_i_576_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_573_, v_as_574_, v_sz_boxed_578_, v_i_boxed_579_, v_b_577_);
lean_dec_ref(v_as_574_);
lean_dec(v___x_573_);
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
lean_object* v_snd_759_; lean_object* v_fst_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_819_; 
v_snd_759_ = lean_ctor_get(v_a_758_, 1);
v_fst_760_ = lean_ctor_get(v_a_758_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_a_758_);
if (v_isSharedCheck_819_ == 0)
{
v___x_762_ = v_a_758_;
v_isShared_763_ = v_isSharedCheck_819_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_snd_759_);
lean_inc(v_fst_760_);
lean_dec(v_a_758_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_819_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_fst_764_; lean_object* v_snd_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_818_; 
v_fst_764_ = lean_ctor_get(v_snd_759_, 0);
v_snd_765_ = lean_ctor_get(v_snd_759_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_snd_759_);
if (v_isSharedCheck_818_ == 0)
{
v___x_767_ = v_snd_759_;
v_isShared_768_ = v_isSharedCheck_818_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_snd_765_);
lean_inc(v_fst_764_);
lean_dec(v_snd_759_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_818_;
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
lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_nat_dec_eq(v___x_757_, v___x_777_);
v___x_816_ = lean_array_get_size(v_fst_760_);
v___x_817_ = lean_nat_dec_eq(v___x_816_, v___x_777_);
if (v___x_817_ == 0)
{
lean_del_object(v___x_767_);
lean_del_object(v___x_762_);
goto v___jp_779_;
}
else
{
if (v___x_778_ == 0)
{
goto v___jp_769_;
}
else
{
lean_del_object(v___x_767_);
lean_del_object(v___x_762_);
goto v___jp_779_;
}
}
v___jp_779_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_780_ = l_Lean_instInhabitedNamePart_default;
v___x_781_ = lean_array_get_size(v_fst_760_);
v___x_782_ = lean_unsigned_to_nat(1u);
v___x_783_ = lean_nat_sub(v___x_781_, v___x_782_);
v___x_784_ = lean_array_get_borrowed(v___x_780_, v_fst_760_, v___x_783_);
lean_dec(v___x_783_);
lean_inc(v___x_784_);
v___x_785_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_784_);
if (lean_obj_tag(v___x_785_) == 0)
{
if (lean_obj_tag(v___x_784_) == 1)
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = lean_unsigned_to_nat(2u);
v___x_787_ = lean_nat_dec_le(v___x_786_, v___x_781_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec(v_snd_765_);
v___x_788_ = lean_box(v___x_778_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_fst_764_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_fst_760_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v_a_758_ = v___x_790_;
goto _start;
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = lean_nat_sub(v___x_781_, v___x_786_);
v___x_793_ = lean_array_get_borrowed(v___x_780_, v_fst_760_, v___x_792_);
lean_dec(v___x_792_);
lean_inc(v___x_793_);
v___x_794_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_793_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec(v_snd_765_);
v___x_795_ = lean_box(v___x_778_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_fst_764_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_fst_760_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v_a_758_ = v___x_797_;
goto _start;
}
else
{
lean_object* v_val_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_val_799_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v___x_794_, 1);
v___x_800_ = lean_array_push(v_fst_764_, v_val_799_);
v___x_801_ = lean_array_pop(v_fst_760_);
v___x_802_ = lean_array_pop(v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_800_);
lean_ctor_set(v___x_803_, 1, v_snd_765_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v_a_758_ = v___x_804_;
goto _start;
}
}
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec(v_snd_765_);
v___x_806_ = lean_box(v___x_778_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_fst_764_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v_fst_760_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v_a_758_ = v___x_808_;
goto _start;
}
}
else
{
lean_object* v_val_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_val_810_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_val_810_);
lean_dec_ref_known(v___x_785_, 1);
v___x_811_ = lean_array_push(v_fst_764_, v_val_810_);
v___x_812_ = lean_array_pop(v_fst_760_);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v_snd_765_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v_a_758_ = v___x_814_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg___boxed(lean_object* v___x_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_820_, v_a_821_);
lean_dec(v___x_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(lean_object* v___x_828_, lean_object* v_as_829_, size_t v_sz_830_, size_t v_i_831_, lean_object* v_b_832_){
_start:
{
lean_object* v_a_834_; lean_object* v___y_839_; lean_object* v___y_840_; uint8_t v___x_852_; 
v___x_852_ = lean_usize_dec_lt(v_i_831_, v_sz_830_);
if (v___x_852_ == 0)
{
return v_b_832_;
}
else
{
lean_object* v_a_853_; lean_object* v_name_854_; lean_object* v___x_855_; uint8_t v___x_856_; lean_object* v___y_858_; lean_object* v___x_865_; uint8_t v___x_866_; 
v_a_853_ = lean_array_uget_borrowed(v_as_829_, v_i_831_);
v_name_854_ = lean_ctor_get(v_a_853_, 0);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_nat_dec_eq(v___x_828_, v___x_855_);
v___x_865_ = lean_string_utf8_byte_size(v_name_854_);
v___x_866_ = lean_nat_dec_eq(v___x_865_, v___x_855_);
if (v___x_866_ == 0)
{
lean_inc_ref(v_name_854_);
v___y_858_ = v_name_854_;
goto v___jp_857_;
}
else
{
lean_object* v___x_867_; 
v___x_867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_858_ = v___x_867_;
goto v___jp_857_;
}
v___jp_857_:
{
lean_object* v_flags_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_flags_859_ = lean_ctor_get(v_a_853_, 1);
v___x_860_ = lean_array_get_size(v_flags_859_);
v___x_861_ = lean_nat_dec_eq(v___x_860_, v___x_855_);
if (v___x_861_ == 0)
{
lean_inc_ref(v_flags_859_);
v___y_839_ = v___y_858_;
v___y_840_ = v_flags_859_;
goto v___jp_838_;
}
else
{
if (v___x_856_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_863_ = lean_string_append(v_b_832_, v___x_862_);
v___x_864_ = lean_string_append(v___x_863_, v___y_858_);
lean_dec_ref(v___y_858_);
v_a_834_ = v___x_864_;
goto v___jp_833_;
}
else
{
lean_inc_ref(v_flags_859_);
v___y_839_ = v___y_858_;
v___y_840_ = v_flags_859_;
goto v___jp_838_;
}
}
}
}
v___jp_833_:
{
size_t v___x_835_; size_t v___x_836_; 
v___x_835_ = ((size_t)1ULL);
v___x_836_ = lean_usize_add(v_i_831_, v___x_835_);
v_i_831_ = v___x_836_;
v_b_832_ = v_a_834_;
goto _start;
}
v___jp_838_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_842_ = lean_string_append(v_b_832_, v___x_841_);
v___x_843_ = lean_string_append(v___x_842_, v___y_839_);
lean_dec_ref(v___y_839_);
v___x_844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1));
v___x_845_ = lean_string_append(v___x_843_, v___x_844_);
v___x_846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
v___x_847_ = lean_array_to_list(v___y_840_);
v___x_848_ = l_String_intercalate(v___x_846_, v___x_847_);
v___x_849_ = lean_string_append(v___x_845_, v___x_848_);
lean_dec_ref(v___x_848_);
v___x_850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_851_ = lean_string_append(v___x_849_, v___x_850_);
v_a_834_ = v___x_851_;
goto v___jp_833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___boxed(lean_object* v___x_868_, lean_object* v_as_869_, lean_object* v_sz_870_, lean_object* v_i_871_, lean_object* v_b_872_){
_start:
{
size_t v_sz_boxed_873_; size_t v_i_boxed_874_; lean_object* v_res_875_; 
v_sz_boxed_873_ = lean_unbox_usize(v_sz_870_);
lean_dec(v_sz_870_);
v_i_boxed_874_ = lean_unbox_usize(v_i_871_);
lean_dec(v_i_871_);
v_res_875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v___x_868_, v_as_869_, v_sz_boxed_873_, v_i_boxed_874_, v_b_872_);
lean_dec_ref(v_as_869_);
lean_dec(v___x_868_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(lean_object* v_components_884_){
_start:
{
lean_object* v___x_885_; lean_object* v___y_887_; lean_object* v_result_888_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___x_904_; uint8_t v___x_905_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_913_; lean_object* v_parts_914_; lean_object* v_specEntries_915_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v_entries_925_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; 
v___x_885_ = lean_array_get_size(v_components_884_);
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_nat_dec_eq(v___x_885_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_938_; lean_object* v_fst_939_; lean_object* v_snd_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_994_; 
v___x_938_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_components_884_, v___x_904_, v___x_885_);
v_fst_939_ = lean_ctor_get(v___x_938_, 0);
v_snd_940_ = lean_ctor_get(v___x_938_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_994_ == 0)
{
v___x_942_ = v___x_938_;
v_isShared_943_ = v_isSharedCheck_994_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_snd_940_);
lean_inc(v_fst_939_);
lean_dec(v___x_938_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_994_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_parts_944_; lean_object* v_flags_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v_parts_944_ = l_Array_extract___redArg(v_components_884_, v_fst_939_, v___x_885_);
v_flags_945_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1));
v___x_946_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2));
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v___x_946_);
lean_ctor_set(v___x_942_, 0, v_parts_944_);
v___x_948_ = v___x_942_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_parts_944_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_946_);
v___x_948_ = v_reuseFailAlloc_993_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; lean_object* v_fst_950_; lean_object* v_snd_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_992_; 
v___x_949_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_885_, v___x_948_);
v_fst_950_ = lean_ctor_get(v___x_949_, 0);
v_snd_951_ = lean_ctor_get(v___x_949_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_992_ == 0)
{
v___x_953_ = v___x_949_;
v_isShared_954_ = v_isSharedCheck_992_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_snd_951_);
lean_inc(v_fst_950_);
lean_dec(v___x_949_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_992_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_flags_956_; uint8_t v___x_987_; 
v___x_987_ = lean_unbox(v_snd_940_);
lean_dec(v_snd_940_);
if (v___x_987_ == 0)
{
lean_object* v_fst_988_; 
v_fst_988_ = lean_ctor_get(v_snd_951_, 0);
lean_inc(v_fst_988_);
lean_dec(v_snd_951_);
v_flags_956_ = v_fst_988_;
goto v___jp_955_;
}
else
{
lean_object* v_fst_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_fst_989_ = lean_ctor_get(v_snd_951_, 0);
lean_inc(v_fst_989_);
lean_dec(v_snd_951_);
v___x_990_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3));
v___x_991_ = lean_array_push(v_fst_989_, v___x_990_);
v_flags_956_ = v___x_991_;
goto v___jp_955_;
}
v___jp_955_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_957_ = lean_array_get_size(v_fst_950_);
v___x_958_ = lean_unsigned_to_nat(1u);
v___x_959_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_959_, 0, v___x_904_);
lean_ctor_set(v___x_959_, 1, v___x_957_);
lean_ctor_set(v___x_959_, 2, v___x_958_);
v___x_960_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_885_, v___x_959_, v_fst_950_, v___x_904_);
lean_dec(v_fst_950_);
lean_dec_ref_known(v___x_959_, 3);
v___x_961_ = lean_box(0);
v___x_962_ = lean_array_get_size(v___x_960_);
v___x_963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_963_, 0, v___x_904_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
lean_ctor_set(v___x_963_, 2, v___x_958_);
v___x_964_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_960_, v___x_963_, v___x_961_, v___x_904_);
lean_dec_ref_known(v___x_963_, 3);
if (lean_obj_tag(v___x_964_) == 1)
{
lean_object* v_val_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v_val_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc_n(v_val_965_, 2);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = l_Array_extract___redArg(v___x_960_, v___x_904_, v_val_965_);
v___x_967_ = l_Array_extract___redArg(v___x_960_, v_val_965_, v___x_962_);
lean_dec_ref(v___x_960_);
v___x_968_ = lean_array_get_size(v___x_967_);
v___x_969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_969_, 0, v___x_904_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
lean_ctor_set(v___x_969_, 2, v___x_958_);
v___x_970_ = lean_box(v___x_905_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v___x_970_);
lean_ctor_set(v___x_953_, 0, v_flags_945_);
v___x_972_ = v___x_953_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_flags_945_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_970_);
v___x_972_ = v_reuseFailAlloc_986_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_snd_976_; lean_object* v_snd_977_; lean_object* v_fst_978_; 
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_961_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v_flags_945_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_967_, v___x_885_, v___x_969_, v___x_974_, v___x_904_);
lean_dec_ref_known(v___x_969_, 3);
lean_dec_ref(v___x_967_);
v_snd_976_ = lean_ctor_get(v___x_975_, 1);
lean_inc(v_snd_976_);
v_snd_977_ = lean_ctor_get(v_snd_976_, 1);
lean_inc(v_snd_977_);
v_fst_978_ = lean_ctor_get(v_snd_976_, 0);
lean_inc(v_fst_978_);
lean_dec(v_snd_976_);
if (lean_obj_tag(v_fst_978_) == 1)
{
lean_object* v_fst_979_; lean_object* v_fst_980_; lean_object* v_val_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_fst_979_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_fst_979_);
lean_dec_ref(v___x_975_);
v_fst_980_ = lean_ctor_get(v_snd_977_, 0);
lean_inc(v_fst_980_);
lean_dec(v_snd_977_);
v_val_981_ = lean_ctor_get(v_fst_978_, 0);
lean_inc(v_val_981_);
lean_dec_ref_known(v_fst_978_, 1);
v___x_982_ = lean_array_get_size(v_val_981_);
v___x_983_ = lean_nat_dec_eq(v___x_982_, v___x_904_);
if (v___x_983_ == 0)
{
v___y_931_ = v_fst_979_;
v___y_932_ = v_flags_956_;
v___y_933_ = v___x_966_;
v___y_934_ = v_fst_980_;
v___y_935_ = v_val_981_;
v___y_936_ = v_flags_945_;
goto v___jp_930_;
}
else
{
if (v___x_905_ == 0)
{
lean_dec(v_val_981_);
v___y_921_ = v_flags_956_;
v___y_922_ = v___x_966_;
v___y_923_ = v_fst_980_;
v___y_924_ = v_flags_945_;
v_entries_925_ = v_fst_979_;
goto v___jp_920_;
}
else
{
v___y_931_ = v_fst_979_;
v___y_932_ = v_flags_956_;
v___y_933_ = v___x_966_;
v___y_934_ = v_fst_980_;
v___y_935_ = v_val_981_;
v___y_936_ = v_flags_945_;
goto v___jp_930_;
}
}
}
else
{
lean_object* v_fst_984_; lean_object* v_fst_985_; 
lean_dec(v_fst_978_);
v_fst_984_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_fst_984_);
lean_dec_ref(v___x_975_);
v_fst_985_ = lean_ctor_get(v_snd_977_, 0);
lean_inc(v_fst_985_);
lean_dec(v_snd_977_);
v___y_921_ = v_flags_956_;
v___y_922_ = v___x_966_;
v___y_923_ = v_fst_985_;
v___y_924_ = v_flags_945_;
v_entries_925_ = v_fst_984_;
goto v___jp_920_;
}
}
}
else
{
lean_dec(v___x_964_);
lean_del_object(v___x_953_);
v___y_913_ = v_flags_956_;
v_parts_914_ = v___x_960_;
v_specEntries_915_ = v_flags_945_;
goto v___jp_912_;
}
}
}
}
}
}
else
{
lean_object* v___x_995_; 
v___x_995_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_995_;
}
v___jp_886_:
{
size_t v_sz_889_; size_t v___x_890_; lean_object* v___x_891_; 
v_sz_889_ = lean_array_size(v___y_887_);
v___x_890_ = ((size_t)0ULL);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v___x_885_, v___y_887_, v_sz_889_, v___x_890_, v_result_888_);
lean_dec_ref(v___y_887_);
return v___x_891_;
}
v___jp_892_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_896_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0));
v___x_897_ = lean_string_append(v___y_895_, v___x_896_);
v___x_898_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
v___x_899_ = lean_array_to_list(v___y_893_);
v___x_900_ = l_String_intercalate(v___x_898_, v___x_899_);
v___x_901_ = lean_string_append(v___x_897_, v___x_900_);
lean_dec_ref(v___x_900_);
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_903_ = lean_string_append(v___x_901_, v___x_902_);
v___y_887_ = v___y_894_;
v_result_888_ = v___x_903_;
goto v___jp_886_;
}
v___jp_906_:
{
lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_910_ = lean_array_get_size(v___y_907_);
v___x_911_ = lean_nat_dec_eq(v___x_910_, v___x_904_);
if (v___x_911_ == 0)
{
v___y_893_ = v___y_907_;
v___y_894_ = v___y_908_;
v___y_895_ = v___y_909_;
goto v___jp_892_;
}
else
{
if (v___x_905_ == 0)
{
lean_dec_ref(v___y_907_);
v___y_887_ = v___y_908_;
v_result_888_ = v___y_909_;
goto v___jp_886_;
}
else
{
v___y_893_ = v___y_907_;
v___y_894_ = v___y_908_;
v___y_895_ = v___y_909_;
goto v___jp_892_;
}
}
}
v___jp_912_:
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = lean_array_get_size(v_parts_914_);
v___x_917_ = lean_nat_dec_eq(v___x_916_, v___x_904_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; 
v___x_918_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_parts_914_);
lean_dec_ref(v_parts_914_);
v___y_907_ = v___y_913_;
v___y_908_ = v_specEntries_915_;
v___y_909_ = v___x_918_;
goto v___jp_906_;
}
else
{
lean_object* v___x_919_; 
lean_dec_ref(v_parts_914_);
v___x_919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_907_ = v___y_913_;
v___y_908_ = v_specEntries_915_;
v___y_909_ = v___x_919_;
goto v___jp_906_;
}
}
v___jp_920_:
{
size_t v_sz_926_; size_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_sz_926_ = lean_array_size(v_entries_925_);
v___x_927_ = ((size_t)0ULL);
v___x_928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_885_, v_entries_925_, v_sz_926_, v___x_927_, v___y_924_);
lean_dec_ref(v_entries_925_);
v___x_929_ = l_Array_append___redArg(v___y_922_, v___y_923_);
lean_dec(v___y_923_);
v___y_913_ = v___y_921_;
v_parts_914_ = v___x_929_;
v_specEntries_915_ = v___x_928_;
goto v___jp_912_;
}
v___jp_930_:
{
lean_object* v___x_937_; 
v___x_937_ = lean_array_push(v___y_931_, v___y_935_);
v___y_921_ = v___y_932_;
v___y_922_ = v___y_933_;
v___y_923_ = v___y_934_;
v___y_924_ = v___y_936_;
v_entries_925_ = v___x_937_;
goto v___jp_920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___boxed(lean_object* v_components_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v_components_996_);
lean_dec_ref(v_components_996_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(lean_object* v___x_998_, lean_object* v_inst_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___redArg(v___x_998_, v_a_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___boxed(lean_object* v___x_1002_, lean_object* v_inst_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(v___x_1002_, v_inst_1003_, v_a_1004_);
lean_dec(v___x_1002_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(lean_object* v___x_1006_, lean_object* v_range_1007_, lean_object* v_b_1008_, lean_object* v_i_1009_, lean_object* v_hs_1010_, lean_object* v_hl_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_1006_, v_range_1007_, v_b_1008_, v_i_1009_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___boxed(lean_object* v___x_1013_, lean_object* v_range_1014_, lean_object* v_b_1015_, lean_object* v_i_1016_, lean_object* v_hs_1017_, lean_object* v_hl_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(v___x_1013_, v_range_1014_, v_b_1015_, v_i_1016_, v_hs_1017_, v_hl_1018_);
lean_dec_ref(v_b_1015_);
lean_dec_ref(v_range_1014_);
lean_dec(v___x_1013_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(lean_object* v___x_1020_, lean_object* v_range_1021_, lean_object* v_b_1022_, lean_object* v_i_1023_, lean_object* v_hs_1024_, lean_object* v_hl_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_1020_, v_range_1021_, v_b_1022_, v_i_1023_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___boxed(lean_object* v___x_1027_, lean_object* v_range_1028_, lean_object* v_b_1029_, lean_object* v_i_1030_, lean_object* v_hs_1031_, lean_object* v_hl_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(v___x_1027_, v_range_1028_, v_b_1029_, v_i_1030_, v_hs_1031_, v_hl_1032_);
lean_dec(v_b_1029_);
lean_dec_ref(v_range_1028_);
lean_dec_ref(v___x_1027_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(lean_object* v___x_1034_, lean_object* v___x_1035_, lean_object* v_range_1036_, lean_object* v_b_1037_, lean_object* v_i_1038_, lean_object* v_hs_1039_, lean_object* v_hl_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_1034_, v___x_1035_, v_range_1036_, v_b_1037_, v_i_1038_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___boxed(lean_object* v___x_1042_, lean_object* v___x_1043_, lean_object* v_range_1044_, lean_object* v_b_1045_, lean_object* v_i_1046_, lean_object* v_hs_1047_, lean_object* v_hl_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(v___x_1042_, v___x_1043_, v_range_1044_, v_b_1045_, v_i_1046_, v_hs_1047_, v_hl_1048_);
lean_dec_ref(v_range_1044_);
lean_dec(v___x_1043_);
lean_dec_ref(v___x_1042_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(lean_object* v_body_1050_){
_start:
{
lean_object* v_name_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_name_1051_ = l_Lean_Name_demangle(v_body_1050_);
v___x_1052_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(v_name_1051_);
lean_dec(v_name_1051_);
v___x_1053_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v___x_1052_);
lean_dec_ref(v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody___boxed(lean_object* v_body_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_body_1054_);
lean_dec_ref(v_body_1054_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(lean_object* v_s_1059_, lean_object* v___x_1060_, lean_object* v_a_1061_, lean_object* v_b_1062_){
_start:
{
lean_object* v_startInclusive_1063_; lean_object* v_endExclusive_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_startInclusive_1063_ = lean_ctor_get(v___x_1060_, 1);
v_endExclusive_1064_ = lean_ctor_get(v___x_1060_, 2);
v___x_1065_ = lean_nat_sub(v_endExclusive_1064_, v_startInclusive_1063_);
v___x_1066_ = lean_nat_dec_eq(v_a_1061_, v___x_1065_);
lean_dec(v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___y_1085_; uint8_t v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1091_; uint8_t v___y_1092_; lean_object* v___y_1093_; uint8_t v___y_1094_; uint8_t v___y_1097_; uint32_t v___x_1108_; uint32_t v___x_1109_; uint8_t v___x_1110_; 
lean_dec_ref(v_b_1062_);
v___x_1067_ = lean_box(0);
v___x_1082_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1083_ = lean_string_utf8_next_fast(v_s_1059_, v_a_1061_);
v___x_1108_ = lean_string_utf8_get_fast(v_s_1059_, v_a_1061_);
v___x_1109_ = 95;
v___x_1110_ = lean_uint32_dec_eq(v___x_1108_, v___x_1109_);
if (v___x_1110_ == 0)
{
v___y_1097_ = v___x_1110_;
goto v___jp_1096_;
}
else
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = lean_nat_dec_eq(v_a_1061_, v___x_1111_);
if (v___x_1112_ == 0)
{
v___y_1097_ = v___x_1110_;
goto v___jp_1096_;
}
else
{
lean_dec(v_a_1061_);
v_a_1061_ = v___x_1083_;
v_b_1062_ = v___x_1082_;
goto _start;
}
}
v___jp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1071_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v___y_1069_);
lean_dec_ref(v___y_1069_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___y_1070_);
v___x_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___x_1067_);
v___x_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
v___jp_1076_:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Name_demangle(v___y_1077_);
if (lean_obj_tag(v___x_1079_) == 1)
{
lean_object* v_pre_1080_; 
v_pre_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_pre_1080_);
if (lean_obj_tag(v_pre_1080_) == 0)
{
lean_object* v_str_1081_; 
lean_dec_ref(v___y_1077_);
v_str_1081_ = lean_ctor_get(v___x_1079_, 1);
lean_inc_ref(v_str_1081_);
lean_dec_ref_known(v___x_1079_, 2);
v___y_1069_ = v___y_1078_;
v___y_1070_ = v_str_1081_;
goto v___jp_1068_;
}
else
{
lean_dec(v_pre_1080_);
lean_dec_ref_known(v___x_1079_, 2);
v___y_1069_ = v___y_1078_;
v___y_1070_ = v___y_1077_;
goto v___jp_1068_;
}
}
else
{
lean_dec(v___x_1079_);
v___y_1069_ = v___y_1078_;
v___y_1070_ = v___y_1077_;
goto v___jp_1068_;
}
}
v___jp_1084_:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_Name_demangle_x3f(v___y_1087_);
if (lean_obj_tag(v___x_1088_) == 0)
{
if (v___y_1086_ == 0)
{
lean_dec_ref(v___y_1087_);
lean_dec_ref(v___y_1085_);
v_a_1061_ = v___x_1083_;
v_b_1062_ = v___x_1082_;
goto _start;
}
else
{
v___y_1077_ = v___y_1085_;
v___y_1078_ = v___y_1087_;
goto v___jp_1076_;
}
}
else
{
lean_dec_ref_known(v___x_1088_, 1);
v___y_1077_ = v___y_1085_;
v___y_1078_ = v___y_1087_;
goto v___jp_1076_;
}
}
v___jp_1090_:
{
if (v___y_1094_ == 0)
{
lean_dec_ref(v___y_1093_);
lean_dec_ref(v___y_1091_);
v_a_1061_ = v___x_1083_;
v_b_1062_ = v___x_1082_;
goto _start;
}
else
{
v___y_1085_ = v___y_1091_;
v___y_1086_ = v___y_1092_;
v___y_1087_ = v___y_1093_;
goto v___jp_1084_;
}
}
v___jp_1096_:
{
if (v___y_1097_ == 0)
{
lean_dec(v_a_1061_);
v_a_1061_ = v___x_1083_;
v_b_1062_ = v___x_1082_;
goto _start;
}
else
{
lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = lean_string_utf8_byte_size(v_s_1059_);
v___x_1100_ = lean_nat_dec_eq(v___x_1083_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = lean_string_utf8_extract(v_s_1059_, v___x_1101_, v_a_1061_);
lean_dec(v_a_1061_);
v___x_1103_ = lean_string_utf8_extract(v_s_1059_, v___x_1083_, v___x_1099_);
v___x_1104_ = l_Lean_Name_demangle_x3f(v___x_1102_);
if (lean_obj_tag(v___x_1104_) == 1)
{
lean_object* v_val_1105_; 
v_val_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_val_1105_);
lean_dec_ref_known(v___x_1104_, 1);
if (lean_obj_tag(v_val_1105_) == 1)
{
lean_object* v_pre_1106_; 
v_pre_1106_ = lean_ctor_get(v_val_1105_, 0);
lean_inc(v_pre_1106_);
lean_dec_ref_known(v_val_1105_, 2);
if (lean_obj_tag(v_pre_1106_) == 0)
{
v___y_1085_ = v___x_1102_;
v___y_1086_ = v___x_1100_;
v___y_1087_ = v___x_1103_;
goto v___jp_1084_;
}
else
{
lean_dec(v_pre_1106_);
v___y_1091_ = v___x_1102_;
v___y_1092_ = v___x_1100_;
v___y_1093_ = v___x_1103_;
v___y_1094_ = v___x_1100_;
goto v___jp_1090_;
}
}
else
{
lean_dec(v_val_1105_);
v___y_1091_ = v___x_1102_;
v___y_1092_ = v___x_1100_;
v___y_1093_ = v___x_1103_;
v___y_1094_ = v___x_1100_;
goto v___jp_1090_;
}
}
else
{
lean_dec(v___x_1104_);
v___y_1091_ = v___x_1102_;
v___y_1092_ = v___x_1100_;
v___y_1093_ = v___x_1103_;
v___y_1094_ = v___x_1100_;
goto v___jp_1090_;
}
}
else
{
lean_dec(v_a_1061_);
v_a_1061_ = v___x_1083_;
v_b_1062_ = v___x_1082_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1114_; 
lean_dec(v_a_1061_);
v___x_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_b_1062_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___boxed(lean_object* v_s_1115_, lean_object* v___x_1116_, lean_object* v_a_1117_, lean_object* v_b_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1115_, v___x_1116_, v_a_1117_, v_b_1118_);
lean_dec_ref(v___x_1116_);
lean_dec_ref(v_s_1115_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(lean_object* v_s_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1122_ = lean_string_utf8_byte_size(v_s_1120_);
lean_inc_ref(v_s_1120_);
v___x_1123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1123_, 0, v_s_1120_);
lean_ctor_set(v___x_1123_, 1, v___x_1121_);
lean_ctor_set(v___x_1123_, 2, v___x_1122_);
v___x_1124_ = lean_box(0);
v___x_1125_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1126_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1120_, v___x_1123_, v___x_1121_, v___x_1125_);
lean_dec_ref_known(v___x_1123_, 3);
lean_dec_ref(v_s_1120_);
if (lean_obj_tag(v___x_1126_) == 0)
{
return v___x_1124_;
}
else
{
lean_object* v_val_1127_; lean_object* v_fst_1128_; 
v_val_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_val_1127_);
lean_dec_ref_known(v___x_1126_, 1);
v_fst_1128_ = lean_ctor_get(v_val_1127_, 0);
lean_inc(v_fst_1128_);
lean_dec(v_val_1127_);
if (lean_obj_tag(v_fst_1128_) == 0)
{
return v___x_1124_;
}
else
{
return v_fst_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(lean_object* v_s_1129_, lean_object* v___x_1130_, lean_object* v_inst_1131_, lean_object* v_R_1132_, lean_object* v_a_1133_, lean_object* v_b_1134_, lean_object* v_c_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1129_, v___x_1130_, v_a_1133_, v_b_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___boxed(lean_object* v_s_1137_, lean_object* v___x_1138_, lean_object* v_inst_1139_, lean_object* v_R_1140_, lean_object* v_a_1141_, lean_object* v_b_1142_, lean_object* v_c_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(v_s_1137_, v___x_1138_, v_inst_1139_, v_R_1140_, v_a_1141_, v_b_1142_, v_c_1143_);
lean_dec_ref(v___x_1138_);
lean_dec_ref(v_s_1137_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(lean_object* v_s_1145_, lean_object* v___x_1146_, lean_object* v___x_1147_, lean_object* v_a_1148_, lean_object* v_b_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_box(0);
switch(lean_obj_tag(v_a_1148_))
{
case 0:
{
lean_object* v_pos_1151_; lean_object* v___x_1152_; 
v_pos_1151_ = lean_ctor_get(v_a_1148_, 0);
lean_inc(v_pos_1151_);
lean_dec_ref_known(v_a_1148_, 1);
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_pos_1151_);
return v___x_1152_;
}
case 1:
{
lean_object* v_pos_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1162_; 
v_pos_1153_ = lean_ctor_get(v_a_1148_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_a_1148_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1155_ = v_a_1148_;
v_isShared_1156_ = v_isSharedCheck_1162_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_pos_1153_);
lean_dec(v_a_1148_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1162_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1157_ = lean_string_utf8_next_fast(v_s_1145_, v_pos_1153_);
lean_dec(v_pos_1153_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set_tag(v___x_1155_, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1157_);
v___x_1159_ = v___x_1155_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
v_a_1148_ = v___x_1159_;
v_b_1149_ = v___x_1150_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1163_; lean_object* v_table_1164_; lean_object* v_stackPos_1165_; lean_object* v_needlePos_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1217_; 
v_needle_1163_ = lean_ctor_get(v_a_1148_, 0);
v_table_1164_ = lean_ctor_get(v_a_1148_, 1);
v_stackPos_1165_ = lean_ctor_get(v_a_1148_, 2);
v_needlePos_1166_ = lean_ctor_get(v_a_1148_, 3);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_a_1148_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1168_ = v_a_1148_;
v_isShared_1169_ = v_isSharedCheck_1217_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_needlePos_1166_);
lean_inc(v_stackPos_1165_);
lean_inc(v_table_1164_);
lean_inc(v_needle_1163_);
lean_dec(v_a_1148_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1217_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_str_1170_; lean_object* v_startInclusive_1171_; lean_object* v_endExclusive_1172_; lean_object* v_basePos_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v_str_1170_ = lean_ctor_get(v_needle_1163_, 0);
v_startInclusive_1171_ = lean_ctor_get(v_needle_1163_, 1);
v_endExclusive_1172_ = lean_ctor_get(v_needle_1163_, 2);
v_basePos_1173_ = lean_nat_sub(v_stackPos_1165_, v_needlePos_1166_);
v___x_1174_ = lean_nat_sub(v_endExclusive_1172_, v_startInclusive_1171_);
v___x_1175_ = lean_nat_add(v_basePos_1173_, v___x_1174_);
v___x_1176_ = lean_nat_dec_le(v___x_1175_, v___x_1147_);
lean_dec(v___x_1175_);
if (v___x_1176_ == 0)
{
uint8_t v___x_1177_; 
lean_dec(v___x_1174_);
lean_del_object(v___x_1168_);
lean_dec(v_needlePos_1166_);
lean_dec(v_stackPos_1165_);
lean_dec_ref(v_table_1164_);
lean_dec_ref(v_needle_1163_);
v___x_1177_ = lean_nat_dec_lt(v_basePos_1173_, v___x_1147_);
lean_dec(v_basePos_1173_);
if (v___x_1177_ == 0)
{
lean_inc(v_b_1149_);
return v_b_1149_;
}
else
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_box(3);
v_a_1148_ = v___x_1178_;
v_b_1149_ = v___x_1150_;
goto _start;
}
}
else
{
uint8_t v_stackByte_1180_; lean_object* v___x_1181_; uint8_t v_patByte_1182_; uint8_t v___x_1183_; 
lean_dec(v_basePos_1173_);
lean_inc(v_stackPos_1165_);
v_stackByte_1180_ = lean_string_get_byte_fast(v_s_1145_, v_stackPos_1165_);
v___x_1181_ = lean_nat_add(v_startInclusive_1171_, v_needlePos_1166_);
v_patByte_1182_ = lean_string_get_byte_fast(v_str_1170_, v___x_1181_);
v___x_1183_ = lean_uint8_dec_eq(v_stackByte_1180_, v_patByte_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; uint8_t v___x_1185_; 
lean_dec(v___x_1174_);
v___x_1184_ = lean_unsigned_to_nat(0u);
v___x_1185_ = lean_nat_dec_eq(v_needlePos_1166_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v_newNeedlePos_1188_; uint8_t v___x_1189_; 
v___x_1186_ = lean_unsigned_to_nat(1u);
v___x_1187_ = lean_nat_sub(v_needlePos_1166_, v___x_1186_);
lean_dec(v_needlePos_1166_);
v_newNeedlePos_1188_ = lean_array_fget_borrowed(v_table_1164_, v___x_1187_);
lean_dec(v___x_1187_);
v___x_1189_ = lean_nat_dec_eq(v_newNeedlePos_1188_, v___x_1184_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1191_; 
lean_inc(v_newNeedlePos_1188_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 3, v_newNeedlePos_1188_);
v___x_1191_ = v___x_1168_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_needle_1163_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_table_1164_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_stackPos_1165_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_newNeedlePos_1188_);
v___x_1191_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
v_a_1148_ = v___x_1191_;
v_b_1149_ = v___x_1150_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1194_; lean_object* v___x_1196_; 
v_nextStackPos_1194_ = l_String_Slice_posGE___redArg(v___x_1146_, v_stackPos_1165_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 3, v___x_1184_);
lean_ctor_set(v___x_1168_, 2, v_nextStackPos_1194_);
v___x_1196_ = v___x_1168_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_needle_1163_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_table_1164_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_nextStackPos_1194_);
lean_ctor_set(v_reuseFailAlloc_1198_, 3, v___x_1184_);
v___x_1196_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
v_a_1148_ = v___x_1196_;
v_b_1149_ = v___x_1150_;
goto _start;
}
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v_nextStackPos_1201_; lean_object* v___x_1203_; 
lean_dec(v_needlePos_1166_);
v___x_1199_ = lean_unsigned_to_nat(1u);
v___x_1200_ = lean_nat_add(v_stackPos_1165_, v___x_1199_);
lean_dec(v_stackPos_1165_);
v_nextStackPos_1201_ = l_String_Slice_posGE___redArg(v___x_1146_, v___x_1200_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 3, v___x_1184_);
lean_ctor_set(v___x_1168_, 2, v_nextStackPos_1201_);
v___x_1203_ = v___x_1168_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_needle_1163_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_table_1164_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_nextStackPos_1201_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v___x_1184_);
v___x_1203_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
v_a_1148_ = v___x_1203_;
v_b_1149_ = v___x_1150_;
goto _start;
}
}
}
else
{
lean_object* v___x_1206_; lean_object* v_nextStackPos_1207_; lean_object* v_nextNeedlePos_1208_; uint8_t v___x_1209_; 
v___x_1206_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1207_ = lean_nat_add(v_stackPos_1165_, v___x_1206_);
lean_dec(v_stackPos_1165_);
v_nextNeedlePos_1208_ = lean_nat_add(v_needlePos_1166_, v___x_1206_);
lean_dec(v_needlePos_1166_);
v___x_1209_ = lean_nat_dec_eq(v_nextNeedlePos_1208_, v___x_1174_);
lean_dec(v___x_1174_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1211_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 3, v_nextNeedlePos_1208_);
lean_ctor_set(v___x_1168_, 2, v_nextStackPos_1207_);
v___x_1211_ = v___x_1168_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_needle_1163_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_table_1164_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_nextStackPos_1207_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_nextNeedlePos_1208_);
v___x_1211_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
v_a_1148_ = v___x_1211_;
goto _start;
}
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_del_object(v___x_1168_);
lean_dec_ref(v_table_1164_);
lean_dec_ref(v_needle_1163_);
v___x_1214_ = lean_nat_sub(v_nextStackPos_1207_, v_nextNeedlePos_1208_);
lean_dec(v_nextNeedlePos_1208_);
lean_dec(v_nextStackPos_1207_);
v___x_1215_ = l_String_Slice_pos_x21(v___x_1146_, v___x_1214_);
lean_dec(v___x_1214_);
v___x_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
return v___x_1216_;
}
}
}
}
}
default: 
{
lean_inc(v_b_1149_);
return v_b_1149_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg___boxed(lean_object* v_s_1218_, lean_object* v___x_1219_, lean_object* v___x_1220_, lean_object* v_a_1221_, lean_object* v_b_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1218_, v___x_1219_, v___x_1220_, v_a_1221_, v_b_1222_);
lean_dec(v_b_1222_);
lean_dec(v___x_1220_);
lean_dec_ref(v___x_1219_);
lean_dec_ref(v_s_1218_);
return v_res_1223_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0));
v___x_1226_ = lean_string_utf8_byte_size(v___x_1225_);
return v___x_1226_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1);
v___x_1229_ = lean_nat_dec_eq(v___x_1228_, v___x_1227_);
return v___x_1229_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1230_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0));
v___x_1233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v___x_1231_);
lean_ctor_set(v___x_1233_, 2, v___x_1230_);
return v___x_1233_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
v___x_1235_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1234_);
return v___x_1235_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4);
v___x_1238_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
v___x_1239_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
lean_ctor_set(v___x_1239_, 1, v___x_1237_);
lean_ctor_set(v___x_1239_, 2, v___x_1236_);
lean_ctor_set(v___x_1239_, 3, v___x_1236_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(lean_object* v_s_1242_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___y_1247_; uint8_t v___x_1256_; 
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_string_utf8_byte_size(v_s_1242_);
lean_inc_ref(v_s_1242_);
v___x_1245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1245_, 0, v_s_1242_);
lean_ctor_set(v___x_1245_, 1, v___x_1243_);
lean_ctor_set(v___x_1245_, 2, v___x_1244_);
v___x_1256_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5);
v___y_1247_ = v___x_1257_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1258_; 
v___x_1258_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1247_ = v___x_1258_;
goto v___jp_1246_;
}
v___jp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_box(0);
lean_inc(v___y_1247_);
v___x_1249_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1242_, v___x_1245_, v___x_1244_, v___y_1247_, v___x_1248_);
lean_dec_ref_known(v___x_1245_, 3);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_s_1242_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
return v___x_1251_;
}
else
{
lean_object* v_val_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_val_1252_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_val_1252_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1253_ = lean_string_utf8_extract(v_s_1242_, v___x_1243_, v_val_1252_);
v___x_1254_ = lean_string_utf8_extract(v_s_1242_, v_val_1252_, v___x_1244_);
lean_dec(v_val_1252_);
lean_dec_ref(v_s_1242_);
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1253_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
return v___x_1255_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(lean_object* v_s_1259_, lean_object* v___x_1260_, lean_object* v___x_1261_, lean_object* v_inst_1262_, lean_object* v_R_1263_, lean_object* v_a_1264_, lean_object* v_b_1265_, lean_object* v_c_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1259_, v___x_1260_, v___x_1261_, v_a_1264_, v_b_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___boxed(lean_object* v_s_1268_, lean_object* v___x_1269_, lean_object* v___x_1270_, lean_object* v_inst_1271_, lean_object* v_R_1272_, lean_object* v_a_1273_, lean_object* v_b_1274_, lean_object* v_c_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(v_s_1268_, v___x_1269_, v___x_1270_, v_inst_1271_, v_R_1272_, v_a_1273_, v_b_1274_, v_c_1275_);
lean_dec(v_b_1274_);
lean_dec(v___x_1270_);
lean_dec_ref(v___x_1269_);
lean_dec_ref(v_s_1268_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(lean_object* v_s_1288_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10));
lean_inc_ref(v_s_1288_);
v___x_1405_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1288_, v___x_1404_);
if (lean_obj_tag(v___x_1405_) == 1)
{
lean_object* v_val_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1419_; 
v_val_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_val_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1410_ = lean_string_utf8_byte_size(v_val_1406_);
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = lean_nat_dec_eq(v___x_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
lean_dec_ref(v_s_1288_);
v___x_1413_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1414_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1406_);
lean_dec(v_val_1406_);
v___x_1415_ = lean_string_append(v___x_1413_, v___x_1414_);
lean_dec_ref(v___x_1414_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1415_);
v___x_1417_ = v___x_1408_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
else
{
lean_del_object(v___x_1408_);
lean_dec(v_val_1406_);
goto v___jp_1382_;
}
}
}
else
{
lean_dec(v___x_1405_);
goto v___jp_1382_;
}
v___jp_1289_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0));
v___x_1291_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1288_, v___x_1290_);
if (lean_obj_tag(v___x_1291_) == 1)
{
lean_object* v_val_1292_; lean_object* v___x_1293_; 
v_val_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_val_1292_);
lean_dec_ref_known(v___x_1291_, 1);
v___x_1293_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1292_);
if (lean_obj_tag(v___x_1293_) == 1)
{
lean_object* v_val_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1308_; 
v_val_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1308_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_val_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1308_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_fst_1298_; lean_object* v_snd_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
v_fst_1298_ = lean_ctor_get(v_val_1294_, 0);
lean_inc(v_fst_1298_);
v_snd_1299_ = lean_ctor_get(v_val_1294_, 1);
lean_inc(v_snd_1299_);
lean_dec(v_val_1294_);
v___x_1300_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1301_ = lean_string_append(v_fst_1298_, v___x_1300_);
v___x_1302_ = lean_string_append(v___x_1301_, v_snd_1299_);
lean_dec(v_snd_1299_);
v___x_1303_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1304_ = lean_string_append(v___x_1302_, v___x_1303_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1304_);
v___x_1306_ = v___x_1296_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
else
{
lean_object* v___x_1309_; 
lean_dec(v___x_1293_);
v___x_1309_ = lean_box(0);
return v___x_1309_;
}
}
else
{
lean_object* v___x_1310_; 
lean_dec(v___x_1291_);
v___x_1310_ = lean_box(0);
return v___x_1310_;
}
}
v___jp_1311_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3));
lean_inc_ref(v_s_1288_);
v___x_1313_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1288_, v___x_1312_);
if (lean_obj_tag(v___x_1313_) == 1)
{
lean_object* v_val_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1325_; 
v_val_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1325_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_val_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1325_;
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
lean_object* v___x_1321_; lean_object* v___x_1323_; 
lean_dec_ref(v_s_1288_);
v___x_1321_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1314_);
lean_dec(v_val_1314_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1321_);
v___x_1323_ = v___x_1316_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
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
v___jp_1326_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4));
lean_inc_ref(v_s_1288_);
v___x_1328_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1288_, v___x_1327_);
if (lean_obj_tag(v___x_1328_) == 1)
{
lean_object* v_val_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1342_; 
v_val_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1342_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_val_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1342_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1333_ = lean_string_utf8_byte_size(v_val_1329_);
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = lean_nat_dec_eq(v___x_1333_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
lean_dec_ref(v_s_1288_);
v___x_1336_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1337_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1329_);
lean_dec(v_val_1329_);
v___x_1338_ = lean_string_append(v___x_1336_, v___x_1337_);
lean_dec_ref(v___x_1337_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1338_);
v___x_1340_ = v___x_1331_;
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
else
{
lean_del_object(v___x_1331_);
lean_dec(v_val_1329_);
goto v___jp_1311_;
}
}
}
else
{
lean_dec(v___x_1328_);
goto v___jp_1311_;
}
}
v___jp_1343_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6));
lean_inc_ref(v_s_1288_);
v___x_1345_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1288_, v___x_1344_);
if (lean_obj_tag(v___x_1345_) == 1)
{
lean_object* v_val_1346_; lean_object* v___x_1347_; 
v_val_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_val_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1346_);
if (lean_obj_tag(v___x_1347_) == 1)
{
lean_object* v_val_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref(v_s_1288_);
v_val_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1364_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_val_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1364_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v_fst_1352_; lean_object* v_snd_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v_fst_1352_ = lean_ctor_get(v_val_1348_, 0);
lean_inc(v_fst_1352_);
v_snd_1353_ = lean_ctor_get(v_val_1348_, 1);
lean_inc(v_snd_1353_);
lean_dec(v_val_1348_);
v___x_1354_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1355_ = lean_string_append(v___x_1354_, v_fst_1352_);
lean_dec(v_fst_1352_);
v___x_1356_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1357_ = lean_string_append(v___x_1355_, v___x_1356_);
v___x_1358_ = lean_string_append(v___x_1357_, v_snd_1353_);
lean_dec(v_snd_1353_);
v___x_1359_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1360_ = lean_string_append(v___x_1358_, v___x_1359_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1360_);
v___x_1362_ = v___x_1350_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
else
{
lean_dec(v___x_1347_);
goto v___jp_1326_;
}
}
else
{
lean_dec(v___x_1345_);
goto v___jp_1326_;
}
}
v___jp_1365_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7));
lean_inc_ref(v_s_1288_);
v___x_1367_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1288_, v___x_1366_);
if (lean_obj_tag(v___x_1367_) == 1)
{
lean_object* v_val_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1381_; 
v_val_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1381_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_val_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1381_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = lean_string_utf8_byte_size(v_val_1368_);
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = lean_nat_dec_eq(v___x_1372_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
lean_dec_ref(v_s_1288_);
v___x_1375_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1376_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1368_);
lean_dec(v_val_1368_);
v___x_1377_ = lean_string_append(v___x_1375_, v___x_1376_);
lean_dec_ref(v___x_1376_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1377_);
v___x_1379_ = v___x_1370_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
else
{
lean_del_object(v___x_1370_);
lean_dec(v_val_1368_);
goto v___jp_1343_;
}
}
}
else
{
lean_dec(v___x_1367_);
goto v___jp_1343_;
}
}
v___jp_1382_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8));
lean_inc_ref(v_s_1288_);
v___x_1384_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1288_, v___x_1383_);
if (lean_obj_tag(v___x_1384_) == 1)
{
lean_object* v_val_1385_; lean_object* v___x_1386_; 
v_val_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_val_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1385_);
if (lean_obj_tag(v___x_1386_) == 1)
{
lean_object* v_val_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1403_; 
lean_dec_ref(v_s_1288_);
v_val_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1403_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_val_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1403_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_fst_1391_; lean_object* v_snd_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v_fst_1391_ = lean_ctor_get(v_val_1387_, 0);
lean_inc(v_fst_1391_);
v_snd_1392_ = lean_ctor_get(v_val_1387_, 1);
lean_inc(v_snd_1392_);
lean_dec(v_val_1387_);
v___x_1393_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1394_ = lean_string_append(v___x_1393_, v_fst_1391_);
lean_dec(v_fst_1391_);
v___x_1395_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1396_ = lean_string_append(v___x_1394_, v___x_1395_);
v___x_1397_ = lean_string_append(v___x_1396_, v_snd_1392_);
lean_dec(v_snd_1392_);
v___x_1398_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1399_ = lean_string_append(v___x_1397_, v___x_1398_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1399_);
v___x_1401_ = v___x_1389_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
else
{
lean_dec(v___x_1386_);
goto v___jp_1365_;
}
}
else
{
lean_dec(v___x_1384_);
goto v___jp_1365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleSymbol(lean_object* v_symbol_1429_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1430_ = lean_string_utf8_byte_size(v_symbol_1429_);
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = lean_nat_dec_eq(v___x_1430_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v_fst_1434_; lean_object* v_snd_1435_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1433_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(v_symbol_1429_);
v_fst_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc_n(v_fst_1434_, 2);
v_snd_1435_ = lean_ctor_get(v___x_1433_, 1);
lean_inc(v_snd_1435_);
lean_dec_ref(v___x_1433_);
v___x_1460_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__5));
v___x_1461_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_fst_1434_, v___x_1460_);
if (lean_obj_tag(v___x_1461_) == 1)
{
lean_object* v_val_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1482_; 
v_val_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1482_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_val_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1482_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
uint8_t v___x_1466_; 
lean_inc(v_val_1462_);
v___x_1466_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_1462_);
if (v___x_1466_ == 0)
{
lean_del_object(v___x_1464_);
lean_dec(v_val_1462_);
goto v___jp_1436_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v_r_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
lean_dec(v_fst_1434_);
v___x_1467_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__6));
v___x_1468_ = lean_string_append(v___x_1467_, v_val_1462_);
lean_dec(v_val_1462_);
v___x_1469_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__7));
v_r_1470_ = lean_string_append(v___x_1468_, v___x_1469_);
v___x_1471_ = lean_string_utf8_byte_size(v_snd_1435_);
v___x_1472_ = lean_nat_dec_eq(v___x_1471_, v___x_1431_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1473_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1474_ = lean_string_append(v_r_1470_, v___x_1473_);
v___x_1475_ = lean_string_append(v___x_1474_, v_snd_1435_);
lean_dec(v_snd_1435_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1475_);
v___x_1477_ = v___x_1464_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
else
{
lean_object* v___x_1480_; 
lean_dec(v_snd_1435_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v_r_1470_);
v___x_1480_ = v___x_1464_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_r_1470_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
else
{
lean_dec(v___x_1461_);
goto v___jp_1436_;
}
v___jp_1436_:
{
lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__0));
v___x_1438_ = lean_string_dec_eq(v_fst_1434_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; 
v___x_1439_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(v_fst_1434_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_dec(v_snd_1435_);
return v___x_1439_;
}
else
{
lean_object* v_val_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_val_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_val_1440_);
v___x_1441_ = lean_string_utf8_byte_size(v_snd_1435_);
v___x_1442_ = lean_nat_dec_eq(v___x_1441_, v___x_1431_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1452_; 
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v___x_1439_, 0);
lean_dec(v_unused_1453_);
v___x_1444_ = v___x_1439_;
v_isShared_1445_ = v_isSharedCheck_1452_;
goto v_resetjp_1443_;
}
else
{
lean_dec(v___x_1439_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1452_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1446_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1447_ = lean_string_append(v_val_1440_, v___x_1446_);
v___x_1448_ = lean_string_append(v___x_1447_, v_snd_1435_);
lean_dec(v_snd_1435_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1448_);
v___x_1450_ = v___x_1444_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
else
{
lean_dec(v_val_1440_);
lean_dec(v_snd_1435_);
return v___x_1439_;
}
}
}
else
{
lean_object* v___x_1454_; uint8_t v___x_1455_; 
lean_dec(v_fst_1434_);
v___x_1454_ = lean_string_utf8_byte_size(v_snd_1435_);
v___x_1455_ = lean_nat_dec_eq(v___x_1454_, v___x_1431_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__2));
v___x_1457_ = lean_string_append(v___x_1456_, v_snd_1435_);
lean_dec(v_snd_1435_);
v___x_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
return v___x_1458_;
}
else
{
lean_object* v___x_1459_; 
lean_dec(v_snd_1435_);
v___x_1459_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__4));
return v___x_1459_;
}
}
}
}
else
{
lean_object* v___x_1483_; 
lean_dec_ref(v_symbol_1429_);
v___x_1483_ = lean_box(0);
return v___x_1483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(lean_object* v_s_1484_, lean_object* v_pos_1485_, lean_object* v_pred_1486_){
_start:
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = lean_string_utf8_byte_size(v_s_1484_);
v___x_1488_ = lean_nat_dec_eq(v_pos_1485_, v___x_1487_);
if (v___x_1488_ == 0)
{
uint32_t v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1489_ = lean_string_utf8_get_fast(v_s_1484_, v_pos_1485_);
v___x_1490_ = lean_box_uint32(v___x_1489_);
lean_inc_ref(v_pred_1486_);
v___x_1491_ = lean_apply_1(v_pred_1486_, v___x_1490_);
v___x_1492_ = lean_unbox(v___x_1491_);
if (v___x_1492_ == 0)
{
lean_dec_ref(v_pred_1486_);
return v_pos_1485_;
}
else
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_string_utf8_next_fast(v_s_1484_, v_pos_1485_);
lean_dec(v_pos_1485_);
v_pos_1485_ = v___x_1493_;
goto _start;
}
}
else
{
lean_dec_ref(v_pred_1486_);
return v_pos_1485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile___boxed(lean_object* v_s_1495_, lean_object* v_pos_1496_, lean_object* v_pred_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_s_1495_, v_pos_1496_, v_pred_1497_);
lean_dec_ref(v_s_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(lean_object* v_s_1499_, lean_object* v_p_u2081_1500_, lean_object* v_p_u2082_1501_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1502_ = lean_unsigned_to_nat(0u);
v___x_1503_ = lean_string_utf8_extract(v_s_1499_, v___x_1502_, v_p_u2081_1500_);
v___x_1504_ = lean_string_utf8_extract(v_s_1499_, v_p_u2081_1500_, v_p_u2082_1501_);
v___x_1505_ = lean_string_utf8_byte_size(v_s_1499_);
v___x_1506_ = lean_string_utf8_extract(v_s_1499_, v_p_u2082_1501_, v___x_1505_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1504_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1503_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082___boxed(lean_object* v_s_1509_, lean_object* v_p_u2081_1510_, lean_object* v_p_u2082_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_s_1509_, v_p_u2081_1510_, v_p_u2082_1511_);
lean_dec(v_p_u2082_1511_);
lean_dec(v_p_u2081_1510_);
lean_dec_ref(v_s_1509_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(lean_object* v___x_1513_, lean_object* v___x_1514_, lean_object* v_line_1515_, lean_object* v_a_1516_, lean_object* v_b_1517_){
_start:
{
lean_object* v_startInclusive_1518_; lean_object* v_endExclusive_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v_startInclusive_1518_ = lean_ctor_get(v___x_1513_, 1);
v_endExclusive_1519_ = lean_ctor_get(v___x_1513_, 2);
v___x_1520_ = lean_nat_sub(v_endExclusive_1519_, v_startInclusive_1518_);
v___x_1521_ = lean_nat_dec_eq(v_a_1516_, v___x_1520_);
lean_dec(v___x_1520_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___y_1525_; uint32_t v___x_1530_; uint32_t v___x_1531_; uint8_t v___x_1532_; 
v___x_1522_ = lean_box(0);
v___x_1523_ = lean_nat_add(v___x_1514_, v_a_1516_);
v___x_1530_ = lean_string_utf8_get_fast(v_line_1515_, v___x_1523_);
v___x_1531_ = 43;
v___x_1532_ = lean_uint32_dec_eq(v___x_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
uint32_t v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = 41;
v___x_1534_ = lean_uint32_dec_eq(v___x_1530_, v___x_1533_);
v___y_1525_ = v___x_1534_;
goto v___jp_1524_;
}
else
{
v___y_1525_ = v___x_1532_;
goto v___jp_1524_;
}
v___jp_1524_:
{
if (v___y_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec(v_a_1516_);
v___x_1526_ = lean_string_utf8_next_fast(v_line_1515_, v___x_1523_);
lean_dec(v___x_1523_);
v___x_1527_ = lean_nat_sub(v___x_1526_, v___x_1514_);
v_a_1516_ = v___x_1527_;
v_b_1517_ = v___x_1522_;
goto _start;
}
else
{
lean_object* v___x_1529_; 
lean_dec(v___x_1523_);
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v_a_1516_);
return v___x_1529_;
}
}
}
else
{
lean_dec(v_a_1516_);
lean_inc(v_b_1517_);
return v_b_1517_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg___boxed(lean_object* v___x_1535_, lean_object* v___x_1536_, lean_object* v_line_1537_, lean_object* v_a_1538_, lean_object* v_b_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1535_, v___x_1536_, v_line_1537_, v_a_1538_, v_b_1539_);
lean_dec(v_b_1539_);
lean_dec_ref(v_line_1537_);
lean_dec(v___x_1536_);
lean_dec_ref(v___x_1535_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(lean_object* v___x_1541_, lean_object* v_line_1542_, lean_object* v_a_1543_, lean_object* v_b_1544_){
_start:
{
lean_object* v_startInclusive_1545_; lean_object* v_endExclusive_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_startInclusive_1545_ = lean_ctor_get(v___x_1541_, 1);
v_endExclusive_1546_ = lean_ctor_get(v___x_1541_, 2);
v___x_1547_ = lean_nat_sub(v_endExclusive_1546_, v_startInclusive_1545_);
v___x_1548_ = lean_nat_dec_eq(v_a_1543_, v___x_1547_);
lean_dec(v___x_1547_);
if (v___x_1548_ == 0)
{
uint32_t v___x_1549_; uint32_t v___x_1550_; uint8_t v___x_1551_; 
v___x_1549_ = lean_string_utf8_get_fast(v_line_1542_, v_a_1543_);
v___x_1550_ = 40;
v___x_1551_ = lean_uint32_dec_eq(v___x_1549_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_box(0);
v___x_1553_ = lean_string_utf8_next_fast(v_line_1542_, v_a_1543_);
lean_dec(v_a_1543_);
v_a_1543_ = v___x_1553_;
v_b_1544_ = v___x_1552_;
goto _start;
}
else
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1555_, 0, v_a_1543_);
return v___x_1555_;
}
}
else
{
lean_dec(v_a_1543_);
lean_inc(v_b_1544_);
return v_b_1544_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg___boxed(lean_object* v___x_1556_, lean_object* v_line_1557_, lean_object* v_a_1558_, lean_object* v_b_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1556_, v_line_1557_, v_a_1558_, v_b_1559_);
lean_dec(v_b_1559_);
lean_dec_ref(v_line_1557_);
lean_dec_ref(v___x_1556_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(lean_object* v_line_1561_){
_start:
{
lean_object* v_searcher_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_searcher_1562_ = lean_unsigned_to_nat(0u);
v___x_1563_ = lean_string_utf8_byte_size(v_line_1561_);
lean_inc_ref(v_line_1561_);
v___x_1564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1564_, 0, v_line_1561_);
lean_ctor_set(v___x_1564_, 1, v_searcher_1562_);
lean_ctor_set(v___x_1564_, 2, v___x_1563_);
v___x_1565_ = lean_box(0);
v___x_1566_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1564_, v_line_1561_, v_searcher_1562_, v___x_1565_);
lean_dec_ref_known(v___x_1564_, 3);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_dec_ref(v_line_1561_);
return v___x_1565_;
}
else
{
lean_object* v_val_1567_; uint8_t v___x_1568_; 
v_val_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_val_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v___x_1568_ = lean_nat_dec_eq(v_val_1567_, v___x_1563_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = lean_string_utf8_next_fast(v_line_1561_, v_val_1567_);
lean_dec(v_val_1567_);
lean_inc_ref(v_line_1561_);
v___x_1570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1570_, 0, v_line_1561_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
lean_ctor_set(v___x_1570_, 2, v___x_1563_);
v___x_1571_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1570_, v___x_1569_, v_line_1561_, v_searcher_1562_, v___x_1565_);
lean_dec_ref_known(v___x_1570_, 3);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_dec_ref(v_line_1561_);
return v___x_1565_;
}
else
{
lean_object* v_val_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1582_; 
v_val_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1582_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_val_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1582_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = lean_nat_add(v___x_1569_, v_val_1572_);
lean_dec(v_val_1572_);
v___x_1577_ = lean_nat_dec_eq(v___x_1576_, v___x_1569_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1578_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1561_, v___x_1569_, v___x_1576_);
lean_dec(v___x_1576_);
lean_dec_ref(v_line_1561_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1578_);
v___x_1580_ = v___x_1574_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
else
{
lean_dec(v___x_1576_);
lean_del_object(v___x_1574_);
lean_dec_ref(v_line_1561_);
return v___x_1565_;
}
}
}
}
else
{
lean_dec(v_val_1567_);
lean_dec_ref(v_line_1561_);
return v___x_1565_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(lean_object* v___x_1583_, lean_object* v_line_1584_, lean_object* v_inst_1585_, lean_object* v_R_1586_, lean_object* v_a_1587_, lean_object* v_b_1588_, lean_object* v_c_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1583_, v_line_1584_, v_a_1587_, v_b_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___boxed(lean_object* v___x_1591_, lean_object* v_line_1592_, lean_object* v_inst_1593_, lean_object* v_R_1594_, lean_object* v_a_1595_, lean_object* v_b_1596_, lean_object* v_c_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(v___x_1591_, v_line_1592_, v_inst_1593_, v_R_1594_, v_a_1595_, v_b_1596_, v_c_1597_);
lean_dec(v_b_1596_);
lean_dec_ref(v_line_1592_);
lean_dec_ref(v___x_1591_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(lean_object* v___x_1599_, lean_object* v___x_1600_, lean_object* v_line_1601_, lean_object* v_inst_1602_, lean_object* v_R_1603_, lean_object* v_a_1604_, lean_object* v_b_1605_, lean_object* v_c_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1599_, v___x_1600_, v_line_1601_, v_a_1604_, v_b_1605_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___boxed(lean_object* v___x_1608_, lean_object* v___x_1609_, lean_object* v_line_1610_, lean_object* v_inst_1611_, lean_object* v_R_1612_, lean_object* v_a_1613_, lean_object* v_b_1614_, lean_object* v_c_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(v___x_1608_, v___x_1609_, v_line_1610_, v_inst_1611_, v_R_1612_, v_a_1613_, v_b_1614_, v_c_1615_);
lean_dec(v_b_1614_);
lean_dec_ref(v_line_1610_);
lean_dec(v___x_1609_);
lean_dec_ref(v___x_1608_);
return v_res_1616_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(uint32_t v_x_1617_){
_start:
{
uint32_t v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = 32;
v___x_1619_ = lean_uint32_dec_eq(v_x_1617_, v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed(lean_object* v_x_1620_){
_start:
{
uint32_t v_x_2608__boxed_1621_; uint8_t v_res_1622_; lean_object* v_r_1623_; 
v_x_2608__boxed_1621_ = lean_unbox_uint32(v_x_1620_);
lean_dec(v_x_1620_);
v_res_1622_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(v_x_2608__boxed_1621_);
v_r_1623_ = lean_box(v_res_1622_);
return v_r_1623_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(uint32_t v_x_1624_){
_start:
{
uint8_t v___y_1626_; uint8_t v___y_1632_; uint32_t v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = 48;
v___x_1638_ = lean_uint32_dec_le(v___x_1637_, v_x_1624_);
if (v___x_1638_ == 0)
{
v___y_1632_ = v___x_1638_;
goto v___jp_1631_;
}
else
{
uint32_t v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = 57;
v___x_1640_ = lean_uint32_dec_le(v_x_1624_, v___x_1639_);
v___y_1632_ = v___x_1640_;
goto v___jp_1631_;
}
v___jp_1625_:
{
if (v___y_1626_ == 0)
{
uint32_t v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = 65;
v___x_1628_ = lean_uint32_dec_le(v___x_1627_, v_x_1624_);
if (v___x_1628_ == 0)
{
return v___x_1628_;
}
else
{
uint32_t v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = 70;
v___x_1630_ = lean_uint32_dec_le(v_x_1624_, v___x_1629_);
return v___x_1630_;
}
}
else
{
return v___y_1626_;
}
}
v___jp_1631_:
{
if (v___y_1632_ == 0)
{
uint32_t v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = 97;
v___x_1634_ = lean_uint32_dec_le(v___x_1633_, v_x_1624_);
if (v___x_1634_ == 0)
{
v___y_1626_ = v___x_1634_;
goto v___jp_1625_;
}
else
{
uint32_t v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = 102;
v___x_1636_ = lean_uint32_dec_le(v_x_1624_, v___x_1635_);
v___y_1626_ = v___x_1636_;
goto v___jp_1625_;
}
}
else
{
return v___y_1632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed(lean_object* v_x_1641_){
_start:
{
uint32_t v_x_2615__boxed_1642_; uint8_t v_res_1643_; lean_object* v_r_1644_; 
v_x_2615__boxed_1642_ = lean_unbox_uint32(v_x_1641_);
lean_dec(v_x_1641_);
v_res_1643_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(v_x_2615__boxed_1642_);
v_r_1644_ = lean_box(v_res_1643_);
return v_r_1644_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(lean_object* v___x_1645_, lean_object* v_line_1646_, lean_object* v___x_1647_, lean_object* v___x_1648_, lean_object* v_a_1649_, lean_object* v_b_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_box(0);
switch(lean_obj_tag(v_a_1649_))
{
case 0:
{
lean_object* v_pos_1652_; lean_object* v___x_1653_; 
v_pos_1652_ = lean_ctor_get(v_a_1649_, 0);
lean_inc(v_pos_1652_);
lean_dec_ref_known(v_a_1649_, 1);
v___x_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1653_, 0, v_pos_1652_);
return v___x_1653_;
}
case 1:
{
lean_object* v_pos_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1665_; 
v_pos_1654_ = lean_ctor_get(v_a_1649_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_a_1649_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1656_ = v_a_1649_;
v_isShared_1657_ = v_isSharedCheck_1665_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_pos_1654_);
lean_dec(v_a_1649_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1665_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1658_ = lean_nat_add(v___x_1645_, v_pos_1654_);
lean_dec(v_pos_1654_);
v___x_1659_ = lean_string_utf8_next_fast(v_line_1646_, v___x_1658_);
lean_dec(v___x_1658_);
v___x_1660_ = lean_nat_sub(v___x_1659_, v___x_1645_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set_tag(v___x_1656_, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1660_);
v___x_1662_ = v___x_1656_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
v_a_1649_ = v___x_1662_;
v_b_1650_ = v___x_1651_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1666_; lean_object* v_table_1667_; lean_object* v_stackPos_1668_; lean_object* v_needlePos_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1722_; 
v_needle_1666_ = lean_ctor_get(v_a_1649_, 0);
v_table_1667_ = lean_ctor_get(v_a_1649_, 1);
v_stackPos_1668_ = lean_ctor_get(v_a_1649_, 2);
v_needlePos_1669_ = lean_ctor_get(v_a_1649_, 3);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_a_1649_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1671_ = v_a_1649_;
v_isShared_1672_ = v_isSharedCheck_1722_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_needlePos_1669_);
lean_inc(v_stackPos_1668_);
lean_inc(v_table_1667_);
lean_inc(v_needle_1666_);
lean_dec(v_a_1649_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1722_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v_str_1673_; lean_object* v_startInclusive_1674_; lean_object* v_endExclusive_1675_; lean_object* v_basePos_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v_str_1673_ = lean_ctor_get(v_needle_1666_, 0);
v_startInclusive_1674_ = lean_ctor_get(v_needle_1666_, 1);
v_endExclusive_1675_ = lean_ctor_get(v_needle_1666_, 2);
v_basePos_1676_ = lean_nat_sub(v_stackPos_1668_, v_needlePos_1669_);
v___x_1677_ = lean_nat_sub(v_endExclusive_1675_, v_startInclusive_1674_);
v___x_1678_ = lean_nat_add(v_basePos_1676_, v___x_1677_);
v___x_1679_ = lean_nat_sub(v___x_1648_, v___x_1645_);
v___x_1680_ = lean_nat_dec_le(v___x_1678_, v___x_1679_);
lean_dec(v___x_1678_);
if (v___x_1680_ == 0)
{
uint8_t v___x_1681_; 
lean_dec(v___x_1677_);
lean_del_object(v___x_1671_);
lean_dec(v_needlePos_1669_);
lean_dec(v_stackPos_1668_);
lean_dec_ref(v_table_1667_);
lean_dec_ref(v_needle_1666_);
v___x_1681_ = lean_nat_dec_lt(v_basePos_1676_, v___x_1679_);
lean_dec(v___x_1679_);
lean_dec(v_basePos_1676_);
if (v___x_1681_ == 0)
{
lean_inc(v_b_1650_);
return v_b_1650_;
}
else
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_box(3);
v_a_1649_ = v___x_1682_;
v_b_1650_ = v___x_1651_;
goto _start;
}
}
else
{
lean_object* v___x_1684_; uint8_t v_stackByte_1685_; lean_object* v___x_1686_; uint8_t v_patByte_1687_; uint8_t v___x_1688_; 
lean_dec(v___x_1679_);
lean_dec(v_basePos_1676_);
v___x_1684_ = lean_nat_add(v___x_1645_, v_stackPos_1668_);
v_stackByte_1685_ = lean_string_get_byte_fast(v_line_1646_, v___x_1684_);
v___x_1686_ = lean_nat_add(v_startInclusive_1674_, v_needlePos_1669_);
v_patByte_1687_ = lean_string_get_byte_fast(v_str_1673_, v___x_1686_);
v___x_1688_ = lean_uint8_dec_eq(v_stackByte_1685_, v_patByte_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; uint8_t v___x_1690_; 
lean_dec(v___x_1677_);
v___x_1689_ = lean_unsigned_to_nat(0u);
v___x_1690_ = lean_nat_dec_eq(v_needlePos_1669_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v_newNeedlePos_1693_; uint8_t v___x_1694_; 
v___x_1691_ = lean_unsigned_to_nat(1u);
v___x_1692_ = lean_nat_sub(v_needlePos_1669_, v___x_1691_);
lean_dec(v_needlePos_1669_);
v_newNeedlePos_1693_ = lean_array_fget_borrowed(v_table_1667_, v___x_1692_);
lean_dec(v___x_1692_);
v___x_1694_ = lean_nat_dec_eq(v_newNeedlePos_1693_, v___x_1689_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1696_; 
lean_inc(v_newNeedlePos_1693_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 3, v_newNeedlePos_1693_);
v___x_1696_ = v___x_1671_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_needle_1666_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_table_1667_);
lean_ctor_set(v_reuseFailAlloc_1698_, 2, v_stackPos_1668_);
lean_ctor_set(v_reuseFailAlloc_1698_, 3, v_newNeedlePos_1693_);
v___x_1696_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
v_a_1649_ = v___x_1696_;
v_b_1650_ = v___x_1651_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1699_; lean_object* v___x_1701_; 
v_nextStackPos_1699_ = l_String_Slice_posGE___redArg(v___x_1647_, v_stackPos_1668_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 3, v___x_1689_);
lean_ctor_set(v___x_1671_, 2, v_nextStackPos_1699_);
v___x_1701_ = v___x_1671_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_needle_1666_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_table_1667_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_nextStackPos_1699_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v___x_1689_);
v___x_1701_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
v_a_1649_ = v___x_1701_;
v_b_1650_ = v___x_1651_;
goto _start;
}
}
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v_nextStackPos_1706_; lean_object* v___x_1708_; 
lean_dec(v_needlePos_1669_);
v___x_1704_ = lean_unsigned_to_nat(1u);
v___x_1705_ = lean_nat_add(v_stackPos_1668_, v___x_1704_);
lean_dec(v_stackPos_1668_);
v_nextStackPos_1706_ = l_String_Slice_posGE___redArg(v___x_1647_, v___x_1705_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 3, v___x_1689_);
lean_ctor_set(v___x_1671_, 2, v_nextStackPos_1706_);
v___x_1708_ = v___x_1671_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_needle_1666_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_table_1667_);
lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_nextStackPos_1706_);
lean_ctor_set(v_reuseFailAlloc_1710_, 3, v___x_1689_);
v___x_1708_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
v_a_1649_ = v___x_1708_;
v_b_1650_ = v___x_1651_;
goto _start;
}
}
}
else
{
lean_object* v___x_1711_; lean_object* v_nextStackPos_1712_; lean_object* v_nextNeedlePos_1713_; uint8_t v___x_1714_; 
v___x_1711_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1712_ = lean_nat_add(v_stackPos_1668_, v___x_1711_);
lean_dec(v_stackPos_1668_);
v_nextNeedlePos_1713_ = lean_nat_add(v_needlePos_1669_, v___x_1711_);
lean_dec(v_needlePos_1669_);
v___x_1714_ = lean_nat_dec_eq(v_nextNeedlePos_1713_, v___x_1677_);
lean_dec(v___x_1677_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1716_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 3, v_nextNeedlePos_1713_);
lean_ctor_set(v___x_1671_, 2, v_nextStackPos_1712_);
v___x_1716_ = v___x_1671_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_needle_1666_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_table_1667_);
lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_nextStackPos_1712_);
lean_ctor_set(v_reuseFailAlloc_1718_, 3, v_nextNeedlePos_1713_);
v___x_1716_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
v_a_1649_ = v___x_1716_;
goto _start;
}
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_del_object(v___x_1671_);
lean_dec_ref(v_table_1667_);
lean_dec_ref(v_needle_1666_);
v___x_1719_ = lean_nat_sub(v_nextStackPos_1712_, v_nextNeedlePos_1713_);
lean_dec(v_nextNeedlePos_1713_);
lean_dec(v_nextStackPos_1712_);
v___x_1720_ = l_String_Slice_pos_x21(v___x_1647_, v___x_1719_);
lean_dec(v___x_1719_);
v___x_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
return v___x_1721_;
}
}
}
}
}
default: 
{
lean_inc(v_b_1650_);
return v_b_1650_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg___boxed(lean_object* v___x_1723_, lean_object* v_line_1724_, lean_object* v___x_1725_, lean_object* v___x_1726_, lean_object* v_a_1727_, lean_object* v_b_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1723_, v_line_1724_, v___x_1725_, v___x_1726_, v_a_1727_, v_b_1728_);
lean_dec(v_b_1728_);
lean_dec(v___x_1726_);
lean_dec_ref(v___x_1725_);
lean_dec_ref(v_line_1724_);
lean_dec(v___x_1723_);
return v_res_1729_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3));
v___x_1735_ = lean_string_utf8_byte_size(v___x_1734_);
return v___x_1735_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4);
v___x_1738_ = lean_nat_dec_eq(v___x_1737_, v___x_1736_);
return v___x_1738_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1739_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4);
v___x_1740_ = lean_unsigned_to_nat(0u);
v___x_1741_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3));
v___x_1742_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v___x_1740_);
lean_ctor_set(v___x_1742_, 2, v___x_1739_);
return v___x_1742_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6);
v___x_1744_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1743_);
return v___x_1744_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7);
v___x_1747_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6);
v___x_1748_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v___x_1746_);
lean_ctor_set(v___x_1748_, 2, v___x_1745_);
lean_ctor_set(v___x_1748_, 3, v___x_1745_);
return v___x_1748_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2));
v___x_1750_ = lean_string_utf8_byte_size(v___x_1749_);
return v___x_1750_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1751_ = lean_unsigned_to_nat(0u);
v___x_1752_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
v___x_1753_ = lean_nat_dec_eq(v___x_1752_, v___x_1751_);
return v___x_1753_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1754_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
v___x_1755_ = lean_unsigned_to_nat(0u);
v___x_1756_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2));
v___x_1757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v___x_1755_);
lean_ctor_set(v___x_1757_, 2, v___x_1754_);
return v___x_1757_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11);
v___x_1759_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1758_);
return v___x_1759_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1760_ = lean_unsigned_to_nat(0u);
v___x_1761_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12);
v___x_1762_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11);
v___x_1763_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v___x_1761_);
lean_ctor_set(v___x_1763_, 2, v___x_1760_);
lean_ctor_set(v___x_1763_, 3, v___x_1760_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(lean_object* v_line_1764_){
_start:
{
lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___f_1772_; lean_object* v___f_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___x_1784_; lean_object* v___y_1786_; uint8_t v___x_1801_; 
v___f_1772_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0));
v___f_1773_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1));
v___x_1774_ = lean_unsigned_to_nat(0u);
v___x_1775_ = lean_string_utf8_byte_size(v_line_1764_);
lean_inc_ref(v_line_1764_);
v___x_1784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1784_, 0, v_line_1764_);
lean_ctor_set(v___x_1784_, 1, v___x_1774_);
lean_ctor_set(v___x_1784_, 2, v___x_1775_);
v___x_1801_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13);
v___y_1786_ = v___x_1802_;
goto v___jp_1785_;
}
else
{
lean_object* v___x_1803_; 
v___x_1803_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1786_ = v___x_1803_;
goto v___jp_1785_;
}
v___jp_1765_:
{
uint8_t v___x_1768_; 
v___x_1768_ = lean_nat_dec_eq(v___y_1767_, v___y_1766_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1764_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v_line_1764_);
v___x_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
return v___x_1770_;
}
else
{
lean_object* v___x_1771_; 
lean_dec(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v_line_1764_);
v___x_1771_ = lean_box(0);
return v___x_1771_;
}
}
v___jp_1776_:
{
lean_object* v___x_1781_; 
lean_inc(v___y_1780_);
v___x_1781_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___y_1778_, v_line_1764_, v___y_1779_, v___x_1775_, v___y_1780_, v___y_1777_);
lean_dec_ref(v___y_1779_);
if (lean_obj_tag(v___x_1781_) == 0)
{
v___y_1766_ = v___y_1778_;
v___y_1767_ = v___x_1775_;
goto v___jp_1765_;
}
else
{
lean_object* v_val_1782_; lean_object* v___x_1783_; 
v_val_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_val_1782_);
lean_dec_ref_known(v___x_1781_, 1);
v___x_1783_ = lean_nat_add(v___y_1778_, v_val_1782_);
lean_dec(v_val_1782_);
v___y_1766_ = v___y_1778_;
v___y_1767_ = v___x_1783_;
goto v___jp_1765_;
}
}
v___jp_1785_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_box(0);
lean_inc(v___y_1786_);
v___x_1788_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_line_1764_, v___x_1784_, v___x_1775_, v___y_1786_, v___x_1787_);
lean_dec_ref_known(v___x_1784_, 3);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_dec_ref(v_line_1764_);
return v___x_1787_;
}
else
{
lean_object* v_val_1789_; uint8_t v___x_1790_; 
v_val_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_val_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = lean_nat_dec_eq(v_val_1789_, v___x_1775_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = lean_string_utf8_next_fast(v_line_1764_, v_val_1789_);
lean_dec(v_val_1789_);
v___x_1792_ = lean_nat_dec_eq(v___x_1791_, v___x_1775_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1793_ = lean_string_utf8_next_fast(v_line_1764_, v___x_1791_);
v___x_1794_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1764_, v___x_1793_, v___f_1773_);
v___x_1795_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1764_, v___x_1794_, v___f_1772_);
v___x_1796_ = lean_nat_dec_eq(v___x_1795_, v___x_1775_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
lean_inc(v___x_1795_);
lean_inc_ref(v_line_1764_);
v___x_1797_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1797_, 0, v_line_1764_);
lean_ctor_set(v___x_1797_, 1, v___x_1795_);
lean_ctor_set(v___x_1797_, 2, v___x_1775_);
v___x_1798_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8);
v___y_1777_ = v___x_1787_;
v___y_1778_ = v___x_1795_;
v___y_1779_ = v___x_1797_;
v___y_1780_ = v___x_1799_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1777_ = v___x_1787_;
v___y_1778_ = v___x_1795_;
v___y_1779_ = v___x_1797_;
v___y_1780_ = v___x_1800_;
goto v___jp_1776_;
}
}
else
{
lean_dec(v___x_1795_);
lean_dec_ref(v_line_1764_);
return v___x_1787_;
}
}
else
{
lean_dec_ref(v_line_1764_);
return v___x_1787_;
}
}
else
{
lean_dec(v_val_1789_);
lean_dec_ref(v_line_1764_);
return v___x_1787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(lean_object* v___x_1804_, lean_object* v_line_1805_, lean_object* v___x_1806_, lean_object* v___x_1807_, lean_object* v_inst_1808_, lean_object* v_R_1809_, lean_object* v_a_1810_, lean_object* v_b_1811_, lean_object* v_c_1812_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1804_, v_line_1805_, v___x_1806_, v___x_1807_, v_a_1810_, v_b_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___boxed(lean_object* v___x_1814_, lean_object* v_line_1815_, lean_object* v___x_1816_, lean_object* v___x_1817_, lean_object* v_inst_1818_, lean_object* v_R_1819_, lean_object* v_a_1820_, lean_object* v_b_1821_, lean_object* v_c_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(v___x_1814_, v_line_1815_, v___x_1816_, v___x_1817_, v_inst_1818_, v_R_1819_, v_a_1820_, v_b_1821_, v_c_1822_);
lean_dec(v_b_1821_);
lean_dec(v___x_1817_);
lean_dec_ref(v___x_1816_);
lean_dec_ref(v_line_1815_);
lean_dec(v___x_1814_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(lean_object* v_line_1824_){
_start:
{
lean_object* v___x_1825_; 
lean_inc_ref(v_line_1824_);
v___x_1825_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(v_line_1824_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v___x_1826_; 
v___x_1826_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(v_line_1824_);
return v___x_1826_;
}
else
{
lean_dec_ref(v_line_1824_);
return v___x_1825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleBtLine(lean_object* v_line_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(v_line_1827_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v___x_1829_; 
v___x_1829_ = lean_box(0);
return v___x_1829_;
}
else
{
lean_object* v_val_1830_; lean_object* v_snd_1831_; lean_object* v_fst_1832_; lean_object* v_fst_1833_; lean_object* v_snd_1834_; lean_object* v___x_1835_; 
v_val_1830_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_val_1830_);
lean_dec_ref_known(v___x_1828_, 1);
v_snd_1831_ = lean_ctor_get(v_val_1830_, 1);
lean_inc(v_snd_1831_);
v_fst_1832_ = lean_ctor_get(v_val_1830_, 0);
lean_inc(v_fst_1832_);
lean_dec(v_val_1830_);
v_fst_1833_ = lean_ctor_get(v_snd_1831_, 0);
lean_inc(v_fst_1833_);
v_snd_1834_ = lean_ctor_get(v_snd_1831_, 1);
lean_inc(v_snd_1834_);
lean_dec(v_snd_1831_);
v___x_1835_ = l_Lean_Name_Demangle_demangleSymbol(v_fst_1833_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_dec(v_snd_1834_);
lean_dec(v_fst_1832_);
return v___x_1835_;
}
else
{
lean_object* v_val_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1845_; 
v_val_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1845_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_val_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1845_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1840_ = lean_string_append(v_fst_1832_, v_val_1836_);
lean_dec(v_val_1836_);
v___x_1841_ = lean_string_append(v___x_1840_, v_snd_1834_);
lean_dec(v_snd_1834_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1841_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_demangle_bt_line_cstr(lean_object* v_line_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_Name_Demangle_demangleBtLine(v_line_1846_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v___x_1848_; 
v___x_1848_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_1848_;
}
else
{
lean_object* v_val_1849_; 
v_val_1849_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_val_1849_);
lean_dec_ref_known(v___x_1847_, 1);
return v_val_1849_;
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
