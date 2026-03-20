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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedNamePart_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqNamePart_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lean_Name_demangle(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
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
static lean_once_cell_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___boxed(lean_object*, lean_object*);
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
lean_dec_ref(v___x_10_);
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
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_69_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_69_, 0, v_s_65_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
v___x_70_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(v___x_69_, v___x_67_);
lean_dec_ref(v___x_69_);
v___x_71_ = lean_nat_sub(v___x_66_, v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_nat_dec_eq(v___x_71_, v___x_67_);
lean_dec(v___x_71_);
return v___x_72_;
}
else
{
uint8_t v___x_73_; 
lean_dec_ref(v_s_65_);
v___x_73_ = 0;
return v___x_73_;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(lean_object* v_as_98_, size_t v_i_99_, size_t v_stop_100_, lean_object* v_b_101_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0___boxed(lean_object* v_as_113_, lean_object* v_i_114_, lean_object* v_stop_115_, lean_object* v_b_116_){
_start:
{
size_t v_i_boxed_117_; size_t v_stop_boxed_118_; lean_object* v_res_119_; 
v_i_boxed_117_ = lean_unbox_usize(v_i_114_);
lean_dec(v_i_114_);
v_stop_boxed_118_ = lean_unbox_usize(v_stop_115_);
lean_dec(v_stop_115_);
v_res_119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_as_113_, v_i_boxed_117_, v_stop_boxed_118_, v_b_116_);
lean_dec_ref(v_as_113_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(lean_object* v_parts_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_121_ = lean_box(0);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_array_get_size(v_parts_120_);
v___x_124_ = lean_nat_dec_lt(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
return v___x_121_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = lean_nat_dec_le(v___x_123_, v___x_123_);
if (v___x_125_ == 0)
{
if (v___x_124_ == 0)
{
return v___x_121_;
}
else
{
size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v___x_126_ = ((size_t)0ULL);
v___x_127_ = lean_usize_of_nat(v___x_123_);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_parts_120_, v___x_126_, v___x_127_, v___x_121_);
return v___x_128_;
}
}
else
{
size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; 
v___x_129_ = ((size_t)0ULL);
v___x_130_ = lean_usize_of_nat(v___x_123_);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_parts_120_, v___x_129_, v___x_130_, v___x_121_);
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName___boxed(lean_object* v_parts_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(v_parts_132_);
lean_dec_ref(v_parts_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(lean_object* v_comps_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = lean_array_get_size(v_comps_135_);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_nat_dec_eq(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = 1;
v___x_140_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(v_comps_135_);
v___x_141_ = l_Lean_Name_toString(v___x_140_, v___x_139_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; 
v___x_142_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___boxed(lean_object* v_comps_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_comps_143_);
lean_dec_ref(v_comps_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(lean_object* v_c_173_){
_start:
{
if (lean_obj_tag(v_c_173_) == 0)
{
lean_object* v_s_176_; uint8_t v___y_178_; uint8_t v___y_187_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_s_176_ = lean_ctor_get(v_c_173_, 0);
lean_inc_ref(v_s_176_);
lean_dec_ref(v_c_173_);
v___x_200_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11));
v___x_201_ = lean_string_dec_eq(v_s_176_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12));
v___x_203_ = lean_string_dec_eq(v_s_176_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13));
v___x_205_ = lean_string_dec_eq(v_s_176_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_206_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14));
v___x_207_ = lean_string_dec_eq(v_s_176_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15));
v___x_209_ = lean_string_dec_eq(v_s_176_, v___x_208_);
v___y_187_ = v___x_209_;
goto v___jp_186_;
}
else
{
v___y_187_ = v___x_207_;
goto v___jp_186_;
}
}
else
{
lean_object* v___x_210_; 
lean_dec_ref(v_s_176_);
v___x_210_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__17));
return v___x_210_;
}
}
else
{
lean_object* v___x_211_; 
lean_dec_ref(v_s_176_);
v___x_211_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__19));
return v___x_211_;
}
}
else
{
lean_object* v___x_212_; 
lean_dec_ref(v_s_176_);
v___x_212_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__21));
return v___x_212_;
}
v___jp_177_:
{
if (v___y_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__2));
v___x_180_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_176_, v___x_179_);
if (lean_obj_tag(v___x_180_) == 0)
{
return v___x_180_;
}
else
{
lean_object* v_val_181_; uint8_t v___x_182_; 
v_val_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_val_181_);
lean_dec_ref(v___x_180_);
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
else
{
lean_object* v___x_185_; 
lean_dec_ref(v_s_176_);
v___x_185_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_185_;
}
}
v___jp_186_:
{
if (v___y_187_ == 0)
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3));
v___x_189_ = lean_string_dec_eq(v_s_176_, v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4));
v___x_191_ = lean_string_dec_eq(v_s_176_, v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5));
v___x_193_ = lean_string_dec_eq(v_s_176_, v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6));
lean_inc_ref(v_s_176_);
v___x_195_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_176_, v___x_194_);
if (lean_obj_tag(v___x_195_) == 0)
{
v___y_178_ = v___x_193_;
goto v___jp_177_;
}
else
{
lean_object* v_val_196_; uint8_t v___x_197_; 
v_val_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_val_196_);
lean_dec_ref(v___x_195_);
v___x_197_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_196_);
v___y_178_ = v___x_197_;
goto v___jp_177_;
}
}
else
{
lean_object* v___x_198_; 
lean_dec_ref(v_s_176_);
v___x_198_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8));
return v___x_198_;
}
}
else
{
lean_object* v___x_199_; 
lean_dec_ref(v_s_176_);
v___x_199_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10));
return v___x_199_;
}
}
else
{
lean_dec_ref(v_s_176_);
goto v___jp_174_;
}
}
else
{
lean_dec_ref(v_s_176_);
goto v___jp_174_;
}
}
}
else
{
lean_object* v___x_213_; 
lean_dec_ref(v_c_173_);
v___x_213_ = lean_box(0);
return v___x_213_;
}
v___jp_174_:
{
lean_object* v___x_175_; 
v___x_175_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_175_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(lean_object* v_c_215_){
_start:
{
if (lean_obj_tag(v_c_215_) == 0)
{
lean_object* v_s_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_s_216_ = lean_ctor_get(v_c_215_, 0);
lean_inc_ref(v_s_216_);
lean_dec_ref(v_c_215_);
v___x_217_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___closed__0));
v___x_218_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_216_, v___x_217_);
if (lean_obj_tag(v___x_218_) == 0)
{
uint8_t v___x_219_; 
v___x_219_ = 0;
return v___x_219_;
}
else
{
lean_object* v_val_220_; uint8_t v___x_221_; 
v_val_220_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_val_220_);
lean_dec_ref(v___x_218_);
v___x_221_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_220_);
return v___x_221_;
}
}
else
{
uint8_t v___x_222_; 
lean_dec_ref(v_c_215_);
v___x_222_ = 0;
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___boxed(lean_object* v_c_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(v_c_223_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(lean_object* v_x_226_, lean_object* v_x_227_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
if (lean_obj_tag(v_x_227_) == 0)
{
uint8_t v___x_228_; 
v___x_228_ = 1;
return v___x_228_;
}
else
{
uint8_t v___x_229_; 
v___x_229_ = 0;
return v___x_229_;
}
}
else
{
if (lean_obj_tag(v_x_227_) == 0)
{
uint8_t v___x_230_; 
v___x_230_ = 0;
return v___x_230_;
}
else
{
lean_object* v_val_231_; lean_object* v_val_232_; uint8_t v___x_233_; 
v_val_231_ = lean_ctor_get(v_x_226_, 0);
v_val_232_ = lean_ctor_get(v_x_227_, 0);
v___x_233_ = l_Lean_instBEqNamePart_beq(v_val_231_, v_val_232_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0___boxed(lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v_x_234_, v_x_235_);
lean_dec(v_x_235_);
lean_dec(v_x_234_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(lean_object* v_stop_245_, lean_object* v_start_246_, uint8_t v___y_247_, lean_object* v_comps_248_, lean_object* v_range_249_, lean_object* v_b_250_, lean_object* v_i_251_){
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
return v_b_250_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___y_260_; lean_object* v___x_275_; uint8_t v___x_276_; 
lean_dec_ref(v_b_250_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_box(0);
v___x_257_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0));
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_array_get_size(v_comps_248_);
v___x_276_ = lean_nat_dec_lt(v_i_251_, v___x_275_);
if (v___x_276_ == 0)
{
v___y_260_ = v___x_255_;
goto v___jp_259_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_array_fget_borrowed(v_comps_248_, v_i_251_);
lean_inc(v___x_277_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
v___y_260_ = v___x_278_;
goto v___jp_259_;
}
v___jp_259_:
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2));
v___x_262_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_260_, v___x_261_);
lean_dec(v___y_260_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
v___x_263_ = lean_nat_add(v_i_251_, v_step_253_);
lean_dec(v_i_251_);
v_b_250_ = v___x_257_;
v_i_251_ = v___x_263_;
goto _start;
}
else
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = lean_nat_add(v_i_251_, v___x_258_);
lean_dec(v_i_251_);
v___x_266_ = lean_nat_dec_lt(v___x_265_, v_stop_245_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec(v___x_265_);
v___x_267_ = lean_box(v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_start_246_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_256_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec(v_start_246_);
v___x_271_ = lean_box(v___y_247_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_265_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_256_);
return v___x_274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___boxed(lean_object* v_stop_279_, lean_object* v_start_280_, lean_object* v___y_281_, lean_object* v_comps_282_, lean_object* v_range_283_, lean_object* v_b_284_, lean_object* v_i_285_){
_start:
{
uint8_t v___y_946__boxed_286_; lean_object* v_res_287_; 
v___y_946__boxed_286_ = lean_unbox(v___y_281_);
v_res_287_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_279_, v_start_280_, v___y_946__boxed_286_, v_comps_282_, v_range_283_, v_b_284_, v_i_285_);
lean_dec_ref(v_range_283_);
lean_dec_ref(v_comps_282_);
lean_dec(v_stop_279_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(lean_object* v_comps_293_, lean_object* v_start_294_, lean_object* v_stop_295_){
_start:
{
uint8_t v___y_297_; lean_object* v___y_318_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_321_ = lean_unsigned_to_nat(3u);
v___x_322_ = lean_nat_sub(v_stop_295_, v_start_294_);
v___x_323_ = lean_nat_dec_le(v___x_321_, v___x_322_);
lean_dec(v___x_322_);
if (v___x_323_ == 0)
{
v___y_297_ = v___x_323_;
goto v___jp_296_;
}
else
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_array_get_size(v_comps_293_);
v___x_325_ = lean_nat_dec_lt(v_start_294_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
v___x_326_ = lean_box(0);
v___y_318_ = v___x_326_;
goto v___jp_317_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_array_fget_borrowed(v_comps_293_, v_start_294_);
lean_inc(v___x_327_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
v___y_318_ = v___x_328_;
goto v___jp_317_;
}
}
v___jp_296_:
{
if (v___y_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v_stop_295_);
v___x_298_ = lean_box(v___y_297_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_start_294_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_fst_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_315_; 
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_add(v_start_294_, v___x_300_);
lean_inc(v_stop_295_);
lean_inc(v___x_301_);
v___x_302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v_stop_295_);
lean_ctor_set(v___x_302_, 2, v___x_300_);
v___x_303_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0));
lean_inc(v_start_294_);
v___x_304_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_295_, v_start_294_, v___y_297_, v_comps_293_, v___x_302_, v___x_303_, v___x_301_);
lean_dec_ref(v___x_302_);
lean_dec(v_stop_295_);
v_fst_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; 
v_unused_316_ = lean_ctor_get(v___x_304_, 1);
lean_dec(v_unused_316_);
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_315_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_fst_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_315_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
if (lean_obj_tag(v_fst_305_) == 0)
{
uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_309_ = 0;
v___x_310_ = lean_box(v___x_309_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_310_);
lean_ctor_set(v___x_307_, 0, v_start_294_);
v___x_312_ = v___x_307_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_start_294_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
lean_object* v_val_314_; 
lean_del_object(v___x_307_);
lean_dec(v_start_294_);
v_val_314_ = lean_ctor_get(v_fst_305_, 0);
lean_inc(v_val_314_);
lean_dec_ref(v_fst_305_);
return v_val_314_;
}
}
}
}
v___jp_317_:
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2));
v___x_320_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_318_, v___x_319_);
lean_dec(v___y_318_);
v___y_297_ = v___x_320_;
goto v___jp_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___boxed(lean_object* v_comps_329_, lean_object* v_start_330_, lean_object* v_stop_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_comps_329_, v_start_330_, v_stop_331_);
lean_dec_ref(v_comps_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(lean_object* v_stop_333_, lean_object* v_start_334_, uint8_t v___y_335_, lean_object* v_comps_336_, lean_object* v_range_337_, lean_object* v_b_338_, lean_object* v_i_339_, lean_object* v_hs_340_, lean_object* v_hl_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_333_, v_start_334_, v___y_335_, v_comps_336_, v_range_337_, v_b_338_, v_i_339_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___boxed(lean_object* v_stop_343_, lean_object* v_start_344_, lean_object* v___y_345_, lean_object* v_comps_346_, lean_object* v_range_347_, lean_object* v_b_348_, lean_object* v_i_349_, lean_object* v_hs_350_, lean_object* v_hl_351_){
_start:
{
uint8_t v___y_1088__boxed_352_; lean_object* v_res_353_; 
v___y_1088__boxed_352_ = lean_unbox(v___y_345_);
v_res_353_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(v_stop_343_, v_start_344_, v___y_1088__boxed_352_, v_comps_346_, v_range_347_, v_b_348_, v_i_349_, v_hs_350_, v_hl_351_);
lean_dec_ref(v_range_347_);
lean_dec_ref(v_comps_346_);
lean_dec(v_stop_343_);
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
v___x_371_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_369_, v___x_370_);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(lean_object* v_a_385_, lean_object* v_as_386_, size_t v_i_387_, size_t v_stop_388_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0___boxed(lean_object* v_a_396_, lean_object* v_as_397_, lean_object* v_i_398_, lean_object* v_stop_399_){
_start:
{
size_t v_i_boxed_400_; size_t v_stop_boxed_401_; uint8_t v_res_402_; lean_object* v_r_403_; 
v_i_boxed_400_ = lean_unbox_usize(v_i_398_);
lean_dec(v_i_398_);
v_stop_boxed_401_ = lean_unbox_usize(v_stop_399_);
lean_dec(v_stop_399_);
v_res_402_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_396_, v_as_397_, v_i_boxed_400_, v_stop_boxed_401_);
lean_dec_ref(v_as_397_);
lean_dec_ref(v_a_396_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(lean_object* v_as_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_array_get_size(v_as_404_);
v___x_408_ = lean_nat_dec_lt(v___x_406_, v___x_407_);
if (v___x_408_ == 0)
{
return v___x_408_;
}
else
{
if (v___x_408_ == 0)
{
return v___x_408_;
}
else
{
size_t v___x_409_; size_t v___x_410_; uint8_t v___x_411_; 
v___x_409_ = ((size_t)0ULL);
v___x_410_ = lean_usize_of_nat(v___x_407_);
v___x_411_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_405_, v_as_404_, v___x_409_, v___x_410_);
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0___boxed(lean_object* v_as_412_, lean_object* v_a_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_as_412_, v_a_413_);
lean_dec_ref(v_a_413_);
lean_dec_ref(v_as_412_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(lean_object* v_comps_416_, lean_object* v_range_417_, lean_object* v_b_418_, lean_object* v_i_419_){
_start:
{
lean_object* v_stop_420_; lean_object* v_step_421_; lean_object* v_a_423_; uint8_t v___x_426_; 
v_stop_420_ = lean_ctor_get(v_range_417_, 1);
v_step_421_ = lean_ctor_get(v_range_417_, 2);
v___x_426_ = lean_nat_dec_lt(v_i_419_, v_stop_420_);
if (v___x_426_ == 0)
{
lean_dec(v_i_419_);
return v_b_418_;
}
else
{
lean_object* v_fst_427_; lean_object* v_snd_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_452_; 
v_fst_427_ = lean_ctor_get(v_b_418_, 0);
v_snd_428_ = lean_ctor_get(v_b_418_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v_b_418_);
if (v_isSharedCheck_452_ == 0)
{
v___x_430_ = v_b_418_;
v_isShared_431_ = v_isSharedCheck_452_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_snd_428_);
lean_inc(v_fst_427_);
lean_dec(v_b_418_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_452_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = l_Lean_instInhabitedNamePart_default;
v___x_433_ = lean_array_get_borrowed(v___x_432_, v_comps_416_, v_i_419_);
lean_inc(v___x_433_);
v___x_434_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_433_);
if (lean_obj_tag(v___x_434_) == 0)
{
uint8_t v___x_435_; 
lean_inc(v___x_433_);
v___x_435_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(v___x_433_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_438_; 
lean_inc(v___x_433_);
v___x_436_ = lean_array_push(v_fst_427_, v___x_433_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_436_);
v___x_438_ = v___x_430_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_snd_428_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
v_a_423_ = v___x_438_;
goto v___jp_422_;
}
}
else
{
lean_object* v___x_441_; 
if (v_isShared_431_ == 0)
{
v___x_441_ = v___x_430_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_fst_427_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_snd_428_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
v_a_423_ = v___x_441_;
goto v___jp_422_;
}
}
}
else
{
lean_object* v_val_443_; uint8_t v___x_444_; 
v_val_443_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_val_443_);
lean_dec_ref(v___x_434_);
v___x_444_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_snd_428_, v_val_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = lean_array_push(v_snd_428_, v_val_443_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v___x_445_);
v___x_447_ = v___x_430_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_fst_427_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
v_a_423_ = v___x_447_;
goto v___jp_422_;
}
}
else
{
lean_object* v___x_450_; 
lean_dec(v_val_443_);
if (v_isShared_431_ == 0)
{
v___x_450_ = v___x_430_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_fst_427_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_snd_428_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
v_a_423_ = v___x_450_;
goto v___jp_422_;
}
}
}
}
}
v___jp_422_:
{
lean_object* v___x_424_; 
v___x_424_ = lean_nat_add(v_i_419_, v_step_421_);
lean_dec(v_i_419_);
v_b_418_ = v_a_423_;
v_i_419_ = v___x_424_;
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
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1(void){
_start:
{
lean_object* v_parts_460_; lean_object* v___x_461_; 
v_parts_460_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0));
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_parts_460_);
lean_ctor_set(v___x_461_, 1, v_parts_460_);
return v___x_461_;
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
v___x_468_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1);
v___x_469_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_462_, v___x_467_, v___x_468_, v_begin___464_);
lean_dec_ref(v___x_467_);
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
lean_dec_ref(v___x_486_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(lean_object* v___x_551_, lean_object* v_as_552_, size_t v_sz_553_, size_t v_i_554_, lean_object* v_b_555_){
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
lean_inc_ref(v_name_566_);
v_flags_567_ = lean_ctor_get(v___x_563_, 1);
lean_inc_ref(v_flags_567_);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_string_utf8_byte_size(v_name_566_);
lean_dec_ref(v_name_566_);
v___x_570_ = lean_nat_dec_eq(v___x_569_, v___x_568_);
if (v___x_570_ == 0)
{
lean_dec_ref(v_flags_567_);
goto v___jp_564_;
}
else
{
uint8_t v_cont_571_; 
v_cont_571_ = lean_nat_dec_eq(v___x_551_, v___x_568_);
if (v_cont_571_ == 0)
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = lean_array_get_size(v_flags_567_);
lean_dec_ref(v_flags_567_);
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
lean_dec_ref(v_flags_567_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5___boxed(lean_object* v___x_574_, lean_object* v_as_575_, lean_object* v_sz_576_, lean_object* v_i_577_, lean_object* v_b_578_){
_start:
{
size_t v_sz_boxed_579_; size_t v_i_boxed_580_; lean_object* v_res_581_; 
v_sz_boxed_579_ = lean_unbox_usize(v_sz_576_);
lean_dec(v_sz_576_);
v_i_boxed_580_ = lean_unbox_usize(v_i_577_);
lean_dec(v_i_577_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_574_, v_as_575_, v_sz_boxed_579_, v_i_boxed_580_, v_b_578_);
lean_dec_ref(v_as_575_);
lean_dec(v___x_574_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(lean_object* v___x_582_, lean_object* v_b_583_){
_start:
{
lean_object* v_snd_584_; lean_object* v_fst_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_644_; 
v_snd_584_ = lean_ctor_get(v_b_583_, 1);
v_fst_585_ = lean_ctor_get(v_b_583_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v_b_583_);
if (v_isSharedCheck_644_ == 0)
{
v___x_587_ = v_b_583_;
v_isShared_588_ = v_isSharedCheck_644_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_snd_584_);
lean_inc(v_fst_585_);
lean_dec(v_b_583_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_644_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_fst_589_; lean_object* v_snd_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_643_; 
v_fst_589_ = lean_ctor_get(v_snd_584_, 0);
v_snd_590_ = lean_ctor_get(v_snd_584_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_snd_584_);
if (v_isSharedCheck_643_ == 0)
{
v___x_592_ = v_snd_584_;
v_isShared_593_ = v_isSharedCheck_643_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_snd_590_);
lean_inc(v_fst_589_);
lean_dec(v_snd_584_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_643_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
uint8_t v___x_601_; 
v___x_601_ = lean_unbox(v_snd_590_);
if (v___x_601_ == 0)
{
goto v___jp_594_;
}
else
{
lean_object* v___x_602_; uint8_t v_cont_603_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_602_ = lean_unsigned_to_nat(0u);
v_cont_603_ = lean_nat_dec_eq(v___x_582_, v___x_602_);
v___x_641_ = lean_array_get_size(v_fst_585_);
v___x_642_ = lean_nat_dec_eq(v___x_641_, v___x_602_);
if (v___x_642_ == 0)
{
lean_del_object(v___x_592_);
lean_del_object(v___x_587_);
goto v___jp_604_;
}
else
{
if (v_cont_603_ == 0)
{
goto v___jp_594_;
}
else
{
lean_del_object(v___x_592_);
lean_del_object(v___x_587_);
goto v___jp_604_;
}
}
v___jp_604_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v_last_609_; lean_object* v___x_610_; 
v___x_605_ = l_Lean_instInhabitedNamePart_default;
v___x_606_ = lean_array_get_size(v_fst_585_);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = lean_nat_sub(v___x_606_, v___x_607_);
v_last_609_ = lean_array_get_borrowed(v___x_605_, v_fst_585_, v___x_608_);
lean_dec(v___x_608_);
lean_inc(v_last_609_);
v___x_610_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v_last_609_);
if (lean_obj_tag(v___x_610_) == 0)
{
if (lean_obj_tag(v_last_609_) == 1)
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(2u);
v___x_612_ = lean_nat_dec_le(v___x_611_, v___x_606_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec(v_snd_590_);
v___x_613_ = lean_box(v_cont_603_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v_fst_589_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v_fst_585_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v_b_583_ = v___x_615_;
goto _start;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = lean_nat_sub(v___x_606_, v___x_611_);
v___x_618_ = lean_array_get_borrowed(v___x_605_, v_fst_585_, v___x_617_);
lean_dec(v___x_617_);
lean_inc(v___x_618_);
v___x_619_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_618_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v_snd_590_);
v___x_620_ = lean_box(v_cont_603_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_fst_589_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v_fst_585_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v_b_583_ = v___x_622_;
goto _start;
}
else
{
lean_object* v_val_624_; lean_object* v_flags_625_; lean_object* v___x_626_; lean_object* v_parts_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_val_624_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_val_624_);
lean_dec_ref(v___x_619_);
v_flags_625_ = lean_array_push(v_fst_589_, v_val_624_);
v___x_626_ = lean_array_pop(v_fst_585_);
v_parts_627_ = lean_array_pop(v___x_626_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v_flags_625_);
lean_ctor_set(v___x_628_, 1, v_snd_590_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_parts_627_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v_b_583_ = v___x_629_;
goto _start;
}
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v_snd_590_);
v___x_631_ = lean_box(v_cont_603_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v_fst_589_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v_fst_585_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v_b_583_ = v___x_633_;
goto _start;
}
}
else
{
lean_object* v_val_635_; lean_object* v_flags_636_; lean_object* v_parts_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_val_635_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_val_635_);
lean_dec_ref(v___x_610_);
v_flags_636_ = lean_array_push(v_fst_589_, v_val_635_);
v_parts_637_ = lean_array_pop(v_fst_585_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v_flags_636_);
lean_ctor_set(v___x_638_, 1, v_snd_590_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v_parts_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v_b_583_ = v___x_639_;
goto _start;
}
}
}
v___jp_594_:
{
lean_object* v___x_596_; 
if (v_isShared_593_ == 0)
{
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_fst_589_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_snd_590_);
v___x_596_ = v_reuseFailAlloc_600_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_598_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_596_);
v___x_598_ = v___x_587_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_fst_585_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___boxed(lean_object* v___x_645_, lean_object* v_b_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(v___x_645_, v_b_646_);
lean_dec(v___x_645_);
return v_res_647_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0));
v___x_650_ = lean_string_utf8_byte_size(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(lean_object* v___x_651_, lean_object* v_range_652_, lean_object* v_b_653_, lean_object* v_i_654_){
_start:
{
lean_object* v_stop_655_; lean_object* v_step_656_; lean_object* v_a_658_; uint8_t v___x_661_; 
v_stop_655_ = lean_ctor_get(v_range_652_, 1);
v_step_656_ = lean_ctor_get(v_range_652_, 2);
v___x_661_ = lean_nat_dec_lt(v_i_654_, v_stop_655_);
if (v___x_661_ == 0)
{
lean_dec(v_i_654_);
lean_inc_ref(v_b_653_);
return v_b_653_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = l_Lean_instInhabitedNamePart_default;
v___x_663_ = lean_array_get_borrowed(v___x_662_, v_b_653_, v_i_654_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_s_664_; lean_object* v___x_665_; uint8_t v___y_667_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_s_664_ = lean_ctor_get(v___x_663_, 0);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_669_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0));
v___x_670_ = lean_string_utf8_byte_size(v_s_664_);
v___x_671_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1);
v___x_672_ = lean_nat_dec_le(v___x_671_, v___x_670_);
if (v___x_672_ == 0)
{
uint8_t v_cont_673_; 
v_cont_673_ = lean_nat_dec_eq(v___x_651_, v___x_665_);
v___y_667_ = v_cont_673_;
goto v___jp_666_;
}
else
{
uint8_t v___x_674_; 
v___x_674_ = lean_string_memcmp(v_s_664_, v___x_669_, v___x_665_, v___x_665_, v___x_671_);
v___y_667_ = v___x_674_;
goto v___jp_666_;
}
v___jp_666_:
{
if (v___y_667_ == 0)
{
v_a_658_ = v_b_653_;
goto v___jp_657_;
}
else
{
lean_object* v___x_668_; 
v___x_668_ = l_Array_extract___redArg(v_b_653_, v___x_665_, v_i_654_);
return v___x_668_;
}
}
}
else
{
v_a_658_ = v_b_653_;
goto v___jp_657_;
}
}
v___jp_657_:
{
lean_object* v___x_659_; 
v___x_659_ = lean_nat_add(v_i_654_, v_step_656_);
lean_dec(v_i_654_);
v_b_653_ = v_a_658_;
v_i_654_ = v___x_659_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___boxed(lean_object* v___x_675_, lean_object* v_range_676_, lean_object* v_b_677_, lean_object* v_i_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_675_, v_range_676_, v_b_677_, v_i_678_);
lean_dec_ref(v_b_677_);
lean_dec_ref(v_range_676_);
lean_dec(v___x_675_);
return v_res_679_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0));
v___x_684_ = lean_string_utf8_byte_size(v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(lean_object* v___x_687_, lean_object* v___x_688_, lean_object* v_range_689_, lean_object* v_b_690_, lean_object* v_i_691_){
_start:
{
lean_object* v_stop_692_; lean_object* v_step_693_; lean_object* v_a_695_; uint8_t v___x_698_; 
v_stop_692_ = lean_ctor_get(v_range_689_, 1);
v_step_693_ = lean_ctor_get(v_range_689_, 2);
v___x_698_ = lean_nat_dec_lt(v_i_691_, v_stop_692_);
if (v___x_698_ == 0)
{
lean_dec(v_i_691_);
return v_b_690_;
}
else
{
lean_object* v_snd_699_; lean_object* v_snd_700_; lean_object* v_fst_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_816_; 
v_snd_699_ = lean_ctor_get(v_b_690_, 1);
lean_inc(v_snd_699_);
v_snd_700_ = lean_ctor_get(v_snd_699_, 1);
lean_inc(v_snd_700_);
v_fst_701_ = lean_ctor_get(v_b_690_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v_b_690_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v_b_690_, 1);
lean_dec(v_unused_817_);
v___x_703_ = v_b_690_;
v_isShared_704_ = v_isSharedCheck_816_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_fst_701_);
lean_dec(v_b_690_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_816_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_fst_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_814_; 
v_fst_705_ = lean_ctor_get(v_snd_699_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_snd_699_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v_snd_699_, 1);
lean_dec(v_unused_815_);
v___x_707_ = v_snd_699_;
v_isShared_708_ = v_isSharedCheck_814_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_fst_705_);
lean_dec(v_snd_699_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_814_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_813_; 
v_fst_709_ = lean_ctor_get(v_snd_700_, 0);
v_snd_710_ = lean_ctor_get(v_snd_700_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_snd_700_);
if (v_isSharedCheck_813_ == 0)
{
v___x_712_ = v_snd_700_;
v_isShared_713_ = v_isSharedCheck_813_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snd_710_);
lean_inc(v_fst_709_);
lean_dec(v_snd_700_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_813_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; uint8_t v_cont_715_; uint8_t v___x_716_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v_cont_715_ = lean_nat_dec_eq(v___x_688_, v___x_714_);
v___x_716_ = lean_unbox(v_snd_710_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_717_ = l_Lean_instInhabitedNamePart_default;
v___x_718_ = lean_array_get_borrowed(v___x_717_, v___x_687_, v_i_691_);
v___x_719_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1));
v___x_720_ = l_Lean_instBEqNamePart_beq(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; uint8_t v___y_723_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v_cont_774_; lean_object* v_entries_776_; lean_object* v_currentCtx_777_; 
v___x_721_ = lean_box(0);
v___x_772_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0));
v___x_773_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1));
v_cont_774_ = l_Lean_instBEqNamePart_beq(v___x_718_, v___x_773_);
if (v_cont_774_ == 0)
{
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_s_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_s_782_ = lean_ctor_get(v___x_718_, 0);
v___x_783_ = lean_string_utf8_byte_size(v_s_782_);
v___x_784_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2);
v___x_785_ = lean_nat_dec_le(v___x_784_, v___x_783_);
if (v___x_785_ == 0)
{
v___y_723_ = v_cont_774_;
goto v___jp_722_;
}
else
{
uint8_t v___x_786_; 
v___x_786_ = lean_string_memcmp(v_s_782_, v___x_772_, v___x_714_, v___x_714_, v___x_784_);
v___y_723_ = v___x_786_;
goto v___jp_722_;
}
}
else
{
v___y_723_ = v_cont_715_;
goto v___jp_722_;
}
}
else
{
lean_del_object(v___x_712_);
lean_dec(v_snd_710_);
lean_del_object(v___x_707_);
lean_del_object(v___x_703_);
if (lean_obj_tag(v_fst_705_) == 1)
{
lean_object* v_val_787_; lean_object* v___x_788_; 
v_val_787_ = lean_ctor_get(v_fst_705_, 0);
lean_inc(v_val_787_);
lean_dec_ref(v_fst_705_);
v___x_788_ = lean_array_push(v_fst_701_, v_val_787_);
v_entries_776_ = v___x_788_;
v_currentCtx_777_ = v___x_721_;
goto v___jp_775_;
}
else
{
v_entries_776_ = v_fst_701_;
v_currentCtx_777_ = v_fst_705_;
goto v___jp_775_;
}
}
v___jp_722_:
{
if (v___y_723_ == 0)
{
if (lean_obj_tag(v_fst_705_) == 0)
{
lean_object* v___x_724_; lean_object* v___x_726_; 
lean_inc(v___x_718_);
v___x_724_ = lean_array_push(v_fst_709_, v___x_718_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_724_);
v___x_726_ = v___x_712_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_snd_710_);
v___x_726_ = v_reuseFailAlloc_733_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_726_);
v___x_728_ = v___x_707_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_fst_705_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_728_);
v___x_730_ = v___x_703_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_fst_701_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
v_a_695_ = v___x_730_;
goto v___jp_694_;
}
}
}
}
else
{
lean_object* v_val_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_751_; 
v_val_734_ = lean_ctor_get(v_fst_705_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v_fst_705_);
if (v_isSharedCheck_751_ == 0)
{
v___x_736_ = v_fst_705_;
v_isShared_737_ = v_isSharedCheck_751_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_val_734_);
lean_dec(v_fst_705_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_751_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_740_; 
lean_inc(v___x_718_);
v___x_738_ = lean_array_push(v_val_734_, v___x_718_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_738_);
v___x_740_ = v___x_736_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_750_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_742_; 
if (v_isShared_713_ == 0)
{
v___x_742_ = v___x_712_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_fst_709_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_snd_710_);
v___x_742_ = v_reuseFailAlloc_749_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_744_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_742_);
lean_ctor_set(v___x_707_, 0, v___x_740_);
v___x_744_ = v___x_707_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_742_);
v___x_744_ = v_reuseFailAlloc_748_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_744_);
v___x_746_ = v___x_703_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_fst_701_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
v_a_695_ = v___x_746_;
goto v___jp_694_;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_fst_705_) == 1)
{
lean_object* v_val_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v_val_752_ = lean_ctor_get(v_fst_705_, 0);
lean_inc(v_val_752_);
lean_dec_ref(v_fst_705_);
v___x_753_ = lean_array_push(v_fst_701_, v_val_752_);
if (v_isShared_713_ == 0)
{
v___x_755_ = v___x_712_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_fst_709_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_snd_710_);
v___x_755_ = v_reuseFailAlloc_762_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_757_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_755_);
lean_ctor_set(v___x_707_, 0, v___x_721_);
v___x_757_ = v___x_707_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_755_);
v___x_757_ = v_reuseFailAlloc_761_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_759_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_757_);
lean_ctor_set(v___x_703_, 0, v___x_753_);
v___x_759_ = v___x_703_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
v_a_695_ = v___x_759_;
goto v___jp_694_;
}
}
}
}
else
{
lean_object* v___x_764_; 
if (v_isShared_713_ == 0)
{
v___x_764_ = v___x_712_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_fst_709_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_snd_710_);
v___x_764_ = v_reuseFailAlloc_771_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_766_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_764_);
v___x_766_ = v___x_707_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_fst_705_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_764_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_766_);
v___x_768_ = v___x_703_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_fst_701_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
v_a_695_ = v___x_768_;
goto v___jp_694_;
}
}
}
}
}
}
v___jp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_778_ = lean_box(v_cont_774_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v_fst_709_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v_currentCtx_777_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v_entries_776_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v_a_695_ = v___x_781_;
goto v___jp_694_;
}
}
else
{
lean_object* v_entries_790_; 
if (lean_obj_tag(v_fst_705_) == 1)
{
lean_object* v_val_801_; lean_object* v___x_802_; 
v_val_801_ = lean_ctor_get(v_fst_705_, 0);
lean_inc(v_val_801_);
lean_dec_ref(v_fst_705_);
v___x_802_ = lean_array_push(v_fst_701_, v_val_801_);
v_entries_790_ = v___x_802_;
goto v___jp_789_;
}
else
{
lean_dec(v_fst_705_);
v_entries_790_ = v_fst_701_;
goto v___jp_789_;
}
v___jp_789_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__3));
if (v_isShared_713_ == 0)
{
v___x_793_ = v___x_712_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_fst_709_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_snd_710_);
v___x_793_ = v_reuseFailAlloc_800_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_793_);
lean_ctor_set(v___x_707_, 0, v___x_791_);
v___x_795_ = v___x_707_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_793_);
v___x_795_ = v_reuseFailAlloc_799_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_797_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_795_);
lean_ctor_set(v___x_703_, 0, v_entries_790_);
v___x_797_ = v___x_703_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_entries_790_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
v_a_695_ = v___x_797_;
goto v___jp_694_;
}
}
}
}
}
}
else
{
lean_object* v___x_803_; lean_object* v___x_805_; 
lean_dec(v_snd_710_);
v___x_803_ = lean_box(v_cont_715_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v___x_803_);
v___x_805_ = v___x_712_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_fst_709_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_803_);
v___x_805_ = v_reuseFailAlloc_812_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_805_);
v___x_807_ = v___x_707_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_fst_705_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_805_);
v___x_807_ = v_reuseFailAlloc_811_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_809_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_807_);
v___x_809_ = v___x_703_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_fst_701_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
v_a_695_ = v___x_809_;
goto v___jp_694_;
}
}
}
}
}
}
}
}
v___jp_694_:
{
lean_object* v___x_696_; 
v___x_696_ = lean_nat_add(v_i_691_, v_step_693_);
lean_dec(v_i_691_);
v_b_690_ = v_a_695_;
v_i_691_ = v___x_696_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___boxed(lean_object* v___x_818_, lean_object* v___x_819_, lean_object* v_range_820_, lean_object* v_b_821_, lean_object* v_i_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_818_, v___x_819_, v_range_820_, v_b_821_, v_i_822_);
lean_dec_ref(v_range_820_);
lean_dec(v___x_819_);
lean_dec_ref(v___x_818_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(lean_object* v___x_829_, lean_object* v_as_830_, size_t v_sz_831_, size_t v_i_832_, lean_object* v_b_833_){
_start:
{
lean_object* v_a_835_; lean_object* v___y_840_; lean_object* v___y_841_; uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_lt(v_i_832_, v_sz_831_);
if (v___x_853_ == 0)
{
return v_b_833_;
}
else
{
lean_object* v_a_854_; lean_object* v_name_855_; lean_object* v___x_856_; uint8_t v_cont_857_; lean_object* v___y_859_; lean_object* v___x_866_; uint8_t v___x_867_; 
v_a_854_ = lean_array_uget_borrowed(v_as_830_, v_i_832_);
v_name_855_ = lean_ctor_get(v_a_854_, 0);
v___x_856_ = lean_unsigned_to_nat(0u);
v_cont_857_ = lean_nat_dec_eq(v___x_829_, v___x_856_);
v___x_866_ = lean_string_utf8_byte_size(v_name_855_);
v___x_867_ = lean_nat_dec_eq(v___x_866_, v___x_856_);
if (v___x_867_ == 0)
{
lean_inc_ref(v_name_855_);
v___y_859_ = v_name_855_;
goto v___jp_858_;
}
else
{
lean_object* v___x_868_; 
v___x_868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_859_ = v___x_868_;
goto v___jp_858_;
}
v___jp_858_:
{
lean_object* v_flags_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v_flags_860_ = lean_ctor_get(v_a_854_, 1);
v___x_861_ = lean_array_get_size(v_flags_860_);
v___x_862_ = lean_nat_dec_eq(v___x_861_, v___x_856_);
if (v___x_862_ == 0)
{
lean_inc_ref(v_flags_860_);
v___y_840_ = v_flags_860_;
v___y_841_ = v___y_859_;
goto v___jp_839_;
}
else
{
if (v_cont_857_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_864_ = lean_string_append(v_b_833_, v___x_863_);
v___x_865_ = lean_string_append(v___x_864_, v___y_859_);
lean_dec_ref(v___y_859_);
v_a_835_ = v___x_865_;
goto v___jp_834_;
}
else
{
lean_inc_ref(v_flags_860_);
v___y_840_ = v_flags_860_;
v___y_841_ = v___y_859_;
goto v___jp_839_;
}
}
}
}
v___jp_834_:
{
size_t v___x_836_; size_t v___x_837_; 
v___x_836_ = ((size_t)1ULL);
v___x_837_ = lean_usize_add(v_i_832_, v___x_836_);
v_i_832_ = v___x_837_;
v_b_833_ = v_a_835_;
goto _start;
}
v___jp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_843_ = lean_string_append(v_b_833_, v___x_842_);
v___x_844_ = lean_string_append(v___x_843_, v___y_841_);
lean_dec_ref(v___y_841_);
v___x_845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1));
v___x_846_ = lean_string_append(v___x_844_, v___x_845_);
v___x_847_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
v___x_848_ = lean_array_to_list(v___y_840_);
v___x_849_ = l_String_intercalate(v___x_847_, v___x_848_);
v___x_850_ = lean_string_append(v___x_846_, v___x_849_);
lean_dec_ref(v___x_849_);
v___x_851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_852_ = lean_string_append(v___x_850_, v___x_851_);
v_a_835_ = v___x_852_;
goto v___jp_834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___boxed(lean_object* v___x_869_, lean_object* v_as_870_, lean_object* v_sz_871_, lean_object* v_i_872_, lean_object* v_b_873_){
_start:
{
size_t v_sz_boxed_874_; size_t v_i_boxed_875_; lean_object* v_res_876_; 
v_sz_boxed_874_ = lean_unbox_usize(v_sz_871_);
lean_dec(v_sz_871_);
v_i_boxed_875_ = lean_unbox_usize(v_i_872_);
lean_dec(v_i_872_);
v_res_876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v___x_869_, v_as_870_, v_sz_boxed_874_, v_i_boxed_875_, v_b_873_);
lean_dec_ref(v_as_870_);
lean_dec(v___x_869_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(lean_object* v_components_885_){
_start:
{
lean_object* v___x_886_; lean_object* v___y_888_; lean_object* v_result_889_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___x_905_; uint8_t v_cont_906_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_914_; lean_object* v_parts_915_; lean_object* v_specEntries_916_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v_entries_926_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; 
v___x_886_ = lean_array_get_size(v_components_885_);
v___x_905_ = lean_unsigned_to_nat(0u);
v_cont_906_ = lean_nat_dec_eq(v___x_886_, v___x_905_);
if (v_cont_906_ == 0)
{
lean_object* v___x_939_; lean_object* v_fst_940_; lean_object* v_snd_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_995_; 
v___x_939_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_components_885_, v___x_905_, v___x_886_);
v_fst_940_ = lean_ctor_get(v___x_939_, 0);
v_snd_941_ = lean_ctor_get(v___x_939_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_995_ == 0)
{
v___x_943_ = v___x_939_;
v_isShared_944_ = v_isSharedCheck_995_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_snd_941_);
lean_inc(v_fst_940_);
lean_dec(v___x_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_995_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_parts_945_; lean_object* v_flags_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v_parts_945_ = l_Array_extract___redArg(v_components_885_, v_fst_940_, v___x_886_);
v_flags_946_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1));
v___x_947_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2));
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_947_);
lean_ctor_set(v___x_943_, 0, v_parts_945_);
v___x_949_ = v___x_943_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_parts_945_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_947_);
v___x_949_ = v_reuseFailAlloc_994_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v_fst_951_; lean_object* v_snd_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_993_; 
v___x_950_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(v___x_886_, v___x_949_);
v_fst_951_ = lean_ctor_get(v___x_950_, 0);
v_snd_952_ = lean_ctor_get(v___x_950_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_993_ == 0)
{
v___x_954_ = v___x_950_;
v_isShared_955_ = v_isSharedCheck_993_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_snd_952_);
lean_inc(v_fst_951_);
lean_dec(v___x_950_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_993_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_flags_957_; uint8_t v___x_988_; 
v___x_988_ = lean_unbox(v_snd_941_);
lean_dec(v_snd_941_);
if (v___x_988_ == 0)
{
lean_object* v_fst_989_; 
v_fst_989_ = lean_ctor_get(v_snd_952_, 0);
lean_inc(v_fst_989_);
lean_dec(v_snd_952_);
v_flags_957_ = v_fst_989_;
goto v___jp_956_;
}
else
{
lean_object* v_fst_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_fst_990_ = lean_ctor_get(v_snd_952_, 0);
lean_inc(v_fst_990_);
lean_dec(v_snd_952_);
v___x_991_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3));
v___x_992_ = lean_array_push(v_fst_990_, v___x_991_);
v_flags_957_ = v___x_992_;
goto v___jp_956_;
}
v___jp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_958_ = lean_array_get_size(v_fst_951_);
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_960_, 0, v___x_905_);
lean_ctor_set(v___x_960_, 1, v___x_958_);
lean_ctor_set(v___x_960_, 2, v___x_959_);
v___x_961_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_886_, v___x_960_, v_fst_951_, v___x_905_);
lean_dec(v_fst_951_);
lean_dec_ref(v___x_960_);
v___x_962_ = lean_box(0);
v___x_963_ = lean_array_get_size(v___x_961_);
v___x_964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_964_, 0, v___x_905_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
lean_ctor_set(v___x_964_, 2, v___x_959_);
v___x_965_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_961_, v___x_964_, v___x_962_, v___x_905_);
lean_dec_ref(v___x_964_);
if (lean_obj_tag(v___x_965_) == 1)
{
lean_object* v_val_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v_val_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_val_966_);
lean_dec_ref(v___x_965_);
lean_inc(v_val_966_);
v___x_967_ = l_Array_extract___redArg(v___x_961_, v___x_905_, v_val_966_);
v___x_968_ = l_Array_extract___redArg(v___x_961_, v_val_966_, v___x_963_);
lean_dec_ref(v___x_961_);
v___x_969_ = lean_array_get_size(v___x_968_);
v___x_970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_970_, 0, v___x_905_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
lean_ctor_set(v___x_970_, 2, v___x_959_);
v___x_971_ = lean_box(v_cont_906_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v___x_971_);
lean_ctor_set(v___x_954_, 0, v_flags_946_);
v___x_973_ = v___x_954_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_flags_946_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_971_);
v___x_973_ = v_reuseFailAlloc_987_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_snd_977_; lean_object* v_snd_978_; lean_object* v_fst_979_; 
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_962_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v_flags_946_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_968_, v___x_886_, v___x_970_, v___x_975_, v___x_905_);
lean_dec_ref(v___x_970_);
lean_dec_ref(v___x_968_);
v_snd_977_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_snd_977_);
v_snd_978_ = lean_ctor_get(v_snd_977_, 1);
lean_inc(v_snd_978_);
v_fst_979_ = lean_ctor_get(v_snd_977_, 0);
lean_inc(v_fst_979_);
lean_dec(v_snd_977_);
if (lean_obj_tag(v_fst_979_) == 1)
{
lean_object* v_fst_980_; lean_object* v_fst_981_; lean_object* v_val_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v_fst_980_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_fst_980_);
lean_dec_ref(v___x_976_);
v_fst_981_ = lean_ctor_get(v_snd_978_, 0);
lean_inc(v_fst_981_);
lean_dec(v_snd_978_);
v_val_982_ = lean_ctor_get(v_fst_979_, 0);
lean_inc(v_val_982_);
lean_dec_ref(v_fst_979_);
v___x_983_ = lean_array_get_size(v_val_982_);
v___x_984_ = lean_nat_dec_eq(v___x_983_, v___x_905_);
if (v___x_984_ == 0)
{
v___y_932_ = v___x_967_;
v___y_933_ = v_flags_946_;
v___y_934_ = v_fst_981_;
v___y_935_ = v_val_982_;
v___y_936_ = v_flags_957_;
v___y_937_ = v_fst_980_;
goto v___jp_931_;
}
else
{
if (v_cont_906_ == 0)
{
lean_dec(v_val_982_);
v___y_922_ = v___x_967_;
v___y_923_ = v_flags_946_;
v___y_924_ = v_fst_981_;
v___y_925_ = v_flags_957_;
v_entries_926_ = v_fst_980_;
goto v___jp_921_;
}
else
{
v___y_932_ = v___x_967_;
v___y_933_ = v_flags_946_;
v___y_934_ = v_fst_981_;
v___y_935_ = v_val_982_;
v___y_936_ = v_flags_957_;
v___y_937_ = v_fst_980_;
goto v___jp_931_;
}
}
}
else
{
lean_object* v_fst_985_; lean_object* v_fst_986_; 
lean_dec(v_fst_979_);
v_fst_985_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_fst_985_);
lean_dec_ref(v___x_976_);
v_fst_986_ = lean_ctor_get(v_snd_978_, 0);
lean_inc(v_fst_986_);
lean_dec(v_snd_978_);
v___y_922_ = v___x_967_;
v___y_923_ = v_flags_946_;
v___y_924_ = v_fst_986_;
v___y_925_ = v_flags_957_;
v_entries_926_ = v_fst_985_;
goto v___jp_921_;
}
}
}
else
{
lean_dec(v___x_965_);
lean_del_object(v___x_954_);
v___y_914_ = v_flags_957_;
v_parts_915_ = v___x_961_;
v_specEntries_916_ = v_flags_946_;
goto v___jp_913_;
}
}
}
}
}
}
else
{
lean_object* v___x_996_; 
v___x_996_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_996_;
}
v___jp_887_:
{
size_t v_sz_890_; size_t v___x_891_; lean_object* v___x_892_; 
v_sz_890_ = lean_array_size(v___y_888_);
v___x_891_ = ((size_t)0ULL);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v___x_886_, v___y_888_, v_sz_890_, v___x_891_, v_result_889_);
lean_dec_ref(v___y_888_);
return v___x_892_;
}
v___jp_893_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_897_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0));
v___x_898_ = lean_string_append(v___y_896_, v___x_897_);
v___x_899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
v___x_900_ = lean_array_to_list(v___y_895_);
v___x_901_ = l_String_intercalate(v___x_899_, v___x_900_);
v___x_902_ = lean_string_append(v___x_898_, v___x_901_);
lean_dec_ref(v___x_901_);
v___x_903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_904_ = lean_string_append(v___x_902_, v___x_903_);
v___y_888_ = v___y_894_;
v_result_889_ = v___x_904_;
goto v___jp_887_;
}
v___jp_907_:
{
lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = lean_array_get_size(v___y_909_);
v___x_912_ = lean_nat_dec_eq(v___x_911_, v___x_905_);
if (v___x_912_ == 0)
{
v___y_894_ = v___y_908_;
v___y_895_ = v___y_909_;
v___y_896_ = v___y_910_;
goto v___jp_893_;
}
else
{
if (v_cont_906_ == 0)
{
lean_dec_ref(v___y_909_);
v___y_888_ = v___y_908_;
v_result_889_ = v___y_910_;
goto v___jp_887_;
}
else
{
v___y_894_ = v___y_908_;
v___y_895_ = v___y_909_;
v___y_896_ = v___y_910_;
goto v___jp_893_;
}
}
}
v___jp_913_:
{
lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_917_ = lean_array_get_size(v_parts_915_);
v___x_918_ = lean_nat_dec_eq(v___x_917_, v___x_905_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
v___x_919_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_parts_915_);
lean_dec_ref(v_parts_915_);
v___y_908_ = v_specEntries_916_;
v___y_909_ = v___y_914_;
v___y_910_ = v___x_919_;
goto v___jp_907_;
}
else
{
lean_object* v___x_920_; 
lean_dec_ref(v_parts_915_);
v___x_920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_908_ = v_specEntries_916_;
v___y_909_ = v___y_914_;
v___y_910_ = v___x_920_;
goto v___jp_907_;
}
}
v___jp_921_:
{
size_t v_sz_927_; size_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_sz_927_ = lean_array_size(v_entries_926_);
v___x_928_ = ((size_t)0ULL);
v___x_929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_886_, v_entries_926_, v_sz_927_, v___x_928_, v___y_923_);
lean_dec_ref(v_entries_926_);
v___x_930_ = l_Array_append___redArg(v___y_922_, v___y_924_);
lean_dec(v___y_924_);
v___y_914_ = v___y_925_;
v_parts_915_ = v___x_930_;
v_specEntries_916_ = v___x_929_;
goto v___jp_913_;
}
v___jp_931_:
{
lean_object* v___x_938_; 
v___x_938_ = lean_array_push(v___y_937_, v___y_935_);
v___y_922_ = v___y_932_;
v___y_923_ = v___y_933_;
v___y_924_ = v___y_934_;
v___y_925_ = v___y_936_;
v_entries_926_ = v___x_938_;
goto v___jp_921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___boxed(lean_object* v_components_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v_components_997_);
lean_dec_ref(v_components_997_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(lean_object* v___x_999_, lean_object* v_range_1000_, lean_object* v_b_1001_, lean_object* v_i_1002_, lean_object* v_hs_1003_, lean_object* v_hl_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_999_, v_range_1000_, v_b_1001_, v_i_1002_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___boxed(lean_object* v___x_1006_, lean_object* v_range_1007_, lean_object* v_b_1008_, lean_object* v_i_1009_, lean_object* v_hs_1010_, lean_object* v_hl_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(v___x_1006_, v_range_1007_, v_b_1008_, v_i_1009_, v_hs_1010_, v_hl_1011_);
lean_dec_ref(v_b_1008_);
lean_dec_ref(v_range_1007_);
lean_dec(v___x_1006_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(lean_object* v___x_1013_, lean_object* v_range_1014_, lean_object* v_b_1015_, lean_object* v_i_1016_, lean_object* v_hs_1017_, lean_object* v_hl_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_1013_, v_range_1014_, v_b_1015_, v_i_1016_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___boxed(lean_object* v___x_1020_, lean_object* v_range_1021_, lean_object* v_b_1022_, lean_object* v_i_1023_, lean_object* v_hs_1024_, lean_object* v_hl_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(v___x_1020_, v_range_1021_, v_b_1022_, v_i_1023_, v_hs_1024_, v_hl_1025_);
lean_dec(v_b_1022_);
lean_dec_ref(v_range_1021_);
lean_dec_ref(v___x_1020_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(lean_object* v___x_1027_, lean_object* v___x_1028_, lean_object* v_range_1029_, lean_object* v_b_1030_, lean_object* v_i_1031_, lean_object* v_hs_1032_, lean_object* v_hl_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_1027_, v___x_1028_, v_range_1029_, v_b_1030_, v_i_1031_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___boxed(lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v_range_1037_, lean_object* v_b_1038_, lean_object* v_i_1039_, lean_object* v_hs_1040_, lean_object* v_hl_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(v___x_1035_, v___x_1036_, v_range_1037_, v_b_1038_, v_i_1039_, v_hs_1040_, v_hl_1041_);
lean_dec_ref(v_range_1037_);
lean_dec(v___x_1036_);
lean_dec_ref(v___x_1035_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(lean_object* v_body_1043_){
_start:
{
lean_object* v_name_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_name_1044_ = l_Lean_Name_demangle(v_body_1043_);
v___x_1045_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(v_name_1044_);
lean_dec(v_name_1044_);
v___x_1046_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v___x_1045_);
lean_dec_ref(v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody___boxed(lean_object* v_body_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_body_1047_);
lean_dec_ref(v_body_1047_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(lean_object* v_s_1052_, lean_object* v___x_1053_, lean_object* v_a_1054_, lean_object* v_b_1055_){
_start:
{
lean_object* v_startInclusive_1056_; lean_object* v_endExclusive_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_startInclusive_1056_ = lean_ctor_get(v___x_1053_, 1);
v_endExclusive_1057_ = lean_ctor_get(v___x_1053_, 2);
v___x_1058_ = lean_nat_sub(v_endExclusive_1057_, v_startInclusive_1056_);
v___x_1059_ = lean_nat_dec_eq(v_a_1054_, v___x_1058_);
lean_dec(v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___y_1078_; uint8_t v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1084_; uint8_t v___y_1085_; lean_object* v___y_1086_; uint8_t v___y_1087_; uint8_t v___y_1090_; uint32_t v___x_1101_; uint32_t v___x_1102_; uint8_t v___x_1103_; 
lean_dec_ref(v_b_1055_);
v___x_1060_ = lean_box(0);
v___x_1075_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1076_ = lean_string_utf8_next_fast(v_s_1052_, v_a_1054_);
v___x_1101_ = lean_string_utf8_get_fast(v_s_1052_, v_a_1054_);
v___x_1102_ = 95;
v___x_1103_ = lean_uint32_dec_eq(v___x_1101_, v___x_1102_);
if (v___x_1103_ == 0)
{
v___y_1090_ = v___x_1103_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = lean_nat_dec_eq(v_a_1054_, v___x_1104_);
if (v___x_1105_ == 0)
{
v___y_1090_ = v___x_1103_;
goto v___jp_1089_;
}
else
{
lean_dec(v_a_1054_);
v_a_1054_ = v___x_1076_;
v_b_1055_ = v___x_1075_;
goto _start;
}
}
v___jp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1064_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v___y_1062_);
lean_dec_ref(v___y_1062_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___y_1063_);
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_1060_);
v___x_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
v___jp_1069_:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Name_demangle(v___y_1071_);
if (lean_obj_tag(v___x_1072_) == 1)
{
lean_object* v_pre_1073_; 
v_pre_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_pre_1073_);
if (lean_obj_tag(v_pre_1073_) == 0)
{
lean_object* v_str_1074_; 
lean_dec_ref(v___y_1071_);
v_str_1074_ = lean_ctor_get(v___x_1072_, 1);
lean_inc_ref(v_str_1074_);
lean_dec_ref(v___x_1072_);
v___y_1062_ = v___y_1070_;
v___y_1063_ = v_str_1074_;
goto v___jp_1061_;
}
else
{
lean_dec(v_pre_1073_);
lean_dec_ref(v___x_1072_);
v___y_1062_ = v___y_1070_;
v___y_1063_ = v___y_1071_;
goto v___jp_1061_;
}
}
else
{
lean_dec(v___x_1072_);
v___y_1062_ = v___y_1070_;
v___y_1063_ = v___y_1071_;
goto v___jp_1061_;
}
}
v___jp_1077_:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_Name_demangle_x3f(v___y_1078_);
if (lean_obj_tag(v___x_1081_) == 0)
{
if (v___y_1079_ == 0)
{
lean_dec_ref(v___y_1080_);
lean_dec_ref(v___y_1078_);
v_a_1054_ = v___x_1076_;
v_b_1055_ = v___x_1075_;
goto _start;
}
else
{
v___y_1070_ = v___y_1078_;
v___y_1071_ = v___y_1080_;
goto v___jp_1069_;
}
}
else
{
lean_dec_ref(v___x_1081_);
v___y_1070_ = v___y_1078_;
v___y_1071_ = v___y_1080_;
goto v___jp_1069_;
}
}
v___jp_1083_:
{
if (v___y_1087_ == 0)
{
lean_dec_ref(v___y_1086_);
lean_dec_ref(v___y_1084_);
v_a_1054_ = v___x_1076_;
v_b_1055_ = v___x_1075_;
goto _start;
}
else
{
v___y_1078_ = v___y_1084_;
v___y_1079_ = v___y_1085_;
v___y_1080_ = v___y_1086_;
goto v___jp_1077_;
}
}
v___jp_1089_:
{
if (v___y_1090_ == 0)
{
lean_dec(v_a_1054_);
v_a_1054_ = v___x_1076_;
v_b_1055_ = v___x_1075_;
goto _start;
}
else
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = lean_string_utf8_byte_size(v_s_1052_);
v___x_1093_ = lean_nat_dec_eq(v___x_1076_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = lean_string_utf8_extract(v_s_1052_, v___x_1094_, v_a_1054_);
lean_dec(v_a_1054_);
v___x_1096_ = lean_string_utf8_extract(v_s_1052_, v___x_1076_, v___x_1092_);
v___x_1097_ = l_Lean_Name_demangle_x3f(v___x_1095_);
if (lean_obj_tag(v___x_1097_) == 1)
{
lean_object* v_val_1098_; 
v_val_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_val_1098_);
lean_dec_ref(v___x_1097_);
if (lean_obj_tag(v_val_1098_) == 1)
{
lean_object* v_pre_1099_; 
v_pre_1099_ = lean_ctor_get(v_val_1098_, 0);
lean_inc(v_pre_1099_);
lean_dec_ref(v_val_1098_);
if (lean_obj_tag(v_pre_1099_) == 0)
{
v___y_1078_ = v___x_1096_;
v___y_1079_ = v___x_1093_;
v___y_1080_ = v___x_1095_;
goto v___jp_1077_;
}
else
{
lean_dec(v_pre_1099_);
v___y_1084_ = v___x_1096_;
v___y_1085_ = v___x_1093_;
v___y_1086_ = v___x_1095_;
v___y_1087_ = v___x_1093_;
goto v___jp_1083_;
}
}
else
{
lean_dec(v_val_1098_);
v___y_1084_ = v___x_1096_;
v___y_1085_ = v___x_1093_;
v___y_1086_ = v___x_1095_;
v___y_1087_ = v___x_1093_;
goto v___jp_1083_;
}
}
else
{
lean_dec(v___x_1097_);
v___y_1084_ = v___x_1096_;
v___y_1085_ = v___x_1093_;
v___y_1086_ = v___x_1095_;
v___y_1087_ = v___x_1093_;
goto v___jp_1083_;
}
}
else
{
lean_dec(v_a_1054_);
v_a_1054_ = v___x_1076_;
v_b_1055_ = v___x_1075_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1107_; 
lean_dec(v_a_1054_);
v___x_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1107_, 0, v_b_1055_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___boxed(lean_object* v_s_1108_, lean_object* v___x_1109_, lean_object* v_a_1110_, lean_object* v_b_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1108_, v___x_1109_, v_a_1110_, v_b_1111_);
lean_dec_ref(v___x_1109_);
lean_dec_ref(v_s_1108_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(lean_object* v_s_1113_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = lean_string_utf8_byte_size(v_s_1113_);
lean_inc_ref(v_s_1113_);
v___x_1116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1116_, 0, v_s_1113_);
lean_ctor_set(v___x_1116_, 1, v___x_1114_);
lean_ctor_set(v___x_1116_, 2, v___x_1115_);
v___x_1117_ = lean_box(0);
v___x_1118_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1119_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1113_, v___x_1116_, v___x_1114_, v___x_1118_);
lean_dec_ref(v___x_1116_);
lean_dec_ref(v_s_1113_);
if (lean_obj_tag(v___x_1119_) == 0)
{
return v___x_1117_;
}
else
{
lean_object* v_val_1120_; lean_object* v_fst_1121_; 
v_val_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_val_1120_);
lean_dec_ref(v___x_1119_);
v_fst_1121_ = lean_ctor_get(v_val_1120_, 0);
lean_inc(v_fst_1121_);
lean_dec(v_val_1120_);
if (lean_obj_tag(v_fst_1121_) == 0)
{
return v___x_1117_;
}
else
{
return v_fst_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(lean_object* v_s_1122_, lean_object* v___x_1123_, lean_object* v_inst_1124_, lean_object* v_R_1125_, lean_object* v_a_1126_, lean_object* v_b_1127_, lean_object* v_c_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1122_, v___x_1123_, v_a_1126_, v_b_1127_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___boxed(lean_object* v_s_1130_, lean_object* v___x_1131_, lean_object* v_inst_1132_, lean_object* v_R_1133_, lean_object* v_a_1134_, lean_object* v_b_1135_, lean_object* v_c_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(v_s_1130_, v___x_1131_, v_inst_1132_, v_R_1133_, v_a_1134_, v_b_1135_, v_c_1136_);
lean_dec_ref(v___x_1131_);
lean_dec_ref(v_s_1130_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(lean_object* v_s_1138_, lean_object* v___x_1139_, lean_object* v___x_1140_, lean_object* v_a_1141_, lean_object* v_b_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_box(0);
switch(lean_obj_tag(v_a_1141_))
{
case 0:
{
lean_object* v_pos_1144_; lean_object* v___x_1145_; 
lean_dec(v_b_1142_);
v_pos_1144_ = lean_ctor_get(v_a_1141_, 0);
lean_inc(v_pos_1144_);
lean_dec_ref(v_a_1141_);
v___x_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_pos_1144_);
return v___x_1145_;
}
case 1:
{
lean_object* v_pos_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_b_1142_);
v_pos_1146_ = lean_ctor_get(v_a_1141_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_a_1141_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1148_ = v_a_1141_;
v_isShared_1149_ = v_isSharedCheck_1155_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_pos_1146_);
lean_dec(v_a_1141_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1155_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = lean_string_utf8_next_fast(v_s_1138_, v_pos_1146_);
lean_dec(v_pos_1146_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1150_);
v___x_1152_ = v___x_1148_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
v_a_1141_ = v___x_1152_;
v_b_1142_ = v___x_1143_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1156_; lean_object* v_table_1157_; lean_object* v_stackPos_1158_; lean_object* v_needlePos_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1210_; 
v_needle_1156_ = lean_ctor_get(v_a_1141_, 0);
v_table_1157_ = lean_ctor_get(v_a_1141_, 1);
v_stackPos_1158_ = lean_ctor_get(v_a_1141_, 2);
v_needlePos_1159_ = lean_ctor_get(v_a_1141_, 3);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_a_1141_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1161_ = v_a_1141_;
v_isShared_1162_ = v_isSharedCheck_1210_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_needlePos_1159_);
lean_inc(v_stackPos_1158_);
lean_inc(v_table_1157_);
lean_inc(v_needle_1156_);
lean_dec(v_a_1141_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1210_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_str_1163_; lean_object* v_startInclusive_1164_; lean_object* v_endExclusive_1165_; lean_object* v_basePos_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v_str_1163_ = lean_ctor_get(v_needle_1156_, 0);
v_startInclusive_1164_ = lean_ctor_get(v_needle_1156_, 1);
v_endExclusive_1165_ = lean_ctor_get(v_needle_1156_, 2);
v_basePos_1166_ = lean_nat_sub(v_stackPos_1158_, v_needlePos_1159_);
v___x_1167_ = lean_nat_sub(v_endExclusive_1165_, v_startInclusive_1164_);
v___x_1168_ = lean_nat_add(v_basePos_1166_, v___x_1167_);
v___x_1169_ = lean_nat_dec_le(v___x_1168_, v___x_1140_);
lean_dec(v___x_1168_);
if (v___x_1169_ == 0)
{
uint8_t v___x_1170_; 
lean_dec(v___x_1167_);
lean_del_object(v___x_1161_);
lean_dec(v_needlePos_1159_);
lean_dec(v_stackPos_1158_);
lean_dec_ref(v_table_1157_);
lean_dec_ref(v_needle_1156_);
v___x_1170_ = lean_nat_dec_lt(v_basePos_1166_, v___x_1140_);
lean_dec(v_basePos_1166_);
if (v___x_1170_ == 0)
{
return v_b_1142_;
}
else
{
lean_object* v___x_1171_; 
lean_dec(v_b_1142_);
v___x_1171_ = lean_box(3);
v_a_1141_ = v___x_1171_;
v_b_1142_ = v___x_1143_;
goto _start;
}
}
else
{
uint8_t v_stackByte_1173_; lean_object* v___x_1174_; uint8_t v_patByte_1175_; uint8_t v___x_1176_; 
lean_dec(v_basePos_1166_);
lean_inc(v_stackPos_1158_);
v_stackByte_1173_ = lean_string_get_byte_fast(v_s_1138_, v_stackPos_1158_);
v___x_1174_ = lean_nat_add(v_startInclusive_1164_, v_needlePos_1159_);
v_patByte_1175_ = lean_string_get_byte_fast(v_str_1163_, v___x_1174_);
v___x_1176_ = lean_uint8_dec_eq(v_stackByte_1173_, v_patByte_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
lean_dec(v___x_1167_);
lean_dec(v_b_1142_);
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = lean_nat_dec_eq(v_needlePos_1159_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v_newNeedlePos_1181_; uint8_t v___x_1182_; 
v___x_1179_ = lean_unsigned_to_nat(1u);
v___x_1180_ = lean_nat_sub(v_needlePos_1159_, v___x_1179_);
lean_dec(v_needlePos_1159_);
v_newNeedlePos_1181_ = lean_array_fget_borrowed(v_table_1157_, v___x_1180_);
lean_dec(v___x_1180_);
v___x_1182_ = lean_nat_dec_eq(v_newNeedlePos_1181_, v___x_1177_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1184_; 
lean_inc(v_newNeedlePos_1181_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 3, v_newNeedlePos_1181_);
v___x_1184_ = v___x_1161_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_needle_1156_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_table_1157_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_stackPos_1158_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v_newNeedlePos_1181_);
v___x_1184_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
v_a_1141_ = v___x_1184_;
v_b_1142_ = v___x_1143_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1187_; lean_object* v___x_1189_; 
v_nextStackPos_1187_ = l_String_Slice_posGE___redArg(v___x_1139_, v_stackPos_1158_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 3, v___x_1177_);
lean_ctor_set(v___x_1161_, 2, v_nextStackPos_1187_);
v___x_1189_ = v___x_1161_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_needle_1156_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_table_1157_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v_nextStackPos_1187_);
lean_ctor_set(v_reuseFailAlloc_1191_, 3, v___x_1177_);
v___x_1189_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
v_a_1141_ = v___x_1189_;
v_b_1142_ = v___x_1143_;
goto _start;
}
}
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_nextStackPos_1194_; lean_object* v___x_1196_; 
lean_dec(v_needlePos_1159_);
v___x_1192_ = lean_unsigned_to_nat(1u);
v___x_1193_ = lean_nat_add(v_stackPos_1158_, v___x_1192_);
lean_dec(v_stackPos_1158_);
v_nextStackPos_1194_ = l_String_Slice_posGE___redArg(v___x_1139_, v___x_1193_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 3, v___x_1177_);
lean_ctor_set(v___x_1161_, 2, v_nextStackPos_1194_);
v___x_1196_ = v___x_1161_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_needle_1156_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_table_1157_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_nextStackPos_1194_);
lean_ctor_set(v_reuseFailAlloc_1198_, 3, v___x_1177_);
v___x_1196_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
v_a_1141_ = v___x_1196_;
v_b_1142_ = v___x_1143_;
goto _start;
}
}
}
else
{
lean_object* v___x_1199_; lean_object* v_nextStackPos_1200_; lean_object* v_nextNeedlePos_1201_; uint8_t v___x_1202_; 
v___x_1199_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1200_ = lean_nat_add(v_stackPos_1158_, v___x_1199_);
lean_dec(v_stackPos_1158_);
v_nextNeedlePos_1201_ = lean_nat_add(v_needlePos_1159_, v___x_1199_);
lean_dec(v_needlePos_1159_);
v___x_1202_ = lean_nat_dec_eq(v_nextNeedlePos_1201_, v___x_1167_);
lean_dec(v___x_1167_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1204_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 3, v_nextNeedlePos_1201_);
lean_ctor_set(v___x_1161_, 2, v_nextStackPos_1200_);
v___x_1204_ = v___x_1161_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_needle_1156_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_table_1157_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_nextStackPos_1200_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_nextNeedlePos_1201_);
v___x_1204_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
v_a_1141_ = v___x_1204_;
goto _start;
}
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_del_object(v___x_1161_);
lean_dec_ref(v_table_1157_);
lean_dec_ref(v_needle_1156_);
lean_dec(v_b_1142_);
v___x_1207_ = lean_nat_sub(v_nextStackPos_1200_, v_nextNeedlePos_1201_);
lean_dec(v_nextNeedlePos_1201_);
lean_dec(v_nextStackPos_1200_);
v___x_1208_ = l_String_Slice_pos_x21(v___x_1139_, v___x_1207_);
lean_dec(v___x_1207_);
v___x_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
}
}
}
default: 
{
return v_b_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg___boxed(lean_object* v_s_1211_, lean_object* v___x_1212_, lean_object* v___x_1213_, lean_object* v_a_1214_, lean_object* v_b_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1211_, v___x_1212_, v___x_1213_, v_a_1214_, v_b_1215_);
lean_dec(v___x_1213_);
lean_dec_ref(v___x_1212_);
lean_dec_ref(v_s_1211_);
return v_res_1216_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0));
v___x_1219_ = lean_string_utf8_byte_size(v___x_1218_);
return v___x_1219_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1);
v___x_1222_ = lean_nat_dec_eq(v___x_1221_, v___x_1220_);
return v___x_1222_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1223_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1);
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1225_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0));
v___x_1226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___x_1224_);
lean_ctor_set(v___x_1226_, 2, v___x_1223_);
return v___x_1226_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
v___x_1228_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4);
v___x_1231_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
v___x_1232_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v___x_1230_);
lean_ctor_set(v___x_1232_, 2, v___x_1229_);
lean_ctor_set(v___x_1232_, 3, v___x_1229_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(lean_object* v_s_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___y_1240_; uint8_t v___x_1249_; 
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = lean_string_utf8_byte_size(v_s_1235_);
lean_inc_ref(v_s_1235_);
v___x_1238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1238_, 0, v_s_1235_);
lean_ctor_set(v___x_1238_, 1, v___x_1236_);
lean_ctor_set(v___x_1238_, 2, v___x_1237_);
v___x_1249_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5);
v___y_1240_ = v___x_1250_;
goto v___jp_1239_;
}
else
{
lean_object* v___x_1251_; 
v___x_1251_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1240_ = v___x_1251_;
goto v___jp_1239_;
}
v___jp_1239_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_box(0);
v___x_1242_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1235_, v___x_1238_, v___x_1237_, v___y_1240_, v___x_1241_);
lean_dec_ref(v___x_1238_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_s_1235_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
return v___x_1244_;
}
else
{
lean_object* v_val_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_val_1245_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_val_1245_);
lean_dec_ref(v___x_1242_);
v___x_1246_ = lean_string_utf8_extract(v_s_1235_, v___x_1236_, v_val_1245_);
v___x_1247_ = lean_string_utf8_extract(v_s_1235_, v_val_1245_, v___x_1237_);
lean_dec(v_val_1245_);
lean_dec_ref(v_s_1235_);
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1246_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
return v___x_1248_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(lean_object* v_s_1252_, lean_object* v___x_1253_, lean_object* v___x_1254_, lean_object* v_inst_1255_, lean_object* v_R_1256_, lean_object* v_a_1257_, lean_object* v_b_1258_, lean_object* v_c_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1252_, v___x_1253_, v___x_1254_, v_a_1257_, v_b_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___boxed(lean_object* v_s_1261_, lean_object* v___x_1262_, lean_object* v___x_1263_, lean_object* v_inst_1264_, lean_object* v_R_1265_, lean_object* v_a_1266_, lean_object* v_b_1267_, lean_object* v_c_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(v_s_1261_, v___x_1262_, v___x_1263_, v_inst_1264_, v_R_1265_, v_a_1266_, v_b_1267_, v_c_1268_);
lean_dec(v___x_1263_);
lean_dec_ref(v___x_1262_);
lean_dec_ref(v_s_1261_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(lean_object* v_s_1281_){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10));
lean_inc_ref(v_s_1281_);
v___x_1398_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1281_, v___x_1397_);
if (lean_obj_tag(v___x_1398_) == 1)
{
lean_object* v_val_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1412_; 
v_val_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1412_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_val_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1412_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1403_ = lean_string_utf8_byte_size(v_val_1399_);
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_nat_dec_eq(v___x_1403_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_dec_ref(v_s_1281_);
v___x_1406_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1407_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1399_);
lean_dec(v_val_1399_);
v___x_1408_ = lean_string_append(v___x_1406_, v___x_1407_);
lean_dec_ref(v___x_1407_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1408_);
v___x_1410_ = v___x_1401_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
else
{
lean_del_object(v___x_1401_);
lean_dec(v_val_1399_);
goto v___jp_1375_;
}
}
}
else
{
lean_dec(v___x_1398_);
goto v___jp_1375_;
}
v___jp_1282_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0));
v___x_1284_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1281_, v___x_1283_);
if (lean_obj_tag(v___x_1284_) == 1)
{
lean_object* v_val_1285_; lean_object* v___x_1286_; 
v_val_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_val_1285_);
lean_dec_ref(v___x_1284_);
v___x_1286_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1285_);
if (lean_obj_tag(v___x_1286_) == 1)
{
lean_object* v_val_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1301_; 
v_val_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1301_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_val_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1301_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v_fst_1291_; lean_object* v_snd_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
v_fst_1291_ = lean_ctor_get(v_val_1287_, 0);
lean_inc(v_fst_1291_);
v_snd_1292_ = lean_ctor_get(v_val_1287_, 1);
lean_inc(v_snd_1292_);
lean_dec(v_val_1287_);
v___x_1293_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1294_ = lean_string_append(v_fst_1291_, v___x_1293_);
v___x_1295_ = lean_string_append(v___x_1294_, v_snd_1292_);
lean_dec(v_snd_1292_);
v___x_1296_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1297_ = lean_string_append(v___x_1295_, v___x_1296_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1297_);
v___x_1299_ = v___x_1289_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
else
{
lean_object* v___x_1302_; 
lean_dec(v___x_1286_);
v___x_1302_ = lean_box(0);
return v___x_1302_;
}
}
else
{
lean_object* v___x_1303_; 
lean_dec(v___x_1284_);
v___x_1303_ = lean_box(0);
return v___x_1303_;
}
}
v___jp_1304_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3));
lean_inc_ref(v_s_1281_);
v___x_1306_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1281_, v___x_1305_);
if (lean_obj_tag(v___x_1306_) == 1)
{
lean_object* v_val_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1318_; 
v_val_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1318_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_val_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1318_;
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
lean_object* v___x_1314_; lean_object* v___x_1316_; 
lean_dec_ref(v_s_1281_);
v___x_1314_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1307_);
lean_dec(v_val_1307_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1314_);
v___x_1316_ = v___x_1309_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
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
v___jp_1319_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4));
lean_inc_ref(v_s_1281_);
v___x_1321_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1281_, v___x_1320_);
if (lean_obj_tag(v___x_1321_) == 1)
{
lean_object* v_val_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1335_; 
v_val_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1335_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_val_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1335_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1326_ = lean_string_utf8_byte_size(v_val_1322_);
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = lean_nat_dec_eq(v___x_1326_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
lean_dec_ref(v_s_1281_);
v___x_1329_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1330_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1322_);
lean_dec(v_val_1322_);
v___x_1331_ = lean_string_append(v___x_1329_, v___x_1330_);
lean_dec_ref(v___x_1330_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1331_);
v___x_1333_ = v___x_1324_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
else
{
lean_del_object(v___x_1324_);
lean_dec(v_val_1322_);
goto v___jp_1304_;
}
}
}
else
{
lean_dec(v___x_1321_);
goto v___jp_1304_;
}
}
v___jp_1336_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6));
lean_inc_ref(v_s_1281_);
v___x_1338_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1281_, v___x_1337_);
if (lean_obj_tag(v___x_1338_) == 1)
{
lean_object* v_val_1339_; lean_object* v___x_1340_; 
v_val_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_val_1339_);
lean_dec_ref(v___x_1338_);
v___x_1340_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1339_);
if (lean_obj_tag(v___x_1340_) == 1)
{
lean_object* v_val_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref(v_s_1281_);
v_val_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1357_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_val_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1357_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_fst_1345_; lean_object* v_snd_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v_fst_1345_ = lean_ctor_get(v_val_1341_, 0);
lean_inc(v_fst_1345_);
v_snd_1346_ = lean_ctor_get(v_val_1341_, 1);
lean_inc(v_snd_1346_);
lean_dec(v_val_1341_);
v___x_1347_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1348_ = lean_string_append(v___x_1347_, v_fst_1345_);
lean_dec(v_fst_1345_);
v___x_1349_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1350_ = lean_string_append(v___x_1348_, v___x_1349_);
v___x_1351_ = lean_string_append(v___x_1350_, v_snd_1346_);
lean_dec(v_snd_1346_);
v___x_1352_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1353_);
v___x_1355_ = v___x_1343_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
else
{
lean_dec(v___x_1340_);
goto v___jp_1319_;
}
}
else
{
lean_dec(v___x_1338_);
goto v___jp_1319_;
}
}
v___jp_1358_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7));
lean_inc_ref(v_s_1281_);
v___x_1360_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1281_, v___x_1359_);
if (lean_obj_tag(v___x_1360_) == 1)
{
lean_object* v_val_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1374_; 
v_val_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1374_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_val_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1374_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1365_ = lean_string_utf8_byte_size(v_val_1361_);
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_nat_dec_eq(v___x_1365_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_dec_ref(v_s_1281_);
v___x_1368_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1369_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1361_);
lean_dec(v_val_1361_);
v___x_1370_ = lean_string_append(v___x_1368_, v___x_1369_);
lean_dec_ref(v___x_1369_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1370_);
v___x_1372_ = v___x_1363_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
else
{
lean_del_object(v___x_1363_);
lean_dec(v_val_1361_);
goto v___jp_1336_;
}
}
}
else
{
lean_dec(v___x_1360_);
goto v___jp_1336_;
}
}
v___jp_1375_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8));
lean_inc_ref(v_s_1281_);
v___x_1377_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1281_, v___x_1376_);
if (lean_obj_tag(v___x_1377_) == 1)
{
lean_object* v_val_1378_; lean_object* v___x_1379_; 
v_val_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_val_1378_);
lean_dec_ref(v___x_1377_);
v___x_1379_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1378_);
if (lean_obj_tag(v___x_1379_) == 1)
{
lean_object* v_val_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v_s_1281_);
v_val_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1396_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_val_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1396_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_fst_1384_; lean_object* v_snd_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v_fst_1384_ = lean_ctor_get(v_val_1380_, 0);
lean_inc(v_fst_1384_);
v_snd_1385_ = lean_ctor_get(v_val_1380_, 1);
lean_inc(v_snd_1385_);
lean_dec(v_val_1380_);
v___x_1386_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1387_ = lean_string_append(v___x_1386_, v_fst_1384_);
lean_dec(v_fst_1384_);
v___x_1388_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1389_ = lean_string_append(v___x_1387_, v___x_1388_);
v___x_1390_ = lean_string_append(v___x_1389_, v_snd_1385_);
lean_dec(v_snd_1385_);
v___x_1391_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1392_ = lean_string_append(v___x_1390_, v___x_1391_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1392_);
v___x_1394_ = v___x_1382_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
else
{
lean_dec(v___x_1379_);
goto v___jp_1358_;
}
}
else
{
lean_dec(v___x_1377_);
goto v___jp_1358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleSymbol(lean_object* v_symbol_1422_){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1423_ = lean_string_utf8_byte_size(v_symbol_1422_);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = lean_nat_dec_eq(v___x_1423_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v_fst_1427_; lean_object* v_snd_1428_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1426_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(v_symbol_1422_);
v_fst_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_fst_1427_);
v_snd_1428_ = lean_ctor_get(v___x_1426_, 1);
lean_inc(v_snd_1428_);
lean_dec_ref(v___x_1426_);
v___x_1453_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__5));
lean_inc(v_fst_1427_);
v___x_1454_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_fst_1427_, v___x_1453_);
if (lean_obj_tag(v___x_1454_) == 1)
{
lean_object* v_val_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1475_; 
v_val_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1475_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_val_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1475_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
uint8_t v___x_1459_; 
lean_inc(v_val_1455_);
v___x_1459_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_1455_);
if (v___x_1459_ == 0)
{
lean_del_object(v___x_1457_);
lean_dec(v_val_1455_);
goto v___jp_1429_;
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v_r_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
lean_dec(v_fst_1427_);
v___x_1460_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__6));
v___x_1461_ = lean_string_append(v___x_1460_, v_val_1455_);
lean_dec(v_val_1455_);
v___x_1462_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__7));
v_r_1463_ = lean_string_append(v___x_1461_, v___x_1462_);
v___x_1464_ = lean_string_utf8_byte_size(v_snd_1428_);
v___x_1465_ = lean_nat_dec_eq(v___x_1464_, v___x_1424_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1466_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1467_ = lean_string_append(v_r_1463_, v___x_1466_);
v___x_1468_ = lean_string_append(v___x_1467_, v_snd_1428_);
lean_dec(v_snd_1428_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1468_);
v___x_1470_ = v___x_1457_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
else
{
lean_object* v___x_1473_; 
lean_dec(v_snd_1428_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v_r_1463_);
v___x_1473_ = v___x_1457_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_r_1463_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
else
{
lean_dec(v___x_1454_);
goto v___jp_1429_;
}
v___jp_1429_:
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__0));
v___x_1431_ = lean_string_dec_eq(v_fst_1427_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(v_fst_1427_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_dec(v_snd_1428_);
return v___x_1432_;
}
else
{
lean_object* v_val_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v_val_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_val_1433_);
v___x_1434_ = lean_string_utf8_byte_size(v_snd_1428_);
v___x_1435_ = lean_nat_dec_eq(v___x_1434_, v___x_1424_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1445_; 
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v___x_1432_, 0);
lean_dec(v_unused_1446_);
v___x_1437_ = v___x_1432_;
v_isShared_1438_ = v_isSharedCheck_1445_;
goto v_resetjp_1436_;
}
else
{
lean_dec(v___x_1432_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1445_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1439_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1440_ = lean_string_append(v_val_1433_, v___x_1439_);
v___x_1441_ = lean_string_append(v___x_1440_, v_snd_1428_);
lean_dec(v_snd_1428_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1441_);
v___x_1443_ = v___x_1437_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
else
{
lean_dec(v_val_1433_);
lean_dec(v_snd_1428_);
return v___x_1432_;
}
}
}
else
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
lean_dec(v_fst_1427_);
v___x_1447_ = lean_string_utf8_byte_size(v_snd_1428_);
v___x_1448_ = lean_nat_dec_eq(v___x_1447_, v___x_1424_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__2));
v___x_1450_ = lean_string_append(v___x_1449_, v_snd_1428_);
lean_dec(v_snd_1428_);
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
else
{
lean_object* v___x_1452_; 
lean_dec(v_snd_1428_);
v___x_1452_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__4));
return v___x_1452_;
}
}
}
}
else
{
lean_object* v___x_1476_; 
lean_dec_ref(v_symbol_1422_);
v___x_1476_ = lean_box(0);
return v___x_1476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(lean_object* v_s_1477_, lean_object* v_pos_1478_, lean_object* v_pred_1479_){
_start:
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = lean_string_utf8_byte_size(v_s_1477_);
v___x_1481_ = lean_nat_dec_eq(v_pos_1478_, v___x_1480_);
if (v___x_1481_ == 0)
{
uint32_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1482_ = lean_string_utf8_get_fast(v_s_1477_, v_pos_1478_);
v___x_1483_ = lean_box_uint32(v___x_1482_);
lean_inc_ref(v_pred_1479_);
v___x_1484_ = lean_apply_1(v_pred_1479_, v___x_1483_);
v___x_1485_ = lean_unbox(v___x_1484_);
if (v___x_1485_ == 0)
{
lean_dec_ref(v_pred_1479_);
return v_pos_1478_;
}
else
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_string_utf8_next_fast(v_s_1477_, v_pos_1478_);
lean_dec(v_pos_1478_);
v_pos_1478_ = v___x_1486_;
goto _start;
}
}
else
{
lean_dec_ref(v_pred_1479_);
return v_pos_1478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile___boxed(lean_object* v_s_1488_, lean_object* v_pos_1489_, lean_object* v_pred_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_s_1488_, v_pos_1489_, v_pred_1490_);
lean_dec_ref(v_s_1488_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(lean_object* v_s_1492_, lean_object* v_p_u2081_1493_, lean_object* v_p_u2082_1494_){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = lean_string_utf8_extract(v_s_1492_, v___x_1495_, v_p_u2081_1493_);
v___x_1497_ = lean_string_utf8_extract(v_s_1492_, v_p_u2081_1493_, v_p_u2082_1494_);
v___x_1498_ = lean_string_utf8_byte_size(v_s_1492_);
v___x_1499_ = lean_string_utf8_extract(v_s_1492_, v_p_u2082_1494_, v___x_1498_);
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1497_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1496_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082___boxed(lean_object* v_s_1502_, lean_object* v_p_u2081_1503_, lean_object* v_p_u2082_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_s_1502_, v_p_u2081_1503_, v_p_u2082_1504_);
lean_dec(v_p_u2082_1504_);
lean_dec(v_p_u2081_1503_);
lean_dec_ref(v_s_1502_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(lean_object* v___x_1506_, lean_object* v___x_1507_, lean_object* v_line_1508_, lean_object* v_a_1509_, lean_object* v_b_1510_){
_start:
{
lean_object* v_startInclusive_1511_; lean_object* v_endExclusive_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_startInclusive_1511_ = lean_ctor_get(v___x_1506_, 1);
v_endExclusive_1512_ = lean_ctor_get(v___x_1506_, 2);
v___x_1513_ = lean_nat_sub(v_endExclusive_1512_, v_startInclusive_1511_);
v___x_1514_ = lean_nat_dec_eq(v_a_1509_, v___x_1513_);
lean_dec(v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___y_1518_; uint32_t v___x_1523_; uint32_t v___x_1524_; uint8_t v___x_1525_; 
lean_dec(v_b_1510_);
v___x_1515_ = lean_box(0);
v___x_1516_ = lean_nat_add(v___x_1507_, v_a_1509_);
v___x_1523_ = lean_string_utf8_get_fast(v_line_1508_, v___x_1516_);
v___x_1524_ = 43;
v___x_1525_ = lean_uint32_dec_eq(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
uint32_t v___x_1526_; uint8_t v___x_1527_; 
v___x_1526_ = 41;
v___x_1527_ = lean_uint32_dec_eq(v___x_1523_, v___x_1526_);
v___y_1518_ = v___x_1527_;
goto v___jp_1517_;
}
else
{
v___y_1518_ = v___x_1525_;
goto v___jp_1517_;
}
v___jp_1517_:
{
if (v___y_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec(v_a_1509_);
v___x_1519_ = lean_string_utf8_next_fast(v_line_1508_, v___x_1516_);
lean_dec(v___x_1516_);
v___x_1520_ = lean_nat_sub(v___x_1519_, v___x_1507_);
v_a_1509_ = v___x_1520_;
v_b_1510_ = v___x_1515_;
goto _start;
}
else
{
lean_object* v___x_1522_; 
lean_dec(v___x_1516_);
v___x_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1522_, 0, v_a_1509_);
return v___x_1522_;
}
}
}
else
{
lean_dec(v_a_1509_);
return v_b_1510_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg___boxed(lean_object* v___x_1528_, lean_object* v___x_1529_, lean_object* v_line_1530_, lean_object* v_a_1531_, lean_object* v_b_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1528_, v___x_1529_, v_line_1530_, v_a_1531_, v_b_1532_);
lean_dec_ref(v_line_1530_);
lean_dec(v___x_1529_);
lean_dec_ref(v___x_1528_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(lean_object* v___x_1534_, lean_object* v_line_1535_, lean_object* v_a_1536_, lean_object* v_b_1537_){
_start:
{
lean_object* v_startInclusive_1538_; lean_object* v_endExclusive_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v_startInclusive_1538_ = lean_ctor_get(v___x_1534_, 1);
v_endExclusive_1539_ = lean_ctor_get(v___x_1534_, 2);
v___x_1540_ = lean_nat_sub(v_endExclusive_1539_, v_startInclusive_1538_);
v___x_1541_ = lean_nat_dec_eq(v_a_1536_, v___x_1540_);
lean_dec(v___x_1540_);
if (v___x_1541_ == 0)
{
uint32_t v___x_1542_; uint32_t v___x_1543_; uint8_t v___x_1544_; 
lean_dec(v_b_1537_);
v___x_1542_ = lean_string_utf8_get_fast(v_line_1535_, v_a_1536_);
v___x_1543_ = 40;
v___x_1544_ = lean_uint32_dec_eq(v___x_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_box(0);
v___x_1546_ = lean_string_utf8_next_fast(v_line_1535_, v_a_1536_);
lean_dec(v_a_1536_);
v_a_1536_ = v___x_1546_;
v_b_1537_ = v___x_1545_;
goto _start;
}
else
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_a_1536_);
return v___x_1548_;
}
}
else
{
lean_dec(v_a_1536_);
return v_b_1537_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg___boxed(lean_object* v___x_1549_, lean_object* v_line_1550_, lean_object* v_a_1551_, lean_object* v_b_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1549_, v_line_1550_, v_a_1551_, v_b_1552_);
lean_dec_ref(v_line_1550_);
lean_dec_ref(v___x_1549_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(lean_object* v_line_1554_){
_start:
{
lean_object* v_searcher_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_searcher_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_string_utf8_byte_size(v_line_1554_);
lean_inc_ref(v_line_1554_);
v___x_1557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1557_, 0, v_line_1554_);
lean_ctor_set(v___x_1557_, 1, v_searcher_1555_);
lean_ctor_set(v___x_1557_, 2, v___x_1556_);
v___x_1558_ = lean_box(0);
v___x_1559_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1557_, v_line_1554_, v_searcher_1555_, v___x_1558_);
lean_dec_ref(v___x_1557_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_dec_ref(v_line_1554_);
return v___x_1558_;
}
else
{
lean_object* v_val_1560_; uint8_t v___x_1561_; 
v_val_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_val_1560_);
lean_dec_ref(v___x_1559_);
v___x_1561_ = lean_nat_dec_eq(v_val_1560_, v___x_1556_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = lean_string_utf8_next_fast(v_line_1554_, v_val_1560_);
lean_dec(v_val_1560_);
lean_inc_ref(v_line_1554_);
v___x_1563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1563_, 0, v_line_1554_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
lean_ctor_set(v___x_1563_, 2, v___x_1556_);
v___x_1564_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1563_, v___x_1562_, v_line_1554_, v_searcher_1555_, v___x_1558_);
lean_dec_ref(v___x_1563_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_dec_ref(v_line_1554_);
return v___x_1558_;
}
else
{
lean_object* v_val_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1575_; 
v_val_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1575_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_val_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1575_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1569_ = lean_nat_add(v___x_1562_, v_val_1565_);
lean_dec(v_val_1565_);
v___x_1570_ = lean_nat_dec_eq(v___x_1569_, v___x_1562_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1554_, v___x_1562_, v___x_1569_);
lean_dec(v___x_1569_);
lean_dec_ref(v_line_1554_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1571_);
v___x_1573_ = v___x_1567_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
else
{
lean_dec(v___x_1569_);
lean_del_object(v___x_1567_);
lean_dec_ref(v_line_1554_);
return v___x_1558_;
}
}
}
}
else
{
lean_dec(v_val_1560_);
lean_dec_ref(v_line_1554_);
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(lean_object* v___x_1576_, lean_object* v_line_1577_, lean_object* v_inst_1578_, lean_object* v_R_1579_, lean_object* v_a_1580_, lean_object* v_b_1581_, lean_object* v_c_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1576_, v_line_1577_, v_a_1580_, v_b_1581_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___boxed(lean_object* v___x_1584_, lean_object* v_line_1585_, lean_object* v_inst_1586_, lean_object* v_R_1587_, lean_object* v_a_1588_, lean_object* v_b_1589_, lean_object* v_c_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(v___x_1584_, v_line_1585_, v_inst_1586_, v_R_1587_, v_a_1588_, v_b_1589_, v_c_1590_);
lean_dec_ref(v_line_1585_);
lean_dec_ref(v___x_1584_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v_line_1594_, lean_object* v_inst_1595_, lean_object* v_R_1596_, lean_object* v_a_1597_, lean_object* v_b_1598_, lean_object* v_c_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1592_, v___x_1593_, v_line_1594_, v_a_1597_, v_b_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___boxed(lean_object* v___x_1601_, lean_object* v___x_1602_, lean_object* v_line_1603_, lean_object* v_inst_1604_, lean_object* v_R_1605_, lean_object* v_a_1606_, lean_object* v_b_1607_, lean_object* v_c_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(v___x_1601_, v___x_1602_, v_line_1603_, v_inst_1604_, v_R_1605_, v_a_1606_, v_b_1607_, v_c_1608_);
lean_dec_ref(v_line_1603_);
lean_dec(v___x_1602_);
lean_dec_ref(v___x_1601_);
return v_res_1609_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(uint32_t v_x_1610_){
_start:
{
uint32_t v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = 32;
v___x_1612_ = lean_uint32_dec_eq(v_x_1610_, v___x_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed(lean_object* v_x_1613_){
_start:
{
uint32_t v_x_2608__boxed_1614_; uint8_t v_res_1615_; lean_object* v_r_1616_; 
v_x_2608__boxed_1614_ = lean_unbox_uint32(v_x_1613_);
lean_dec(v_x_1613_);
v_res_1615_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(v_x_2608__boxed_1614_);
v_r_1616_ = lean_box(v_res_1615_);
return v_r_1616_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(uint32_t v_x_1617_){
_start:
{
uint8_t v___y_1619_; uint8_t v___y_1625_; uint32_t v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = 48;
v___x_1631_ = lean_uint32_dec_le(v___x_1630_, v_x_1617_);
if (v___x_1631_ == 0)
{
v___y_1625_ = v___x_1631_;
goto v___jp_1624_;
}
else
{
uint32_t v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = 57;
v___x_1633_ = lean_uint32_dec_le(v_x_1617_, v___x_1632_);
v___y_1625_ = v___x_1633_;
goto v___jp_1624_;
}
v___jp_1618_:
{
if (v___y_1619_ == 0)
{
uint32_t v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = 65;
v___x_1621_ = lean_uint32_dec_le(v___x_1620_, v_x_1617_);
if (v___x_1621_ == 0)
{
return v___x_1621_;
}
else
{
uint32_t v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = 70;
v___x_1623_ = lean_uint32_dec_le(v_x_1617_, v___x_1622_);
return v___x_1623_;
}
}
else
{
return v___y_1619_;
}
}
v___jp_1624_:
{
if (v___y_1625_ == 0)
{
uint32_t v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = 97;
v___x_1627_ = lean_uint32_dec_le(v___x_1626_, v_x_1617_);
if (v___x_1627_ == 0)
{
v___y_1619_ = v___x_1627_;
goto v___jp_1618_;
}
else
{
uint32_t v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = 102;
v___x_1629_ = lean_uint32_dec_le(v_x_1617_, v___x_1628_);
v___y_1619_ = v___x_1629_;
goto v___jp_1618_;
}
}
else
{
return v___y_1625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed(lean_object* v_x_1634_){
_start:
{
uint32_t v_x_2615__boxed_1635_; uint8_t v_res_1636_; lean_object* v_r_1637_; 
v_x_2615__boxed_1635_ = lean_unbox_uint32(v_x_1634_);
lean_dec(v_x_1634_);
v_res_1636_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(v_x_2615__boxed_1635_);
v_r_1637_ = lean_box(v_res_1636_);
return v_r_1637_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(lean_object* v___x_1638_, lean_object* v_line_1639_, lean_object* v___x_1640_, lean_object* v___x_1641_, lean_object* v_a_1642_, lean_object* v_b_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_box(0);
switch(lean_obj_tag(v_a_1642_))
{
case 0:
{
lean_object* v_pos_1645_; lean_object* v___x_1646_; 
lean_dec(v_b_1643_);
v_pos_1645_ = lean_ctor_get(v_a_1642_, 0);
lean_inc(v_pos_1645_);
lean_dec_ref(v_a_1642_);
v___x_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_pos_1645_);
return v___x_1646_;
}
case 1:
{
lean_object* v_pos_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_b_1643_);
v_pos_1647_ = lean_ctor_get(v_a_1642_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_a_1642_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1649_ = v_a_1642_;
v_isShared_1650_ = v_isSharedCheck_1658_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_pos_1647_);
lean_dec(v_a_1642_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1658_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; 
v___x_1651_ = lean_nat_add(v___x_1638_, v_pos_1647_);
lean_dec(v_pos_1647_);
v___x_1652_ = lean_string_utf8_next_fast(v_line_1639_, v___x_1651_);
lean_dec(v___x_1651_);
v___x_1653_ = lean_nat_sub(v___x_1652_, v___x_1638_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set_tag(v___x_1649_, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1653_);
v___x_1655_ = v___x_1649_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
v_a_1642_ = v___x_1655_;
v_b_1643_ = v___x_1644_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1659_; lean_object* v_table_1660_; lean_object* v_stackPos_1661_; lean_object* v_needlePos_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1715_; 
v_needle_1659_ = lean_ctor_get(v_a_1642_, 0);
v_table_1660_ = lean_ctor_get(v_a_1642_, 1);
v_stackPos_1661_ = lean_ctor_get(v_a_1642_, 2);
v_needlePos_1662_ = lean_ctor_get(v_a_1642_, 3);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_a_1642_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1664_ = v_a_1642_;
v_isShared_1665_ = v_isSharedCheck_1715_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_needlePos_1662_);
lean_inc(v_stackPos_1661_);
lean_inc(v_table_1660_);
lean_inc(v_needle_1659_);
lean_dec(v_a_1642_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1715_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_str_1666_; lean_object* v_startInclusive_1667_; lean_object* v_endExclusive_1668_; lean_object* v_basePos_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v_str_1666_ = lean_ctor_get(v_needle_1659_, 0);
v_startInclusive_1667_ = lean_ctor_get(v_needle_1659_, 1);
v_endExclusive_1668_ = lean_ctor_get(v_needle_1659_, 2);
v_basePos_1669_ = lean_nat_sub(v_stackPos_1661_, v_needlePos_1662_);
v___x_1670_ = lean_nat_sub(v_endExclusive_1668_, v_startInclusive_1667_);
v___x_1671_ = lean_nat_add(v_basePos_1669_, v___x_1670_);
v___x_1672_ = lean_nat_sub(v___x_1641_, v___x_1638_);
v___x_1673_ = lean_nat_dec_le(v___x_1671_, v___x_1672_);
lean_dec(v___x_1671_);
if (v___x_1673_ == 0)
{
uint8_t v___x_1674_; 
lean_dec(v___x_1670_);
lean_del_object(v___x_1664_);
lean_dec(v_needlePos_1662_);
lean_dec(v_stackPos_1661_);
lean_dec_ref(v_table_1660_);
lean_dec_ref(v_needle_1659_);
v___x_1674_ = lean_nat_dec_lt(v_basePos_1669_, v___x_1672_);
lean_dec(v___x_1672_);
lean_dec(v_basePos_1669_);
if (v___x_1674_ == 0)
{
return v_b_1643_;
}
else
{
lean_object* v___x_1675_; 
lean_dec(v_b_1643_);
v___x_1675_ = lean_box(3);
v_a_1642_ = v___x_1675_;
v_b_1643_ = v___x_1644_;
goto _start;
}
}
else
{
lean_object* v___x_1677_; uint8_t v_stackByte_1678_; lean_object* v___x_1679_; uint8_t v_patByte_1680_; uint8_t v___x_1681_; 
lean_dec(v___x_1672_);
lean_dec(v_basePos_1669_);
v___x_1677_ = lean_nat_add(v___x_1638_, v_stackPos_1661_);
v_stackByte_1678_ = lean_string_get_byte_fast(v_line_1639_, v___x_1677_);
v___x_1679_ = lean_nat_add(v_startInclusive_1667_, v_needlePos_1662_);
v_patByte_1680_ = lean_string_get_byte_fast(v_str_1666_, v___x_1679_);
v___x_1681_ = lean_uint8_dec_eq(v_stackByte_1678_, v_patByte_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; uint8_t v___x_1683_; 
lean_dec(v___x_1670_);
lean_dec(v_b_1643_);
v___x_1682_ = lean_unsigned_to_nat(0u);
v___x_1683_ = lean_nat_dec_eq(v_needlePos_1662_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v_newNeedlePos_1686_; uint8_t v___x_1687_; 
v___x_1684_ = lean_unsigned_to_nat(1u);
v___x_1685_ = lean_nat_sub(v_needlePos_1662_, v___x_1684_);
lean_dec(v_needlePos_1662_);
v_newNeedlePos_1686_ = lean_array_fget_borrowed(v_table_1660_, v___x_1685_);
lean_dec(v___x_1685_);
v___x_1687_ = lean_nat_dec_eq(v_newNeedlePos_1686_, v___x_1682_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1689_; 
lean_inc(v_newNeedlePos_1686_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 3, v_newNeedlePos_1686_);
v___x_1689_ = v___x_1664_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_needle_1659_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_table_1660_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_stackPos_1661_);
lean_ctor_set(v_reuseFailAlloc_1691_, 3, v_newNeedlePos_1686_);
v___x_1689_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
v_a_1642_ = v___x_1689_;
v_b_1643_ = v___x_1644_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1692_; lean_object* v___x_1694_; 
v_nextStackPos_1692_ = l_String_Slice_posGE___redArg(v___x_1640_, v_stackPos_1661_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 3, v___x_1682_);
lean_ctor_set(v___x_1664_, 2, v_nextStackPos_1692_);
v___x_1694_ = v___x_1664_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_needle_1659_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_table_1660_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_nextStackPos_1692_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v___x_1682_);
v___x_1694_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
v_a_1642_ = v___x_1694_;
v_b_1643_ = v___x_1644_;
goto _start;
}
}
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v_nextStackPos_1699_; lean_object* v___x_1701_; 
lean_dec(v_needlePos_1662_);
v___x_1697_ = lean_unsigned_to_nat(1u);
v___x_1698_ = lean_nat_add(v_stackPos_1661_, v___x_1697_);
lean_dec(v_stackPos_1661_);
v_nextStackPos_1699_ = l_String_Slice_posGE___redArg(v___x_1640_, v___x_1698_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 3, v___x_1682_);
lean_ctor_set(v___x_1664_, 2, v_nextStackPos_1699_);
v___x_1701_ = v___x_1664_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_needle_1659_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_table_1660_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_nextStackPos_1699_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v___x_1682_);
v___x_1701_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
v_a_1642_ = v___x_1701_;
v_b_1643_ = v___x_1644_;
goto _start;
}
}
}
else
{
lean_object* v___x_1704_; lean_object* v_nextStackPos_1705_; lean_object* v_nextNeedlePos_1706_; uint8_t v___x_1707_; 
v___x_1704_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1705_ = lean_nat_add(v_stackPos_1661_, v___x_1704_);
lean_dec(v_stackPos_1661_);
v_nextNeedlePos_1706_ = lean_nat_add(v_needlePos_1662_, v___x_1704_);
lean_dec(v_needlePos_1662_);
v___x_1707_ = lean_nat_dec_eq(v_nextNeedlePos_1706_, v___x_1670_);
lean_dec(v___x_1670_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1709_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 3, v_nextNeedlePos_1706_);
lean_ctor_set(v___x_1664_, 2, v_nextStackPos_1705_);
v___x_1709_ = v___x_1664_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_needle_1659_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_table_1660_);
lean_ctor_set(v_reuseFailAlloc_1711_, 2, v_nextStackPos_1705_);
lean_ctor_set(v_reuseFailAlloc_1711_, 3, v_nextNeedlePos_1706_);
v___x_1709_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
v_a_1642_ = v___x_1709_;
goto _start;
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_del_object(v___x_1664_);
lean_dec_ref(v_table_1660_);
lean_dec_ref(v_needle_1659_);
lean_dec(v_b_1643_);
v___x_1712_ = lean_nat_sub(v_nextStackPos_1705_, v_nextNeedlePos_1706_);
lean_dec(v_nextNeedlePos_1706_);
lean_dec(v_nextStackPos_1705_);
v___x_1713_ = l_String_Slice_pos_x21(v___x_1640_, v___x_1712_);
lean_dec(v___x_1712_);
v___x_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
return v___x_1714_;
}
}
}
}
}
default: 
{
return v_b_1643_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg___boxed(lean_object* v___x_1716_, lean_object* v_line_1717_, lean_object* v___x_1718_, lean_object* v___x_1719_, lean_object* v_a_1720_, lean_object* v_b_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1716_, v_line_1717_, v___x_1718_, v___x_1719_, v_a_1720_, v_b_1721_);
lean_dec(v___x_1719_);
lean_dec_ref(v___x_1718_);
lean_dec_ref(v_line_1717_);
lean_dec(v___x_1716_);
return v_res_1722_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3));
v___x_1728_ = lean_string_utf8_byte_size(v___x_1727_);
return v___x_1728_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1729_ = lean_unsigned_to_nat(0u);
v___x_1730_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4);
v___x_1731_ = lean_nat_dec_eq(v___x_1730_, v___x_1729_);
return v___x_1731_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1732_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4);
v___x_1733_ = lean_unsigned_to_nat(0u);
v___x_1734_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3));
v___x_1735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
lean_ctor_set(v___x_1735_, 1, v___x_1733_);
lean_ctor_set(v___x_1735_, 2, v___x_1732_);
return v___x_1735_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6);
v___x_1737_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1736_);
return v___x_1737_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1738_ = lean_unsigned_to_nat(0u);
v___x_1739_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7);
v___x_1740_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6);
v___x_1741_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
lean_ctor_set(v___x_1741_, 1, v___x_1739_);
lean_ctor_set(v___x_1741_, 2, v___x_1738_);
lean_ctor_set(v___x_1741_, 3, v___x_1738_);
return v___x_1741_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9(void){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2));
v___x_1743_ = lean_string_utf8_byte_size(v___x_1742_);
return v___x_1743_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
v___x_1746_ = lean_nat_dec_eq(v___x_1745_, v___x_1744_);
return v___x_1746_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1747_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2));
v___x_1750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v___x_1748_);
lean_ctor_set(v___x_1750_, 2, v___x_1747_);
return v___x_1750_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11);
v___x_1752_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1751_);
return v___x_1752_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12);
v___x_1755_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11);
v___x_1756_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v___x_1754_);
lean_ctor_set(v___x_1756_, 2, v___x_1753_);
lean_ctor_set(v___x_1756_, 3, v___x_1753_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(lean_object* v_line_1757_){
_start:
{
lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___f_1765_; lean_object* v___f_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___x_1777_; lean_object* v___y_1779_; uint8_t v___x_1794_; 
v___f_1765_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0));
v___f_1766_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1));
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = lean_string_utf8_byte_size(v_line_1757_);
lean_inc_ref(v_line_1757_);
v___x_1777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1777_, 0, v_line_1757_);
lean_ctor_set(v___x_1777_, 1, v___x_1767_);
lean_ctor_set(v___x_1777_, 2, v___x_1768_);
v___x_1794_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13);
v___y_1779_ = v___x_1795_;
goto v___jp_1778_;
}
else
{
lean_object* v___x_1796_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1779_ = v___x_1796_;
goto v___jp_1778_;
}
v___jp_1758_:
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_nat_dec_eq(v___y_1760_, v___y_1759_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1757_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v_line_1757_);
v___x_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
else
{
lean_object* v___x_1764_; 
lean_dec(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v_line_1757_);
v___x_1764_ = lean_box(0);
return v___x_1764_;
}
}
v___jp_1769_:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___y_1772_, v_line_1757_, v___y_1771_, v___x_1768_, v___y_1773_, v___y_1770_);
lean_dec_ref(v___y_1771_);
if (lean_obj_tag(v___x_1774_) == 0)
{
v___y_1759_ = v___y_1772_;
v___y_1760_ = v___x_1768_;
goto v___jp_1758_;
}
else
{
lean_object* v_val_1775_; lean_object* v___x_1776_; 
v_val_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_val_1775_);
lean_dec_ref(v___x_1774_);
v___x_1776_ = lean_nat_add(v___y_1772_, v_val_1775_);
lean_dec(v_val_1775_);
v___y_1759_ = v___y_1772_;
v___y_1760_ = v___x_1776_;
goto v___jp_1758_;
}
}
v___jp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = lean_box(0);
v___x_1781_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_line_1757_, v___x_1777_, v___x_1768_, v___y_1779_, v___x_1780_);
lean_dec_ref(v___x_1777_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_dec_ref(v_line_1757_);
return v___x_1780_;
}
else
{
lean_object* v_val_1782_; uint8_t v___x_1783_; 
v_val_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_val_1782_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = lean_nat_dec_eq(v_val_1782_, v___x_1768_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = lean_string_utf8_next_fast(v_line_1757_, v_val_1782_);
lean_dec(v_val_1782_);
v___x_1785_ = lean_nat_dec_eq(v___x_1784_, v___x_1768_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1786_ = lean_string_utf8_next_fast(v_line_1757_, v___x_1784_);
v___x_1787_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1757_, v___x_1786_, v___f_1766_);
v___x_1788_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1757_, v___x_1787_, v___f_1765_);
v___x_1789_ = lean_nat_dec_eq(v___x_1788_, v___x_1768_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
lean_inc(v___x_1788_);
lean_inc_ref(v_line_1757_);
v___x_1790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1790_, 0, v_line_1757_);
lean_ctor_set(v___x_1790_, 1, v___x_1788_);
lean_ctor_set(v___x_1790_, 2, v___x_1768_);
v___x_1791_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8);
v___y_1770_ = v___x_1780_;
v___y_1771_ = v___x_1790_;
v___y_1772_ = v___x_1788_;
v___y_1773_ = v___x_1792_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1793_; 
v___x_1793_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1770_ = v___x_1780_;
v___y_1771_ = v___x_1790_;
v___y_1772_ = v___x_1788_;
v___y_1773_ = v___x_1793_;
goto v___jp_1769_;
}
}
else
{
lean_dec(v___x_1788_);
lean_dec_ref(v_line_1757_);
return v___x_1780_;
}
}
else
{
lean_dec_ref(v_line_1757_);
return v___x_1780_;
}
}
else
{
lean_dec(v_val_1782_);
lean_dec_ref(v_line_1757_);
return v___x_1780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(lean_object* v___x_1797_, lean_object* v_line_1798_, lean_object* v___x_1799_, lean_object* v___x_1800_, lean_object* v_inst_1801_, lean_object* v_R_1802_, lean_object* v_a_1803_, lean_object* v_b_1804_, lean_object* v_c_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1797_, v_line_1798_, v___x_1799_, v___x_1800_, v_a_1803_, v_b_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___boxed(lean_object* v___x_1807_, lean_object* v_line_1808_, lean_object* v___x_1809_, lean_object* v___x_1810_, lean_object* v_inst_1811_, lean_object* v_R_1812_, lean_object* v_a_1813_, lean_object* v_b_1814_, lean_object* v_c_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(v___x_1807_, v_line_1808_, v___x_1809_, v___x_1810_, v_inst_1811_, v_R_1812_, v_a_1813_, v_b_1814_, v_c_1815_);
lean_dec(v___x_1810_);
lean_dec_ref(v___x_1809_);
lean_dec_ref(v_line_1808_);
lean_dec(v___x_1807_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(lean_object* v_line_1817_){
_start:
{
lean_object* v___x_1818_; 
lean_inc_ref(v_line_1817_);
v___x_1818_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(v_line_1817_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1819_; 
v___x_1819_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(v_line_1817_);
return v___x_1819_;
}
else
{
lean_dec_ref(v_line_1817_);
return v___x_1818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleBtLine(lean_object* v_line_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(v_line_1820_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_box(0);
return v___x_1822_;
}
else
{
lean_object* v_val_1823_; lean_object* v_snd_1824_; lean_object* v_fst_1825_; lean_object* v_fst_1826_; lean_object* v_snd_1827_; lean_object* v___x_1828_; 
v_val_1823_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_val_1823_);
lean_dec_ref(v___x_1821_);
v_snd_1824_ = lean_ctor_get(v_val_1823_, 1);
lean_inc(v_snd_1824_);
v_fst_1825_ = lean_ctor_get(v_val_1823_, 0);
lean_inc(v_fst_1825_);
lean_dec(v_val_1823_);
v_fst_1826_ = lean_ctor_get(v_snd_1824_, 0);
lean_inc(v_fst_1826_);
v_snd_1827_ = lean_ctor_get(v_snd_1824_, 1);
lean_inc(v_snd_1827_);
lean_dec(v_snd_1824_);
v___x_1828_ = l_Lean_Name_Demangle_demangleSymbol(v_fst_1826_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_dec(v_snd_1827_);
lean_dec(v_fst_1825_);
return v___x_1828_;
}
else
{
lean_object* v_val_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1838_; 
v_val_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1838_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_val_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1838_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1833_ = lean_string_append(v_fst_1825_, v_val_1829_);
lean_dec(v_val_1829_);
v___x_1834_ = lean_string_append(v___x_1833_, v_snd_1827_);
lean_dec(v_snd_1827_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1834_);
v___x_1836_ = v___x_1831_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_demangle_bt_line_cstr(lean_object* v_line_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_Name_Demangle_demangleBtLine(v_line_1839_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_1841_;
}
else
{
lean_object* v_val_1842_; 
v_val_1842_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_val_1842_);
lean_dec_ref(v___x_1840_);
return v_val_1842_;
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
