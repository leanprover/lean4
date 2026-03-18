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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(lean_object* v_s_41_, lean_object* v_curr_42_){
_start:
{
lean_object* v_str_43_; lean_object* v_startInclusive_44_; lean_object* v_endExclusive_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___y_49_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v_str_43_ = lean_ctor_get(v_s_41_, 0);
v_startInclusive_44_ = lean_ctor_get(v_s_41_, 1);
v_endExclusive_45_ = lean_ctor_get(v_s_41_, 2);
v___x_46_ = lean_nat_add(v_startInclusive_44_, v_curr_42_);
lean_inc(v_endExclusive_45_);
lean_inc(v___x_46_);
lean_inc_ref(v_str_43_);
v___x_47_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_47_, 0, v_str_43_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
lean_ctor_set(v___x_47_, 2, v_endExclusive_45_);
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_nat_sub(v_endExclusive_45_, v___x_46_);
v___x_57_ = lean_nat_dec_eq(v___x_55_, v___x_56_);
lean_dec(v___x_56_);
if (v___x_57_ == 0)
{
uint32_t v___x_58_; uint32_t v___x_59_; uint8_t v___x_60_; 
v___x_58_ = lean_string_utf8_get_fast(v_str_43_, v___x_46_);
v___x_59_ = 48;
v___x_60_ = lean_uint32_dec_le(v___x_59_, v___x_58_);
if (v___x_60_ == 0)
{
v___y_49_ = v___x_60_;
goto v___jp_48_;
}
else
{
uint32_t v___x_61_; uint8_t v___x_62_; 
v___x_61_ = 57;
v___x_62_ = lean_uint32_dec_le(v___x_58_, v___x_61_);
v___y_49_ = v___x_62_;
goto v___jp_48_;
}
}
else
{
lean_dec(v___x_46_);
lean_dec(v_curr_42_);
return v___x_47_;
}
v___jp_48_:
{
if (v___y_49_ == 0)
{
lean_dec(v___x_46_);
lean_dec(v_curr_42_);
return v___x_47_;
}
else
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_50_ = lean_string_utf8_next_fast(v_str_43_, v___x_46_);
v___x_51_ = lean_nat_sub(v___x_50_, v___x_46_);
lean_dec(v___x_46_);
v___x_52_ = lean_nat_add(v_curr_42_, v___x_51_);
lean_dec(v___x_51_);
v___x_53_ = lean_nat_dec_lt(v_curr_42_, v___x_52_);
lean_dec(v_curr_42_);
if (v___x_53_ == 0)
{
lean_dec(v___x_52_);
return v___x_47_;
}
else
{
lean_dec_ref(v___x_47_);
v_curr_42_ = v___x_52_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0___boxed(lean_object* v_s_63_, lean_object* v_curr_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(v_s_63_, v_curr_64_);
lean_dec_ref(v_s_63_);
return v_res_65_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(lean_object* v_s_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_string_utf8_byte_size(v_s_66_);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_nat_dec_eq(v___x_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_startInclusive_72_; lean_object* v_endExclusive_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_70_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_70_, 0, v_s_66_);
lean_ctor_set(v___x_70_, 1, v___x_68_);
lean_ctor_set(v___x_70_, 2, v___x_67_);
v___x_71_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits_spec__0(v___x_70_, v___x_68_);
lean_dec_ref(v___x_70_);
v_startInclusive_72_ = lean_ctor_get(v___x_71_, 1);
lean_inc(v_startInclusive_72_);
v_endExclusive_73_ = lean_ctor_get(v___x_71_, 2);
lean_inc(v_endExclusive_73_);
lean_dec_ref(v___x_71_);
v___x_74_ = lean_nat_sub(v_endExclusive_73_, v_startInclusive_72_);
lean_dec(v_startInclusive_72_);
lean_dec(v_endExclusive_73_);
v___x_75_ = lean_nat_dec_eq(v___x_74_, v___x_68_);
lean_dec(v___x_74_);
return v___x_75_;
}
else
{
uint8_t v___x_76_; 
lean_dec_ref(v_s_66_);
v___x_76_ = 0;
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits___boxed(lean_object* v_s_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_s_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go(lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
switch(lean_obj_tag(v_a_80_))
{
case 0:
{
return v_a_81_;
}
case 1:
{
lean_object* v_pre_82_; lean_object* v_str_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_pre_82_ = lean_ctor_get(v_a_80_, 0);
v_str_83_ = lean_ctor_get(v_a_80_, 1);
lean_inc_ref(v_str_83_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v_str_83_);
v___x_85_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v_a_81_);
v_a_80_ = v_pre_82_;
v_a_81_ = v___x_85_;
goto _start;
}
default: 
{
lean_object* v_pre_87_; lean_object* v_i_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_pre_87_ = lean_ctor_get(v_a_80_, 0);
v_i_88_ = lean_ctor_get(v_a_80_, 1);
lean_inc(v_i_88_);
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v_i_88_);
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v_a_81_);
v_a_80_ = v_pre_87_;
v_a_81_ = v___x_90_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go___boxed(lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go(v_a_92_, v_a_93_);
lean_dec(v_a_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(lean_object* v_n_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_box(0);
v___x_97_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts_go(v_n_95_, v___x_96_);
v___x_98_ = lean_array_mk(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts___boxed(lean_object* v_n_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(v_n_99_);
lean_dec(v_n_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(lean_object* v_as_101_, size_t v_i_102_, size_t v_stop_103_, lean_object* v_b_104_){
_start:
{
lean_object* v___y_106_; uint8_t v___x_110_; 
v___x_110_ = lean_usize_dec_eq(v_i_102_, v_stop_103_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
v___x_111_ = lean_array_uget_borrowed(v_as_101_, v_i_102_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_s_112_; lean_object* v___x_113_; 
v_s_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc_ref(v_s_112_);
v___x_113_ = l_Lean_Name_str___override(v_b_104_, v_s_112_);
v___y_106_ = v___x_113_;
goto v___jp_105_;
}
else
{
lean_object* v_n_114_; lean_object* v___x_115_; 
v_n_114_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_n_114_);
v___x_115_ = l_Lean_Name_num___override(v_b_104_, v_n_114_);
v___y_106_ = v___x_115_;
goto v___jp_105_;
}
}
else
{
return v_b_104_;
}
v___jp_105_:
{
size_t v___x_107_; size_t v___x_108_; 
v___x_107_ = ((size_t)1ULL);
v___x_108_ = lean_usize_add(v_i_102_, v___x_107_);
v_i_102_ = v___x_108_;
v_b_104_ = v___y_106_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0___boxed(lean_object* v_as_116_, lean_object* v_i_117_, lean_object* v_stop_118_, lean_object* v_b_119_){
_start:
{
size_t v_i_boxed_120_; size_t v_stop_boxed_121_; lean_object* v_res_122_; 
v_i_boxed_120_ = lean_unbox_usize(v_i_117_);
lean_dec(v_i_117_);
v_stop_boxed_121_ = lean_unbox_usize(v_stop_118_);
lean_dec(v_stop_118_);
v_res_122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_as_116_, v_i_boxed_120_, v_stop_boxed_121_, v_b_119_);
lean_dec_ref(v_as_116_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(lean_object* v_parts_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_124_ = lean_box(0);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_array_get_size(v_parts_123_);
v___x_127_ = lean_nat_dec_lt(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
return v___x_124_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = lean_nat_dec_le(v___x_126_, v___x_126_);
if (v___x_128_ == 0)
{
if (v___x_127_ == 0)
{
return v___x_124_;
}
else
{
size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; 
v___x_129_ = ((size_t)0ULL);
v___x_130_ = lean_usize_of_nat(v___x_126_);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_parts_123_, v___x_129_, v___x_130_, v___x_124_);
return v___x_131_;
}
}
else
{
size_t v___x_132_; size_t v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((size_t)0ULL);
v___x_133_ = lean_usize_of_nat(v___x_126_);
v___x_134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName_spec__0(v_parts_123_, v___x_132_, v___x_133_, v___x_124_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName___boxed(lean_object* v_parts_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(v_parts_135_);
lean_dec_ref(v_parts_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(lean_object* v_comps_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_139_ = lean_array_get_size(v_comps_138_);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_nat_dec_eq(v___x_139_, v___x_140_);
if (v___x_141_ == 0)
{
uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = 1;
v___x_143_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_namePartsToName(v_comps_138_);
v___x_144_ = l_Lean_Name_toString(v___x_143_, v___x_142_);
return v___x_144_;
}
else
{
lean_object* v___x_145_; 
v___x_145_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___boxed(lean_object* v_comps_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_comps_146_);
lean_dec_ref(v_comps_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(lean_object* v_c_176_){
_start:
{
if (lean_obj_tag(v_c_176_) == 0)
{
lean_object* v_s_179_; uint8_t v___y_181_; uint8_t v___y_190_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_s_179_ = lean_ctor_get(v_c_176_, 0);
lean_inc_ref(v_s_179_);
lean_dec_ref(v_c_176_);
v___x_203_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__11));
v___x_204_ = lean_string_dec_eq(v_s_179_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__12));
v___x_206_ = lean_string_dec_eq(v_s_179_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__13));
v___x_208_ = lean_string_dec_eq(v_s_179_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__14));
v___x_210_ = lean_string_dec_eq(v_s_179_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__15));
v___x_212_ = lean_string_dec_eq(v_s_179_, v___x_211_);
v___y_190_ = v___x_212_;
goto v___jp_189_;
}
else
{
v___y_190_ = v___x_210_;
goto v___jp_189_;
}
}
else
{
lean_object* v___x_213_; 
lean_dec_ref(v_s_179_);
v___x_213_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__17));
return v___x_213_;
}
}
else
{
lean_object* v___x_214_; 
lean_dec_ref(v_s_179_);
v___x_214_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__19));
return v___x_214_;
}
}
else
{
lean_object* v___x_215_; 
lean_dec_ref(v_s_179_);
v___x_215_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__21));
return v___x_215_;
}
v___jp_180_:
{
if (v___y_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__2));
v___x_183_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_179_, v___x_182_);
if (lean_obj_tag(v___x_183_) == 0)
{
return v___x_183_;
}
else
{
lean_object* v_val_184_; uint8_t v___x_185_; 
v_val_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_val_184_);
lean_dec_ref(v___x_183_);
v___x_185_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(0);
return v___x_186_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_187_;
}
}
}
else
{
lean_object* v___x_188_; 
lean_dec_ref(v_s_179_);
v___x_188_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_188_;
}
}
v___jp_189_:
{
if (v___y_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__3));
v___x_192_ = lean_string_dec_eq(v_s_179_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__4));
v___x_194_ = lean_string_dec_eq(v_s_179_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__5));
v___x_196_ = lean_string_dec_eq(v_s_179_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__6));
lean_inc_ref(v_s_179_);
v___x_198_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_179_, v___x_197_);
if (lean_obj_tag(v___x_198_) == 0)
{
v___y_181_ = v___x_196_;
goto v___jp_180_;
}
else
{
lean_object* v_val_199_; uint8_t v___x_200_; 
v_val_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_val_199_);
lean_dec_ref(v___x_198_);
v___x_200_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_199_);
v___y_181_ = v___x_200_;
goto v___jp_180_;
}
}
else
{
lean_object* v___x_201_; 
lean_dec_ref(v_s_179_);
v___x_201_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__8));
return v___x_201_;
}
}
else
{
lean_object* v___x_202_; 
lean_dec_ref(v_s_179_);
v___x_202_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__10));
return v___x_202_;
}
}
else
{
lean_dec_ref(v_s_179_);
goto v___jp_177_;
}
}
else
{
lean_dec_ref(v_s_179_);
goto v___jp_177_;
}
}
}
else
{
lean_object* v___x_216_; 
lean_dec_ref(v_c_176_);
v___x_216_ = lean_box(0);
return v___x_216_;
}
v___jp_177_:
{
lean_object* v___x_178_; 
v___x_178_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix___closed__1));
return v___x_178_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(lean_object* v_c_218_){
_start:
{
if (lean_obj_tag(v_c_218_) == 0)
{
lean_object* v_s_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_s_219_ = lean_ctor_get(v_c_218_, 0);
lean_inc_ref(v_s_219_);
lean_dec_ref(v_c_218_);
v___x_220_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___closed__0));
v___x_221_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_219_, v___x_220_);
if (lean_obj_tag(v___x_221_) == 0)
{
uint8_t v___x_222_; 
v___x_222_ = 0;
return v___x_222_;
}
else
{
lean_object* v_val_223_; uint8_t v___x_224_; 
v_val_223_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_223_);
lean_dec_ref(v___x_221_);
v___x_224_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_223_);
return v___x_224_;
}
}
else
{
uint8_t v___x_225_; 
lean_dec_ref(v_c_218_);
v___x_225_ = 0;
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex___boxed(lean_object* v_c_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(v_c_226_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
if (lean_obj_tag(v_x_230_) == 0)
{
uint8_t v___x_231_; 
v___x_231_ = 1;
return v___x_231_;
}
else
{
uint8_t v___x_232_; 
v___x_232_ = 0;
return v___x_232_;
}
}
else
{
if (lean_obj_tag(v_x_230_) == 0)
{
uint8_t v___x_233_; 
v___x_233_ = 0;
return v___x_233_;
}
else
{
lean_object* v_val_234_; lean_object* v_val_235_; uint8_t v___x_236_; 
v_val_234_ = lean_ctor_get(v_x_229_, 0);
v_val_235_ = lean_ctor_get(v_x_230_, 0);
v___x_236_ = l_Lean_instBEqNamePart_beq(v_val_234_, v_val_235_);
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0___boxed(lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v_x_237_, v_x_238_);
lean_dec(v_x_238_);
lean_dec(v_x_237_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(lean_object* v_stop_248_, lean_object* v_start_249_, uint8_t v___y_250_, lean_object* v_comps_251_, lean_object* v_range_252_, lean_object* v_b_253_, lean_object* v_i_254_){
_start:
{
lean_object* v_stop_255_; lean_object* v_step_256_; uint8_t v___x_257_; 
v_stop_255_ = lean_ctor_get(v_range_252_, 1);
v_step_256_ = lean_ctor_get(v_range_252_, 2);
v___x_257_ = lean_nat_dec_lt(v_i_254_, v_stop_255_);
if (v___x_257_ == 0)
{
lean_dec(v_i_254_);
lean_dec(v_start_249_);
return v_b_253_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___y_263_; lean_object* v___x_278_; uint8_t v___x_279_; 
lean_dec_ref(v_b_253_);
v___x_258_ = lean_box(0);
v___x_259_ = lean_box(0);
v___x_260_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0));
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_array_get_size(v_comps_251_);
v___x_279_ = lean_nat_dec_lt(v_i_254_, v___x_278_);
if (v___x_279_ == 0)
{
v___y_263_ = v___x_258_;
goto v___jp_262_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_array_fget_borrowed(v_comps_251_, v_i_254_);
lean_inc(v___x_280_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
v___y_263_ = v___x_281_;
goto v___jp_262_;
}
v___jp_262_:
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2));
v___x_265_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_263_, v___x_264_);
lean_dec(v___y_263_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = lean_nat_add(v_i_254_, v_step_256_);
lean_dec(v_i_254_);
v_b_253_ = v___x_260_;
v_i_254_ = v___x_266_;
goto _start;
}
else
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_nat_add(v_i_254_, v___x_261_);
lean_dec(v_i_254_);
v___x_269_ = lean_nat_dec_lt(v___x_268_, v_stop_248_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec(v___x_268_);
v___x_270_ = lean_box(v___x_269_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v_start_249_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_259_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec(v_start_249_);
v___x_274_ = lean_box(v___y_250_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_268_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_259_);
return v___x_277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___boxed(lean_object* v_stop_282_, lean_object* v_start_283_, lean_object* v___y_284_, lean_object* v_comps_285_, lean_object* v_range_286_, lean_object* v_b_287_, lean_object* v_i_288_){
_start:
{
uint8_t v___y_946__boxed_289_; lean_object* v_res_290_; 
v___y_946__boxed_289_ = lean_unbox(v___y_284_);
v_res_290_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_282_, v_start_283_, v___y_946__boxed_289_, v_comps_285_, v_range_286_, v_b_287_, v_i_288_);
lean_dec_ref(v_range_286_);
lean_dec_ref(v_comps_285_);
lean_dec(v_stop_282_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(lean_object* v_comps_296_, lean_object* v_start_297_, lean_object* v_stop_298_){
_start:
{
uint8_t v___y_300_; lean_object* v___y_321_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_324_ = lean_unsigned_to_nat(3u);
v___x_325_ = lean_nat_sub(v_stop_298_, v_start_297_);
v___x_326_ = lean_nat_dec_le(v___x_324_, v___x_325_);
lean_dec(v___x_325_);
if (v___x_326_ == 0)
{
v___y_300_ = v___x_326_;
goto v___jp_299_;
}
else
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_array_get_size(v_comps_296_);
v___x_328_ = lean_nat_dec_lt(v_start_297_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_box(0);
v___y_321_ = v___x_329_;
goto v___jp_320_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_array_fget_borrowed(v_comps_296_, v_start_297_);
lean_inc(v___x_330_);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
v___y_321_ = v___x_331_;
goto v___jp_320_;
}
}
v___jp_299_:
{
if (v___y_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v_stop_298_);
v___x_301_ = lean_box(v___y_300_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v_start_297_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
return v___x_302_;
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v_fst_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_318_; 
v___x_303_ = lean_unsigned_to_nat(1u);
v___x_304_ = lean_nat_add(v_start_297_, v___x_303_);
lean_inc(v_stop_298_);
lean_inc(v___x_304_);
v___x_305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v_stop_298_);
lean_ctor_set(v___x_305_, 2, v___x_303_);
v___x_306_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__0));
lean_inc(v_start_297_);
v___x_307_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_298_, v_start_297_, v___y_300_, v_comps_296_, v___x_305_, v___x_306_, v___x_304_);
lean_dec_ref(v___x_305_);
lean_dec(v_stop_298_);
v_fst_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; 
v_unused_319_ = lean_ctor_get(v___x_307_, 1);
lean_dec(v_unused_319_);
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_fst_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
if (lean_obj_tag(v_fst_308_) == 0)
{
uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_312_ = 0;
v___x_313_ = lean_box(v___x_312_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v___x_313_);
lean_ctor_set(v___x_310_, 0, v_start_297_);
v___x_315_ = v___x_310_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_start_297_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
lean_object* v_val_317_; 
lean_del_object(v___x_310_);
lean_dec(v_start_297_);
v_val_317_ = lean_ctor_get(v_fst_308_, 0);
lean_inc(v_val_317_);
lean_dec_ref(v_fst_308_);
return v_val_317_;
}
}
}
}
v___jp_320_:
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2));
v___x_323_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_321_, v___x_322_);
lean_dec(v___y_321_);
v___y_300_ = v___x_323_;
goto v___jp_299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___boxed(lean_object* v_comps_332_, lean_object* v_start_333_, lean_object* v_stop_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_comps_332_, v_start_333_, v_stop_334_);
lean_dec_ref(v_comps_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(lean_object* v_stop_336_, lean_object* v_start_337_, uint8_t v___y_338_, lean_object* v_comps_339_, lean_object* v_range_340_, lean_object* v_b_341_, lean_object* v_i_342_, lean_object* v_hs_343_, lean_object* v_hl_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg(v_stop_336_, v_start_337_, v___y_338_, v_comps_339_, v_range_340_, v_b_341_, v_i_342_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___boxed(lean_object* v_stop_346_, lean_object* v_start_347_, lean_object* v___y_348_, lean_object* v_comps_349_, lean_object* v_range_350_, lean_object* v_b_351_, lean_object* v_i_352_, lean_object* v_hs_353_, lean_object* v_hl_354_){
_start:
{
uint8_t v___y_1088__boxed_355_; lean_object* v_res_356_; 
v___y_1088__boxed_355_ = lean_unbox(v___y_348_);
v_res_356_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1(v_stop_346_, v_start_347_, v___y_1088__boxed_355_, v_comps_349_, v_range_350_, v_b_351_, v_i_352_, v_hs_353_, v_hl_354_);
lean_dec_ref(v_range_350_);
lean_dec_ref(v_comps_349_);
lean_dec(v_stop_346_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(lean_object* v___x_357_, lean_object* v_comps_358_, lean_object* v_range_359_, lean_object* v_b_360_, lean_object* v_i_361_){
_start:
{
lean_object* v_stop_362_; lean_object* v_step_363_; uint8_t v___x_364_; 
v_stop_362_ = lean_ctor_get(v_range_359_, 1);
v_step_363_ = lean_ctor_get(v_range_359_, 2);
v___x_364_ = lean_nat_dec_lt(v_i_361_, v_stop_362_);
if (v___x_364_ == 0)
{
lean_dec(v_i_361_);
lean_inc(v_b_360_);
return v_b_360_;
}
else
{
lean_object* v___x_365_; uint8_t v___y_367_; lean_object* v___y_372_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_array_get_size(v_comps_358_);
v___x_378_ = lean_nat_dec_lt(v_i_361_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
v___x_379_ = lean_box(0);
v___y_372_ = v___x_379_;
goto v___jp_371_;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_array_fget_borrowed(v_comps_358_, v_i_361_);
lean_inc(v___x_380_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v___y_372_ = v___x_381_;
goto v___jp_371_;
}
v___jp_366_:
{
if (v___y_367_ == 0)
{
lean_object* v___x_368_; 
v___x_368_ = lean_nat_add(v_i_361_, v_step_363_);
lean_dec(v_i_361_);
v_i_361_ = v___x_368_;
goto _start;
}
else
{
lean_object* v___x_370_; 
v___x_370_ = lean_nat_add(v_i_361_, v___x_365_);
lean_dec(v_i_361_);
return v___x_370_;
}
}
v___jp_371_:
{
lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_373_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__1___redArg___closed__2));
v___x_374_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_372_, v___x_373_);
lean_dec(v___y_372_);
if (v___x_374_ == 0)
{
v___y_367_ = v___x_374_;
goto v___jp_366_;
}
else
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = lean_nat_add(v_i_361_, v___x_365_);
v___x_376_ = lean_nat_dec_lt(v___x_375_, v___x_357_);
lean_dec(v___x_375_);
v___y_367_ = v___x_376_;
goto v___jp_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg___boxed(lean_object* v___x_382_, lean_object* v_comps_383_, lean_object* v_range_384_, lean_object* v_b_385_, lean_object* v_i_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_382_, v_comps_383_, v_range_384_, v_b_385_, v_i_386_);
lean_dec(v_b_385_);
lean_dec_ref(v_range_384_);
lean_dec_ref(v_comps_383_);
lean_dec(v___x_382_);
return v_res_387_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(lean_object* v_a_388_, lean_object* v_as_389_, size_t v_i_390_, size_t v_stop_391_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = lean_usize_dec_eq(v_i_390_, v_stop_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = lean_array_uget_borrowed(v_as_389_, v_i_390_);
v___x_394_ = lean_string_dec_eq(v_a_388_, v___x_393_);
if (v___x_394_ == 0)
{
size_t v___x_395_; size_t v___x_396_; 
v___x_395_ = ((size_t)1ULL);
v___x_396_ = lean_usize_add(v_i_390_, v___x_395_);
v_i_390_ = v___x_396_;
goto _start;
}
else
{
return v___x_394_;
}
}
else
{
uint8_t v___x_398_; 
v___x_398_ = 0;
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0___boxed(lean_object* v_a_399_, lean_object* v_as_400_, lean_object* v_i_401_, lean_object* v_stop_402_){
_start:
{
size_t v_i_boxed_403_; size_t v_stop_boxed_404_; uint8_t v_res_405_; lean_object* v_r_406_; 
v_i_boxed_403_ = lean_unbox_usize(v_i_401_);
lean_dec(v_i_401_);
v_stop_boxed_404_ = lean_unbox_usize(v_stop_402_);
lean_dec(v_stop_402_);
v_res_405_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_399_, v_as_400_, v_i_boxed_403_, v_stop_boxed_404_);
lean_dec_ref(v_as_400_);
lean_dec_ref(v_a_399_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(lean_object* v_as_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = lean_array_get_size(v_as_407_);
v___x_411_ = lean_nat_dec_lt(v___x_409_, v___x_410_);
if (v___x_411_ == 0)
{
return v___x_411_;
}
else
{
if (v___x_411_ == 0)
{
return v___x_411_;
}
else
{
size_t v___x_412_; size_t v___x_413_; uint8_t v___x_414_; 
v___x_412_ = ((size_t)0ULL);
v___x_413_ = lean_usize_of_nat(v___x_410_);
v___x_414_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0_spec__0(v_a_408_, v_as_407_, v___x_412_, v___x_413_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0___boxed(lean_object* v_as_415_, lean_object* v_a_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_as_415_, v_a_416_);
lean_dec_ref(v_a_416_);
lean_dec_ref(v_as_415_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(lean_object* v_comps_419_, lean_object* v_range_420_, lean_object* v_b_421_, lean_object* v_i_422_){
_start:
{
lean_object* v_stop_423_; lean_object* v_step_424_; lean_object* v_a_426_; uint8_t v___x_429_; 
v_stop_423_ = lean_ctor_get(v_range_420_, 1);
v_step_424_ = lean_ctor_get(v_range_420_, 2);
v___x_429_ = lean_nat_dec_lt(v_i_422_, v_stop_423_);
if (v___x_429_ == 0)
{
lean_dec(v_i_422_);
return v_b_421_;
}
else
{
lean_object* v_fst_430_; lean_object* v_snd_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_455_; 
v_fst_430_ = lean_ctor_get(v_b_421_, 0);
v_snd_431_ = lean_ctor_get(v_b_421_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_b_421_);
if (v_isSharedCheck_455_ == 0)
{
v___x_433_ = v_b_421_;
v_isShared_434_ = v_isSharedCheck_455_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_snd_431_);
lean_inc(v_fst_430_);
lean_dec(v_b_421_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_455_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = l_Lean_instInhabitedNamePart_default;
v___x_436_ = lean_array_get_borrowed(v___x_435_, v_comps_419_, v_i_422_);
lean_inc(v___x_436_);
v___x_437_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
uint8_t v___x_438_; 
lean_inc(v___x_436_);
v___x_438_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isSpecIndex(v___x_436_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_441_; 
lean_inc(v___x_436_);
v___x_439_ = lean_array_push(v_fst_430_, v___x_436_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_439_);
v___x_441_ = v___x_433_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_snd_431_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
v_a_426_ = v___x_441_;
goto v___jp_425_;
}
}
else
{
lean_object* v___x_444_; 
if (v_isShared_434_ == 0)
{
v___x_444_ = v___x_433_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_fst_430_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_snd_431_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
v_a_426_ = v___x_444_;
goto v___jp_425_;
}
}
}
else
{
lean_object* v_val_446_; uint8_t v___x_447_; 
v_val_446_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_446_);
lean_dec_ref(v___x_437_);
v___x_447_ = l_Array_contains___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__0(v_snd_431_, v_val_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_array_push(v_snd_431_, v_val_446_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_448_);
v___x_450_ = v___x_433_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_fst_430_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
v_a_426_ = v___x_450_;
goto v___jp_425_;
}
}
else
{
lean_object* v___x_453_; 
lean_dec(v_val_446_);
if (v_isShared_434_ == 0)
{
v___x_453_ = v___x_433_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_fst_430_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_snd_431_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
v_a_426_ = v___x_453_;
goto v___jp_425_;
}
}
}
}
}
v___jp_425_:
{
lean_object* v___x_427_; 
v___x_427_ = lean_nat_add(v_i_422_, v_step_424_);
lean_dec(v_i_422_);
v_b_421_ = v_a_426_;
v_i_422_ = v___x_427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg___boxed(lean_object* v_comps_456_, lean_object* v_range_457_, lean_object* v_b_458_, lean_object* v_i_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_456_, v_range_457_, v_b_458_, v_i_459_);
lean_dec_ref(v_range_457_);
lean_dec_ref(v_comps_456_);
return v_res_460_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1(void){
_start:
{
lean_object* v_parts_463_; lean_object* v___x_464_; 
v_parts_463_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__0));
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_parts_463_);
lean_ctor_set(v___x_464_, 1, v_parts_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(lean_object* v_comps_465_){
_start:
{
lean_object* v_begin___467_; lean_object* v_begin___483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___y_487_; lean_object* v___y_492_; uint8_t v___x_495_; 
v_begin___483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_unsigned_to_nat(3u);
v___x_485_ = lean_array_get_size(v_comps_465_);
v___x_495_ = lean_nat_dec_le(v___x_484_, v___x_485_);
if (v___x_495_ == 0)
{
v___y_487_ = v___x_495_;
goto v___jp_486_;
}
else
{
uint8_t v___x_496_; 
v___x_496_ = lean_nat_dec_lt(v_begin___483_, v___x_485_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
v___x_497_ = lean_box(0);
v___y_492_ = v___x_497_;
goto v___jp_491_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_array_fget_borrowed(v_comps_465_, v_begin___483_);
lean_inc(v___x_498_);
v___x_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
v___y_492_ = v___x_499_;
goto v___jp_491_;
}
}
v___jp_466_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_fst_473_; lean_object* v_snd_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_482_; 
v___x_468_ = lean_array_get_size(v_comps_465_);
v___x_469_ = lean_unsigned_to_nat(1u);
lean_inc(v_begin___467_);
v___x_470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_470_, 0, v_begin___467_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
lean_ctor_set(v___x_470_, 2, v___x_469_);
v___x_471_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___closed__1);
v___x_472_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_465_, v___x_470_, v___x_471_, v_begin___467_);
lean_dec_ref(v___x_470_);
v_fst_473_ = lean_ctor_get(v___x_472_, 0);
v_snd_474_ = lean_ctor_get(v___x_472_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_482_ == 0)
{
v___x_476_ = v___x_472_;
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_snd_474_);
lean_inc(v_fst_473_);
lean_dec(v___x_472_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_fst_473_);
lean_dec(v_fst_473_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_478_);
v___x_480_ = v___x_476_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_snd_474_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
v___jp_486_:
{
if (v___y_487_ == 0)
{
v_begin___467_ = v_begin___483_;
goto v___jp_466_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_485_);
lean_ctor_set(v___x_489_, 2, v___x_488_);
v___x_490_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_485_, v_comps_465_, v___x_489_, v_begin___483_, v___x_488_);
lean_dec_ref(v___x_489_);
v_begin___467_ = v___x_490_;
goto v___jp_466_;
}
}
v___jp_491_:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate___closed__2));
v___x_494_ = l_Option_instBEq_beq___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate_spec__0(v___y_492_, v___x_493_);
lean_dec(v___y_492_);
v___y_487_ = v___x_494_;
goto v___jp_486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext___boxed(lean_object* v_comps_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(v_comps_500_);
lean_dec_ref(v_comps_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1(lean_object* v_comps_502_, lean_object* v_range_503_, lean_object* v_b_504_, lean_object* v_i_505_, lean_object* v_hs_506_, lean_object* v_hl_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___redArg(v_comps_502_, v_range_503_, v_b_504_, v_i_505_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1___boxed(lean_object* v_comps_509_, lean_object* v_range_510_, lean_object* v_b_511_, lean_object* v_i_512_, lean_object* v_hs_513_, lean_object* v_hl_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__1(v_comps_509_, v_range_510_, v_b_511_, v_i_512_, v_hs_513_, v_hl_514_);
lean_dec_ref(v_range_510_);
lean_dec_ref(v_comps_509_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2(lean_object* v___x_516_, lean_object* v_comps_517_, lean_object* v_range_518_, lean_object* v_b_519_, lean_object* v_i_520_, lean_object* v_hs_521_, lean_object* v_hl_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___redArg(v___x_516_, v_comps_517_, v_range_518_, v_b_519_, v_i_520_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2___boxed(lean_object* v___x_524_, lean_object* v_comps_525_, lean_object* v_range_526_, lean_object* v_b_527_, lean_object* v_i_528_, lean_object* v_hs_529_, lean_object* v_hl_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext_spec__2(v___x_524_, v_comps_525_, v_range_526_, v_b_527_, v_i_528_, v_hs_529_, v_hl_530_);
lean_dec(v_b_527_);
lean_dec_ref(v_range_526_);
lean_dec_ref(v_comps_525_);
lean_dec(v___x_524_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(lean_object* v___x_535_, lean_object* v_range_536_, lean_object* v_b_537_, lean_object* v_i_538_){
_start:
{
lean_object* v_stop_539_; lean_object* v_step_540_; uint8_t v___x_541_; 
v_stop_539_ = lean_ctor_get(v_range_536_, 1);
v_step_540_ = lean_ctor_get(v_range_536_, 2);
v___x_541_ = lean_nat_dec_lt(v_i_538_, v_stop_539_);
if (v___x_541_ == 0)
{
lean_dec(v_i_538_);
lean_inc(v_b_537_);
return v_b_537_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_542_ = l_Lean_instInhabitedNamePart_default;
v___x_543_ = lean_array_get_borrowed(v___x_542_, v___x_535_, v_i_538_);
v___x_544_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1));
v___x_545_ = l_Lean_instBEqNamePart_beq(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_nat_add(v_i_538_, v_step_540_);
lean_dec(v_i_538_);
v_i_538_ = v___x_546_;
goto _start;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v_i_538_);
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___boxed(lean_object* v___x_549_, lean_object* v_range_550_, lean_object* v_b_551_, lean_object* v_i_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_549_, v_range_550_, v_b_551_, v_i_552_);
lean_dec(v_b_551_);
lean_dec_ref(v_range_550_);
lean_dec_ref(v___x_549_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(lean_object* v___x_554_, lean_object* v_as_555_, size_t v_sz_556_, size_t v_i_557_, lean_object* v_b_558_){
_start:
{
lean_object* v_a_560_; uint8_t v___x_564_; 
v___x_564_ = lean_usize_dec_lt(v_i_557_, v_sz_556_);
if (v___x_564_ == 0)
{
return v_b_558_;
}
else
{
lean_object* v_a_565_; lean_object* v___x_566_; lean_object* v_name_569_; lean_object* v_flags_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_a_565_ = lean_array_uget_borrowed(v_as_555_, v_i_557_);
v___x_566_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_processSpecContext(v_a_565_);
v_name_569_ = lean_ctor_get(v___x_566_, 0);
lean_inc_ref(v_name_569_);
v_flags_570_ = lean_ctor_get(v___x_566_, 1);
lean_inc_ref(v_flags_570_);
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = lean_string_utf8_byte_size(v_name_569_);
lean_dec_ref(v_name_569_);
v___x_573_ = lean_nat_dec_eq(v___x_572_, v___x_571_);
if (v___x_573_ == 0)
{
lean_dec_ref(v_flags_570_);
goto v___jp_567_;
}
else
{
uint8_t v_cont_574_; 
v_cont_574_ = lean_nat_dec_eq(v___x_554_, v___x_571_);
if (v_cont_574_ == 0)
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = lean_array_get_size(v_flags_570_);
lean_dec_ref(v_flags_570_);
v___x_576_ = lean_nat_dec_eq(v___x_575_, v___x_571_);
if (v___x_576_ == 0)
{
goto v___jp_567_;
}
else
{
lean_dec_ref(v___x_566_);
v_a_560_ = v_b_558_;
goto v___jp_559_;
}
}
else
{
lean_dec_ref(v_flags_570_);
goto v___jp_567_;
}
}
v___jp_567_:
{
lean_object* v___x_568_; 
v___x_568_ = lean_array_push(v_b_558_, v___x_566_);
v_a_560_ = v___x_568_;
goto v___jp_559_;
}
}
v___jp_559_:
{
size_t v___x_561_; size_t v___x_562_; 
v___x_561_ = ((size_t)1ULL);
v___x_562_ = lean_usize_add(v_i_557_, v___x_561_);
v_i_557_ = v___x_562_;
v_b_558_ = v_a_560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5___boxed(lean_object* v___x_577_, lean_object* v_as_578_, lean_object* v_sz_579_, lean_object* v_i_580_, lean_object* v_b_581_){
_start:
{
size_t v_sz_boxed_582_; size_t v_i_boxed_583_; lean_object* v_res_584_; 
v_sz_boxed_582_ = lean_unbox_usize(v_sz_579_);
lean_dec(v_sz_579_);
v_i_boxed_583_ = lean_unbox_usize(v_i_580_);
lean_dec(v_i_580_);
v_res_584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_577_, v_as_578_, v_sz_boxed_582_, v_i_boxed_583_, v_b_581_);
lean_dec_ref(v_as_578_);
lean_dec(v___x_577_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(lean_object* v___x_585_, lean_object* v_b_586_){
_start:
{
lean_object* v_snd_587_; lean_object* v_fst_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_647_; 
v_snd_587_ = lean_ctor_get(v_b_586_, 1);
v_fst_588_ = lean_ctor_get(v_b_586_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_b_586_);
if (v_isSharedCheck_647_ == 0)
{
v___x_590_ = v_b_586_;
v_isShared_591_ = v_isSharedCheck_647_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_snd_587_);
lean_inc(v_fst_588_);
lean_dec(v_b_586_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_647_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_646_; 
v_fst_592_ = lean_ctor_get(v_snd_587_, 0);
v_snd_593_ = lean_ctor_get(v_snd_587_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v_snd_587_);
if (v_isSharedCheck_646_ == 0)
{
v___x_595_ = v_snd_587_;
v_isShared_596_ = v_isSharedCheck_646_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_snd_593_);
lean_inc(v_fst_592_);
lean_dec(v_snd_587_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_646_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
uint8_t v___x_604_; 
v___x_604_ = lean_unbox(v_snd_593_);
if (v___x_604_ == 0)
{
goto v___jp_597_;
}
else
{
lean_object* v___x_605_; uint8_t v_cont_606_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_605_ = lean_unsigned_to_nat(0u);
v_cont_606_ = lean_nat_dec_eq(v___x_585_, v___x_605_);
v___x_644_ = lean_array_get_size(v_fst_588_);
v___x_645_ = lean_nat_dec_eq(v___x_644_, v___x_605_);
if (v___x_645_ == 0)
{
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
goto v___jp_607_;
}
else
{
if (v_cont_606_ == 0)
{
goto v___jp_597_;
}
else
{
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
goto v___jp_607_;
}
}
v___jp_607_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v_last_612_; lean_object* v___x_613_; 
v___x_608_ = l_Lean_instInhabitedNamePart_default;
v___x_609_ = lean_array_get_size(v_fst_588_);
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = lean_nat_sub(v___x_609_, v___x_610_);
v_last_612_ = lean_array_get_borrowed(v___x_608_, v_fst_588_, v___x_611_);
lean_dec(v___x_611_);
lean_inc(v_last_612_);
v___x_613_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v_last_612_);
if (lean_obj_tag(v___x_613_) == 0)
{
if (lean_obj_tag(v_last_612_) == 1)
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(2u);
v___x_615_ = lean_nat_dec_le(v___x_614_, v___x_609_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
lean_dec(v_snd_593_);
v___x_616_ = lean_box(v_cont_606_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v_fst_592_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v_fst_588_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v_b_586_ = v___x_618_;
goto _start;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = lean_nat_sub(v___x_609_, v___x_614_);
v___x_621_ = lean_array_get_borrowed(v___x_608_, v_fst_588_, v___x_620_);
lean_dec(v___x_620_);
lean_inc(v___x_621_);
v___x_622_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_matchSuffix(v___x_621_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v_snd_593_);
v___x_623_ = lean_box(v_cont_606_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v_fst_592_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_fst_588_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v_b_586_ = v___x_625_;
goto _start;
}
else
{
lean_object* v_val_627_; lean_object* v_flags_628_; lean_object* v___x_629_; lean_object* v_parts_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_val_627_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_val_627_);
lean_dec_ref(v___x_622_);
v_flags_628_ = lean_array_push(v_fst_592_, v_val_627_);
v___x_629_ = lean_array_pop(v_fst_588_);
v_parts_630_ = lean_array_pop(v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v_flags_628_);
lean_ctor_set(v___x_631_, 1, v_snd_593_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v_parts_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v_b_586_ = v___x_632_;
goto _start;
}
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v_snd_593_);
v___x_634_ = lean_box(v_cont_606_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v_fst_592_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v_fst_588_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v_b_586_ = v___x_636_;
goto _start;
}
}
else
{
lean_object* v_val_638_; lean_object* v_flags_639_; lean_object* v_parts_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_val_638_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_val_638_);
lean_dec_ref(v___x_613_);
v_flags_639_ = lean_array_push(v_fst_592_, v_val_638_);
v_parts_640_ = lean_array_pop(v_fst_588_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v_flags_639_);
lean_ctor_set(v___x_641_, 1, v_snd_593_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v_parts_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v_b_586_ = v___x_642_;
goto _start;
}
}
}
v___jp_597_:
{
lean_object* v___x_599_; 
if (v_isShared_596_ == 0)
{
v___x_599_ = v___x_595_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_fst_592_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_snd_593_);
v___x_599_ = v_reuseFailAlloc_603_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_601_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_599_);
v___x_601_ = v___x_590_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_fst_588_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0___boxed(lean_object* v___x_648_, lean_object* v_b_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(v___x_648_, v_b_649_);
lean_dec(v___x_648_);
return v_res_650_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0));
v___x_653_ = lean_string_utf8_byte_size(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(lean_object* v___x_654_, lean_object* v_range_655_, lean_object* v_b_656_, lean_object* v_i_657_){
_start:
{
lean_object* v_stop_658_; lean_object* v_step_659_; lean_object* v_a_661_; uint8_t v___x_664_; 
v_stop_658_ = lean_ctor_get(v_range_655_, 1);
v_step_659_ = lean_ctor_get(v_range_655_, 2);
v___x_664_ = lean_nat_dec_lt(v_i_657_, v_stop_658_);
if (v___x_664_ == 0)
{
lean_dec(v_i_657_);
lean_inc_ref(v_b_656_);
return v_b_656_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = l_Lean_instInhabitedNamePart_default;
v___x_666_ = lean_array_get_borrowed(v___x_665_, v_b_656_, v_i_657_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_s_667_; lean_object* v___x_668_; uint8_t v___y_670_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_s_667_ = lean_ctor_get(v___x_666_, 0);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_672_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__0));
v___x_673_ = lean_string_utf8_byte_size(v_s_667_);
v___x_674_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___closed__1);
v___x_675_ = lean_nat_dec_le(v___x_674_, v___x_673_);
if (v___x_675_ == 0)
{
uint8_t v_cont_676_; 
v_cont_676_ = lean_nat_dec_eq(v___x_654_, v___x_668_);
v___y_670_ = v_cont_676_;
goto v___jp_669_;
}
else
{
uint8_t v___x_677_; 
v___x_677_ = lean_string_memcmp(v_s_667_, v___x_672_, v___x_668_, v___x_668_, v___x_674_);
v___y_670_ = v___x_677_;
goto v___jp_669_;
}
v___jp_669_:
{
if (v___y_670_ == 0)
{
v_a_661_ = v_b_656_;
goto v___jp_660_;
}
else
{
lean_object* v___x_671_; 
v___x_671_ = l_Array_extract___redArg(v_b_656_, v___x_668_, v_i_657_);
return v___x_671_;
}
}
}
else
{
v_a_661_ = v_b_656_;
goto v___jp_660_;
}
}
v___jp_660_:
{
lean_object* v___x_662_; 
v___x_662_ = lean_nat_add(v_i_657_, v_step_659_);
lean_dec(v_i_657_);
v_b_656_ = v_a_661_;
v_i_657_ = v___x_662_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg___boxed(lean_object* v___x_678_, lean_object* v_range_679_, lean_object* v_b_680_, lean_object* v_i_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_678_, v_range_679_, v_b_680_, v_i_681_);
lean_dec_ref(v_b_680_);
lean_dec_ref(v_range_679_);
lean_dec(v___x_678_);
return v_res_682_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0));
v___x_687_ = lean_string_utf8_byte_size(v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(lean_object* v___x_690_, lean_object* v___x_691_, lean_object* v_range_692_, lean_object* v_b_693_, lean_object* v_i_694_){
_start:
{
lean_object* v_stop_695_; lean_object* v_step_696_; lean_object* v_a_698_; uint8_t v___x_701_; 
v_stop_695_ = lean_ctor_get(v_range_692_, 1);
v_step_696_ = lean_ctor_get(v_range_692_, 2);
v___x_701_ = lean_nat_dec_lt(v_i_694_, v_stop_695_);
if (v___x_701_ == 0)
{
lean_dec(v_i_694_);
return v_b_693_;
}
else
{
lean_object* v_snd_702_; lean_object* v_snd_703_; lean_object* v_fst_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_819_; 
v_snd_702_ = lean_ctor_get(v_b_693_, 1);
lean_inc(v_snd_702_);
v_snd_703_ = lean_ctor_get(v_snd_702_, 1);
lean_inc(v_snd_703_);
v_fst_704_ = lean_ctor_get(v_b_693_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_b_693_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_b_693_, 1);
lean_dec(v_unused_820_);
v___x_706_ = v_b_693_;
v_isShared_707_ = v_isSharedCheck_819_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_fst_704_);
lean_dec(v_b_693_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_819_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_fst_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_817_; 
v_fst_708_ = lean_ctor_get(v_snd_702_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v_snd_702_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_snd_702_, 1);
lean_dec(v_unused_818_);
v___x_710_ = v_snd_702_;
v_isShared_711_ = v_isSharedCheck_817_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_fst_708_);
lean_dec(v_snd_702_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_817_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v_fst_712_; lean_object* v_snd_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_816_; 
v_fst_712_ = lean_ctor_get(v_snd_703_, 0);
v_snd_713_ = lean_ctor_get(v_snd_703_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v_snd_703_);
if (v_isSharedCheck_816_ == 0)
{
v___x_715_ = v_snd_703_;
v_isShared_716_ = v_isSharedCheck_816_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_snd_713_);
lean_inc(v_fst_712_);
lean_dec(v_snd_703_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_816_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; uint8_t v_cont_718_; uint8_t v___x_719_; 
v___x_717_ = lean_unsigned_to_nat(0u);
v_cont_718_ = lean_nat_dec_eq(v___x_691_, v___x_717_);
v___x_719_ = lean_unbox(v_snd_713_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_720_ = l_Lean_instInhabitedNamePart_default;
v___x_721_ = lean_array_get_borrowed(v___x_720_, v___x_690_, v_i_694_);
v___x_722_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg___closed__1));
v___x_723_ = l_Lean_instBEqNamePart_beq(v___x_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; uint8_t v___y_726_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v_cont_777_; lean_object* v_entries_779_; lean_object* v_currentCtx_780_; 
v___x_724_ = lean_box(0);
v___x_775_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__0));
v___x_776_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__1));
v_cont_777_ = l_Lean_instBEqNamePart_beq(v___x_721_, v___x_776_);
if (v_cont_777_ == 0)
{
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_s_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_s_785_ = lean_ctor_get(v___x_721_, 0);
v___x_786_ = lean_string_utf8_byte_size(v_s_785_);
v___x_787_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__2);
v___x_788_ = lean_nat_dec_le(v___x_787_, v___x_786_);
if (v___x_788_ == 0)
{
v___y_726_ = v_cont_777_;
goto v___jp_725_;
}
else
{
uint8_t v___x_789_; 
v___x_789_ = lean_string_memcmp(v_s_785_, v___x_775_, v___x_717_, v___x_717_, v___x_787_);
v___y_726_ = v___x_789_;
goto v___jp_725_;
}
}
else
{
v___y_726_ = v_cont_718_;
goto v___jp_725_;
}
}
else
{
lean_del_object(v___x_715_);
lean_dec(v_snd_713_);
lean_del_object(v___x_710_);
lean_del_object(v___x_706_);
if (lean_obj_tag(v_fst_708_) == 1)
{
lean_object* v_val_790_; lean_object* v___x_791_; 
v_val_790_ = lean_ctor_get(v_fst_708_, 0);
lean_inc(v_val_790_);
lean_dec_ref(v_fst_708_);
v___x_791_ = lean_array_push(v_fst_704_, v_val_790_);
v_entries_779_ = v___x_791_;
v_currentCtx_780_ = v___x_724_;
goto v___jp_778_;
}
else
{
v_entries_779_ = v_fst_704_;
v_currentCtx_780_ = v_fst_708_;
goto v___jp_778_;
}
}
v___jp_725_:
{
if (v___y_726_ == 0)
{
if (lean_obj_tag(v_fst_708_) == 0)
{
lean_object* v___x_727_; lean_object* v___x_729_; 
lean_inc(v___x_721_);
v___x_727_ = lean_array_push(v_fst_712_, v___x_721_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_727_);
v___x_729_ = v___x_715_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_snd_713_);
v___x_729_ = v_reuseFailAlloc_736_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_731_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_729_);
v___x_731_ = v___x_710_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_fst_708_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_729_);
v___x_731_ = v_reuseFailAlloc_735_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_733_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_731_);
v___x_733_ = v___x_706_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_fst_704_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
v_a_698_ = v___x_733_;
goto v___jp_697_;
}
}
}
}
else
{
lean_object* v_val_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_754_; 
v_val_737_ = lean_ctor_get(v_fst_708_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v_fst_708_);
if (v_isSharedCheck_754_ == 0)
{
v___x_739_ = v_fst_708_;
v_isShared_740_ = v_isSharedCheck_754_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_val_737_);
lean_dec(v_fst_708_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_754_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
lean_inc(v___x_721_);
v___x_741_ = lean_array_push(v_val_737_, v___x_721_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_741_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_753_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_716_ == 0)
{
v___x_745_ = v___x_715_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_fst_712_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_snd_713_);
v___x_745_ = v_reuseFailAlloc_752_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_747_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_745_);
lean_ctor_set(v___x_710_, 0, v___x_743_);
v___x_747_ = v___x_710_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_745_);
v___x_747_ = v_reuseFailAlloc_751_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_749_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_747_);
v___x_749_ = v___x_706_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_fst_704_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
v_a_698_ = v___x_749_;
goto v___jp_697_;
}
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_fst_708_) == 1)
{
lean_object* v_val_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v_val_755_ = lean_ctor_get(v_fst_708_, 0);
lean_inc(v_val_755_);
lean_dec_ref(v_fst_708_);
v___x_756_ = lean_array_push(v_fst_704_, v_val_755_);
if (v_isShared_716_ == 0)
{
v___x_758_ = v___x_715_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_fst_712_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_snd_713_);
v___x_758_ = v_reuseFailAlloc_765_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_760_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_758_);
lean_ctor_set(v___x_710_, 0, v___x_724_);
v___x_760_ = v___x_710_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_758_);
v___x_760_ = v_reuseFailAlloc_764_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_762_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_760_);
lean_ctor_set(v___x_706_, 0, v___x_756_);
v___x_762_ = v___x_706_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
v_a_698_ = v___x_762_;
goto v___jp_697_;
}
}
}
}
else
{
lean_object* v___x_767_; 
if (v_isShared_716_ == 0)
{
v___x_767_ = v___x_715_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_fst_712_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_snd_713_);
v___x_767_ = v_reuseFailAlloc_774_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_767_);
v___x_769_ = v___x_710_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_fst_708_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_767_);
v___x_769_ = v_reuseFailAlloc_773_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_771_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_769_);
v___x_771_ = v___x_706_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_fst_704_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
v_a_698_ = v___x_771_;
goto v___jp_697_;
}
}
}
}
}
}
v___jp_778_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_781_ = lean_box(v_cont_777_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_fst_712_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v_currentCtx_780_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_entries_779_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v_a_698_ = v___x_784_;
goto v___jp_697_;
}
}
else
{
lean_object* v_entries_793_; 
if (lean_obj_tag(v_fst_708_) == 1)
{
lean_object* v_val_804_; lean_object* v___x_805_; 
v_val_804_ = lean_ctor_get(v_fst_708_, 0);
lean_inc(v_val_804_);
lean_dec_ref(v_fst_708_);
v___x_805_ = lean_array_push(v_fst_704_, v_val_804_);
v_entries_793_ = v___x_805_;
goto v___jp_792_;
}
else
{
lean_dec(v_fst_708_);
v_entries_793_ = v_fst_704_;
goto v___jp_792_;
}
v___jp_792_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_794_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___closed__3));
if (v_isShared_716_ == 0)
{
v___x_796_ = v___x_715_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_fst_712_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_snd_713_);
v___x_796_ = v_reuseFailAlloc_803_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_798_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_796_);
lean_ctor_set(v___x_710_, 0, v___x_794_);
v___x_798_ = v___x_710_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___x_796_);
v___x_798_ = v_reuseFailAlloc_802_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_800_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_798_);
lean_ctor_set(v___x_706_, 0, v_entries_793_);
v___x_800_ = v___x_706_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_entries_793_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
v_a_698_ = v___x_800_;
goto v___jp_697_;
}
}
}
}
}
}
else
{
lean_object* v___x_806_; lean_object* v___x_808_; 
lean_dec(v_snd_713_);
v___x_806_ = lean_box(v_cont_718_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v___x_806_);
v___x_808_ = v___x_715_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_fst_712_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_806_);
v___x_808_ = v_reuseFailAlloc_815_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_808_);
v___x_810_ = v___x_710_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_fst_708_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_808_);
v___x_810_ = v_reuseFailAlloc_814_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_812_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_810_);
v___x_812_ = v___x_706_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_fst_704_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v_a_698_ = v___x_812_;
goto v___jp_697_;
}
}
}
}
}
}
}
}
v___jp_697_:
{
lean_object* v___x_699_; 
v___x_699_ = lean_nat_add(v_i_694_, v_step_696_);
lean_dec(v_i_694_);
v_b_693_ = v_a_698_;
v_i_694_ = v___x_699_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg___boxed(lean_object* v___x_821_, lean_object* v___x_822_, lean_object* v_range_823_, lean_object* v_b_824_, lean_object* v_i_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_821_, v___x_822_, v_range_823_, v_b_824_, v_i_825_);
lean_dec_ref(v_range_823_);
lean_dec(v___x_822_);
lean_dec_ref(v___x_821_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(lean_object* v___x_832_, lean_object* v_as_833_, size_t v_sz_834_, size_t v_i_835_, lean_object* v_b_836_){
_start:
{
lean_object* v_a_838_; lean_object* v___y_843_; lean_object* v___y_844_; uint8_t v___x_856_; 
v___x_856_ = lean_usize_dec_lt(v_i_835_, v_sz_834_);
if (v___x_856_ == 0)
{
return v_b_836_;
}
else
{
lean_object* v_a_857_; lean_object* v_name_858_; lean_object* v___x_859_; uint8_t v_cont_860_; lean_object* v___y_862_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_a_857_ = lean_array_uget_borrowed(v_as_833_, v_i_835_);
v_name_858_ = lean_ctor_get(v_a_857_, 0);
v___x_859_ = lean_unsigned_to_nat(0u);
v_cont_860_ = lean_nat_dec_eq(v___x_832_, v___x_859_);
v___x_869_ = lean_string_utf8_byte_size(v_name_858_);
v___x_870_ = lean_nat_dec_eq(v___x_869_, v___x_859_);
if (v___x_870_ == 0)
{
lean_inc_ref(v_name_858_);
v___y_862_ = v_name_858_;
goto v___jp_861_;
}
else
{
lean_object* v___x_871_; 
v___x_871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_862_ = v___x_871_;
goto v___jp_861_;
}
v___jp_861_:
{
lean_object* v_flags_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v_flags_863_ = lean_ctor_get(v_a_857_, 1);
v___x_864_ = lean_array_get_size(v_flags_863_);
v___x_865_ = lean_nat_dec_eq(v___x_864_, v___x_859_);
if (v___x_865_ == 0)
{
lean_inc_ref(v_flags_863_);
v___y_843_ = v_flags_863_;
v___y_844_ = v___y_862_;
goto v___jp_842_;
}
else
{
if (v_cont_860_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_867_ = lean_string_append(v_b_836_, v___x_866_);
v___x_868_ = lean_string_append(v___x_867_, v___y_862_);
lean_dec_ref(v___y_862_);
v_a_838_ = v___x_868_;
goto v___jp_837_;
}
else
{
lean_inc_ref(v_flags_863_);
v___y_843_ = v_flags_863_;
v___y_844_ = v___y_862_;
goto v___jp_842_;
}
}
}
}
v___jp_837_:
{
size_t v___x_839_; size_t v___x_840_; 
v___x_839_ = ((size_t)1ULL);
v___x_840_ = lean_usize_add(v_i_835_, v___x_839_);
v_i_835_ = v___x_840_;
v_b_836_ = v_a_838_;
goto _start;
}
v___jp_842_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__0));
v___x_846_ = lean_string_append(v_b_836_, v___x_845_);
v___x_847_ = lean_string_append(v___x_846_, v___y_844_);
lean_dec_ref(v___y_844_);
v___x_848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__1));
v___x_849_ = lean_string_append(v___x_847_, v___x_848_);
v___x_850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
v___x_851_ = lean_array_to_list(v___y_843_);
v___x_852_ = l_String_intercalate(v___x_850_, v___x_851_);
v___x_853_ = lean_string_append(v___x_849_, v___x_852_);
lean_dec_ref(v___x_852_);
v___x_854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_855_ = lean_string_append(v___x_853_, v___x_854_);
v_a_838_ = v___x_855_;
goto v___jp_837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___boxed(lean_object* v___x_872_, lean_object* v_as_873_, lean_object* v_sz_874_, lean_object* v_i_875_, lean_object* v_b_876_){
_start:
{
size_t v_sz_boxed_877_; size_t v_i_boxed_878_; lean_object* v_res_879_; 
v_sz_boxed_877_ = lean_unbox_usize(v_sz_874_);
lean_dec(v_sz_874_);
v_i_boxed_878_ = lean_unbox_usize(v_i_875_);
lean_dec(v_i_875_);
v_res_879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v___x_872_, v_as_873_, v_sz_boxed_877_, v_i_boxed_878_, v_b_876_);
lean_dec_ref(v_as_873_);
lean_dec(v___x_872_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(lean_object* v_components_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___y_891_; lean_object* v_result_892_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___x_908_; uint8_t v_cont_909_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_917_; lean_object* v_parts_918_; lean_object* v_specEntries_919_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v_entries_929_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; 
v___x_889_ = lean_array_get_size(v_components_888_);
v___x_908_ = lean_unsigned_to_nat(0u);
v_cont_909_ = lean_nat_dec_eq(v___x_889_, v___x_908_);
if (v_cont_909_ == 0)
{
lean_object* v___x_942_; lean_object* v_fst_943_; lean_object* v_snd_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_998_; 
v___x_942_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripPrivate(v_components_888_, v___x_908_, v___x_889_);
v_fst_943_ = lean_ctor_get(v___x_942_, 0);
v_snd_944_ = lean_ctor_get(v___x_942_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_998_ == 0)
{
v___x_946_ = v___x_942_;
v_isShared_947_ = v_isSharedCheck_998_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_snd_944_);
lean_inc(v_fst_943_);
lean_dec(v___x_942_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_998_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_parts_948_; lean_object* v_flags_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v_parts_948_ = l_Array_extract___redArg(v_components_888_, v_fst_943_, v___x_889_);
v_flags_949_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__1));
v___x_950_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__2));
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v___x_950_);
lean_ctor_set(v___x_946_, 0, v_parts_948_);
v___x_952_ = v___x_946_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_parts_948_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_950_);
v___x_952_ = v_reuseFailAlloc_997_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; lean_object* v_fst_954_; lean_object* v_snd_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_996_; 
v___x_953_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__0(v___x_889_, v___x_952_);
v_fst_954_ = lean_ctor_get(v___x_953_, 0);
v_snd_955_ = lean_ctor_get(v___x_953_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_996_ == 0)
{
v___x_957_ = v___x_953_;
v_isShared_958_ = v_isSharedCheck_996_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_snd_955_);
lean_inc(v_fst_954_);
lean_dec(v___x_953_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_996_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_flags_960_; uint8_t v___x_991_; 
v___x_991_ = lean_unbox(v_snd_944_);
lean_dec(v_snd_944_);
if (v___x_991_ == 0)
{
lean_object* v_fst_992_; 
v_fst_992_ = lean_ctor_get(v_snd_955_, 0);
lean_inc(v_fst_992_);
lean_dec(v_snd_955_);
v_flags_960_ = v_fst_992_;
goto v___jp_959_;
}
else
{
lean_object* v_fst_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_fst_993_ = lean_ctor_get(v_snd_955_, 0);
lean_inc(v_fst_993_);
lean_dec(v_snd_955_);
v___x_994_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__3));
v___x_995_ = lean_array_push(v_fst_993_, v___x_994_);
v_flags_960_ = v___x_995_;
goto v___jp_959_;
}
v___jp_959_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_961_ = lean_array_get_size(v_fst_954_);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_963_, 0, v___x_908_);
lean_ctor_set(v___x_963_, 1, v___x_961_);
lean_ctor_set(v___x_963_, 2, v___x_962_);
v___x_964_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_889_, v___x_963_, v_fst_954_, v___x_908_);
lean_dec(v_fst_954_);
lean_dec_ref(v___x_963_);
v___x_965_ = lean_box(0);
v___x_966_ = lean_array_get_size(v___x_964_);
v___x_967_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_967_, 0, v___x_908_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
lean_ctor_set(v___x_967_, 2, v___x_962_);
v___x_968_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_964_, v___x_967_, v___x_965_, v___x_908_);
lean_dec_ref(v___x_967_);
if (lean_obj_tag(v___x_968_) == 1)
{
lean_object* v_val_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v_val_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_val_969_);
lean_dec_ref(v___x_968_);
lean_inc(v_val_969_);
v___x_970_ = l_Array_extract___redArg(v___x_964_, v___x_908_, v_val_969_);
v___x_971_ = l_Array_extract___redArg(v___x_964_, v_val_969_, v___x_966_);
lean_dec_ref(v___x_964_);
v___x_972_ = lean_array_get_size(v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_973_, 0, v___x_908_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
lean_ctor_set(v___x_973_, 2, v___x_962_);
v___x_974_ = lean_box(v_cont_909_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___x_974_);
lean_ctor_set(v___x_957_, 0, v_flags_949_);
v___x_976_ = v___x_957_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_flags_949_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v___x_974_);
v___x_976_ = v_reuseFailAlloc_990_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_snd_980_; lean_object* v_snd_981_; lean_object* v_fst_982_; 
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_965_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v_flags_949_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_971_, v___x_889_, v___x_973_, v___x_978_, v___x_908_);
lean_dec_ref(v___x_973_);
lean_dec_ref(v___x_971_);
v_snd_980_ = lean_ctor_get(v___x_979_, 1);
lean_inc(v_snd_980_);
v_snd_981_ = lean_ctor_get(v_snd_980_, 1);
lean_inc(v_snd_981_);
v_fst_982_ = lean_ctor_get(v_snd_980_, 0);
lean_inc(v_fst_982_);
lean_dec(v_snd_980_);
if (lean_obj_tag(v_fst_982_) == 1)
{
lean_object* v_fst_983_; lean_object* v_fst_984_; lean_object* v_val_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_fst_983_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_fst_983_);
lean_dec_ref(v___x_979_);
v_fst_984_ = lean_ctor_get(v_snd_981_, 0);
lean_inc(v_fst_984_);
lean_dec(v_snd_981_);
v_val_985_ = lean_ctor_get(v_fst_982_, 0);
lean_inc(v_val_985_);
lean_dec_ref(v_fst_982_);
v___x_986_ = lean_array_get_size(v_val_985_);
v___x_987_ = lean_nat_dec_eq(v___x_986_, v___x_908_);
if (v___x_987_ == 0)
{
v___y_935_ = v_flags_960_;
v___y_936_ = v_flags_949_;
v___y_937_ = v_fst_983_;
v___y_938_ = v___x_970_;
v___y_939_ = v_fst_984_;
v___y_940_ = v_val_985_;
goto v___jp_934_;
}
else
{
if (v_cont_909_ == 0)
{
lean_dec(v_val_985_);
v___y_925_ = v_flags_960_;
v___y_926_ = v_flags_949_;
v___y_927_ = v___x_970_;
v___y_928_ = v_fst_984_;
v_entries_929_ = v_fst_983_;
goto v___jp_924_;
}
else
{
v___y_935_ = v_flags_960_;
v___y_936_ = v_flags_949_;
v___y_937_ = v_fst_983_;
v___y_938_ = v___x_970_;
v___y_939_ = v_fst_984_;
v___y_940_ = v_val_985_;
goto v___jp_934_;
}
}
}
else
{
lean_object* v_fst_988_; lean_object* v_fst_989_; 
lean_dec(v_fst_982_);
v_fst_988_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_fst_988_);
lean_dec_ref(v___x_979_);
v_fst_989_ = lean_ctor_get(v_snd_981_, 0);
lean_inc(v_fst_989_);
lean_dec(v_snd_981_);
v___y_925_ = v_flags_960_;
v___y_926_ = v_flags_949_;
v___y_927_ = v___x_970_;
v___y_928_ = v_fst_989_;
v_entries_929_ = v_fst_988_;
goto v___jp_924_;
}
}
}
else
{
lean_dec(v___x_968_);
lean_del_object(v___x_957_);
v___y_917_ = v_flags_960_;
v_parts_918_ = v___x_964_;
v_specEntries_919_ = v_flags_949_;
goto v___jp_916_;
}
}
}
}
}
}
else
{
lean_object* v___x_999_; 
v___x_999_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_999_;
}
v___jp_890_:
{
size_t v_sz_893_; size_t v___x_894_; lean_object* v___x_895_; 
v_sz_893_ = lean_array_size(v___y_891_);
v___x_894_ = ((size_t)0ULL);
v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1(v___x_889_, v___y_891_, v_sz_893_, v___x_894_, v_result_892_);
lean_dec_ref(v___y_891_);
return v___x_895_;
}
v___jp_896_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_900_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___closed__0));
v___x_901_ = lean_string_append(v___y_899_, v___x_900_);
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__2));
v___x_903_ = lean_array_to_list(v___y_897_);
v___x_904_ = l_String_intercalate(v___x_902_, v___x_903_);
v___x_905_ = lean_string_append(v___x_901_, v___x_904_);
lean_dec_ref(v___x_904_);
v___x_906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__3));
v___x_907_ = lean_string_append(v___x_905_, v___x_906_);
v___y_891_ = v___y_898_;
v_result_892_ = v___x_907_;
goto v___jp_890_;
}
v___jp_910_:
{
lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_914_ = lean_array_get_size(v___y_911_);
v___x_915_ = lean_nat_dec_eq(v___x_914_, v___x_908_);
if (v___x_915_ == 0)
{
v___y_897_ = v___y_911_;
v___y_898_ = v___y_912_;
v___y_899_ = v___y_913_;
goto v___jp_896_;
}
else
{
if (v_cont_909_ == 0)
{
lean_dec_ref(v___y_911_);
v___y_891_ = v___y_912_;
v_result_892_ = v___y_913_;
goto v___jp_890_;
}
else
{
v___y_897_ = v___y_911_;
v___y_898_ = v___y_912_;
v___y_899_ = v___y_913_;
goto v___jp_896_;
}
}
}
v___jp_916_:
{
lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_920_ = lean_array_get_size(v_parts_918_);
v___x_921_ = lean_nat_dec_eq(v___x_920_, v___x_908_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
v___x_922_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts(v_parts_918_);
lean_dec_ref(v_parts_918_);
v___y_911_ = v___y_917_;
v___y_912_ = v_specEntries_919_;
v___y_913_ = v___x_922_;
goto v___jp_910_;
}
else
{
lean_object* v___x_923_; 
lean_dec_ref(v_parts_918_);
v___x_923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__1___closed__4));
v___y_911_ = v___y_917_;
v___y_912_ = v_specEntries_919_;
v___y_913_ = v___x_923_;
goto v___jp_910_;
}
}
v___jp_924_:
{
size_t v_sz_930_; size_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_sz_930_ = lean_array_size(v_entries_929_);
v___x_931_ = ((size_t)0ULL);
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__5(v___x_889_, v_entries_929_, v_sz_930_, v___x_931_, v___y_926_);
lean_dec_ref(v_entries_929_);
v___x_933_ = l_Array_append___redArg(v___y_927_, v___y_928_);
lean_dec(v___y_928_);
v___y_917_ = v___y_925_;
v_parts_918_ = v___x_933_;
v_specEntries_919_ = v___x_932_;
goto v___jp_916_;
}
v___jp_934_:
{
lean_object* v___x_941_; 
v___x_941_ = lean_array_push(v___y_937_, v___y_940_);
v___y_925_ = v___y_935_;
v___y_926_ = v___y_936_;
v___y_927_ = v___y_938_;
v___y_928_ = v___y_939_;
v_entries_929_ = v___x_941_;
goto v___jp_924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts___boxed(lean_object* v_components_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v_components_1000_);
lean_dec_ref(v_components_1000_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(lean_object* v___x_1002_, lean_object* v_range_1003_, lean_object* v_b_1004_, lean_object* v_i_1005_, lean_object* v_hs_1006_, lean_object* v_hl_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___redArg(v___x_1002_, v_range_1003_, v_b_1004_, v_i_1005_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2___boxed(lean_object* v___x_1009_, lean_object* v_range_1010_, lean_object* v_b_1011_, lean_object* v_i_1012_, lean_object* v_hs_1013_, lean_object* v_hl_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__2(v___x_1009_, v_range_1010_, v_b_1011_, v_i_1012_, v_hs_1013_, v_hl_1014_);
lean_dec_ref(v_b_1011_);
lean_dec_ref(v_range_1010_);
lean_dec(v___x_1009_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(lean_object* v___x_1016_, lean_object* v_range_1017_, lean_object* v_b_1018_, lean_object* v_i_1019_, lean_object* v_hs_1020_, lean_object* v_hl_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___redArg(v___x_1016_, v_range_1017_, v_b_1018_, v_i_1019_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3___boxed(lean_object* v___x_1023_, lean_object* v_range_1024_, lean_object* v_b_1025_, lean_object* v_i_1026_, lean_object* v_hs_1027_, lean_object* v_hl_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__3(v___x_1023_, v_range_1024_, v_b_1025_, v_i_1026_, v_hs_1027_, v_hl_1028_);
lean_dec(v_b_1025_);
lean_dec_ref(v_range_1024_);
lean_dec_ref(v___x_1023_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(lean_object* v___x_1030_, lean_object* v___x_1031_, lean_object* v_range_1032_, lean_object* v_b_1033_, lean_object* v_i_1034_, lean_object* v_hs_1035_, lean_object* v_hl_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___redArg(v___x_1030_, v___x_1031_, v_range_1032_, v_b_1033_, v_i_1034_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4___boxed(lean_object* v___x_1038_, lean_object* v___x_1039_, lean_object* v_range_1040_, lean_object* v_b_1041_, lean_object* v_i_1042_, lean_object* v_hs_1043_, lean_object* v_hl_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts_spec__4(v___x_1038_, v___x_1039_, v_range_1040_, v_b_1041_, v_i_1042_, v_hs_1043_, v_hl_1044_);
lean_dec_ref(v_range_1040_);
lean_dec(v___x_1039_);
lean_dec_ref(v___x_1038_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(lean_object* v_body_1046_){
_start:
{
lean_object* v_name_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_name_1047_ = l_Lean_Name_demangle(v_body_1046_);
v___x_1048_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_nameToNameParts(v_name_1047_);
lean_dec(v_name_1047_);
v___x_1049_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_postprocessNameParts(v___x_1048_);
lean_dec_ref(v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody___boxed(lean_object* v_body_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_body_1050_);
lean_dec_ref(v_body_1050_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(lean_object* v_s_1055_, lean_object* v___x_1056_, lean_object* v_a_1057_, lean_object* v_b_1058_){
_start:
{
lean_object* v_startInclusive_1059_; lean_object* v_endExclusive_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_startInclusive_1059_ = lean_ctor_get(v___x_1056_, 1);
v_endExclusive_1060_ = lean_ctor_get(v___x_1056_, 2);
v___x_1061_ = lean_nat_sub(v_endExclusive_1060_, v_startInclusive_1059_);
v___x_1062_ = lean_nat_dec_eq(v_a_1057_, v___x_1061_);
lean_dec(v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___y_1081_; uint8_t v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1087_; uint8_t v___y_1088_; lean_object* v___y_1089_; uint8_t v___y_1090_; uint8_t v___y_1093_; uint32_t v___x_1104_; uint32_t v___x_1105_; uint8_t v___x_1106_; 
lean_dec_ref(v_b_1058_);
v___x_1063_ = lean_box(0);
v___x_1078_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1079_ = lean_string_utf8_next_fast(v_s_1055_, v_a_1057_);
v___x_1104_ = lean_string_utf8_get_fast(v_s_1055_, v_a_1057_);
v___x_1105_ = 95;
v___x_1106_ = lean_uint32_dec_eq(v___x_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
v___y_1093_ = v___x_1106_;
goto v___jp_1092_;
}
else
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_nat_dec_eq(v_a_1057_, v___x_1107_);
if (v___x_1108_ == 0)
{
v___y_1093_ = v___x_1106_;
goto v___jp_1092_;
}
else
{
lean_dec(v_a_1057_);
v_a_1057_ = v___x_1079_;
v_b_1058_ = v___x_1078_;
goto _start;
}
}
v___jp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1067_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v___y_1065_);
lean_dec_ref(v___y_1065_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v___y_1066_);
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1063_);
v___x_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
return v___x_1071_;
}
v___jp_1072_:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_Name_demangle(v___y_1074_);
if (lean_obj_tag(v___x_1075_) == 1)
{
lean_object* v_pre_1076_; 
v_pre_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_pre_1076_);
if (lean_obj_tag(v_pre_1076_) == 0)
{
lean_object* v_str_1077_; 
lean_dec_ref(v___y_1074_);
v_str_1077_ = lean_ctor_get(v___x_1075_, 1);
lean_inc_ref(v_str_1077_);
lean_dec_ref(v___x_1075_);
v___y_1065_ = v___y_1073_;
v___y_1066_ = v_str_1077_;
goto v___jp_1064_;
}
else
{
lean_dec_ref(v___x_1075_);
lean_dec(v_pre_1076_);
v___y_1065_ = v___y_1073_;
v___y_1066_ = v___y_1074_;
goto v___jp_1064_;
}
}
else
{
lean_dec(v___x_1075_);
v___y_1065_ = v___y_1073_;
v___y_1066_ = v___y_1074_;
goto v___jp_1064_;
}
}
v___jp_1080_:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Name_demangle_x3f(v___y_1081_);
if (lean_obj_tag(v___x_1084_) == 0)
{
if (v___y_1082_ == 0)
{
lean_dec_ref(v___y_1083_);
lean_dec_ref(v___y_1081_);
v_a_1057_ = v___x_1079_;
v_b_1058_ = v___x_1078_;
goto _start;
}
else
{
v___y_1073_ = v___y_1081_;
v___y_1074_ = v___y_1083_;
goto v___jp_1072_;
}
}
else
{
lean_dec_ref(v___x_1084_);
v___y_1073_ = v___y_1081_;
v___y_1074_ = v___y_1083_;
goto v___jp_1072_;
}
}
v___jp_1086_:
{
if (v___y_1090_ == 0)
{
lean_dec_ref(v___y_1089_);
lean_dec_ref(v___y_1087_);
v_a_1057_ = v___x_1079_;
v_b_1058_ = v___x_1078_;
goto _start;
}
else
{
v___y_1081_ = v___y_1087_;
v___y_1082_ = v___y_1088_;
v___y_1083_ = v___y_1089_;
goto v___jp_1080_;
}
}
v___jp_1092_:
{
if (v___y_1093_ == 0)
{
lean_dec(v_a_1057_);
v_a_1057_ = v___x_1079_;
v_b_1058_ = v___x_1078_;
goto _start;
}
else
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = lean_string_utf8_byte_size(v_s_1055_);
v___x_1096_ = lean_nat_dec_eq(v___x_1079_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = lean_string_utf8_extract(v_s_1055_, v___x_1097_, v_a_1057_);
lean_dec(v_a_1057_);
v___x_1099_ = lean_string_utf8_extract(v_s_1055_, v___x_1079_, v___x_1095_);
v___x_1100_ = l_Lean_Name_demangle_x3f(v___x_1098_);
if (lean_obj_tag(v___x_1100_) == 1)
{
lean_object* v_val_1101_; 
v_val_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_val_1101_);
lean_dec_ref(v___x_1100_);
if (lean_obj_tag(v_val_1101_) == 1)
{
lean_object* v_pre_1102_; 
v_pre_1102_ = lean_ctor_get(v_val_1101_, 0);
lean_inc(v_pre_1102_);
lean_dec_ref(v_val_1101_);
if (lean_obj_tag(v_pre_1102_) == 0)
{
v___y_1081_ = v___x_1099_;
v___y_1082_ = v___x_1096_;
v___y_1083_ = v___x_1098_;
goto v___jp_1080_;
}
else
{
lean_dec(v_pre_1102_);
v___y_1087_ = v___x_1099_;
v___y_1088_ = v___x_1096_;
v___y_1089_ = v___x_1098_;
v___y_1090_ = v___x_1096_;
goto v___jp_1086_;
}
}
else
{
lean_dec(v_val_1101_);
v___y_1087_ = v___x_1099_;
v___y_1088_ = v___x_1096_;
v___y_1089_ = v___x_1098_;
v___y_1090_ = v___x_1096_;
goto v___jp_1086_;
}
}
else
{
lean_dec(v___x_1100_);
v___y_1087_ = v___x_1099_;
v___y_1088_ = v___x_1096_;
v___y_1089_ = v___x_1098_;
v___y_1090_ = v___x_1096_;
goto v___jp_1086_;
}
}
else
{
lean_dec(v_a_1057_);
v_a_1057_ = v___x_1079_;
v_b_1058_ = v___x_1078_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1110_; 
lean_dec(v_a_1057_);
v___x_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1110_, 0, v_b_1058_);
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___boxed(lean_object* v_s_1111_, lean_object* v___x_1112_, lean_object* v_a_1113_, lean_object* v_b_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1111_, v___x_1112_, v_a_1113_, v_b_1114_);
lean_dec_ref(v___x_1112_);
lean_dec_ref(v_s_1111_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(lean_object* v_s_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1117_ = lean_unsigned_to_nat(0u);
v___x_1118_ = lean_string_utf8_byte_size(v_s_1116_);
lean_inc_ref(v_s_1116_);
v___x_1119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1119_, 0, v_s_1116_);
lean_ctor_set(v___x_1119_, 1, v___x_1117_);
lean_ctor_set(v___x_1119_, 2, v___x_1118_);
v___x_1120_ = lean_box(0);
v___x_1121_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg___closed__0));
v___x_1122_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1116_, v___x_1119_, v___x_1117_, v___x_1121_);
lean_dec_ref(v___x_1119_);
lean_dec_ref(v_s_1116_);
if (lean_obj_tag(v___x_1122_) == 0)
{
return v___x_1120_;
}
else
{
lean_object* v_val_1123_; lean_object* v_fst_1124_; 
v_val_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_val_1123_);
lean_dec_ref(v___x_1122_);
v_fst_1124_ = lean_ctor_get(v_val_1123_, 0);
lean_inc(v_fst_1124_);
lean_dec(v_val_1123_);
if (lean_obj_tag(v_fst_1124_) == 0)
{
return v___x_1120_;
}
else
{
return v_fst_1124_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(lean_object* v_s_1125_, lean_object* v___x_1126_, lean_object* v_inst_1127_, lean_object* v_R_1128_, lean_object* v_a_1129_, lean_object* v_b_1130_, lean_object* v_c_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___redArg(v_s_1125_, v___x_1126_, v_a_1129_, v_b_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0___boxed(lean_object* v_s_1133_, lean_object* v___x_1134_, lean_object* v_inst_1135_, lean_object* v_R_1136_, lean_object* v_a_1137_, lean_object* v_b_1138_, lean_object* v_c_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg_spec__0(v_s_1133_, v___x_1134_, v_inst_1135_, v_R_1136_, v_a_1137_, v_b_1138_, v_c_1139_);
lean_dec_ref(v___x_1134_);
lean_dec_ref(v_s_1133_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(lean_object* v_s_1141_, lean_object* v___x_1142_, lean_object* v___x_1143_, lean_object* v_a_1144_, lean_object* v_b_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_box(0);
switch(lean_obj_tag(v_a_1144_))
{
case 0:
{
lean_object* v_pos_1147_; lean_object* v___x_1148_; 
lean_dec(v_b_1145_);
v_pos_1147_ = lean_ctor_get(v_a_1144_, 0);
lean_inc(v_pos_1147_);
lean_dec_ref(v_a_1144_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_pos_1147_);
return v___x_1148_;
}
case 1:
{
lean_object* v_pos_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1158_; 
lean_dec(v_b_1145_);
v_pos_1149_ = lean_ctor_get(v_a_1144_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_a_1144_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1151_ = v_a_1144_;
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_pos_1149_);
lean_dec(v_a_1144_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = lean_string_utf8_next_fast(v_s_1141_, v_pos_1149_);
lean_dec(v_pos_1149_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1153_);
v___x_1155_ = v___x_1151_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
v_a_1144_ = v___x_1155_;
v_b_1145_ = v___x_1146_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1159_; lean_object* v_table_1160_; lean_object* v_stackPos_1161_; lean_object* v_needlePos_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1213_; 
v_needle_1159_ = lean_ctor_get(v_a_1144_, 0);
v_table_1160_ = lean_ctor_get(v_a_1144_, 1);
v_stackPos_1161_ = lean_ctor_get(v_a_1144_, 2);
v_needlePos_1162_ = lean_ctor_get(v_a_1144_, 3);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_a_1144_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1164_ = v_a_1144_;
v_isShared_1165_ = v_isSharedCheck_1213_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_needlePos_1162_);
lean_inc(v_stackPos_1161_);
lean_inc(v_table_1160_);
lean_inc(v_needle_1159_);
lean_dec(v_a_1144_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1213_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_str_1166_; lean_object* v_startInclusive_1167_; lean_object* v_endExclusive_1168_; lean_object* v_basePos_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_str_1166_ = lean_ctor_get(v_needle_1159_, 0);
v_startInclusive_1167_ = lean_ctor_get(v_needle_1159_, 1);
v_endExclusive_1168_ = lean_ctor_get(v_needle_1159_, 2);
v_basePos_1169_ = lean_nat_sub(v_stackPos_1161_, v_needlePos_1162_);
v___x_1170_ = lean_nat_sub(v_endExclusive_1168_, v_startInclusive_1167_);
v___x_1171_ = lean_nat_add(v_basePos_1169_, v___x_1170_);
v___x_1172_ = lean_nat_dec_le(v___x_1171_, v___x_1143_);
lean_dec(v___x_1171_);
if (v___x_1172_ == 0)
{
uint8_t v___x_1173_; 
lean_dec(v___x_1170_);
lean_del_object(v___x_1164_);
lean_dec(v_needlePos_1162_);
lean_dec(v_stackPos_1161_);
lean_dec_ref(v_table_1160_);
lean_dec_ref(v_needle_1159_);
v___x_1173_ = lean_nat_dec_lt(v_basePos_1169_, v___x_1143_);
lean_dec(v_basePos_1169_);
if (v___x_1173_ == 0)
{
return v_b_1145_;
}
else
{
lean_object* v___x_1174_; 
lean_dec(v_b_1145_);
v___x_1174_ = lean_box(3);
v_a_1144_ = v___x_1174_;
v_b_1145_ = v___x_1146_;
goto _start;
}
}
else
{
uint8_t v_stackByte_1176_; lean_object* v___x_1177_; uint8_t v_patByte_1178_; uint8_t v___x_1179_; 
lean_dec(v_basePos_1169_);
lean_inc(v_stackPos_1161_);
v_stackByte_1176_ = lean_string_get_byte_fast(v_s_1141_, v_stackPos_1161_);
v___x_1177_ = lean_nat_add(v_startInclusive_1167_, v_needlePos_1162_);
v_patByte_1178_ = lean_string_get_byte_fast(v_str_1166_, v___x_1177_);
v___x_1179_ = lean_uint8_dec_eq(v_stackByte_1176_, v_patByte_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
lean_dec(v___x_1170_);
lean_dec(v_b_1145_);
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1181_ = lean_nat_dec_eq(v_needlePos_1162_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_newNeedlePos_1184_; uint8_t v___x_1185_; 
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = lean_nat_sub(v_needlePos_1162_, v___x_1182_);
lean_dec(v_needlePos_1162_);
v_newNeedlePos_1184_ = lean_array_fget_borrowed(v_table_1160_, v___x_1183_);
lean_dec(v___x_1183_);
v___x_1185_ = lean_nat_dec_eq(v_newNeedlePos_1184_, v___x_1180_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1187_; 
lean_inc(v_newNeedlePos_1184_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 3, v_newNeedlePos_1184_);
v___x_1187_ = v___x_1164_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_needle_1159_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_table_1160_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_stackPos_1161_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v_newNeedlePos_1184_);
v___x_1187_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
v_a_1144_ = v___x_1187_;
v_b_1145_ = v___x_1146_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1190_; lean_object* v___x_1192_; 
v_nextStackPos_1190_ = l_String_Slice_posGE___redArg(v___x_1142_, v_stackPos_1161_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 3, v___x_1180_);
lean_ctor_set(v___x_1164_, 2, v_nextStackPos_1190_);
v___x_1192_ = v___x_1164_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_needle_1159_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_table_1160_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_nextStackPos_1190_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v___x_1180_);
v___x_1192_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
v_a_1144_ = v___x_1192_;
v_b_1145_ = v___x_1146_;
goto _start;
}
}
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v_nextStackPos_1197_; lean_object* v___x_1199_; 
lean_dec(v_needlePos_1162_);
v___x_1195_ = lean_unsigned_to_nat(1u);
v___x_1196_ = lean_nat_add(v_stackPos_1161_, v___x_1195_);
lean_dec(v_stackPos_1161_);
v_nextStackPos_1197_ = l_String_Slice_posGE___redArg(v___x_1142_, v___x_1196_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 3, v___x_1180_);
lean_ctor_set(v___x_1164_, 2, v_nextStackPos_1197_);
v___x_1199_ = v___x_1164_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_needle_1159_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_table_1160_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_nextStackPos_1197_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v___x_1180_);
v___x_1199_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
v_a_1144_ = v___x_1199_;
v_b_1145_ = v___x_1146_;
goto _start;
}
}
}
else
{
lean_object* v___x_1202_; lean_object* v_nextStackPos_1203_; lean_object* v_nextNeedlePos_1204_; uint8_t v___x_1205_; 
v___x_1202_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1203_ = lean_nat_add(v_stackPos_1161_, v___x_1202_);
lean_dec(v_stackPos_1161_);
v_nextNeedlePos_1204_ = lean_nat_add(v_needlePos_1162_, v___x_1202_);
lean_dec(v_needlePos_1162_);
v___x_1205_ = lean_nat_dec_eq(v_nextNeedlePos_1204_, v___x_1170_);
lean_dec(v___x_1170_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1207_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 3, v_nextNeedlePos_1204_);
lean_ctor_set(v___x_1164_, 2, v_nextStackPos_1203_);
v___x_1207_ = v___x_1164_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_needle_1159_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_table_1160_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_nextStackPos_1203_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_nextNeedlePos_1204_);
v___x_1207_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
v_a_1144_ = v___x_1207_;
goto _start;
}
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_del_object(v___x_1164_);
lean_dec_ref(v_table_1160_);
lean_dec_ref(v_needle_1159_);
lean_dec(v_b_1145_);
v___x_1210_ = lean_nat_sub(v_nextStackPos_1203_, v_nextNeedlePos_1204_);
lean_dec(v_nextNeedlePos_1204_);
lean_dec(v_nextStackPos_1203_);
v___x_1211_ = l_String_Slice_pos_x21(v___x_1142_, v___x_1210_);
lean_dec(v___x_1210_);
v___x_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
}
}
}
default: 
{
return v_b_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg___boxed(lean_object* v_s_1214_, lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v_a_1217_, lean_object* v_b_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1214_, v___x_1215_, v___x_1216_, v_a_1217_, v_b_1218_);
lean_dec(v___x_1216_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v_s_1214_);
return v_res_1219_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0));
v___x_1222_ = lean_string_utf8_byte_size(v___x_1221_);
return v___x_1222_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1);
v___x_1225_ = lean_nat_dec_eq(v___x_1224_, v___x_1223_);
return v___x_1225_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1226_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__1);
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__0));
v___x_1229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v___x_1227_);
lean_ctor_set(v___x_1229_, 2, v___x_1226_);
return v___x_1229_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
v___x_1231_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1230_);
return v___x_1231_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__4);
v___x_1234_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__3);
v___x_1235_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v___x_1233_);
lean_ctor_set(v___x_1235_, 2, v___x_1232_);
lean_ctor_set(v___x_1235_, 3, v___x_1232_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(lean_object* v_s_1238_){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___y_1243_; uint8_t v___x_1252_; 
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_string_utf8_byte_size(v_s_1238_);
lean_inc_ref(v_s_1238_);
v___x_1241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1241_, 0, v_s_1238_);
lean_ctor_set(v___x_1241_, 1, v___x_1239_);
lean_ctor_set(v___x_1241_, 2, v___x_1240_);
v___x_1252_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__2);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__5);
v___y_1243_ = v___x_1253_;
goto v___jp_1242_;
}
else
{
lean_object* v___x_1254_; 
v___x_1254_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1243_ = v___x_1254_;
goto v___jp_1242_;
}
v___jp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_box(0);
v___x_1245_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1238_, v___x_1241_, v___x_1240_, v___y_1243_, v___x_1244_);
lean_dec_ref(v___x_1241_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_s_1238_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
return v___x_1247_;
}
else
{
lean_object* v_val_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v_val_1248_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_val_1248_);
lean_dec_ref(v___x_1245_);
v___x_1249_ = lean_string_utf8_extract(v_s_1238_, v___x_1239_, v_val_1248_);
v___x_1250_ = lean_string_utf8_extract(v_s_1238_, v_val_1248_, v___x_1240_);
lean_dec(v_val_1248_);
lean_dec_ref(v_s_1238_);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
return v___x_1251_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(lean_object* v_s_1255_, lean_object* v___x_1256_, lean_object* v___x_1257_, lean_object* v_inst_1258_, lean_object* v_R_1259_, lean_object* v_a_1260_, lean_object* v_b_1261_, lean_object* v_c_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_s_1255_, v___x_1256_, v___x_1257_, v_a_1260_, v_b_1261_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___boxed(lean_object* v_s_1264_, lean_object* v___x_1265_, lean_object* v___x_1266_, lean_object* v_inst_1267_, lean_object* v_R_1268_, lean_object* v_a_1269_, lean_object* v_b_1270_, lean_object* v_c_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0(v_s_1264_, v___x_1265_, v___x_1266_, v_inst_1267_, v_R_1268_, v_a_1269_, v_b_1270_, v_c_1271_);
lean_dec(v___x_1266_);
lean_dec_ref(v___x_1265_);
lean_dec_ref(v_s_1264_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(lean_object* v_s_1284_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__10));
lean_inc_ref(v_s_1284_);
v___x_1401_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1284_, v___x_1400_);
if (lean_obj_tag(v___x_1401_) == 1)
{
lean_object* v_val_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1415_; 
v_val_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1415_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_val_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1415_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1406_ = lean_string_utf8_byte_size(v_val_1402_);
v___x_1407_ = lean_unsigned_to_nat(0u);
v___x_1408_ = lean_nat_dec_eq(v___x_1406_, v___x_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_dec_ref(v_s_1284_);
v___x_1409_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1410_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1402_);
lean_dec(v_val_1402_);
v___x_1411_ = lean_string_append(v___x_1409_, v___x_1410_);
lean_dec_ref(v___x_1410_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1411_);
v___x_1413_ = v___x_1404_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
else
{
lean_del_object(v___x_1404_);
lean_dec(v_val_1402_);
goto v___jp_1378_;
}
}
}
else
{
lean_dec(v___x_1401_);
goto v___jp_1378_;
}
v___jp_1285_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__0));
v___x_1287_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1284_, v___x_1286_);
if (lean_obj_tag(v___x_1287_) == 1)
{
lean_object* v_val_1288_; lean_object* v___x_1289_; 
v_val_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_val_1288_);
lean_dec_ref(v___x_1287_);
v___x_1289_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1288_);
if (lean_obj_tag(v___x_1289_) == 1)
{
lean_object* v_val_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1304_; 
v_val_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1304_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_val_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1304_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_fst_1294_; lean_object* v_snd_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v_fst_1294_ = lean_ctor_get(v_val_1290_, 0);
lean_inc(v_fst_1294_);
v_snd_1295_ = lean_ctor_get(v_val_1290_, 1);
lean_inc(v_snd_1295_);
lean_dec(v_val_1290_);
v___x_1296_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1297_ = lean_string_append(v_fst_1294_, v___x_1296_);
v___x_1298_ = lean_string_append(v___x_1297_, v_snd_1295_);
lean_dec(v_snd_1295_);
v___x_1299_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1300_ = lean_string_append(v___x_1298_, v___x_1299_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1300_);
v___x_1302_ = v___x_1292_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
else
{
lean_object* v___x_1305_; 
lean_dec(v___x_1289_);
v___x_1305_ = lean_box(0);
return v___x_1305_;
}
}
else
{
lean_object* v___x_1306_; 
lean_dec(v___x_1287_);
v___x_1306_ = lean_box(0);
return v___x_1306_;
}
}
v___jp_1307_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__3));
lean_inc_ref(v_s_1284_);
v___x_1309_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1284_, v___x_1308_);
if (lean_obj_tag(v___x_1309_) == 1)
{
lean_object* v_val_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1321_; 
v_val_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1321_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_val_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1321_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1314_ = lean_string_utf8_byte_size(v_val_1310_);
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = lean_nat_dec_eq(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
lean_dec_ref(v_s_1284_);
v___x_1317_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1310_);
lean_dec(v_val_1310_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1317_);
v___x_1319_ = v___x_1312_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
else
{
lean_del_object(v___x_1312_);
lean_dec(v_val_1310_);
goto v___jp_1285_;
}
}
}
else
{
lean_dec(v___x_1309_);
goto v___jp_1285_;
}
}
v___jp_1322_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__4));
lean_inc_ref(v_s_1284_);
v___x_1324_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1284_, v___x_1323_);
if (lean_obj_tag(v___x_1324_) == 1)
{
lean_object* v_val_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1338_; 
v_val_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1338_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_val_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1338_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1329_ = lean_string_utf8_byte_size(v_val_1325_);
v___x_1330_ = lean_unsigned_to_nat(0u);
v___x_1331_ = lean_nat_dec_eq(v___x_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
lean_dec_ref(v_s_1284_);
v___x_1332_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1333_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1325_);
lean_dec(v_val_1325_);
v___x_1334_ = lean_string_append(v___x_1332_, v___x_1333_);
lean_dec_ref(v___x_1333_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1334_);
v___x_1336_ = v___x_1327_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
else
{
lean_del_object(v___x_1327_);
lean_dec(v_val_1325_);
goto v___jp_1307_;
}
}
}
else
{
lean_dec(v___x_1324_);
goto v___jp_1307_;
}
}
v___jp_1339_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__6));
lean_inc_ref(v_s_1284_);
v___x_1341_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1284_, v___x_1340_);
if (lean_obj_tag(v___x_1341_) == 1)
{
lean_object* v_val_1342_; lean_object* v___x_1343_; 
v_val_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_val_1342_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1342_);
if (lean_obj_tag(v___x_1343_) == 1)
{
lean_object* v_val_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v_s_1284_);
v_val_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1360_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_val_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1360_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_fst_1348_; lean_object* v_snd_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v_fst_1348_ = lean_ctor_get(v_val_1344_, 0);
lean_inc(v_fst_1348_);
v_snd_1349_ = lean_ctor_get(v_val_1344_, 1);
lean_inc(v_snd_1349_);
lean_dec(v_val_1344_);
v___x_1350_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1351_ = lean_string_append(v___x_1350_, v_fst_1348_);
lean_dec(v_fst_1348_);
v___x_1352_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
v___x_1354_ = lean_string_append(v___x_1353_, v_snd_1349_);
lean_dec(v_snd_1349_);
v___x_1355_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1356_ = lean_string_append(v___x_1354_, v___x_1355_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1356_);
v___x_1358_ = v___x_1346_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_dec(v___x_1343_);
goto v___jp_1322_;
}
}
else
{
lean_dec(v___x_1341_);
goto v___jp_1322_;
}
}
v___jp_1361_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__7));
lean_inc_ref(v_s_1284_);
v___x_1363_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1284_, v___x_1362_);
if (lean_obj_tag(v___x_1363_) == 1)
{
lean_object* v_val_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1377_; 
v_val_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1377_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_val_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1377_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1368_ = lean_string_utf8_byte_size(v_val_1364_);
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = lean_nat_dec_eq(v___x_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_dec_ref(v_s_1284_);
v___x_1371_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__5));
v___x_1372_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleBody(v_val_1364_);
lean_dec(v_val_1364_);
v___x_1373_ = lean_string_append(v___x_1371_, v___x_1372_);
lean_dec_ref(v___x_1372_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1373_);
v___x_1375_ = v___x_1366_;
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
else
{
lean_del_object(v___x_1366_);
lean_dec(v_val_1364_);
goto v___jp_1339_;
}
}
}
else
{
lean_dec(v___x_1363_);
goto v___jp_1339_;
}
}
v___jp_1378_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__8));
lean_inc_ref(v_s_1284_);
v___x_1380_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_s_1284_, v___x_1379_);
if (lean_obj_tag(v___x_1380_) == 1)
{
lean_object* v_val_1381_; lean_object* v___x_1382_; 
v_val_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_val_1381_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleWithPkg(v_val_1381_);
if (lean_obj_tag(v___x_1382_) == 1)
{
lean_object* v_val_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v_s_1284_);
v_val_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1399_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_val_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1399_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v_fst_1387_; lean_object* v_snd_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v_fst_1387_ = lean_ctor_get(v_val_1383_, 0);
lean_inc(v_fst_1387_);
v_snd_1388_ = lean_ctor_get(v_val_1383_, 1);
lean_inc(v_snd_1388_);
lean_dec(v_val_1383_);
v___x_1389_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__9));
v___x_1390_ = lean_string_append(v___x_1389_, v_fst_1387_);
lean_dec(v_fst_1387_);
v___x_1391_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__1));
v___x_1392_ = lean_string_append(v___x_1390_, v___x_1391_);
v___x_1393_ = lean_string_append(v___x_1392_, v_snd_1388_);
lean_dec(v_snd_1388_);
v___x_1394_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore___closed__2));
v___x_1395_ = lean_string_append(v___x_1393_, v___x_1394_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1395_);
v___x_1397_ = v___x_1385_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
else
{
lean_dec(v___x_1382_);
goto v___jp_1361_;
}
}
else
{
lean_dec(v___x_1380_);
goto v___jp_1361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleSymbol(lean_object* v_symbol_1425_){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1426_ = lean_string_utf8_byte_size(v_symbol_1425_);
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_nat_dec_eq(v___x_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v_fst_1430_; lean_object* v_snd_1431_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1429_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix(v_symbol_1425_);
v_fst_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_fst_1430_);
v_snd_1431_ = lean_ctor_get(v___x_1429_, 1);
lean_inc(v_snd_1431_);
lean_dec_ref(v___x_1429_);
v___x_1456_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__5));
lean_inc(v_fst_1430_);
v___x_1457_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_dropPrefix_x3f(v_fst_1430_, v___x_1456_);
if (lean_obj_tag(v___x_1457_) == 1)
{
lean_object* v_val_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1478_; 
v_val_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1478_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_val_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1478_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
uint8_t v___x_1462_; 
lean_inc(v_val_1458_);
v___x_1462_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_isAllDigits(v_val_1458_);
if (v___x_1462_ == 0)
{
lean_del_object(v___x_1460_);
lean_dec(v_val_1458_);
goto v___jp_1432_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v_r_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
lean_dec(v_fst_1430_);
v___x_1463_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__6));
v___x_1464_ = lean_string_append(v___x_1463_, v_val_1458_);
lean_dec(v_val_1458_);
v___x_1465_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__7));
v_r_1466_ = lean_string_append(v___x_1464_, v___x_1465_);
v___x_1467_ = lean_string_utf8_byte_size(v_snd_1431_);
v___x_1468_ = lean_nat_dec_eq(v___x_1467_, v___x_1427_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1469_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1470_ = lean_string_append(v_r_1466_, v___x_1469_);
v___x_1471_ = lean_string_append(v___x_1470_, v_snd_1431_);
lean_dec(v_snd_1431_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1471_);
v___x_1473_ = v___x_1460_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
else
{
lean_object* v___x_1476_; 
lean_dec(v_snd_1431_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v_r_1466_);
v___x_1476_ = v___x_1460_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_r_1466_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
else
{
lean_dec(v___x_1457_);
goto v___jp_1432_;
}
v___jp_1432_:
{
lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__0));
v___x_1434_ = lean_string_dec_eq(v_fst_1430_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_demangleCore(v_fst_1430_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec(v_snd_1431_);
return v___x_1435_;
}
else
{
lean_object* v_val_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v_val_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1436_);
v___x_1437_ = lean_string_utf8_byte_size(v_snd_1431_);
v___x_1438_ = lean_nat_dec_eq(v___x_1437_, v___x_1427_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1448_; 
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v___x_1435_, 0);
lean_dec(v_unused_1449_);
v___x_1440_ = v___x_1435_;
v_isShared_1441_ = v_isSharedCheck_1448_;
goto v_resetjp_1439_;
}
else
{
lean_dec(v___x_1435_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1448_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1442_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__1));
v___x_1443_ = lean_string_append(v_val_1436_, v___x_1442_);
v___x_1444_ = lean_string_append(v___x_1443_, v_snd_1431_);
lean_dec(v_snd_1431_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1444_);
v___x_1446_ = v___x_1440_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
else
{
lean_dec(v_val_1436_);
lean_dec(v_snd_1431_);
return v___x_1435_;
}
}
}
else
{
lean_object* v___x_1450_; uint8_t v___x_1451_; 
lean_dec(v_fst_1430_);
v___x_1450_ = lean_string_utf8_byte_size(v_snd_1431_);
v___x_1451_ = lean_nat_dec_eq(v___x_1450_, v___x_1427_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__2));
v___x_1453_ = lean_string_append(v___x_1452_, v_snd_1431_);
lean_dec(v_snd_1431_);
v___x_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
return v___x_1454_;
}
else
{
lean_object* v___x_1455_; 
lean_dec(v_snd_1431_);
v___x_1455_ = ((lean_object*)(l_Lean_Name_Demangle_demangleSymbol___closed__4));
return v___x_1455_;
}
}
}
}
else
{
lean_object* v___x_1479_; 
lean_dec_ref(v_symbol_1425_);
v___x_1479_ = lean_box(0);
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(lean_object* v_s_1480_, lean_object* v_pos_1481_, lean_object* v_pred_1482_){
_start:
{
lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1483_ = lean_string_utf8_byte_size(v_s_1480_);
v___x_1484_ = lean_nat_dec_eq(v_pos_1481_, v___x_1483_);
if (v___x_1484_ == 0)
{
uint32_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1485_ = lean_string_utf8_get_fast(v_s_1480_, v_pos_1481_);
v___x_1486_ = lean_box_uint32(v___x_1485_);
lean_inc_ref(v_pred_1482_);
v___x_1487_ = lean_apply_1(v_pred_1482_, v___x_1486_);
v___x_1488_ = lean_unbox(v___x_1487_);
if (v___x_1488_ == 0)
{
lean_dec_ref(v_pred_1482_);
return v_pos_1481_;
}
else
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_string_utf8_next_fast(v_s_1480_, v_pos_1481_);
lean_dec(v_pos_1481_);
v_pos_1481_ = v___x_1489_;
goto _start;
}
}
else
{
lean_dec_ref(v_pred_1482_);
return v_pos_1481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile___boxed(lean_object* v_s_1491_, lean_object* v_pos_1492_, lean_object* v_pred_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_s_1491_, v_pos_1492_, v_pred_1493_);
lean_dec_ref(v_s_1491_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(lean_object* v_s_1495_, lean_object* v_p_u2081_1496_, lean_object* v_p_u2082_1497_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = lean_string_utf8_extract(v_s_1495_, v___x_1498_, v_p_u2081_1496_);
v___x_1500_ = lean_string_utf8_extract(v_s_1495_, v_p_u2081_1496_, v_p_u2082_1497_);
v___x_1501_ = lean_string_utf8_byte_size(v_s_1495_);
v___x_1502_ = lean_string_utf8_extract(v_s_1495_, v_p_u2082_1497_, v___x_1501_);
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1500_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1499_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082___boxed(lean_object* v_s_1505_, lean_object* v_p_u2081_1506_, lean_object* v_p_u2082_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_s_1505_, v_p_u2081_1506_, v_p_u2082_1507_);
lean_dec(v_p_u2082_1507_);
lean_dec(v_p_u2081_1506_);
lean_dec_ref(v_s_1505_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(lean_object* v___x_1509_, lean_object* v___x_1510_, lean_object* v_line_1511_, lean_object* v_a_1512_, lean_object* v_b_1513_){
_start:
{
lean_object* v_startInclusive_1514_; lean_object* v_endExclusive_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v_startInclusive_1514_ = lean_ctor_get(v___x_1509_, 1);
v_endExclusive_1515_ = lean_ctor_get(v___x_1509_, 2);
v___x_1516_ = lean_nat_sub(v_endExclusive_1515_, v_startInclusive_1514_);
v___x_1517_ = lean_nat_dec_eq(v_a_1512_, v___x_1516_);
lean_dec(v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; uint8_t v___y_1521_; uint32_t v___x_1526_; uint32_t v___x_1527_; uint8_t v___x_1528_; 
lean_dec(v_b_1513_);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_nat_add(v___x_1510_, v_a_1512_);
v___x_1526_ = lean_string_utf8_get_fast(v_line_1511_, v___x_1519_);
v___x_1527_ = 43;
v___x_1528_ = lean_uint32_dec_eq(v___x_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
uint32_t v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = 41;
v___x_1530_ = lean_uint32_dec_eq(v___x_1526_, v___x_1529_);
v___y_1521_ = v___x_1530_;
goto v___jp_1520_;
}
else
{
v___y_1521_ = v___x_1528_;
goto v___jp_1520_;
}
v___jp_1520_:
{
if (v___y_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
lean_dec(v_a_1512_);
v___x_1522_ = lean_string_utf8_next_fast(v_line_1511_, v___x_1519_);
lean_dec(v___x_1519_);
v___x_1523_ = lean_nat_sub(v___x_1522_, v___x_1510_);
v_a_1512_ = v___x_1523_;
v_b_1513_ = v___x_1518_;
goto _start;
}
else
{
lean_object* v___x_1525_; 
lean_dec(v___x_1519_);
v___x_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_a_1512_);
return v___x_1525_;
}
}
}
else
{
lean_dec(v_a_1512_);
return v_b_1513_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg___boxed(lean_object* v___x_1531_, lean_object* v___x_1532_, lean_object* v_line_1533_, lean_object* v_a_1534_, lean_object* v_b_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1531_, v___x_1532_, v_line_1533_, v_a_1534_, v_b_1535_);
lean_dec_ref(v_line_1533_);
lean_dec(v___x_1532_);
lean_dec_ref(v___x_1531_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(lean_object* v___x_1537_, lean_object* v_line_1538_, lean_object* v_a_1539_, lean_object* v_b_1540_){
_start:
{
lean_object* v_startInclusive_1541_; lean_object* v_endExclusive_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v_startInclusive_1541_ = lean_ctor_get(v___x_1537_, 1);
v_endExclusive_1542_ = lean_ctor_get(v___x_1537_, 2);
v___x_1543_ = lean_nat_sub(v_endExclusive_1542_, v_startInclusive_1541_);
v___x_1544_ = lean_nat_dec_eq(v_a_1539_, v___x_1543_);
lean_dec(v___x_1543_);
if (v___x_1544_ == 0)
{
uint32_t v___x_1545_; uint32_t v___x_1546_; uint8_t v___x_1547_; 
lean_dec(v_b_1540_);
v___x_1545_ = lean_string_utf8_get_fast(v_line_1538_, v_a_1539_);
v___x_1546_ = 40;
v___x_1547_ = lean_uint32_dec_eq(v___x_1545_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_string_utf8_next_fast(v_line_1538_, v_a_1539_);
lean_dec(v_a_1539_);
v_a_1539_ = v___x_1549_;
v_b_1540_ = v___x_1548_;
goto _start;
}
else
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_a_1539_);
return v___x_1551_;
}
}
else
{
lean_dec(v_a_1539_);
return v_b_1540_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg___boxed(lean_object* v___x_1552_, lean_object* v_line_1553_, lean_object* v_a_1554_, lean_object* v_b_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1552_, v_line_1553_, v_a_1554_, v_b_1555_);
lean_dec_ref(v_line_1553_);
lean_dec_ref(v___x_1552_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(lean_object* v_line_1557_){
_start:
{
lean_object* v_searcher_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_searcher_1558_ = lean_unsigned_to_nat(0u);
v___x_1559_ = lean_string_utf8_byte_size(v_line_1557_);
lean_inc_ref(v_line_1557_);
v___x_1560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1560_, 0, v_line_1557_);
lean_ctor_set(v___x_1560_, 1, v_searcher_1558_);
lean_ctor_set(v___x_1560_, 2, v___x_1559_);
v___x_1561_ = lean_box(0);
v___x_1562_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1560_, v_line_1557_, v_searcher_1558_, v___x_1561_);
lean_dec_ref(v___x_1560_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_dec_ref(v_line_1557_);
return v___x_1561_;
}
else
{
lean_object* v_val_1563_; uint8_t v___x_1564_; 
v_val_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_val_1563_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = lean_nat_dec_eq(v_val_1563_, v___x_1559_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = lean_string_utf8_next_fast(v_line_1557_, v_val_1563_);
lean_dec(v_val_1563_);
lean_inc_ref(v_line_1557_);
v___x_1566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1566_, 0, v_line_1557_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
lean_ctor_set(v___x_1566_, 2, v___x_1559_);
v___x_1567_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1566_, v___x_1565_, v_line_1557_, v_searcher_1558_, v___x_1561_);
lean_dec_ref(v___x_1566_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_dec_ref(v_line_1557_);
return v___x_1561_;
}
else
{
lean_object* v_val_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1578_; 
v_val_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1578_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_val_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1578_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = lean_nat_add(v___x_1565_, v_val_1568_);
lean_dec(v_val_1568_);
v___x_1573_ = lean_nat_dec_eq(v___x_1572_, v___x_1565_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1557_, v___x_1565_, v___x_1572_);
lean_dec(v___x_1572_);
lean_dec_ref(v_line_1557_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1574_);
v___x_1576_ = v___x_1570_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
else
{
lean_dec(v___x_1572_);
lean_del_object(v___x_1570_);
lean_dec_ref(v_line_1557_);
return v___x_1561_;
}
}
}
}
else
{
lean_dec(v_val_1563_);
lean_dec_ref(v_line_1557_);
return v___x_1561_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(lean_object* v___x_1579_, lean_object* v_line_1580_, lean_object* v_inst_1581_, lean_object* v_R_1582_, lean_object* v_a_1583_, lean_object* v_b_1584_, lean_object* v_c_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___redArg(v___x_1579_, v_line_1580_, v_a_1583_, v_b_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0___boxed(lean_object* v___x_1587_, lean_object* v_line_1588_, lean_object* v_inst_1589_, lean_object* v_R_1590_, lean_object* v_a_1591_, lean_object* v_b_1592_, lean_object* v_c_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__0(v___x_1587_, v_line_1588_, v_inst_1589_, v_R_1590_, v_a_1591_, v_b_1592_, v_c_1593_);
lean_dec_ref(v_line_1588_);
lean_dec_ref(v___x_1587_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(lean_object* v___x_1595_, lean_object* v___x_1596_, lean_object* v_line_1597_, lean_object* v_inst_1598_, lean_object* v_R_1599_, lean_object* v_a_1600_, lean_object* v_b_1601_, lean_object* v_c_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___redArg(v___x_1595_, v___x_1596_, v_line_1597_, v_a_1600_, v_b_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1___boxed(lean_object* v___x_1604_, lean_object* v___x_1605_, lean_object* v_line_1606_, lean_object* v_inst_1607_, lean_object* v_R_1608_, lean_object* v_a_1609_, lean_object* v_b_1610_, lean_object* v_c_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux_spec__1(v___x_1604_, v___x_1605_, v_line_1606_, v_inst_1607_, v_R_1608_, v_a_1609_, v_b_1610_, v_c_1611_);
lean_dec_ref(v_line_1606_);
lean_dec(v___x_1605_);
lean_dec_ref(v___x_1604_);
return v_res_1612_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(uint32_t v_x_1613_){
_start:
{
uint32_t v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = 32;
v___x_1615_ = lean_uint32_dec_eq(v_x_1613_, v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0___boxed(lean_object* v_x_1616_){
_start:
{
uint32_t v_x_2607__boxed_1617_; uint8_t v_res_1618_; lean_object* v_r_1619_; 
v_x_2607__boxed_1617_ = lean_unbox_uint32(v_x_1616_);
lean_dec(v_x_1616_);
v_res_1618_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__0(v_x_2607__boxed_1617_);
v_r_1619_ = lean_box(v_res_1618_);
return v_r_1619_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(uint32_t v_x_1620_){
_start:
{
uint8_t v___y_1622_; uint8_t v___y_1628_; uint32_t v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = 48;
v___x_1634_ = lean_uint32_dec_le(v___x_1633_, v_x_1620_);
if (v___x_1634_ == 0)
{
v___y_1628_ = v___x_1634_;
goto v___jp_1627_;
}
else
{
uint32_t v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = 57;
v___x_1636_ = lean_uint32_dec_le(v_x_1620_, v___x_1635_);
v___y_1628_ = v___x_1636_;
goto v___jp_1627_;
}
v___jp_1621_:
{
if (v___y_1622_ == 0)
{
uint32_t v___x_1623_; uint8_t v___x_1624_; 
v___x_1623_ = 65;
v___x_1624_ = lean_uint32_dec_le(v___x_1623_, v_x_1620_);
if (v___x_1624_ == 0)
{
return v___x_1624_;
}
else
{
uint32_t v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = 70;
v___x_1626_ = lean_uint32_dec_le(v_x_1620_, v___x_1625_);
return v___x_1626_;
}
}
else
{
return v___y_1622_;
}
}
v___jp_1627_:
{
if (v___y_1628_ == 0)
{
uint32_t v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = 97;
v___x_1630_ = lean_uint32_dec_le(v___x_1629_, v_x_1620_);
if (v___x_1630_ == 0)
{
v___y_1622_ = v___x_1630_;
goto v___jp_1621_;
}
else
{
uint32_t v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = 102;
v___x_1632_ = lean_uint32_dec_le(v_x_1620_, v___x_1631_);
v___y_1622_ = v___x_1632_;
goto v___jp_1621_;
}
}
else
{
return v___y_1628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1___boxed(lean_object* v_x_1637_){
_start:
{
uint32_t v_x_2614__boxed_1638_; uint8_t v_res_1639_; lean_object* v_r_1640_; 
v_x_2614__boxed_1638_ = lean_unbox_uint32(v_x_1637_);
lean_dec(v_x_1637_);
v_res_1639_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___lam__1(v_x_2614__boxed_1638_);
v_r_1640_ = lean_box(v_res_1639_);
return v_r_1640_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(lean_object* v___x_1641_, lean_object* v_line_1642_, lean_object* v___x_1643_, lean_object* v___x_1644_, lean_object* v_a_1645_, lean_object* v_b_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_box(0);
switch(lean_obj_tag(v_a_1645_))
{
case 0:
{
lean_object* v_pos_1648_; lean_object* v___x_1649_; 
lean_dec(v_b_1646_);
v_pos_1648_ = lean_ctor_get(v_a_1645_, 0);
lean_inc(v_pos_1648_);
lean_dec_ref(v_a_1645_);
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_pos_1648_);
return v___x_1649_;
}
case 1:
{
lean_object* v_pos_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1661_; 
lean_dec(v_b_1646_);
v_pos_1650_ = lean_ctor_get(v_a_1645_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_a_1645_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1652_ = v_a_1645_;
v_isShared_1653_ = v_isSharedCheck_1661_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_pos_1650_);
lean_dec(v_a_1645_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1661_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1654_ = lean_nat_add(v___x_1641_, v_pos_1650_);
lean_dec(v_pos_1650_);
v___x_1655_ = lean_string_utf8_next_fast(v_line_1642_, v___x_1654_);
lean_dec(v___x_1654_);
v___x_1656_ = lean_nat_sub(v___x_1655_, v___x_1641_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1656_);
v___x_1658_ = v___x_1652_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
v_a_1645_ = v___x_1658_;
v_b_1646_ = v___x_1647_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1662_; lean_object* v_table_1663_; lean_object* v_stackPos_1664_; lean_object* v_needlePos_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1718_; 
v_needle_1662_ = lean_ctor_get(v_a_1645_, 0);
v_table_1663_ = lean_ctor_get(v_a_1645_, 1);
v_stackPos_1664_ = lean_ctor_get(v_a_1645_, 2);
v_needlePos_1665_ = lean_ctor_get(v_a_1645_, 3);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_a_1645_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1667_ = v_a_1645_;
v_isShared_1668_ = v_isSharedCheck_1718_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_needlePos_1665_);
lean_inc(v_stackPos_1664_);
lean_inc(v_table_1663_);
lean_inc(v_needle_1662_);
lean_dec(v_a_1645_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1718_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_str_1669_; lean_object* v_startInclusive_1670_; lean_object* v_endExclusive_1671_; lean_object* v_basePos_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v_str_1669_ = lean_ctor_get(v_needle_1662_, 0);
v_startInclusive_1670_ = lean_ctor_get(v_needle_1662_, 1);
v_endExclusive_1671_ = lean_ctor_get(v_needle_1662_, 2);
v_basePos_1672_ = lean_nat_sub(v_stackPos_1664_, v_needlePos_1665_);
v___x_1673_ = lean_nat_sub(v_endExclusive_1671_, v_startInclusive_1670_);
v___x_1674_ = lean_nat_add(v_basePos_1672_, v___x_1673_);
v___x_1675_ = lean_nat_sub(v___x_1644_, v___x_1641_);
v___x_1676_ = lean_nat_dec_le(v___x_1674_, v___x_1675_);
lean_dec(v___x_1674_);
if (v___x_1676_ == 0)
{
uint8_t v___x_1677_; 
lean_dec(v___x_1673_);
lean_del_object(v___x_1667_);
lean_dec(v_needlePos_1665_);
lean_dec(v_stackPos_1664_);
lean_dec_ref(v_table_1663_);
lean_dec_ref(v_needle_1662_);
v___x_1677_ = lean_nat_dec_lt(v_basePos_1672_, v___x_1675_);
lean_dec(v___x_1675_);
lean_dec(v_basePos_1672_);
if (v___x_1677_ == 0)
{
return v_b_1646_;
}
else
{
lean_object* v___x_1678_; 
lean_dec(v_b_1646_);
v___x_1678_ = lean_box(3);
v_a_1645_ = v___x_1678_;
v_b_1646_ = v___x_1647_;
goto _start;
}
}
else
{
lean_object* v___x_1680_; uint8_t v_stackByte_1681_; lean_object* v___x_1682_; uint8_t v_patByte_1683_; uint8_t v___x_1684_; 
lean_dec(v___x_1675_);
lean_dec(v_basePos_1672_);
v___x_1680_ = lean_nat_add(v___x_1641_, v_stackPos_1664_);
v_stackByte_1681_ = lean_string_get_byte_fast(v_line_1642_, v___x_1680_);
v___x_1682_ = lean_nat_add(v_startInclusive_1670_, v_needlePos_1665_);
v_patByte_1683_ = lean_string_get_byte_fast(v_str_1669_, v___x_1682_);
v___x_1684_ = lean_uint8_dec_eq(v_stackByte_1681_, v_patByte_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
lean_dec(v___x_1673_);
lean_dec(v_b_1646_);
v___x_1685_ = lean_unsigned_to_nat(0u);
v___x_1686_ = lean_nat_dec_eq(v_needlePos_1665_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v_newNeedlePos_1689_; uint8_t v___x_1690_; 
v___x_1687_ = lean_unsigned_to_nat(1u);
v___x_1688_ = lean_nat_sub(v_needlePos_1665_, v___x_1687_);
lean_dec(v_needlePos_1665_);
v_newNeedlePos_1689_ = lean_array_fget_borrowed(v_table_1663_, v___x_1688_);
lean_dec(v___x_1688_);
v___x_1690_ = lean_nat_dec_eq(v_newNeedlePos_1689_, v___x_1685_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1692_; 
lean_inc(v_newNeedlePos_1689_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 3, v_newNeedlePos_1689_);
v___x_1692_ = v___x_1667_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_needle_1662_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_table_1663_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_stackPos_1664_);
lean_ctor_set(v_reuseFailAlloc_1694_, 3, v_newNeedlePos_1689_);
v___x_1692_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
v_a_1645_ = v___x_1692_;
v_b_1646_ = v___x_1647_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1695_; lean_object* v___x_1697_; 
v_nextStackPos_1695_ = l_String_Slice_posGE___redArg(v___x_1643_, v_stackPos_1664_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 3, v___x_1685_);
lean_ctor_set(v___x_1667_, 2, v_nextStackPos_1695_);
v___x_1697_ = v___x_1667_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_needle_1662_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_table_1663_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_nextStackPos_1695_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v___x_1685_);
v___x_1697_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
v_a_1645_ = v___x_1697_;
v_b_1646_ = v___x_1647_;
goto _start;
}
}
}
else
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v_nextStackPos_1702_; lean_object* v___x_1704_; 
lean_dec(v_needlePos_1665_);
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = lean_nat_add(v_stackPos_1664_, v___x_1700_);
lean_dec(v_stackPos_1664_);
v_nextStackPos_1702_ = l_String_Slice_posGE___redArg(v___x_1643_, v___x_1701_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 3, v___x_1685_);
lean_ctor_set(v___x_1667_, 2, v_nextStackPos_1702_);
v___x_1704_ = v___x_1667_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_needle_1662_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_table_1663_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_nextStackPos_1702_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v___x_1685_);
v___x_1704_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
v_a_1645_ = v___x_1704_;
v_b_1646_ = v___x_1647_;
goto _start;
}
}
}
else
{
lean_object* v___x_1707_; lean_object* v_nextStackPos_1708_; lean_object* v_nextNeedlePos_1709_; uint8_t v___x_1710_; 
v___x_1707_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1708_ = lean_nat_add(v_stackPos_1664_, v___x_1707_);
lean_dec(v_stackPos_1664_);
v_nextNeedlePos_1709_ = lean_nat_add(v_needlePos_1665_, v___x_1707_);
lean_dec(v_needlePos_1665_);
v___x_1710_ = lean_nat_dec_eq(v_nextNeedlePos_1709_, v___x_1673_);
lean_dec(v___x_1673_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1712_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 3, v_nextNeedlePos_1709_);
lean_ctor_set(v___x_1667_, 2, v_nextStackPos_1708_);
v___x_1712_ = v___x_1667_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_needle_1662_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_table_1663_);
lean_ctor_set(v_reuseFailAlloc_1714_, 2, v_nextStackPos_1708_);
lean_ctor_set(v_reuseFailAlloc_1714_, 3, v_nextNeedlePos_1709_);
v___x_1712_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
v_a_1645_ = v___x_1712_;
goto _start;
}
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_del_object(v___x_1667_);
lean_dec_ref(v_table_1663_);
lean_dec_ref(v_needle_1662_);
lean_dec(v_b_1646_);
v___x_1715_ = lean_nat_sub(v_nextStackPos_1708_, v_nextNeedlePos_1709_);
lean_dec(v_nextNeedlePos_1709_);
lean_dec(v_nextStackPos_1708_);
v___x_1716_ = l_String_Slice_pos_x21(v___x_1643_, v___x_1715_);
lean_dec(v___x_1715_);
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
return v___x_1717_;
}
}
}
}
}
default: 
{
return v_b_1646_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg___boxed(lean_object* v___x_1719_, lean_object* v_line_1720_, lean_object* v___x_1721_, lean_object* v___x_1722_, lean_object* v_a_1723_, lean_object* v_b_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1719_, v_line_1720_, v___x_1721_, v___x_1722_, v_a_1723_, v_b_1724_);
lean_dec(v___x_1722_);
lean_dec_ref(v___x_1721_);
lean_dec_ref(v_line_1720_);
lean_dec(v___x_1719_);
return v_res_1725_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3));
v___x_1731_ = lean_string_utf8_byte_size(v___x_1730_);
return v___x_1731_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1732_ = lean_unsigned_to_nat(0u);
v___x_1733_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4);
v___x_1734_ = lean_nat_dec_eq(v___x_1733_, v___x_1732_);
return v___x_1734_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1735_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__4);
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__3));
v___x_1738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
lean_ctor_set(v___x_1738_, 1, v___x_1736_);
lean_ctor_set(v___x_1738_, 2, v___x_1735_);
return v___x_1738_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6);
v___x_1740_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1739_);
return v___x_1740_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__7);
v___x_1743_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__6);
v___x_1744_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
lean_ctor_set(v___x_1744_, 1, v___x_1742_);
lean_ctor_set(v___x_1744_, 2, v___x_1741_);
lean_ctor_set(v___x_1744_, 3, v___x_1741_);
return v___x_1744_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2));
v___x_1746_ = lean_string_utf8_byte_size(v___x_1745_);
return v___x_1746_;
}
}
static uint8_t _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
v___x_1749_ = lean_nat_dec_eq(v___x_1748_, v___x_1747_);
return v___x_1749_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1750_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__9);
v___x_1751_ = lean_unsigned_to_nat(0u);
v___x_1752_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__2));
v___x_1753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v___x_1751_);
lean_ctor_set(v___x_1753_, 2, v___x_1750_);
return v___x_1753_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11);
v___x_1755_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1754_);
return v___x_1755_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__12);
v___x_1758_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__11);
v___x_1759_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___x_1757_);
lean_ctor_set(v___x_1759_, 2, v___x_1756_);
lean_ctor_set(v___x_1759_, 3, v___x_1756_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(lean_object* v_line_1760_){
_start:
{
lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___f_1768_; lean_object* v___f_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___x_1780_; lean_object* v___y_1782_; uint8_t v___x_1797_; 
v___f_1768_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__0));
v___f_1769_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__1));
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = lean_string_utf8_byte_size(v_line_1760_);
lean_inc_ref(v_line_1760_);
v___x_1780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1780_, 0, v_line_1760_);
lean_ctor_set(v___x_1780_, 1, v___x_1770_);
lean_ctor_set(v___x_1780_, 2, v___x_1771_);
v___x_1797_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__10);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__13);
v___y_1782_ = v___x_1798_;
goto v___jp_1781_;
}
else
{
lean_object* v___x_1799_; 
v___x_1799_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1782_ = v___x_1799_;
goto v___jp_1781_;
}
v___jp_1761_:
{
uint8_t v___x_1764_; 
v___x_1764_ = lean_nat_dec_eq(v___y_1763_, v___y_1762_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_splitAt_u2082(v_line_1760_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v_line_1760_);
v___x_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; 
lean_dec(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v_line_1760_);
v___x_1767_ = lean_box(0);
return v___x_1767_;
}
}
v___jp_1772_:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___y_1775_, v_line_1760_, v___y_1774_, v___x_1771_, v___y_1776_, v___y_1773_);
lean_dec_ref(v___y_1774_);
if (lean_obj_tag(v___x_1777_) == 0)
{
v___y_1762_ = v___y_1775_;
v___y_1763_ = v___x_1771_;
goto v___jp_1761_;
}
else
{
lean_object* v_val_1778_; lean_object* v___x_1779_; 
v_val_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_val_1778_);
lean_dec_ref(v___x_1777_);
v___x_1779_ = lean_nat_add(v___y_1775_, v_val_1778_);
lean_dec(v_val_1778_);
v___y_1762_ = v___y_1775_;
v___y_1763_ = v___x_1779_;
goto v___jp_1761_;
}
}
v___jp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_box(0);
v___x_1784_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix_spec__0___redArg(v_line_1760_, v___x_1780_, v___x_1771_, v___y_1782_, v___x_1783_);
lean_dec_ref(v___x_1780_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_dec_ref(v_line_1760_);
return v___x_1783_;
}
else
{
lean_object* v_val_1785_; uint8_t v___x_1786_; 
v_val_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_val_1785_);
lean_dec_ref(v___x_1784_);
v___x_1786_ = lean_nat_dec_eq(v_val_1785_, v___x_1771_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = lean_string_utf8_next_fast(v_line_1760_, v_val_1785_);
lean_dec(v_val_1785_);
v___x_1788_ = lean_nat_dec_eq(v___x_1787_, v___x_1771_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1789_ = lean_string_utf8_next_fast(v_line_1760_, v___x_1787_);
v___x_1790_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1760_, v___x_1789_, v___f_1769_);
v___x_1791_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_skipWhile(v_line_1760_, v___x_1790_, v___f_1768_);
v___x_1792_ = lean_nat_dec_eq(v___x_1791_, v___x_1771_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; uint8_t v___x_1794_; 
lean_inc(v___x_1791_);
lean_inc_ref(v_line_1760_);
v___x_1793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1793_, 0, v_line_1760_);
lean_ctor_set(v___x_1793_, 1, v___x_1791_);
lean_ctor_set(v___x_1793_, 2, v___x_1771_);
v___x_1794_ = lean_uint8_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__5);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_obj_once(&l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8, &l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8_once, _init_l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS___closed__8);
v___y_1773_ = v___x_1783_;
v___y_1774_ = v___x_1793_;
v___y_1775_ = v___x_1791_;
v___y_1776_ = v___x_1795_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1796_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_stripColdSuffix___closed__6));
v___y_1773_ = v___x_1783_;
v___y_1774_ = v___x_1793_;
v___y_1775_ = v___x_1791_;
v___y_1776_ = v___x_1796_;
goto v___jp_1772_;
}
}
else
{
lean_dec(v___x_1791_);
lean_dec_ref(v_line_1760_);
return v___x_1783_;
}
}
else
{
lean_dec_ref(v_line_1760_);
return v___x_1783_;
}
}
else
{
lean_dec(v_val_1785_);
lean_dec_ref(v_line_1760_);
return v___x_1783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(lean_object* v___x_1800_, lean_object* v_line_1801_, lean_object* v___x_1802_, lean_object* v___x_1803_, lean_object* v_inst_1804_, lean_object* v_R_1805_, lean_object* v_a_1806_, lean_object* v_b_1807_, lean_object* v_c_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___redArg(v___x_1800_, v_line_1801_, v___x_1802_, v___x_1803_, v_a_1806_, v_b_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0___boxed(lean_object* v___x_1810_, lean_object* v_line_1811_, lean_object* v___x_1812_, lean_object* v___x_1813_, lean_object* v_inst_1814_, lean_object* v_R_1815_, lean_object* v_a_1816_, lean_object* v_b_1817_, lean_object* v_c_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS_spec__0(v___x_1810_, v_line_1811_, v___x_1812_, v___x_1813_, v_inst_1814_, v_R_1815_, v_a_1816_, v_b_1817_, v_c_1818_);
lean_dec(v___x_1813_);
lean_dec_ref(v___x_1812_);
lean_dec_ref(v_line_1811_);
lean_dec(v___x_1810_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(lean_object* v_line_1820_){
_start:
{
lean_object* v___x_1821_; 
lean_inc_ref(v_line_1820_);
v___x_1821_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryLinux(v_line_1820_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol_tryMacOS(v_line_1820_);
return v___x_1822_;
}
else
{
lean_dec_ref(v_line_1820_);
return v___x_1821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_Demangle_demangleBtLine(lean_object* v_line_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_extractSymbol(v_line_1823_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_box(0);
return v___x_1825_;
}
else
{
lean_object* v_val_1826_; lean_object* v_snd_1827_; lean_object* v_fst_1828_; lean_object* v_fst_1829_; lean_object* v_snd_1830_; lean_object* v___x_1831_; 
v_val_1826_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_val_1826_);
lean_dec_ref(v___x_1824_);
v_snd_1827_ = lean_ctor_get(v_val_1826_, 1);
lean_inc(v_snd_1827_);
v_fst_1828_ = lean_ctor_get(v_val_1826_, 0);
lean_inc(v_fst_1828_);
lean_dec(v_val_1826_);
v_fst_1829_ = lean_ctor_get(v_snd_1827_, 0);
lean_inc(v_fst_1829_);
v_snd_1830_ = lean_ctor_get(v_snd_1827_, 1);
lean_inc(v_snd_1830_);
lean_dec(v_snd_1827_);
v___x_1831_ = l_Lean_Name_Demangle_demangleSymbol(v_fst_1829_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_dec(v_snd_1830_);
lean_dec(v_fst_1828_);
return v___x_1831_;
}
else
{
lean_object* v_val_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1841_; 
v_val_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1841_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_val_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1841_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1836_ = lean_string_append(v_fst_1828_, v_val_1832_);
lean_dec(v_val_1832_);
v___x_1837_ = lean_string_append(v___x_1836_, v_snd_1830_);
lean_dec(v_snd_1830_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1837_);
v___x_1839_ = v___x_1834_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_demangle_bt_line_cstr(lean_object* v_line_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_Name_Demangle_demangleBtLine(v_line_1842_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v___x_1844_; 
v___x_1844_ = ((lean_object*)(l___private_Lean_Compiler_NameDemangling_0__Lean_Name_Demangle_formatNameParts___closed__0));
return v___x_1844_;
}
else
{
lean_object* v_val_1845_; 
v_val_1845_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_val_1845_);
lean_dec_ref(v___x_1843_);
return v_val_1845_;
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
