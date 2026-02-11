// Lean compiler output
// Module: Init.System.FilePath
// Imports: import Init.Data.String.Modify import Init.Data.String.Search public import Init.Data.ToString.Basic import Init.Data.Iterators.Consumers.Collect import Init.System.Platform
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
static const lean_string_object l_System_instInhabitedFilePath_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_System_instInhabitedFilePath_default___closed__0 = (const lean_object*)&l_System_instInhabitedFilePath_default___closed__0_value;
LEAN_EXPORT const lean_object* l_System_instInhabitedFilePath_default = (const lean_object*)&l_System_instInhabitedFilePath_default___closed__0_value;
LEAN_EXPORT const lean_object* l_System_instInhabitedFilePath = (const lean_object*)&l_System_instInhabitedFilePath_default___closed__0_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath___boxed(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_System_instHashableFilePath_hash(lean_object*);
LEAN_EXPORT lean_object* l_System_instHashableFilePath_hash___boxed(lean_object*);
static const lean_closure_object l_System_instHashableFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_System_instHashableFilePath_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_System_instHashableFilePath___closed__0 = (const lean_object*)&l_System_instHashableFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_System_instHashableFilePath = (const lean_object*)&l_System_instHashableFilePath___closed__0_value;
static const lean_string_object l_System_instReprFilePath___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_System_instReprFilePath___lam__0___closed__0 = (const lean_object*)&l_System_instReprFilePath___lam__0___closed__0_value;
static const lean_ctor_object l_System_instReprFilePath___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_System_instReprFilePath___lam__0___closed__0_value)}};
static const lean_object* l_System_instReprFilePath___lam__0___closed__1 = (const lean_object*)&l_System_instReprFilePath___lam__0___closed__1_value;
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_System_instReprFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_System_instReprFilePath___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_System_instReprFilePath___closed__0 = (const lean_object*)&l_System_instReprFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_System_instReprFilePath = (const lean_object*)&l_System_instReprFilePath___closed__0_value;
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0___boxed(lean_object*);
static const lean_closure_object l_System_instToStringFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_System_instToStringFilePath___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_System_instToStringFilePath___closed__0 = (const lean_object*)&l_System_instToStringFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_System_instToStringFilePath = (const lean_object*)&l_System_instToStringFilePath___closed__0_value;
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT uint32_t l_System_FilePath_pathSeparator;
LEAN_EXPORT lean_object* l_System_FilePath_pathSeparators___closed__0___boxed__const__1;
static lean_object* l_System_FilePath_pathSeparators___closed__0;
LEAN_EXPORT lean_object* l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
static lean_object* l_System_FilePath_pathSeparators___closed__1;
LEAN_EXPORT lean_object* l_System_FilePath_pathSeparators;
LEAN_EXPORT uint32_t l_System_FilePath_extSeparator;
static const lean_string_object l_System_FilePath_exeExtension___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "exe"};
static const lean_object* l_System_FilePath_exeExtension___closed__0 = (const lean_object*)&l_System_FilePath_exeExtension___closed__0_value;
LEAN_EXPORT lean_object* l_System_FilePath_exeExtension;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l_List_elem___at___00System_FilePath_normalize_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00System_FilePath_normalize_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
static lean_object* l_System_FilePath_normalize___closed__0;
static uint8_t l_System_FilePath_normalize___closed__1;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
static lean_object* l_System_FilePath_isAbsolute___closed__0;
lean_object* l_String_Slice_Pos_next_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object*);
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_System_FilePath_join___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static const lean_closure_object l_System_FilePath_instDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_System_FilePath_join, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_System_FilePath_instDiv___closed__0 = (const lean_object*)&l_System_FilePath_instDiv___closed__0_value;
LEAN_EXPORT const lean_object* l_System_FilePath_instDiv = (const lean_object*)&l_System_FilePath_instDiv___closed__0_value;
LEAN_EXPORT const lean_object* l_System_FilePath_instHDivString = (const lean_object*)&l_System_FilePath_instDiv___closed__0_value;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object*);
static const lean_string_object l_System_FilePath_fileName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l_System_FilePath_fileName___closed__0 = (const lean_object*)&l_System_FilePath_fileName___closed__0_value;
static const lean_string_object l_System_FilePath_fileName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_System_FilePath_fileName___closed__1 = (const lean_object*)&l_System_FilePath_fileName___closed__1_value;
static lean_object* l_System_FilePath_fileName___closed__2;
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_System_FilePath_extension___closed__0;
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object*, lean_object*);
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0;
static uint8_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2;
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6_value)}};
static const lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_System_FilePath_components___closed__0;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object*);
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object*);
static const lean_closure_object l_System_instCoeStringFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_System_instCoeStringFilePath___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_System_instCoeStringFilePath___closed__0 = (const lean_object*)&l_System_instCoeStringFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_System_instCoeStringFilePath = (const lean_object*)&l_System_instCoeStringFilePath___closed__0_value;
LEAN_EXPORT uint32_t l_System_SearchPath_separator;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___boxed(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(lean_object*, lean_object*);
static lean_object* l_System_SearchPath_toString___closed__0;
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object*);
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_System_instDecidableEqFilePath_decEq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_System_instDecidableEqFilePath(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_System_instHashableFilePath_hash(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = 0;
x_3 = lean_string_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_System_instHashableFilePath_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_System_instHashableFilePath_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = ((lean_object*)(l_System_instReprFilePath___lam__0___closed__1));
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Repr_addAppParen(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_instReprFilePath___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_instToStringFilePath___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static uint32_t _init_l_System_FilePath_pathSeparator() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint32_t x_2; 
x_2 = 47;
return x_2;
}
else
{
uint32_t x_3; 
x_3 = 92;
return x_3;
}
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_System_FilePath_pathSeparators___closed__0___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparators___closed__0;
x_2 = l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_System_FilePath_pathSeparators___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_System_FilePath_pathSeparators___closed__1;
return x_3;
}
}
}
static uint32_t _init_l_System_FilePath_extSeparator() {
_start:
{
uint32_t x_1; 
x_1 = 46;
return x_1;
}
}
static lean_object* _init_l_System_FilePath_exeExtension() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_System_FilePath_exeExtension___closed__0));
return x_3;
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00System_FilePath_normalize_spec__0(uint32_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_unbox_uint32(x_4);
x_7 = lean_uint32_dec_eq(x_1, x_6);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00System_FilePath_normalize_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_List_elem___at___00System_FilePath_normalize_spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_9; uint8_t x_10; 
x_9 = lean_string_utf8_byte_size(x_1);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_11 = l_System_FilePath_pathSeparators;
x_12 = lean_string_utf8_get_fast(x_1, x_2);
x_13 = l_List_elem___at___00System_FilePath_normalize_spec__0(x_12, x_11);
if (x_13 == 0)
{
x_3 = x_12;
goto block_8;
}
else
{
uint32_t x_14; 
x_14 = l_System_FilePath_pathSeparator;
x_3 = x_14;
goto block_8;
}
}
else
{
lean_dec(x_2);
return x_1;
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
x_4 = lean_string_utf8_set(x_1, x_2, x_3);
x_5 = l_Char_utf8Size(x_3);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_5);
lean_dec(x_2);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_System_FilePath_normalize___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_System_FilePath_pathSeparators;
x_2 = l_List_lengthTR___redArg(x_1);
return x_2;
}
}
static uint8_t _init_l_System_FilePath_normalize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_System_FilePath_normalize___closed__0;
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_7; uint32_t x_24; uint8_t x_30; uint8_t x_39; 
x_39 = l_System_Platform_isWindows;
if (x_39 == 0)
{
x_30 = x_39;
goto block_38;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_unsigned_to_nat(2u);
x_41 = lean_string_length(x_1);
x_42 = lean_nat_dec_le(x_40, x_41);
x_30 = x_42;
goto block_38;
}
block_6:
{
uint8_t x_3; 
x_3 = l_System_FilePath_normalize___closed__1;
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_mapAux___at___00System_FilePath_normalize_spec__1(x_2, x_4);
return x_5;
}
else
{
return x_2;
}
}
block_23:
{
if (x_7 == 0)
{
x_2 = x_1;
goto block_6;
}
else
{
lean_object* x_8; uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_string_utf8_get(x_1, x_8);
x_10 = 58;
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
x_2 = x_1;
goto block_6;
}
else
{
lean_object* x_12; uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_string_utf8_get(x_1, x_12);
x_14 = 97;
x_15 = lean_uint32_dec_le(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_string_utf8_set(x_1, x_12, x_13);
x_2 = x_16;
goto block_6;
}
else
{
uint32_t x_17; uint8_t x_18; 
x_17 = 122;
x_18 = lean_uint32_dec_le(x_13, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_string_utf8_set(x_1, x_12, x_13);
x_2 = x_19;
goto block_6;
}
else
{
uint32_t x_20; uint32_t x_21; lean_object* x_22; 
x_20 = 4294967264;
x_21 = lean_uint32_add(x_13, x_20);
x_22 = lean_string_utf8_set(x_1, x_12, x_21);
x_2 = x_22;
goto block_6;
}
}
}
}
}
block_29:
{
uint32_t x_25; uint8_t x_26; 
x_25 = 97;
x_26 = lean_uint32_dec_le(x_25, x_24);
if (x_26 == 0)
{
x_7 = x_26;
goto block_23;
}
else
{
uint32_t x_27; uint8_t x_28; 
x_27 = 122;
x_28 = lean_uint32_dec_le(x_24, x_27);
x_7 = x_28;
goto block_23;
}
}
block_38:
{
if (x_30 == 0)
{
x_2 = x_1;
goto block_6;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
x_34 = l_String_Slice_Pos_get_x3f(x_33, x_31);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 0)
{
uint32_t x_35; 
x_35 = 65;
x_24 = x_35;
goto block_29;
}
else
{
lean_object* x_36; uint32_t x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_unbox_uint32(x_36);
lean_dec(x_36);
x_24 = x_37;
goto block_29;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_unbox_uint32(x_6);
x_9 = lean_unbox_uint32(x_7);
x_10 = lean_uint32_dec_eq(x_8, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 58;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_6; lean_object* x_15; uint32_t x_16; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = l_System_FilePath_pathSeparators;
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_String_Slice_Pos_get_x3f(x_25, x_23);
lean_dec_ref(x_25);
if (lean_obj_tag(x_26) == 0)
{
uint32_t x_27; 
x_27 = 65;
x_16 = x_27;
goto block_22;
}
else
{
lean_object* x_28; uint32_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_unbox_uint32(x_28);
lean_dec(x_28);
x_16 = x_29;
goto block_22;
}
block_5:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_System_FilePath_isAbsolute___closed__0;
x_4 = l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0(x_2, x_3);
lean_dec(x_2);
return x_4;
}
block_14:
{
if (x_6 == 0)
{
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_utf8_byte_size(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = l_String_Slice_Pos_next_x3f(x_9, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_9);
x_11 = lean_box(0);
x_2 = x_11;
goto block_5;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_String_Slice_Pos_get_x3f(x_9, x_12);
lean_dec(x_12);
lean_dec_ref(x_9);
x_2 = x_13;
goto block_5;
}
}
}
block_22:
{
uint8_t x_17; 
x_17 = l_List_elem___at___00System_FilePath_normalize_spec__0(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_System_Platform_isWindows;
if (x_18 == 0)
{
x_6 = x_18;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_string_length(x_1);
x_21 = lean_nat_dec_lt(x_19, x_20);
x_6 = x_21;
goto block_14;
}
}
else
{
lean_dec_ref(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_System_FilePath_isAbsolute(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_FilePath_isAbsolute(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_System_FilePath_isRelative(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_join___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparator;
x_2 = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc_ref(x_2);
x_3 = l_System_FilePath_isAbsolute(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_System_FilePath_join___closed__0;
x_5 = lean_string_append(x_1, x_4);
x_6 = lean_string_append(x_5, x_2);
lean_dec_ref(x_2);
return x_6;
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_System_FilePath_pathSeparators;
x_9 = lean_nat_add(x_7, x_2);
lean_inc(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_nat_sub(x_9, x_7);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = l_String_Slice_Pos_prevAux_go___redArg(x_10, x_13);
lean_dec_ref(x_10);
x_15 = lean_nat_add(x_7, x_14);
x_16 = lean_string_utf8_get_fast(x_6, x_15);
lean_dec(x_15);
x_17 = l_List_elem___at___00System_FilePath_normalize_spec__0(x_16, x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = lean_nat_sub(x_2, x_12);
lean_dec(x_2);
x_20 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_19);
x_2 = x_20;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_14);
return x_22;
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_sub(x_3, x_2);
x_5 = lean_box(0);
x_6 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
x_5 = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(x_4);
lean_dec_ref(x_4);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(x_1, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_nat_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_16; lean_object* x_17; uint32_t x_18; lean_object* x_23; 
lean_inc_ref(x_1);
x_2 = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
x_23 = x_34;
goto block_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_string_utf8_extract(x_1, x_36, x_35);
lean_dec(x_35);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_23 = x_38;
goto block_33;
}
block_15:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_string_length(x_1);
x_6 = lean_nat_dec_eq(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0(x_2, x_9);
lean_dec_ref(x_9);
lean_dec(x_2);
if (x_10 == 0)
{
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_extract(x_1, x_11, x_4);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = lean_box(0);
return x_14;
}
}
block_22:
{
uint8_t x_19; 
x_19 = l_List_elem___at___00System_FilePath_normalize_spec__0(x_18, x_16);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_unsigned_to_nat(3u);
x_3 = x_17;
x_4 = x_20;
goto block_15;
}
else
{
lean_object* x_21; 
x_21 = lean_unsigned_to_nat(1u);
x_3 = x_17;
x_4 = x_21;
goto block_15;
}
}
block_33:
{
uint8_t x_24; 
lean_inc_ref(x_1);
x_24 = l_System_FilePath_isAbsolute(x_1);
if (x_24 == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_System_FilePath_pathSeparators;
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_String_Slice_Pos_get_x3f(x_28, x_26);
lean_dec_ref(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint32_t x_30; 
x_30 = 65;
x_16 = x_25;
x_17 = x_23;
x_18 = x_30;
goto block_22;
}
else
{
lean_object* x_31; uint32_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_unbox_uint32(x_31);
lean_dec(x_31);
x_16 = x_25;
x_17 = x_23;
x_18 = x_32;
goto block_22;
}
}
}
}
}
static lean_object* _init_l_System_FilePath_fileName___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = l_Char_utf8Size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_10; lean_object* x_17; 
lean_inc_ref(x_1);
x_17 = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(x_1);
if (lean_obj_tag(x_17) == 0)
{
x_10 = x_1;
goto block_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_System_FilePath_fileName___closed__2;
x_20 = lean_nat_add(x_18, x_19);
lean_dec(x_18);
x_21 = lean_string_utf8_byte_size(x_1);
x_22 = lean_string_utf8_extract(x_1, x_20, x_21);
lean_dec(x_20);
lean_dec_ref(x_1);
x_10 = x_22;
goto block_16;
}
block_9:
{
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_System_FilePath_fileName___closed__0));
x_5 = lean_string_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec_ref(x_2);
x_7 = lean_box(0);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec_ref(x_2);
x_8 = lean_box(0);
return x_8;
}
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_string_utf8_byte_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_System_FilePath_fileName___closed__1));
x_15 = lean_string_dec_eq(x_10, x_14);
x_2 = x_10;
x_3 = x_15;
goto block_9;
}
else
{
x_2 = x_10;
x_3 = x_13;
goto block_9;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = 46;
x_9 = lean_nat_add(x_7, x_2);
lean_inc(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_nat_sub(x_9, x_7);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = l_String_Slice_Pos_prevAux_go___redArg(x_10, x_13);
lean_dec_ref(x_10);
x_15 = lean_nat_add(x_7, x_14);
x_16 = lean_string_utf8_get_fast(x_6, x_15);
lean_dec(x_15);
x_17 = lean_uint32_dec_eq(x_16, x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = lean_nat_sub(x_2, x_12);
lean_dec(x_2);
x_20 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_19);
x_2 = x_20;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_14);
return x_22;
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_sub(x_3, x_2);
x_5 = lean_box(0);
x_6 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_fileName(x_1);
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_13 = lean_string_utf8_byte_size(x_3);
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_13);
x_16 = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(x_15);
lean_dec_ref(x_15);
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_4 = x_17;
goto block_12;
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec_ref(x_16);
x_4 = x_18;
goto block_12;
}
block_12:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_dec(x_8);
x_9 = lean_string_utf8_extract(x_3, x_5, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_string_utf8_extract(x_3, x_5, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(x_1, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_System_FilePath_extension___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 46;
x_2 = l_Char_utf8Size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_fileName(x_1);
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_4 = x_2;
} else {
 lean_dec_ref(x_2);
 x_4 = lean_box(0);
}
x_15 = lean_string_utf8_byte_size(x_3);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_15);
x_18 = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(x_17);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_5 = x_20;
goto block_14;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
x_5 = x_21;
goto block_14;
}
block_14:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_System_FilePath_extension___closed__0;
x_9 = lean_nat_add(x_5, x_8);
lean_dec(x_5);
x_10 = lean_string_utf8_byte_size(x_3);
x_11 = lean_string_utf8_extract(x_3, x_9, x_10);
lean_dec(x_9);
lean_dec(x_3);
if (lean_is_scalar(x_4)) {
 x_12 = lean_alloc_ctor(1, 1, 0);
} else {
 x_12 = x_4;
}
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_System_FilePath_join(x_4, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_System_FilePath_fileName(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = ((lean_object*)(l_System_FilePath_fileName___closed__1));
x_9 = lean_string_append(x_4, x_8);
x_10 = lean_string_append(x_9, x_2);
x_11 = l_System_FilePath_withFileName(x_1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_System_FilePath_withFileName(x_1, x_4);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_addExtension(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_System_FilePath_fileStem(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = ((lean_object*)(l_System_FilePath_fileName___closed__1));
x_9 = lean_string_append(x_4, x_8);
x_10 = lean_string_append(x_9, x_2);
x_11 = l_System_FilePath_withFileName(x_1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_System_FilePath_withFileName(x_1, x_4);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_withExtension(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_System_FilePath_join___closed__0;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0;
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_System_FilePath_join___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2;
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3;
x_3 = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2;
x_4 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1;
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7));
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_16 = x_4;
} else {
 lean_dec_ref(x_4);
 x_16 = lean_box(0);
}
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_34; 
lean_dec(x_16);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 2);
x_38 = lean_nat_sub(x_37, x_36);
x_39 = lean_nat_dec_eq(x_35, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_inc(x_35);
lean_ctor_set_tag(x_15, 1);
lean_inc(x_35);
x_21 = x_15;
x_22 = x_35;
x_23 = x_35;
goto block_31;
}
else
{
lean_object* x_40; 
lean_free_object(x_15);
x_40 = lean_box(3);
lean_inc(x_35);
x_21 = x_40;
x_22 = x_35;
x_23 = x_35;
goto block_31;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_15, 0);
lean_inc(x_41);
lean_dec(x_15);
x_42 = lean_ctor_get(x_2, 1);
x_43 = lean_ctor_get(x_2, 2);
x_44 = lean_nat_sub(x_43, x_42);
x_45 = lean_nat_dec_eq(x_41, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_inc(x_41);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
lean_inc(x_41);
x_21 = x_46;
x_22 = x_41;
x_23 = x_41;
goto block_31;
}
else
{
lean_object* x_47; 
x_47 = lean_box(3);
lean_inc(x_41);
x_21 = x_47;
x_22 = x_41;
x_23 = x_41;
goto block_31;
}
}
}
case 1:
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_15);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_15, 0);
x_50 = lean_string_utf8_next_fast(x_1, x_49);
lean_dec(x_49);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_50);
x_17 = x_15;
goto block_20;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_15, 0);
lean_inc(x_51);
lean_dec(x_15);
x_52 = lean_string_utf8_next_fast(x_1, x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_17 = x_53;
goto block_20;
}
}
case 2:
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_55 = lean_ctor_get(x_15, 0);
x_56 = lean_ctor_get(x_15, 1);
x_57 = lean_ctor_get(x_15, 2);
x_58 = lean_ctor_get(x_15, 3);
x_59 = lean_ctor_get(x_55, 0);
x_60 = lean_ctor_get(x_55, 1);
x_61 = lean_ctor_get(x_55, 2);
x_62 = lean_nat_sub(x_57, x_58);
x_63 = lean_nat_sub(x_61, x_60);
x_64 = lean_nat_add(x_62, x_63);
x_65 = lean_nat_dec_le(x_64, x_3);
lean_dec(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
lean_dec(x_63);
lean_free_object(x_15);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_56);
lean_dec_ref(x_55);
x_66 = lean_nat_dec_lt(x_62, x_3);
lean_dec(x_62);
if (x_66 == 0)
{
lean_dec(x_16);
goto block_33;
}
else
{
lean_object* x_67; 
x_67 = lean_box(3);
x_17 = x_67;
goto block_20;
}
}
else
{
uint8_t x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; 
lean_dec(x_62);
lean_inc(x_57);
x_68 = lean_string_get_byte_fast(x_1, x_57);
x_69 = lean_nat_add(x_60, x_58);
x_70 = lean_string_get_byte_fast(x_59, x_69);
x_71 = lean_uint8_dec_eq(x_68, x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_63);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_eq(x_58, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_sub(x_58, x_74);
lean_dec(x_58);
x_76 = lean_array_fget_borrowed(x_56, x_75);
lean_dec(x_75);
x_77 = lean_nat_dec_eq(x_76, x_72);
if (x_77 == 0)
{
lean_inc(x_76);
lean_ctor_set(x_15, 3, x_76);
x_17 = x_15;
goto block_20;
}
else
{
lean_object* x_78; 
x_78 = l_String_Slice_posGE___redArg(x_2, x_57);
lean_ctor_set(x_15, 3, x_72);
lean_ctor_set(x_15, 2, x_78);
x_17 = x_15;
goto block_20;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_58);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_57, x_79);
lean_dec(x_57);
x_81 = l_String_Slice_posGE___redArg(x_2, x_80);
lean_ctor_set(x_15, 3, x_72);
lean_ctor_set(x_15, 2, x_81);
x_17 = x_15;
goto block_20;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_16);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_57, x_82);
lean_dec(x_57);
x_84 = lean_nat_add(x_58, x_82);
lean_dec(x_58);
x_85 = lean_nat_dec_eq(x_84, x_63);
lean_dec(x_63);
if (x_85 == 0)
{
lean_object* x_86; 
lean_ctor_set(x_15, 3, x_84);
lean_ctor_set(x_15, 2, x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_14);
lean_ctor_set(x_86, 1, x_15);
x_4 = x_86;
goto _start;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_nat_sub(x_83, x_84);
lean_dec(x_84);
x_89 = l_String_Slice_pos_x21(x_2, x_88);
lean_dec(x_88);
x_90 = l_String_Slice_pos_x21(x_2, x_83);
x_91 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_15, 3, x_91);
lean_ctor_set(x_15, 2, x_83);
x_21 = x_15;
x_22 = x_89;
x_23 = x_90;
goto block_31;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_92 = lean_ctor_get(x_15, 0);
x_93 = lean_ctor_get(x_15, 1);
x_94 = lean_ctor_get(x_15, 2);
x_95 = lean_ctor_get(x_15, 3);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_15);
x_96 = lean_ctor_get(x_92, 0);
x_97 = lean_ctor_get(x_92, 1);
x_98 = lean_ctor_get(x_92, 2);
x_99 = lean_nat_sub(x_94, x_95);
x_100 = lean_nat_sub(x_98, x_97);
x_101 = lean_nat_add(x_99, x_100);
x_102 = lean_nat_dec_le(x_101, x_3);
lean_dec(x_101);
if (x_102 == 0)
{
uint8_t x_103; 
lean_dec(x_100);
lean_dec(x_95);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
x_103 = lean_nat_dec_lt(x_99, x_3);
lean_dec(x_99);
if (x_103 == 0)
{
lean_dec(x_16);
goto block_33;
}
else
{
lean_object* x_104; 
x_104 = lean_box(3);
x_17 = x_104;
goto block_20;
}
}
else
{
uint8_t x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
lean_dec(x_99);
lean_inc(x_94);
x_105 = lean_string_get_byte_fast(x_1, x_94);
x_106 = lean_nat_add(x_97, x_95);
x_107 = lean_string_get_byte_fast(x_96, x_106);
x_108 = lean_uint8_dec_eq(x_105, x_107);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
lean_dec(x_100);
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_nat_dec_eq(x_95, x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_sub(x_95, x_111);
lean_dec(x_95);
x_113 = lean_array_fget_borrowed(x_93, x_112);
lean_dec(x_112);
x_114 = lean_nat_dec_eq(x_113, x_109);
if (x_114 == 0)
{
lean_object* x_115; 
lean_inc(x_113);
x_115 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_115, 0, x_92);
lean_ctor_set(x_115, 1, x_93);
lean_ctor_set(x_115, 2, x_94);
lean_ctor_set(x_115, 3, x_113);
x_17 = x_115;
goto block_20;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = l_String_Slice_posGE___redArg(x_2, x_94);
x_117 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_117, 0, x_92);
lean_ctor_set(x_117, 1, x_93);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_109);
x_17 = x_117;
goto block_20;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_95);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_94, x_118);
lean_dec(x_94);
x_120 = l_String_Slice_posGE___redArg(x_2, x_119);
x_121 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_121, 0, x_92);
lean_ctor_set(x_121, 1, x_93);
lean_ctor_set(x_121, 2, x_120);
lean_ctor_set(x_121, 3, x_109);
x_17 = x_121;
goto block_20;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec(x_16);
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_add(x_94, x_122);
lean_dec(x_94);
x_124 = lean_nat_add(x_95, x_122);
lean_dec(x_95);
x_125 = lean_nat_dec_eq(x_124, x_100);
lean_dec(x_100);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_126, 0, x_92);
lean_ctor_set(x_126, 1, x_93);
lean_ctor_set(x_126, 2, x_123);
lean_ctor_set(x_126, 3, x_124);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_14);
lean_ctor_set(x_127, 1, x_126);
x_4 = x_127;
goto _start;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_nat_sub(x_123, x_124);
lean_dec(x_124);
x_130 = l_String_Slice_pos_x21(x_2, x_129);
lean_dec(x_129);
x_131 = l_String_Slice_pos_x21(x_2, x_123);
x_132 = lean_unsigned_to_nat(0u);
x_133 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_133, 0, x_92);
lean_ctor_set(x_133, 1, x_93);
lean_ctor_set(x_133, 2, x_123);
lean_ctor_set(x_133, 3, x_132);
x_21 = x_133;
x_22 = x_130;
x_23 = x_131;
goto block_31;
}
}
}
}
}
default: 
{
lean_dec(x_16);
goto block_33;
}
}
block_20:
{
lean_object* x_18; 
if (lean_is_scalar(x_16)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_16;
}
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_4 = x_18;
goto _start;
}
block_31:
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_String_Slice_subslice_x21(x_2, x_14, x_22);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_23);
x_6 = x_24;
x_7 = x_26;
x_8 = x_27;
goto block_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_21);
x_6 = x_30;
x_7 = x_28;
x_8 = x_29;
goto block_13;
}
}
block_33:
{
lean_object* x_32; 
x_32 = lean_box(1);
lean_inc(x_3);
x_6 = x_32;
x_7 = x_14;
x_8 = x_3;
goto block_13;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = l_String_Slice_toString(x_9);
lean_dec_ref(x_9);
x_11 = lean_array_push(x_5, x_10);
x_4 = x_6;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
static lean_object* _init_l_System_FilePath_components___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_System_FilePath_normalize(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_2);
lean_inc_ref(x_2);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(x_5);
x_7 = l_System_FilePath_components___closed__0;
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(x_2, x_5, x_4, x_6, x_7);
lean_dec_ref(x_5);
x_9 = lean_array_to_list(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_System_FilePath_join___closed__0;
x_3 = l_String_intercalate(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_instCoeStringFilePath___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static uint32_t _init_l_System_SearchPath_separator() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint32_t x_2; 
x_2 = 58;
return x_2;
}
else
{
uint32_t x_3; 
x_3 = 59;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_nat_sub(x_17, x_16);
x_19 = lean_nat_dec_eq(x_15, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint32_t x_20; uint32_t x_21; uint8_t x_22; 
x_20 = l_System_SearchPath_separator;
x_21 = lean_string_utf8_get_fast(x_1, x_15);
x_22 = lean_uint32_dec_eq(x_21, x_20);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_string_utf8_next_fast(x_1, x_15);
lean_dec(x_15);
lean_ctor_set(x_4, 1, x_23);
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_string_utf8_next_fast(x_1, x_15);
x_26 = lean_nat_sub(x_25, x_15);
x_27 = lean_nat_add(x_15, x_26);
lean_dec(x_26);
x_28 = l_String_Slice_subslice_x21(x_2, x_14, x_15);
lean_inc(x_27);
lean_ctor_set(x_4, 1, x_27);
lean_ctor_set(x_4, 0, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_6 = x_4;
x_7 = x_29;
x_8 = x_30;
goto block_12;
}
}
else
{
lean_object* x_31; 
lean_free_object(x_4);
lean_dec(x_15);
x_31 = lean_box(1);
lean_inc(x_3);
x_6 = x_31;
x_7 = x_14;
x_8 = x_3;
goto block_12;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_nat_sub(x_35, x_34);
x_37 = lean_nat_dec_eq(x_33, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint32_t x_38; uint32_t x_39; uint8_t x_40; 
x_38 = l_System_SearchPath_separator;
x_39 = lean_string_utf8_get_fast(x_1, x_33);
x_40 = lean_uint32_dec_eq(x_39, x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_string_utf8_next_fast(x_1, x_33);
lean_dec(x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_32);
lean_ctor_set(x_42, 1, x_41);
x_4 = x_42;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_string_utf8_next_fast(x_1, x_33);
x_45 = lean_nat_sub(x_44, x_33);
x_46 = lean_nat_add(x_33, x_45);
lean_dec(x_45);
x_47 = l_String_Slice_subslice_x21(x_2, x_32, x_33);
lean_inc(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec_ref(x_47);
x_6 = x_48;
x_7 = x_49;
x_8 = x_50;
goto block_12;
}
}
else
{
lean_object* x_51; 
lean_dec(x_33);
x_51 = lean_box(1);
lean_inc(x_3);
x_6 = x_51;
x_7 = x_32;
x_8 = x_3;
goto block_12;
}
}
}
else
{
lean_dec(x_3);
return x_5;
}
block_12:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_string_utf8_extract(x_1, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_array_push(x_5, x_9);
x_4 = x_6;
x_5 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(x_4);
x_6 = l_System_FilePath_components___closed__0;
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(x_1, x_4, x_3, x_5, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_8 = lean_array_to_list(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l_System_SearchPath_toString___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_SearchPath_separator;
x_2 = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_System_SearchPath_toString___closed__0;
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(x_1, x_3);
x_5 = l_String_intercalate(x_2, x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_FilePath(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_System_FilePath_pathSeparator = _init_l_System_FilePath_pathSeparator();
l_System_FilePath_pathSeparators___closed__0___boxed__const__1 = _init_l_System_FilePath_pathSeparators___closed__0___boxed__const__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__0___boxed__const__1);
l_System_FilePath_pathSeparators___closed__0 = _init_l_System_FilePath_pathSeparators___closed__0();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__0);
l_System_FilePath_pathSeparators___closed__1___boxed__const__1 = _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__1___boxed__const__1);
l_System_FilePath_pathSeparators___closed__1 = _init_l_System_FilePath_pathSeparators___closed__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__1);
l_System_FilePath_pathSeparators = _init_l_System_FilePath_pathSeparators();
lean_mark_persistent(l_System_FilePath_pathSeparators);
l_System_FilePath_extSeparator = _init_l_System_FilePath_extSeparator();
l_System_FilePath_exeExtension = _init_l_System_FilePath_exeExtension();
lean_mark_persistent(l_System_FilePath_exeExtension);
l_System_FilePath_normalize___closed__0 = _init_l_System_FilePath_normalize___closed__0();
lean_mark_persistent(l_System_FilePath_normalize___closed__0);
l_System_FilePath_normalize___closed__1 = _init_l_System_FilePath_normalize___closed__1();
l_System_FilePath_isAbsolute___closed__0___boxed__const__1 = _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1();
lean_mark_persistent(l_System_FilePath_isAbsolute___closed__0___boxed__const__1);
l_System_FilePath_isAbsolute___closed__0 = _init_l_System_FilePath_isAbsolute___closed__0();
lean_mark_persistent(l_System_FilePath_isAbsolute___closed__0);
l_System_FilePath_join___closed__0 = _init_l_System_FilePath_join___closed__0();
lean_mark_persistent(l_System_FilePath_join___closed__0);
l_System_FilePath_fileName___closed__2 = _init_l_System_FilePath_fileName___closed__2();
lean_mark_persistent(l_System_FilePath_fileName___closed__2);
l_System_FilePath_extension___closed__0 = _init_l_System_FilePath_extension___closed__0();
lean_mark_persistent(l_System_FilePath_extension___closed__0);
l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0 = _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0();
lean_mark_persistent(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1 = _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1();
l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2 = _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2();
lean_mark_persistent(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2);
l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3 = _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3();
lean_mark_persistent(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3);
l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4 = _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4();
lean_mark_persistent(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4);
l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5 = _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5();
lean_mark_persistent(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5);
l_System_FilePath_components___closed__0 = _init_l_System_FilePath_components___closed__0();
lean_mark_persistent(l_System_FilePath_components___closed__0);
l_System_SearchPath_separator = _init_l_System_SearchPath_separator();
l_System_SearchPath_toString___closed__0 = _init_l_System_SearchPath_toString___closed__0();
lean_mark_persistent(l_System_SearchPath_toString___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
