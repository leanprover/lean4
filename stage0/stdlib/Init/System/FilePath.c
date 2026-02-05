// Lean compiler output
// Module: Init.System.FilePath
// Imports: public import Init.Data.String.Basic import Init.Data.String.Modify import Init.Data.String.Search
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
LEAN_EXPORT uint8_t l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevAux_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___closed__0;
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
static lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0;
static uint8_t l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__1;
static lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2;
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
static lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__3;
static lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__4;
static lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__5;
static const lean_ctor_object l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__6 = (const lean_object*)&l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__6_value;
static const lean_ctor_object l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__6_value)}};
static const lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__7 = (const lean_object*)&l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__7_value;
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___boxed(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_System_FilePath_components___closed__0;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object*);
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object*);
static const lean_closure_object l_System_instCoeStringFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_System_instCoeStringFilePath___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_System_instCoeStringFilePath___closed__0 = (const lean_object*)&l_System_instCoeStringFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_System_instCoeStringFilePath = (const lean_object*)&l_System_instCoeStringFilePath___closed__0_value;
LEAN_EXPORT uint32_t l_System_SearchPath_separator;
static const lean_ctor_object l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__0 = (const lean_object*)&l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_SearchPath_parse_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_SearchPath_parse_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___lam__0(lean_object* x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_List_elem___at___00System_FilePath_normalize_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___lam__0(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_13 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_12);
lean_inc_ref(x_6);
lean_inc(x_13);
lean_ctor_set(x_2, 0, x_13);
x_14 = lean_nat_add(x_10, x_13);
x_15 = lean_string_utf8_get_fast(x_9, x_14);
lean_dec(x_14);
x_16 = lean_box_uint32(x_15);
x_17 = lean_apply_1(x_6, x_16);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_13);
x_19 = lean_box(0);
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec_ref(x_2);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_13);
return x_21;
}
}
else
{
lean_free_object(x_2);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_3;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_22, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_3);
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_22, x_28);
lean_dec(x_22);
x_30 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_29);
lean_inc_ref(x_23);
lean_inc(x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
x_32 = lean_nat_add(x_27, x_30);
x_33 = lean_string_utf8_get_fast(x_26, x_32);
lean_dec(x_32);
x_34 = lean_box_uint32(x_33);
x_35 = lean_apply_1(x_23, x_34);
x_36 = lean_unbox(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_30);
x_37 = lean_box(0);
x_2 = x_31;
x_3 = x_37;
goto _start;
}
else
{
lean_object* x_39; 
lean_dec_ref(x_31);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_30);
return x_39;
}
}
else
{
lean_dec_ref(x_23);
lean_dec(x_22);
return x_3;
}
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
static lean_object* _init_l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_System_FilePath_pathSeparators;
x_2 = lean_alloc_closure((void*)(l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___closed__0;
x_5 = lean_nat_sub(x_3, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_box(0);
x_8 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(x_1, x_6, x_7);
return x_8;
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
x_19 = l_List_elem___at___00System_FilePath_normalize_spec__0(x_18, x_17);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_unsigned_to_nat(3u);
x_3 = x_16;
x_4 = x_20;
goto block_15;
}
else
{
lean_object* x_21; 
x_21 = lean_unsigned_to_nat(1u);
x_3 = x_16;
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
x_16 = x_23;
x_17 = x_25;
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
x_16 = x_23;
x_17 = x_25;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint32(x_2, sizeof(void*)*1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; uint8_t x_16; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_13 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_12);
lean_inc(x_13);
lean_ctor_set(x_2, 0, x_13);
x_14 = lean_nat_add(x_10, x_13);
x_15 = lean_string_utf8_get_fast(x_9, x_14);
lean_dec(x_14);
x_16 = lean_uint32_dec_eq(x_15, x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
x_17 = lean_box(0);
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_19; 
lean_dec_ref(x_2);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_13);
return x_19;
}
}
else
{
lean_free_object(x_2);
lean_dec(x_5);
return x_3;
}
}
else
{
lean_object* x_20; uint32_t x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get_uint32(x_2, sizeof(void*)*1);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_20, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; uint8_t x_32; 
lean_dec(x_3);
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_20, x_26);
lean_dec(x_20);
x_28 = l_String_Slice_Pos_prevAux_go___redArg(x_1, x_27);
lean_inc(x_28);
x_29 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint32(x_29, sizeof(void*)*1, x_21);
x_30 = lean_nat_add(x_25, x_28);
x_31 = lean_string_utf8_get_fast(x_24, x_30);
lean_dec(x_30);
x_32 = lean_uint32_dec_eq(x_31, x_21);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_28);
x_33 = lean_box(0);
x_2 = x_29;
x_3 = x_33;
goto _start;
}
else
{
lean_object* x_35; 
lean_dec_ref(x_29);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_28);
return x_35;
}
}
else
{
lean_dec(x_20);
return x_3;
}
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
lean_object* x_2; lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = 46;
x_5 = lean_nat_sub(x_3, x_2);
x_6 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set_uint32(x_6, sizeof(void*)*1, x_4);
x_7 = lean_box(0);
x_8 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(x_1, x_6, x_7);
return x_8;
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
static lean_object* _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_System_FilePath_join___closed__0;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static uint8_t _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0;
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_System_FilePath_join___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2;
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__3;
x_3 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2;
x_4 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__1;
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__5;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = ((lean_object*)(l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__7));
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_FilePath_components_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00System_FilePath_components_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_17 = x_5;
} else {
 lean_dec_ref(x_5);
 x_17 = lean_box(0);
}
switch (lean_obj_tag(x_16)) {
case 0:
{
uint8_t x_33; 
lean_dec(x_17);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_nat_sub(x_36, x_35);
x_38 = lean_nat_dec_eq(x_34, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_inc(x_34);
lean_ctor_set_tag(x_16, 1);
lean_inc(x_34);
x_22 = x_16;
x_23 = x_34;
x_24 = x_34;
goto block_30;
}
else
{
lean_object* x_39; 
lean_free_object(x_16);
x_39 = lean_box(3);
lean_inc(x_34);
x_22 = x_39;
x_23 = x_34;
x_24 = x_34;
goto block_30;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
lean_dec(x_16);
x_41 = lean_ctor_get(x_1, 1);
x_42 = lean_ctor_get(x_1, 2);
x_43 = lean_nat_sub(x_42, x_41);
x_44 = lean_nat_dec_eq(x_40, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_inc(x_40);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
lean_inc(x_40);
x_22 = x_45;
x_23 = x_40;
x_24 = x_40;
goto block_30;
}
else
{
lean_object* x_46; 
x_46 = lean_box(3);
lean_inc(x_40);
x_22 = x_46;
x_23 = x_40;
x_24 = x_40;
goto block_30;
}
}
}
case 1:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_16, 0);
x_49 = lean_string_utf8_next_fast(x_2, x_48);
lean_dec(x_48);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_49);
x_18 = x_16;
goto block_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_16, 0);
lean_inc(x_50);
lean_dec(x_16);
x_51 = lean_string_utf8_next_fast(x_2, x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_18 = x_52;
goto block_21;
}
}
case 2:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_16);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_16, 0);
x_55 = lean_ctor_get(x_16, 1);
x_56 = lean_ctor_get(x_16, 2);
x_57 = lean_ctor_get(x_16, 3);
x_58 = lean_nat_dec_lt(x_56, x_4);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
lean_free_object(x_16);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_lt(x_59, x_57);
lean_dec(x_57);
if (x_60 == 0)
{
lean_dec(x_17);
goto block_32;
}
else
{
lean_object* x_61; 
x_61 = lean_box(3);
x_18 = x_61;
goto block_21;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; 
x_62 = lean_ctor_get(x_54, 0);
x_63 = lean_ctor_get(x_54, 1);
x_64 = lean_ctor_get(x_54, 2);
lean_inc(x_56);
x_65 = lean_string_get_byte_fast(x_2, x_56);
x_66 = lean_nat_add(x_63, x_57);
x_67 = lean_string_get_byte_fast(x_62, x_66);
x_68 = lean_uint8_dec_eq(x_65, x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_eq(x_57, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_sub(x_57, x_71);
lean_dec(x_57);
x_73 = lean_array_fget_borrowed(x_55, x_72);
lean_dec(x_72);
x_74 = lean_nat_dec_eq(x_73, x_69);
if (x_74 == 0)
{
lean_inc(x_73);
lean_ctor_set(x_16, 3, x_73);
x_18 = x_16;
goto block_21;
}
else
{
lean_object* x_75; 
x_75 = l_String_Slice_posGE___redArg(x_1, x_56);
lean_ctor_set(x_16, 3, x_69);
lean_ctor_set(x_16, 2, x_75);
x_18 = x_16;
goto block_21;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_57);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_add(x_56, x_76);
lean_dec(x_56);
x_78 = l_String_Slice_posGE___redArg(x_1, x_77);
lean_ctor_set(x_16, 3, x_69);
lean_ctor_set(x_16, 2, x_78);
x_18 = x_16;
goto block_21;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_17);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_56, x_79);
lean_dec(x_56);
x_81 = lean_nat_add(x_57, x_79);
lean_dec(x_57);
x_82 = lean_nat_sub(x_64, x_63);
x_83 = lean_nat_dec_eq(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_82);
lean_ctor_set(x_16, 3, x_81);
lean_ctor_set(x_16, 2, x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_15);
lean_ctor_set(x_84, 1, x_16);
x_5 = x_84;
goto _start;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_81);
x_86 = lean_nat_sub(x_80, x_82);
lean_dec(x_82);
x_87 = l_String_Slice_pos_x21(x_1, x_86);
lean_dec(x_86);
x_88 = l_String_Slice_pos_x21(x_1, x_80);
x_89 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_16, 3, x_89);
lean_ctor_set(x_16, 2, x_80);
x_22 = x_16;
x_23 = x_87;
x_24 = x_88;
goto block_30;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_16, 0);
x_91 = lean_ctor_get(x_16, 1);
x_92 = lean_ctor_get(x_16, 2);
x_93 = lean_ctor_get(x_16, 3);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_16);
x_94 = lean_nat_dec_lt(x_92, x_4);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec_ref(x_90);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_nat_dec_lt(x_95, x_93);
lean_dec(x_93);
if (x_96 == 0)
{
lean_dec(x_17);
goto block_32;
}
else
{
lean_object* x_97; 
x_97 = lean_box(3);
x_18 = x_97;
goto block_21;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_90, 0);
x_99 = lean_ctor_get(x_90, 1);
x_100 = lean_ctor_get(x_90, 2);
lean_inc(x_92);
x_101 = lean_string_get_byte_fast(x_2, x_92);
x_102 = lean_nat_add(x_99, x_93);
x_103 = lean_string_get_byte_fast(x_98, x_102);
x_104 = lean_uint8_dec_eq(x_101, x_103);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_unsigned_to_nat(0u);
x_106 = lean_nat_dec_eq(x_93, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_nat_sub(x_93, x_107);
lean_dec(x_93);
x_109 = lean_array_fget_borrowed(x_91, x_108);
lean_dec(x_108);
x_110 = lean_nat_dec_eq(x_109, x_105);
if (x_110 == 0)
{
lean_object* x_111; 
lean_inc(x_109);
x_111 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_111, 0, x_90);
lean_ctor_set(x_111, 1, x_91);
lean_ctor_set(x_111, 2, x_92);
lean_ctor_set(x_111, 3, x_109);
x_18 = x_111;
goto block_21;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = l_String_Slice_posGE___redArg(x_1, x_92);
x_113 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_113, 0, x_90);
lean_ctor_set(x_113, 1, x_91);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set(x_113, 3, x_105);
x_18 = x_113;
goto block_21;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_93);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_nat_add(x_92, x_114);
lean_dec(x_92);
x_116 = l_String_Slice_posGE___redArg(x_1, x_115);
x_117 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_117, 0, x_90);
lean_ctor_set(x_117, 1, x_91);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_105);
x_18 = x_117;
goto block_21;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_17);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_92, x_118);
lean_dec(x_92);
x_120 = lean_nat_add(x_93, x_118);
lean_dec(x_93);
x_121 = lean_nat_sub(x_100, x_99);
x_122 = lean_nat_dec_eq(x_120, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_121);
x_123 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_123, 0, x_90);
lean_ctor_set(x_123, 1, x_91);
lean_ctor_set(x_123, 2, x_119);
lean_ctor_set(x_123, 3, x_120);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_15);
lean_ctor_set(x_124, 1, x_123);
x_5 = x_124;
goto _start;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_120);
x_126 = lean_nat_sub(x_119, x_121);
lean_dec(x_121);
x_127 = l_String_Slice_pos_x21(x_1, x_126);
lean_dec(x_126);
x_128 = l_String_Slice_pos_x21(x_1, x_119);
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_130, 0, x_90);
lean_ctor_set(x_130, 1, x_91);
lean_ctor_set(x_130, 2, x_119);
lean_ctor_set(x_130, 3, x_129);
x_22 = x_130;
x_23 = x_127;
x_24 = x_128;
goto block_30;
}
}
}
}
}
default: 
{
lean_dec(x_17);
goto block_32;
}
}
block_21:
{
lean_object* x_19; 
if (lean_is_scalar(x_17)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_17;
}
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_5 = x_19;
goto _start;
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_1);
x_25 = l_String_Slice_slice_x21(x_1, x_15, x_23);
lean_dec(x_23);
lean_dec(x_15);
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 2);
lean_inc(x_28);
lean_dec_ref(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_22);
x_7 = x_29;
x_8 = x_26;
x_9 = x_27;
x_10 = x_28;
goto block_14;
}
block_32:
{
lean_object* x_31; 
x_31 = lean_box(1);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = x_31;
x_8 = x_2;
x_9 = x_15;
x_10 = x_3;
goto block_14;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
block_14:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_string_utf8_extract(x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_12 = lean_array_push(x_6, x_11);
x_5 = x_7;
x_6 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
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
x_6 = l_String_Slice_split___at___00System_FilePath_components_spec__0(x_5);
x_7 = l_System_FilePath_components___closed__0;
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(x_5, x_2, x_4, x_4, x_6, x_7);
x_9 = lean_array_to_list(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
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
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_SearchPath_parse_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_String_Slice_split___at___00System_SearchPath_parse_spec__0___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00System_SearchPath_parse_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00System_SearchPath_parse_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_nat_sub(x_18, x_17);
x_20 = lean_nat_dec_eq(x_16, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint32_t x_21; lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_21 = l_System_SearchPath_separator;
x_22 = lean_string_utf8_next_fast(x_2, x_16);
x_23 = lean_string_utf8_get_fast(x_2, x_16);
x_24 = lean_uint32_dec_eq(x_23, x_21);
if (x_24 == 0)
{
lean_dec(x_16);
lean_ctor_set(x_4, 1, x_22);
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_1);
x_26 = l_String_Slice_slice_x21(x_1, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
lean_ctor_set(x_4, 1, x_22);
lean_ctor_set(x_4, 0, x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 2);
lean_inc(x_29);
lean_dec_ref(x_26);
x_6 = x_4;
x_7 = x_27;
x_8 = x_28;
x_9 = x_29;
goto block_13;
}
}
else
{
lean_object* x_30; 
lean_free_object(x_4);
lean_dec(x_16);
x_30 = lean_box(1);
lean_inc(x_3);
lean_inc_ref(x_2);
x_6 = x_30;
x_7 = x_2;
x_8 = x_15;
x_9 = x_3;
goto block_13;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_4, 0);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_4);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_nat_sub(x_34, x_33);
x_36 = lean_nat_dec_eq(x_32, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
uint32_t x_37; lean_object* x_38; uint32_t x_39; uint8_t x_40; 
x_37 = l_System_SearchPath_separator;
x_38 = lean_string_utf8_next_fast(x_2, x_32);
x_39 = lean_string_utf8_get_fast(x_2, x_32);
x_40 = lean_uint32_dec_eq(x_39, x_37);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_38);
x_4 = x_41;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc_ref(x_1);
x_43 = l_String_Slice_slice_x21(x_1, x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_38);
x_45 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 2);
lean_inc(x_47);
lean_dec_ref(x_43);
x_6 = x_44;
x_7 = x_45;
x_8 = x_46;
x_9 = x_47;
goto block_13;
}
}
else
{
lean_object* x_48; 
lean_dec(x_32);
x_48 = lean_box(1);
lean_inc(x_3);
lean_inc_ref(x_2);
x_6 = x_48;
x_7 = x_2;
x_8 = x_31;
x_9 = x_3;
goto block_13;
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
block_13:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_string_utf8_extract(x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_11 = lean_array_push(x_5, x_10);
x_4 = x_6;
x_5 = x_11;
goto _start;
}
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
x_5 = l_String_Slice_split___at___00System_SearchPath_parse_spec__0(x_4);
x_6 = l_System_FilePath_components___closed__0;
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(x_4, x_1, x_3, x_5, x_6);
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
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_FilePath(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
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
l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___closed__0 = _init_l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___closed__0();
lean_mark_persistent(l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___closed__0);
l_System_FilePath_fileName___closed__2 = _init_l_System_FilePath_fileName___closed__2();
lean_mark_persistent(l_System_FilePath_fileName___closed__2);
l_System_FilePath_extension___closed__0 = _init_l_System_FilePath_extension___closed__0();
lean_mark_persistent(l_System_FilePath_extension___closed__0);
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0();
lean_mark_persistent(l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__0);
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__1 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__1();
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2();
lean_mark_persistent(l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__2);
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__3 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__3();
lean_mark_persistent(l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__3);
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__4 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__4();
lean_mark_persistent(l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__4);
l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__5 = _init_l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__5();
lean_mark_persistent(l_String_Slice_split___at___00System_FilePath_components_spec__0___closed__5);
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
