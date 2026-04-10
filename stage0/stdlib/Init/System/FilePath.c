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
extern uint8_t l_System_Platform_isWindows;
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_next_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
static const lean_string_object l_System_instInhabitedFilePath_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_System_instInhabitedFilePath_default___closed__0 = (const lean_object*)&l_System_instInhabitedFilePath_default___closed__0_value;
LEAN_EXPORT const lean_object* l_System_instInhabitedFilePath_default = (const lean_object*)&l_System_instInhabitedFilePath_default___closed__0_value;
LEAN_EXPORT const lean_object* l_System_instInhabitedFilePath = (const lean_object*)&l_System_instInhabitedFilePath_default___closed__0_value;
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_System_instHashableFilePath_hash(lean_object*);
LEAN_EXPORT lean_object* l_System_instHashableFilePath_hash___boxed(lean_object*);
static const lean_closure_object l_System_instHashableFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_System_instHashableFilePath_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_System_instHashableFilePath___closed__0 = (const lean_object*)&l_System_instHashableFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_System_instHashableFilePath = (const lean_object*)&l_System_instHashableFilePath___closed__0_value;
static const lean_string_object l_System_instReprFilePath___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_System_instReprFilePath___lam__0___closed__0 = (const lean_object*)&l_System_instReprFilePath___lam__0___closed__0_value;
static const lean_ctor_object l_System_instReprFilePath___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_System_instReprFilePath___lam__0___closed__0_value)}};
static const lean_object* l_System_instReprFilePath___lam__0___closed__1 = (const lean_object*)&l_System_instReprFilePath___lam__0___closed__1_value;
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
LEAN_EXPORT uint32_t l_System_FilePath_pathSeparator;
LEAN_EXPORT lean_object* l_System_FilePath_pathSeparators___closed__0___boxed__const__1;
static lean_once_cell_t l_System_FilePath_pathSeparators___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_FilePath_pathSeparators___closed__0;
LEAN_EXPORT lean_object* l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
static lean_once_cell_t l_System_FilePath_pathSeparators___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_FilePath_pathSeparators___closed__1;
LEAN_EXPORT lean_object* l_System_FilePath_pathSeparators;
LEAN_EXPORT uint32_t l_System_FilePath_extSeparator;
static const lean_string_object l_System_FilePath_exeExtension___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "exe"};
static const lean_object* l_System_FilePath_exeExtension___closed__0 = (const lean_object*)&l_System_FilePath_exeExtension___closed__0_value;
LEAN_EXPORT lean_object* l_System_FilePath_exeExtension;
LEAN_EXPORT uint8_t l_List_elem___at___00System_FilePath_normalize_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00System_FilePath_normalize_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_System_FilePath_normalize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_FilePath_normalize___closed__0;
static lean_once_cell_t l_System_FilePath_normalize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_System_FilePath_normalize___closed__1;
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
static lean_once_cell_t l_System_FilePath_isAbsolute___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_FilePath_isAbsolute___closed__0;
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object*);
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object*);
static lean_once_cell_t l_System_FilePath_join___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_FilePath_join___closed__0;
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static const lean_closure_object l_System_FilePath_instDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_System_FilePath_join, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_System_FilePath_instDiv___closed__0 = (const lean_object*)&l_System_FilePath_instDiv___closed__0_value;
LEAN_EXPORT const lean_object* l_System_FilePath_instDiv = (const lean_object*)&l_System_FilePath_instDiv___closed__0_value;
LEAN_EXPORT const lean_object* l_System_FilePath_instHDivString = (const lean_object*)&l_System_FilePath_instDiv___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object*);
static const lean_string_object l_System_FilePath_fileName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l_System_FilePath_fileName___closed__0 = (const lean_object*)&l_System_FilePath_fileName___closed__0_value;
static const lean_string_object l_System_FilePath_fileName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_System_FilePath_fileName___closed__1 = (const lean_object*)&l_System_FilePath_fileName___closed__1_value;
static lean_once_cell_t l_System_FilePath_fileName___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_FilePath_fileName___closed__2;
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_System_FilePath_extension___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_FilePath_extension___closed__0;
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6_value)}};
static const lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_System_FilePath_components___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_System_FilePath_components___closed__0 = (const lean_object*)&l_System_FilePath_components___closed__0_value;
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_System_SearchPath_toString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_SearchPath_toString___closed__0;
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object*);
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath_decEq(lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_string_dec_eq(v_x_4_, v_x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath_decEq___boxed(lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_System_instDecidableEqFilePath_decEq(v_x_7_, v_x_8_);
lean_dec_ref(v_x_8_);
lean_dec_ref(v_x_7_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath(lean_object* v_x_11_, lean_object* v_x_12_){
_start:
{
uint8_t v___x_13_; 
v___x_13_ = lean_string_dec_eq(v_x_11_, v_x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath___boxed(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_System_instDecidableEqFilePath(v_x_14_, v_x_15_);
lean_dec_ref(v_x_15_);
lean_dec_ref(v_x_14_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint64_t l_System_instHashableFilePath_hash(lean_object* v_x_18_){
_start:
{
uint64_t v___x_19_; uint64_t v___x_20_; uint64_t v___x_21_; 
v___x_19_ = 0ULL;
v___x_20_ = lean_string_hash(v_x_18_);
v___x_21_ = lean_uint64_mix_hash(v___x_19_, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_System_instHashableFilePath_hash___boxed(lean_object* v_x_22_){
_start:
{
uint64_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_System_instHashableFilePath_hash(v_x_22_);
lean_dec_ref(v_x_22_);
v_r_24_ = lean_box_uint64(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0(lean_object* v_p_30_, lean_object* v___y_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_32_ = ((lean_object*)(l_System_instReprFilePath___lam__0___closed__1));
v___x_33_ = l_String_quote(v_p_30_);
v___x_34_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
v___x_35_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_32_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
v___x_36_ = l_Repr_addAppParen(v___x_35_, v___y_31_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0___boxed(lean_object* v_p_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_System_instReprFilePath___lam__0(v_p_37_, v___y_38_);
lean_dec(v___y_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0(lean_object* v_p_42_){
_start:
{
lean_inc_ref(v_p_42_);
return v_p_42_;
}
}
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0___boxed(lean_object* v_p_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_System_instToStringFilePath___lam__0(v_p_43_);
lean_dec_ref(v_p_43_);
return v_res_44_;
}
}
static uint32_t _init_l_System_FilePath_pathSeparator(void){
_start:
{
uint8_t v___x_47_; 
v___x_47_ = l_System_Platform_isWindows;
if (v___x_47_ == 0)
{
uint32_t v___x_48_; 
v___x_48_ = 47;
return v___x_48_;
}
else
{
uint32_t v___x_49_; 
v___x_49_ = 92;
return v___x_49_;
}
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_50_; lean_object* v___x_51_; 
v___x_50_ = 47;
v___x_51_ = lean_box_uint32(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__0(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_box(0);
v___x_53_ = l_System_FilePath_pathSeparators___closed__0___boxed__const__1;
v___x_54_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_55_; lean_object* v___x_56_; 
v___x_55_ = 92;
v___x_56_ = lean_box_uint32(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__1(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_obj_once(&l_System_FilePath_pathSeparators___closed__0, &l_System_FilePath_pathSeparators___closed__0_once, _init_l_System_FilePath_pathSeparators___closed__0);
v___x_58_ = l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators(void){
_start:
{
uint8_t v___x_60_; 
v___x_60_ = l_System_Platform_isWindows;
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_obj_once(&l_System_FilePath_pathSeparators___closed__0, &l_System_FilePath_pathSeparators___closed__0_once, _init_l_System_FilePath_pathSeparators___closed__0);
return v___x_61_;
}
else
{
lean_object* v___x_62_; 
v___x_62_ = lean_obj_once(&l_System_FilePath_pathSeparators___closed__1, &l_System_FilePath_pathSeparators___closed__1_once, _init_l_System_FilePath_pathSeparators___closed__1);
return v___x_62_;
}
}
}
static uint32_t _init_l_System_FilePath_extSeparator(void){
_start:
{
uint32_t v___x_63_; 
v___x_63_ = 46;
return v___x_63_;
}
}
static lean_object* _init_l_System_FilePath_exeExtension(void){
_start:
{
uint8_t v___x_65_; 
v___x_65_ = l_System_Platform_isWindows;
if (v___x_65_ == 0)
{
lean_object* v___x_66_; 
v___x_66_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
return v___x_66_;
}
else
{
lean_object* v___x_67_; 
v___x_67_ = ((lean_object*)(l_System_FilePath_exeExtension___closed__0));
return v___x_67_;
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00System_FilePath_normalize_spec__0(uint32_t v_a_68_, lean_object* v_x_69_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
uint8_t v___x_70_; 
v___x_70_ = 0;
return v___x_70_;
}
else
{
lean_object* v_head_71_; lean_object* v_tail_72_; uint32_t v___x_73_; uint8_t v___x_74_; 
v_head_71_ = lean_ctor_get(v_x_69_, 0);
v_tail_72_ = lean_ctor_get(v_x_69_, 1);
v___x_73_ = lean_unbox_uint32(v_head_71_);
v___x_74_ = lean_uint32_dec_eq(v_a_68_, v___x_73_);
if (v___x_74_ == 0)
{
v_x_69_ = v_tail_72_;
goto _start;
}
else
{
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00System_FilePath_normalize_spec__0___boxed(lean_object* v_a_76_, lean_object* v_x_77_){
_start:
{
uint32_t v_a_boxed_78_; uint8_t v_res_79_; lean_object* v_r_80_; 
v_a_boxed_78_ = lean_unbox_uint32(v_a_76_);
lean_dec(v_a_76_);
v_res_79_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v_a_boxed_78_, v_x_77_);
lean_dec(v_x_77_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1(lean_object* v_s_81_, lean_object* v_p_82_){
_start:
{
uint32_t v___y_84_; lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_string_utf8_byte_size(v_s_81_);
v___x_90_ = lean_nat_dec_eq(v_p_82_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; uint32_t v___x_92_; uint8_t v___x_93_; 
v___x_91_ = l_System_FilePath_pathSeparators;
v___x_92_ = lean_string_utf8_get_fast(v_s_81_, v_p_82_);
v___x_93_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_92_, v___x_91_);
if (v___x_93_ == 0)
{
v___y_84_ = v___x_92_;
goto v___jp_83_;
}
else
{
uint32_t v___x_94_; 
v___x_94_ = l_System_FilePath_pathSeparator;
v___y_84_ = v___x_94_;
goto v___jp_83_;
}
}
else
{
lean_dec(v_p_82_);
return v_s_81_;
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
lean_inc(v_p_82_);
v___x_85_ = lean_string_utf8_set(v_s_81_, v_p_82_, v___y_84_);
v___x_86_ = l_Char_utf8Size(v___y_84_);
v___x_87_ = lean_nat_add(v_p_82_, v___x_86_);
lean_dec(v___x_86_);
lean_dec(v_p_82_);
v_s_81_ = v___x_85_;
v_p_82_ = v___x_87_;
goto _start;
}
}
}
static lean_object* _init_l_System_FilePath_normalize___closed__0(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = l_System_FilePath_pathSeparators;
v___x_96_ = l_List_lengthTR___redArg(v___x_95_);
return v___x_96_;
}
}
static uint8_t _init_l_System_FilePath_normalize___closed__1(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_obj_once(&l_System_FilePath_normalize___closed__0, &l_System_FilePath_normalize___closed__0_once, _init_l_System_FilePath_normalize___closed__0);
v___x_99_ = lean_nat_dec_eq(v___x_98_, v___x_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object* v_p_100_){
_start:
{
lean_object* v_p_102_; uint8_t v___y_107_; uint32_t v___y_124_; uint8_t v___y_130_; uint8_t v___x_138_; 
v___x_138_ = l_System_Platform_isWindows;
if (v___x_138_ == 0)
{
v___y_130_ = v___x_138_;
goto v___jp_129_;
}
else
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_139_ = lean_unsigned_to_nat(2u);
v___x_140_ = lean_string_length(v_p_100_);
v___x_141_ = lean_nat_dec_le(v___x_139_, v___x_140_);
v___y_130_ = v___x_141_;
goto v___jp_129_;
}
v___jp_101_:
{
uint8_t v___x_103_; 
v___x_103_ = lean_uint8_once(&l_System_FilePath_normalize___closed__1, &l_System_FilePath_normalize___closed__1_once, _init_l_System_FilePath_normalize___closed__1);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v_p_105_; 
v___x_104_ = lean_unsigned_to_nat(0u);
v_p_105_ = l_String_mapAux___at___00System_FilePath_normalize_spec__1(v_p_102_, v___x_104_);
return v_p_105_;
}
else
{
return v_p_102_;
}
}
v___jp_106_:
{
if (v___y_107_ == 0)
{
v_p_102_ = v_p_100_;
goto v___jp_101_;
}
else
{
lean_object* v___x_108_; uint32_t v___x_109_; uint32_t v___x_110_; uint8_t v___x_111_; 
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_string_utf8_get(v_p_100_, v___x_108_);
v___x_110_ = 58;
v___x_111_ = lean_uint32_dec_eq(v___x_109_, v___x_110_);
if (v___x_111_ == 0)
{
v_p_102_ = v_p_100_;
goto v___jp_101_;
}
else
{
lean_object* v___x_112_; uint32_t v___x_113_; uint32_t v___x_114_; uint8_t v___x_115_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_string_utf8_get(v_p_100_, v___x_112_);
v___x_114_ = 97;
v___x_115_ = lean_uint32_dec_le(v___x_114_, v___x_113_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
v___x_116_ = lean_string_utf8_set(v_p_100_, v___x_112_, v___x_113_);
v_p_102_ = v___x_116_;
goto v___jp_101_;
}
else
{
uint32_t v___x_117_; uint8_t v___x_118_; 
v___x_117_ = 122;
v___x_118_ = lean_uint32_dec_le(v___x_113_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; 
v___x_119_ = lean_string_utf8_set(v_p_100_, v___x_112_, v___x_113_);
v_p_102_ = v___x_119_;
goto v___jp_101_;
}
else
{
uint32_t v___x_120_; uint32_t v___x_121_; lean_object* v___x_122_; 
v___x_120_ = 4294967264;
v___x_121_ = lean_uint32_add(v___x_113_, v___x_120_);
v___x_122_ = lean_string_utf8_set(v_p_100_, v___x_112_, v___x_121_);
v_p_102_ = v___x_122_;
goto v___jp_101_;
}
}
}
}
}
v___jp_123_:
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 97;
v___x_126_ = lean_uint32_dec_le(v___x_125_, v___y_124_);
if (v___x_126_ == 0)
{
v___y_107_ = v___x_126_;
goto v___jp_106_;
}
else
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 122;
v___x_128_ = lean_uint32_dec_le(v___y_124_, v___x_127_);
v___y_107_ = v___x_128_;
goto v___jp_106_;
}
}
v___jp_129_:
{
if (v___y_130_ == 0)
{
v_p_102_ = v_p_100_;
goto v___jp_101_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_string_utf8_byte_size(v_p_100_);
lean_inc_ref(v_p_100_);
v___x_133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_133_, 0, v_p_100_);
lean_ctor_set(v___x_133_, 1, v___x_131_);
lean_ctor_set(v___x_133_, 2, v___x_132_);
v___x_134_ = l_String_Slice_Pos_get_x3f(v___x_133_, v___x_131_);
lean_dec_ref(v___x_133_);
if (lean_obj_tag(v___x_134_) == 0)
{
uint32_t v___x_135_; 
v___x_135_ = 65;
v___y_124_ = v___x_135_;
goto v___jp_123_;
}
else
{
lean_object* v_val_136_; uint32_t v___x_137_; 
v_val_136_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_val_136_);
lean_dec_ref(v___x_134_);
v___x_137_ = lean_unbox_uint32(v_val_136_);
lean_dec(v_val_136_);
v___y_124_ = v___x_137_;
goto v___jp_123_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0(lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
if (lean_obj_tag(v_x_143_) == 0)
{
uint8_t v___x_144_; 
v___x_144_ = 1;
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
else
{
if (lean_obj_tag(v_x_143_) == 0)
{
uint8_t v___x_146_; 
v___x_146_ = 0;
return v___x_146_;
}
else
{
lean_object* v_val_147_; lean_object* v_val_148_; uint32_t v___x_149_; uint32_t v___x_150_; uint8_t v___x_151_; 
v_val_147_ = lean_ctor_get(v_x_142_, 0);
v_val_148_ = lean_ctor_get(v_x_143_, 0);
v___x_149_ = lean_unbox_uint32(v_val_147_);
v___x_150_ = lean_unbox_uint32(v_val_148_);
v___x_151_ = lean_uint32_dec_eq(v___x_149_, v___x_150_);
return v___x_151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0(v_x_152_, v_x_153_);
lean_dec(v_x_153_);
lean_dec(v_x_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_156_; lean_object* v___x_157_; 
v___x_156_ = 58;
v___x_157_ = lean_box_uint32(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object* v_p_160_){
_start:
{
lean_object* v___y_162_; uint8_t v___y_166_; lean_object* v___x_174_; uint32_t v___y_176_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_174_ = l_System_FilePath_pathSeparators;
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_string_utf8_byte_size(v_p_160_);
lean_inc_ref(v_p_160_);
v___x_184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_184_, 0, v_p_160_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_183_);
v___x_185_ = l_String_Slice_Pos_get_x3f(v___x_184_, v___x_182_);
lean_dec_ref(v___x_184_);
if (lean_obj_tag(v___x_185_) == 0)
{
uint32_t v___x_186_; 
v___x_186_ = 65;
v___y_176_ = v___x_186_;
goto v___jp_175_;
}
else
{
lean_object* v_val_187_; uint32_t v___x_188_; 
v_val_187_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_val_187_);
lean_dec_ref(v___x_185_);
v___x_188_ = lean_unbox_uint32(v_val_187_);
lean_dec(v_val_187_);
v___y_176_ = v___x_188_;
goto v___jp_175_;
}
v___jp_161_:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_obj_once(&l_System_FilePath_isAbsolute___closed__0, &l_System_FilePath_isAbsolute___closed__0_once, _init_l_System_FilePath_isAbsolute___closed__0);
v___x_164_ = l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__0(v___y_162_, v___x_163_);
lean_dec(v___y_162_);
return v___x_164_;
}
v___jp_165_:
{
if (v___y_166_ == 0)
{
lean_dec_ref(v_p_160_);
return v___y_166_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_string_utf8_byte_size(v_p_160_);
v___x_169_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_169_, 0, v_p_160_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
lean_ctor_set(v___x_169_, 2, v___x_168_);
v___x_170_ = l_String_Slice_Pos_next_x3f(v___x_169_, v___x_167_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v___x_171_; 
lean_dec_ref(v___x_169_);
v___x_171_ = lean_box(0);
v___y_162_ = v___x_171_;
goto v___jp_161_;
}
else
{
lean_object* v_val_172_; lean_object* v___x_173_; 
v_val_172_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_val_172_);
lean_dec_ref(v___x_170_);
v___x_173_ = l_String_Slice_Pos_get_x3f(v___x_169_, v_val_172_);
lean_dec(v_val_172_);
lean_dec_ref(v___x_169_);
v___y_162_ = v___x_173_;
goto v___jp_161_;
}
}
}
v___jp_175_:
{
uint8_t v___x_177_; 
v___x_177_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_176_, v___x_174_);
if (v___x_177_ == 0)
{
uint8_t v___x_178_; 
v___x_178_ = l_System_Platform_isWindows;
if (v___x_178_ == 0)
{
v___y_166_ = v___x_178_;
goto v___jp_165_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_string_length(v_p_160_);
v___x_181_ = lean_nat_dec_lt(v___x_179_, v___x_180_);
v___y_166_ = v___x_181_;
goto v___jp_165_;
}
}
else
{
lean_dec_ref(v_p_160_);
return v___x_177_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object* v_p_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_System_FilePath_isAbsolute(v_p_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object* v_p_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = l_System_FilePath_isAbsolute(v_p_192_);
if (v___x_193_ == 0)
{
uint8_t v___x_194_; 
v___x_194_ = 1;
return v___x_194_;
}
else
{
uint8_t v___x_195_; 
v___x_195_ = 0;
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object* v_p_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l_System_FilePath_isRelative(v_p_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
static lean_object* _init_l_System_FilePath_join___closed__0(void){
_start:
{
uint32_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = l_System_FilePath_pathSeparator;
v___x_200_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_201_ = lean_string_push(v___x_200_, v___x_199_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object* v_p_202_, lean_object* v_sub_203_){
_start:
{
uint8_t v___x_204_; 
lean_inc_ref(v_sub_203_);
v___x_204_ = l_System_FilePath_isAbsolute(v_sub_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_206_ = lean_string_append(v_p_202_, v___x_205_);
v___x_207_ = lean_string_append(v___x_206_, v_sub_203_);
lean_dec_ref(v_sub_203_);
return v___x_207_;
}
else
{
lean_dec_ref(v_p_202_);
return v_sub_203_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(lean_object* v_s_211_, lean_object* v_a_212_, lean_object* v_b_213_){
_start:
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_nat_dec_eq(v_a_212_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v_str_216_; lean_object* v_startInclusive_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint32_t v___x_226_; uint8_t v___x_227_; 
v_str_216_ = lean_ctor_get(v_s_211_, 0);
v_startInclusive_217_ = lean_ctor_get(v_s_211_, 1);
v___x_218_ = l_System_FilePath_pathSeparators;
v___x_219_ = lean_nat_add(v_startInclusive_217_, v_a_212_);
lean_inc(v___x_219_);
lean_inc(v_startInclusive_217_);
lean_inc_ref(v_str_216_);
v___x_220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_220_, 0, v_str_216_);
lean_ctor_set(v___x_220_, 1, v_startInclusive_217_);
lean_ctor_set(v___x_220_, 2, v___x_219_);
v___x_221_ = lean_nat_sub(v___x_219_, v_startInclusive_217_);
lean_dec(v___x_219_);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_sub(v___x_221_, v___x_222_);
lean_dec(v___x_221_);
v___x_224_ = l_String_Slice_posLE(v___x_220_, v___x_223_);
lean_dec_ref(v___x_220_);
v___x_225_ = lean_nat_add(v_startInclusive_217_, v___x_224_);
v___x_226_ = lean_string_utf8_get_fast(v_str_216_, v___x_225_);
lean_dec(v___x_225_);
v___x_227_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_226_, v___x_218_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec(v___x_224_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_nat_sub(v_a_212_, v___x_222_);
lean_dec(v_a_212_);
v___x_230_ = l_String_Slice_posLE(v_s_211_, v___x_229_);
v_a_212_ = v___x_230_;
v_b_213_ = v___x_228_;
goto _start;
}
else
{
lean_object* v___x_232_; 
lean_dec(v_a_212_);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_224_);
return v___x_232_;
}
}
else
{
lean_dec(v_a_212_);
lean_inc(v_b_213_);
return v_b_213_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg___boxed(lean_object* v_s_233_, lean_object* v_a_234_, lean_object* v_b_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_233_, v_a_234_, v_b_235_);
lean_dec(v_b_235_);
lean_dec_ref(v_s_233_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(lean_object* v_s_237_){
_start:
{
lean_object* v_startInclusive_238_; lean_object* v_endExclusive_239_; lean_object* v_searcher_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_startInclusive_238_ = lean_ctor_get(v_s_237_, 1);
v_endExclusive_239_ = lean_ctor_get(v_s_237_, 2);
v_searcher_240_ = lean_nat_sub(v_endExclusive_239_, v_startInclusive_238_);
v___x_241_ = lean_box(0);
v___x_242_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_237_, v_searcher_240_, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___boxed(lean_object* v_s_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v_s_243_);
lean_dec_ref(v_s_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object* v_p_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_string_utf8_byte_size(v_p_245_);
v___x_248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_248_, 0, v_p_245_);
lean_ctor_set(v___x_248_, 1, v___x_246_);
lean_ctor_set(v___x_248_, 2, v___x_247_);
v___x_249_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v___x_248_);
lean_dec_ref(v___x_248_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v___x_250_; 
v___x_250_ = lean_box(0);
return v___x_250_;
}
else
{
lean_object* v_val_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
v_val_251_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_249_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_val_251_);
lean_dec(v___x_249_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_val_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(lean_object* v_s_259_, lean_object* v_inst_260_, lean_object* v_R_261_, lean_object* v_a_262_, lean_object* v_b_263_, lean_object* v_c_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_259_, v_a_262_, v_b_263_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___boxed(lean_object* v_s_266_, lean_object* v_inst_267_, lean_object* v_R_268_, lean_object* v_a_269_, lean_object* v_b_270_, lean_object* v_c_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(v_s_266_, v_inst_267_, v_R_268_, v_a_269_, v_b_270_, v_c_271_);
lean_dec(v_b_270_);
lean_dec_ref(v_s_266_);
return v_res_272_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0(lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_x_273_) == 0)
{
if (lean_obj_tag(v_x_274_) == 0)
{
uint8_t v___x_275_; 
v___x_275_ = 1;
return v___x_275_;
}
else
{
uint8_t v___x_276_; 
v___x_276_ = 0;
return v___x_276_;
}
}
else
{
if (lean_obj_tag(v_x_274_) == 0)
{
uint8_t v___x_277_; 
v___x_277_ = 0;
return v___x_277_;
}
else
{
lean_object* v_val_278_; lean_object* v_val_279_; uint8_t v___x_280_; 
v_val_278_ = lean_ctor_get(v_x_273_, 0);
v_val_279_ = lean_ctor_get(v_x_274_, 0);
v___x_280_ = lean_nat_dec_eq(v_val_278_, v_val_279_);
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0___boxed(lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0(v_x_281_, v_x_282_);
lean_dec(v_x_282_);
lean_dec(v_x_281_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object* v_p_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_301_; lean_object* v___y_302_; uint32_t v___y_303_; lean_object* v___y_308_; 
lean_inc_ref(v_p_285_);
v___x_286_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_285_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v___x_318_; 
v___x_318_ = lean_box(0);
v___y_308_ = v___x_318_;
goto v___jp_307_;
}
else
{
lean_object* v_val_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v_val_319_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_val_319_);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_string_utf8_extract(v_p_285_, v___x_320_, v_val_319_);
lean_dec(v_val_319_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
v___y_308_ = v___x_322_;
goto v___jp_307_;
}
v___jp_287_:
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_string_length(v_p_285_);
v___x_291_ = lean_nat_dec_eq(v___x_290_, v___y_289_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_nat_sub(v___y_289_, v___x_292_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
v___x_295_ = l_Option_instBEq_beq___at___00System_FilePath_parent_spec__0(v___x_286_, v___x_294_);
lean_dec_ref(v___x_294_);
lean_dec(v___x_286_);
if (v___x_295_ == 0)
{
lean_dec_ref(v_p_285_);
return v___y_288_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v___y_288_);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_string_utf8_extract(v_p_285_, v___x_296_, v___y_289_);
lean_dec_ref(v_p_285_);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
else
{
lean_object* v___x_299_; 
lean_dec(v___y_288_);
lean_dec(v___x_286_);
lean_dec_ref(v_p_285_);
v___x_299_ = lean_box(0);
return v___x_299_;
}
}
v___jp_300_:
{
uint8_t v___x_304_; 
v___x_304_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_303_, v___y_301_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_unsigned_to_nat(3u);
v___y_288_ = v___y_302_;
v___y_289_ = v___x_305_;
goto v___jp_287_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_unsigned_to_nat(1u);
v___y_288_ = v___y_302_;
v___y_289_ = v___x_306_;
goto v___jp_287_;
}
}
v___jp_307_:
{
uint8_t v___x_309_; 
lean_inc_ref(v_p_285_);
v___x_309_ = l_System_FilePath_isAbsolute(v_p_285_);
if (v___x_309_ == 0)
{
lean_dec(v___x_286_);
lean_dec_ref(v_p_285_);
return v___y_308_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_310_ = l_System_FilePath_pathSeparators;
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = lean_string_utf8_byte_size(v_p_285_);
lean_inc_ref(v_p_285_);
v___x_313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_313_, 0, v_p_285_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
lean_ctor_set(v___x_313_, 2, v___x_312_);
v___x_314_ = l_String_Slice_Pos_get_x3f(v___x_313_, v___x_311_);
lean_dec_ref(v___x_313_);
if (lean_obj_tag(v___x_314_) == 0)
{
uint32_t v___x_315_; 
v___x_315_ = 65;
v___y_301_ = v___x_310_;
v___y_302_ = v___y_308_;
v___y_303_ = v___x_315_;
goto v___jp_300_;
}
else
{
lean_object* v_val_316_; uint32_t v___x_317_; 
v_val_316_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_val_316_);
lean_dec_ref(v___x_314_);
v___x_317_ = lean_unbox_uint32(v_val_316_);
lean_dec(v_val_316_);
v___y_301_ = v___x_310_;
v___y_302_ = v___y_308_;
v___y_303_ = v___x_317_;
goto v___jp_300_;
}
}
}
}
}
static lean_object* _init_l_System_FilePath_fileName___closed__2(void){
_start:
{
uint32_t v___x_325_; lean_object* v___x_326_; 
v___x_325_ = 47;
v___x_326_ = l_Char_utf8Size(v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object* v_p_327_){
_start:
{
lean_object* v___y_329_; uint8_t v___y_330_; lean_object* v___y_337_; lean_object* v___x_343_; 
lean_inc_ref(v_p_327_);
v___x_343_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_327_);
if (lean_obj_tag(v___x_343_) == 0)
{
v___y_337_ = v_p_327_;
goto v___jp_336_;
}
else
{
lean_object* v_val_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_val_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_val_344_);
lean_dec_ref(v___x_343_);
v___x_345_ = lean_obj_once(&l_System_FilePath_fileName___closed__2, &l_System_FilePath_fileName___closed__2_once, _init_l_System_FilePath_fileName___closed__2);
v___x_346_ = lean_nat_add(v_val_344_, v___x_345_);
lean_dec(v_val_344_);
v___x_347_ = lean_string_utf8_byte_size(v_p_327_);
v___x_348_ = lean_string_utf8_extract(v_p_327_, v___x_346_, v___x_347_);
lean_dec(v___x_346_);
lean_dec_ref(v_p_327_);
v___y_337_ = v___x_348_;
goto v___jp_336_;
}
v___jp_328_:
{
if (v___y_330_ == 0)
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_332_ = lean_string_dec_eq(v___y_329_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v___y_329_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; 
lean_dec_ref(v___y_329_);
v___x_334_ = lean_box(0);
return v___x_334_;
}
}
else
{
lean_object* v___x_335_; 
lean_dec_ref(v___y_329_);
v___x_335_ = lean_box(0);
return v___x_335_;
}
}
v___jp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = lean_string_utf8_byte_size(v___y_337_);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_nat_dec_eq(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
v___x_342_ = lean_string_dec_eq(v___y_337_, v___x_341_);
v___y_329_ = v___y_337_;
v___y_330_ = v___x_342_;
goto v___jp_328_;
}
else
{
v___y_329_ = v___y_337_;
v___y_330_ = v___x_340_;
goto v___jp_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(lean_object* v_s_349_, lean_object* v_a_350_, lean_object* v_b_351_){
_start:
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_nat_dec_eq(v_a_350_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v_str_354_; lean_object* v_startInclusive_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint32_t v___x_363_; uint32_t v___x_364_; uint8_t v___x_365_; 
v_str_354_ = lean_ctor_get(v_s_349_, 0);
v_startInclusive_355_ = lean_ctor_get(v_s_349_, 1);
v___x_356_ = lean_nat_add(v_startInclusive_355_, v_a_350_);
lean_inc(v___x_356_);
lean_inc(v_startInclusive_355_);
lean_inc_ref(v_str_354_);
v___x_357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_357_, 0, v_str_354_);
lean_ctor_set(v___x_357_, 1, v_startInclusive_355_);
lean_ctor_set(v___x_357_, 2, v___x_356_);
v___x_358_ = lean_nat_sub(v___x_356_, v_startInclusive_355_);
lean_dec(v___x_356_);
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_nat_sub(v___x_358_, v___x_359_);
lean_dec(v___x_358_);
v___x_361_ = l_String_Slice_posLE(v___x_357_, v___x_360_);
lean_dec_ref(v___x_357_);
v___x_362_ = lean_nat_add(v_startInclusive_355_, v___x_361_);
v___x_363_ = lean_string_utf8_get_fast(v_str_354_, v___x_362_);
lean_dec(v___x_362_);
v___x_364_ = 46;
v___x_365_ = lean_uint32_dec_eq(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec(v___x_361_);
v___x_366_ = lean_box(0);
v___x_367_ = lean_nat_sub(v_a_350_, v___x_359_);
lean_dec(v_a_350_);
v___x_368_ = l_String_Slice_posLE(v_s_349_, v___x_367_);
v_a_350_ = v___x_368_;
v_b_351_ = v___x_366_;
goto _start;
}
else
{
lean_object* v___x_370_; 
lean_dec(v_a_350_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_361_);
return v___x_370_;
}
}
else
{
lean_dec(v_a_350_);
lean_inc(v_b_351_);
return v_b_351_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg___boxed(lean_object* v_s_371_, lean_object* v_a_372_, lean_object* v_b_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_371_, v_a_372_, v_b_373_);
lean_dec(v_b_373_);
lean_dec_ref(v_s_371_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(lean_object* v_s_375_){
_start:
{
lean_object* v_startInclusive_376_; lean_object* v_endExclusive_377_; lean_object* v_searcher_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_startInclusive_376_ = lean_ctor_get(v_s_375_, 1);
v_endExclusive_377_ = lean_ctor_get(v_s_375_, 2);
v_searcher_378_ = lean_nat_sub(v_endExclusive_377_, v_startInclusive_376_);
v___x_379_ = lean_box(0);
v___x_380_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_375_, v_searcher_378_, v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0___boxed(lean_object* v_s_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v_s_381_);
lean_dec_ref(v_s_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object* v_p_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_System_FilePath_fileName(v_p_383_);
if (lean_obj_tag(v___x_384_) == 0)
{
return v___x_384_;
}
else
{
lean_object* v_val_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_val_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc_n(v_val_385_, 2);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_string_utf8_byte_size(v_val_385_);
v___x_388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_388_, 0, v_val_385_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
lean_ctor_set(v___x_388_, 2, v___x_387_);
v___x_389_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_388_);
lean_dec_ref(v___x_388_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_dec(v_val_385_);
return v___x_384_;
}
else
{
lean_object* v_val_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_399_; 
v_val_390_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_399_ == 0)
{
v___x_392_ = v___x_389_;
v_isShared_393_ = v_isSharedCheck_399_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_val_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_399_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
uint8_t v___x_394_; 
v___x_394_ = lean_nat_dec_eq(v_val_390_, v___x_386_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_397_; 
lean_dec_ref(v___x_384_);
v___x_395_ = lean_string_utf8_extract(v_val_385_, v___x_386_, v_val_390_);
lean_dec(v_val_390_);
lean_dec(v_val_385_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_395_);
v___x_397_ = v___x_392_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
else
{
lean_del_object(v___x_392_);
lean_dec(v_val_390_);
lean_dec(v_val_385_);
return v___x_384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(lean_object* v_s_400_, lean_object* v_inst_401_, lean_object* v_R_402_, lean_object* v_a_403_, lean_object* v_b_404_, lean_object* v_c_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_400_, v_a_403_, v_b_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___boxed(lean_object* v_s_407_, lean_object* v_inst_408_, lean_object* v_R_409_, lean_object* v_a_410_, lean_object* v_b_411_, lean_object* v_c_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(v_s_407_, v_inst_408_, v_R_409_, v_a_410_, v_b_411_, v_c_412_);
lean_dec(v_b_411_);
lean_dec_ref(v_s_407_);
return v_res_413_;
}
}
static lean_object* _init_l_System_FilePath_extension___closed__0(void){
_start:
{
uint32_t v___x_414_; lean_object* v___x_415_; 
v___x_414_ = 46;
v___x_415_ = l_Char_utf8Size(v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object* v_p_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_System_FilePath_fileName(v_p_416_);
if (lean_obj_tag(v___x_417_) == 0)
{
return v___x_417_;
}
else
{
lean_object* v_val_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_val_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc_n(v_val_418_, 2);
lean_dec_ref(v___x_417_);
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_string_utf8_byte_size(v_val_418_);
v___x_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_421_, 0, v_val_418_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
lean_ctor_set(v___x_421_, 2, v___x_420_);
v___x_422_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_421_);
lean_dec_ref(v___x_421_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v___x_423_; 
lean_dec(v_val_418_);
v___x_423_ = lean_box(0);
return v___x_423_;
}
else
{
lean_object* v_val_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_436_; 
v_val_424_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_436_ == 0)
{
v___x_426_ = v___x_422_;
v_isShared_427_ = v_isSharedCheck_436_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_val_424_);
lean_dec(v___x_422_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_436_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
uint8_t v___x_428_; 
v___x_428_ = lean_nat_dec_eq(v_val_424_, v___x_419_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_429_ = lean_obj_once(&l_System_FilePath_extension___closed__0, &l_System_FilePath_extension___closed__0_once, _init_l_System_FilePath_extension___closed__0);
v___x_430_ = lean_nat_add(v_val_424_, v___x_429_);
lean_dec(v_val_424_);
v___x_431_ = lean_string_utf8_extract(v_val_418_, v___x_430_, v___x_420_);
lean_dec(v___x_430_);
lean_dec(v_val_418_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_431_);
v___x_433_ = v___x_426_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
else
{
lean_object* v___x_435_; 
lean_del_object(v___x_426_);
lean_dec(v_val_424_);
lean_dec(v_val_418_);
v___x_435_ = lean_box(0);
return v___x_435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object* v_p_437_, lean_object* v_fname_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_System_FilePath_parent(v_p_437_);
if (lean_obj_tag(v___x_439_) == 0)
{
return v_fname_438_;
}
else
{
lean_object* v_val_440_; lean_object* v___x_441_; 
v_val_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_val_440_);
lean_dec_ref(v___x_439_);
v___x_441_ = l_System_FilePath_join(v_val_440_, v_fname_438_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object* v_p_442_, lean_object* v_ext_443_){
_start:
{
lean_object* v___x_444_; 
lean_inc_ref(v_p_442_);
v___x_444_ = l_System_FilePath_fileName(v_p_442_);
if (lean_obj_tag(v___x_444_) == 0)
{
return v_p_442_;
}
else
{
lean_object* v_val_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_val_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_val_445_);
lean_dec_ref(v___x_444_);
v___x_446_ = lean_string_utf8_byte_size(v_ext_443_);
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = lean_nat_dec_eq(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_449_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
v___x_450_ = lean_string_append(v_val_445_, v___x_449_);
v___x_451_ = lean_string_append(v___x_450_, v_ext_443_);
v___x_452_ = l_System_FilePath_withFileName(v_p_442_, v___x_451_);
return v___x_452_;
}
else
{
lean_object* v___x_453_; 
v___x_453_ = l_System_FilePath_withFileName(v_p_442_, v_val_445_);
return v___x_453_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object* v_p_454_, lean_object* v_ext_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_System_FilePath_addExtension(v_p_454_, v_ext_455_);
lean_dec_ref(v_ext_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object* v_p_457_, lean_object* v_ext_458_){
_start:
{
lean_object* v___x_459_; 
lean_inc_ref(v_p_457_);
v___x_459_ = l_System_FilePath_fileStem(v_p_457_);
if (lean_obj_tag(v___x_459_) == 0)
{
return v_p_457_;
}
else
{
lean_object* v_val_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v_val_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_val_460_);
lean_dec_ref(v___x_459_);
v___x_461_ = lean_string_utf8_byte_size(v_ext_458_);
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_nat_dec_eq(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_464_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
v___x_465_ = lean_string_append(v_val_460_, v___x_464_);
v___x_466_ = lean_string_append(v___x_465_, v_ext_458_);
v___x_467_ = l_System_FilePath_withFileName(v_p_457_, v___x_466_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; 
v___x_468_ = l_System_FilePath_withFileName(v_p_457_, v_val_460_);
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object* v_p_469_, lean_object* v_ext_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_System_FilePath_withExtension(v_p_469_, v_ext_470_);
lean_dec_ref(v_ext_470_);
return v_res_471_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_473_ = lean_string_utf8_byte_size(v___x_472_);
return v___x_473_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
v___x_476_ = lean_nat_dec_eq(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_477_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_478_);
lean_ctor_set(v___x_480_, 2, v___x_477_);
return v___x_480_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2);
v___x_482_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3);
v___x_485_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2);
v___x_486_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
lean_ctor_set(v___x_486_, 2, v___x_483_);
lean_ctor_set(v___x_486_, 3, v___x_483_);
return v___x_486_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4);
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(lean_object* v_s_495_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
v___x_497_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5);
return v___x_497_;
}
else
{
lean_object* v___x_498_; 
v___x_498_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7));
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(lean_object* v_s_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v_s_499_);
lean_dec_ref(v_s_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object* v___x_501_, lean_object* v___x_502_, lean_object* v___x_503_, lean_object* v_a_504_, lean_object* v_b_505_){
_start:
{
lean_object* v_it_507_; lean_object* v_startInclusive_508_; lean_object* v_endExclusive_509_; 
if (lean_obj_tag(v_a_504_) == 0)
{
lean_object* v_currPos_514_; lean_object* v_searcher_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_619_; 
v_currPos_514_ = lean_ctor_get(v_a_504_, 0);
v_searcher_515_ = lean_ctor_get(v_a_504_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_a_504_);
if (v_isSharedCheck_619_ == 0)
{
v___x_517_ = v_a_504_;
v_isShared_518_ = v_isSharedCheck_619_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_searcher_515_);
lean_inc(v_currPos_514_);
lean_dec(v_a_504_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_619_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v_it_520_; lean_object* v_it_526_; lean_object* v_startPos_527_; lean_object* v_endPos_528_; 
switch(lean_obj_tag(v_searcher_515_))
{
case 0:
{
lean_object* v_pos_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_553_; 
lean_del_object(v___x_517_);
v_pos_541_ = lean_ctor_get(v_searcher_515_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v_searcher_515_);
if (v_isSharedCheck_553_ == 0)
{
v___x_543_ = v_searcher_515_;
v_isShared_544_ = v_isSharedCheck_553_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_pos_541_);
lean_dec(v_searcher_515_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_553_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v_startInclusive_545_; lean_object* v_endExclusive_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_startInclusive_545_ = lean_ctor_get(v___x_502_, 1);
v_endExclusive_546_ = lean_ctor_get(v___x_502_, 2);
v___x_547_ = lean_nat_sub(v_endExclusive_546_, v_startInclusive_545_);
v___x_548_ = lean_nat_dec_eq(v_pos_541_, v___x_547_);
lean_dec(v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_550_; 
lean_inc(v_pos_541_);
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 1);
v___x_550_ = v___x_543_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_pos_541_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_inc(v_pos_541_);
v_it_526_ = v___x_550_;
v_startPos_527_ = v_pos_541_;
v_endPos_528_ = v_pos_541_;
goto v___jp_525_;
}
}
else
{
lean_object* v___x_552_; 
lean_del_object(v___x_543_);
v___x_552_ = lean_box(3);
lean_inc(v_pos_541_);
v_it_526_ = v___x_552_;
v_startPos_527_ = v_pos_541_;
v_endPos_528_ = v_pos_541_;
goto v___jp_525_;
}
}
}
case 1:
{
lean_object* v_pos_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_562_; 
v_pos_554_ = lean_ctor_get(v_searcher_515_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_searcher_515_);
if (v_isSharedCheck_562_ == 0)
{
v___x_556_ = v_searcher_515_;
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_pos_554_);
lean_dec(v_searcher_515_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = lean_string_utf8_next_fast(v___x_501_, v_pos_554_);
lean_dec(v_pos_554_);
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 0);
lean_ctor_set(v___x_556_, 0, v___x_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
v_it_520_ = v___x_560_;
goto v___jp_519_;
}
}
}
case 2:
{
lean_object* v_needle_563_; lean_object* v_table_564_; lean_object* v_stackPos_565_; lean_object* v_needlePos_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_618_; 
v_needle_563_ = lean_ctor_get(v_searcher_515_, 0);
v_table_564_ = lean_ctor_get(v_searcher_515_, 1);
v_stackPos_565_ = lean_ctor_get(v_searcher_515_, 2);
v_needlePos_566_ = lean_ctor_get(v_searcher_515_, 3);
v_isSharedCheck_618_ = !lean_is_exclusive(v_searcher_515_);
if (v_isSharedCheck_618_ == 0)
{
v___x_568_ = v_searcher_515_;
v_isShared_569_ = v_isSharedCheck_618_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_needlePos_566_);
lean_inc(v_stackPos_565_);
lean_inc(v_table_564_);
lean_inc(v_needle_563_);
lean_dec(v_searcher_515_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_618_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v_str_570_; lean_object* v_startInclusive_571_; lean_object* v_endExclusive_572_; lean_object* v_basePos_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_str_570_ = lean_ctor_get(v_needle_563_, 0);
v_startInclusive_571_ = lean_ctor_get(v_needle_563_, 1);
v_endExclusive_572_ = lean_ctor_get(v_needle_563_, 2);
v_basePos_573_ = lean_nat_sub(v_stackPos_565_, v_needlePos_566_);
v___x_574_ = lean_nat_sub(v_endExclusive_572_, v_startInclusive_571_);
v___x_575_ = lean_nat_add(v_basePos_573_, v___x_574_);
v___x_576_ = lean_nat_dec_le(v___x_575_, v___x_503_);
lean_dec(v___x_575_);
if (v___x_576_ == 0)
{
uint8_t v___x_577_; 
lean_dec(v___x_574_);
lean_del_object(v___x_568_);
lean_dec(v_needlePos_566_);
lean_dec(v_stackPos_565_);
lean_dec_ref(v_table_564_);
lean_dec_ref(v_needle_563_);
v___x_577_ = lean_nat_dec_lt(v_basePos_573_, v___x_503_);
lean_dec(v_basePos_573_);
if (v___x_577_ == 0)
{
lean_del_object(v___x_517_);
goto v___jp_539_;
}
else
{
lean_object* v___x_578_; 
v___x_578_ = lean_box(3);
v_it_520_ = v___x_578_;
goto v___jp_519_;
}
}
else
{
uint8_t v_stackByte_579_; lean_object* v___x_580_; uint8_t v_patByte_581_; uint8_t v___x_582_; 
lean_dec(v_basePos_573_);
lean_inc(v_stackPos_565_);
v_stackByte_579_ = lean_string_get_byte_fast(v___x_501_, v_stackPos_565_);
v___x_580_ = lean_nat_add(v_startInclusive_571_, v_needlePos_566_);
v_patByte_581_ = lean_string_get_byte_fast(v_str_570_, v___x_580_);
v___x_582_ = lean_uint8_dec_eq(v_stackByte_579_, v_patByte_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; uint8_t v___x_584_; 
lean_dec(v___x_574_);
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_nat_dec_eq(v_needlePos_566_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v_newNeedlePos_587_; uint8_t v___x_588_; 
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = lean_nat_sub(v_needlePos_566_, v___x_585_);
lean_dec(v_needlePos_566_);
v_newNeedlePos_587_ = lean_array_fget_borrowed(v_table_564_, v___x_586_);
lean_dec(v___x_586_);
v___x_588_ = lean_nat_dec_eq(v_newNeedlePos_587_, v___x_583_);
if (v___x_588_ == 0)
{
lean_object* v___x_590_; 
lean_inc(v_newNeedlePos_587_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 3, v_newNeedlePos_587_);
v___x_590_ = v___x_568_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_needle_563_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_table_564_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_stackPos_565_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_newNeedlePos_587_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
v_it_520_ = v___x_590_;
goto v___jp_519_;
}
}
else
{
lean_object* v_nextStackPos_592_; lean_object* v___x_594_; 
v_nextStackPos_592_ = l_String_Slice_posGE___redArg(v___x_502_, v_stackPos_565_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 3, v___x_583_);
lean_ctor_set(v___x_568_, 2, v_nextStackPos_592_);
v___x_594_ = v___x_568_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_needle_563_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_table_564_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_nextStackPos_592_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v___x_583_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
v_it_520_ = v___x_594_;
goto v___jp_519_;
}
}
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v_nextStackPos_598_; lean_object* v___x_600_; 
lean_dec(v_needlePos_566_);
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_nat_add(v_stackPos_565_, v___x_596_);
lean_dec(v_stackPos_565_);
v_nextStackPos_598_ = l_String_Slice_posGE___redArg(v___x_502_, v___x_597_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 3, v___x_583_);
lean_ctor_set(v___x_568_, 2, v_nextStackPos_598_);
v___x_600_ = v___x_568_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_needle_563_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_table_564_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_nextStackPos_598_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v___x_583_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
v_it_520_ = v___x_600_;
goto v___jp_519_;
}
}
}
else
{
lean_object* v___x_602_; lean_object* v_nextStackPos_603_; lean_object* v_nextNeedlePos_604_; uint8_t v___x_605_; 
lean_del_object(v___x_517_);
v___x_602_ = lean_unsigned_to_nat(1u);
v_nextStackPos_603_ = lean_nat_add(v_stackPos_565_, v___x_602_);
lean_dec(v_stackPos_565_);
v_nextNeedlePos_604_ = lean_nat_add(v_needlePos_566_, v___x_602_);
lean_dec(v_needlePos_566_);
v___x_605_ = lean_nat_dec_eq(v_nextNeedlePos_604_, v___x_574_);
lean_dec(v___x_574_);
if (v___x_605_ == 0)
{
lean_object* v___x_607_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 3, v_nextNeedlePos_604_);
lean_ctor_set(v___x_568_, 2, v_nextStackPos_603_);
v___x_607_ = v___x_568_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_needle_563_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_table_564_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_nextStackPos_603_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v_nextNeedlePos_604_);
v___x_607_ = v_reuseFailAlloc_610_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; 
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v_currPos_514_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v_a_504_ = v___x_608_;
goto _start;
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_611_ = lean_nat_sub(v_nextStackPos_603_, v_nextNeedlePos_604_);
lean_dec(v_nextNeedlePos_604_);
v___x_612_ = l_String_Slice_pos_x21(v___x_502_, v___x_611_);
lean_dec(v___x_611_);
v___x_613_ = l_String_Slice_pos_x21(v___x_502_, v_nextStackPos_603_);
v___x_614_ = lean_unsigned_to_nat(0u);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 3, v___x_614_);
lean_ctor_set(v___x_568_, 2, v_nextStackPos_603_);
v___x_616_ = v___x_568_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_needle_563_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_table_564_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_nextStackPos_603_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
v_it_526_ = v___x_616_;
v_startPos_527_ = v___x_612_;
v_endPos_528_ = v___x_613_;
goto v___jp_525_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_517_);
goto v___jp_539_;
}
}
v___jp_519_:
{
lean_object* v___x_522_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 1, v_it_520_);
v___x_522_ = v___x_517_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_currPos_514_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_it_520_);
v___x_522_ = v_reuseFailAlloc_524_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
v_a_504_ = v___x_522_;
goto _start;
}
}
v___jp_525_:
{
lean_object* v_slice_529_; lean_object* v_startInclusive_530_; lean_object* v_endExclusive_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
v_slice_529_ = l_String_Slice_subslice_x21(v___x_502_, v_currPos_514_, v_startPos_527_);
v_startInclusive_530_ = lean_ctor_get(v_slice_529_, 0);
v_endExclusive_531_ = lean_ctor_get(v_slice_529_, 1);
v_isSharedCheck_538_ = !lean_is_exclusive(v_slice_529_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v_slice_529_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_endExclusive_531_);
lean_inc(v_startInclusive_530_);
lean_dec(v_slice_529_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v_nextIt_536_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v_it_526_);
lean_ctor_set(v___x_533_, 0, v_endPos_528_);
v_nextIt_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_endPos_528_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_it_526_);
v_nextIt_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
v_it_507_ = v_nextIt_536_;
v_startInclusive_508_ = v_startInclusive_530_;
v_endExclusive_509_ = v_endExclusive_531_;
goto v___jp_506_;
}
}
}
v___jp_539_:
{
lean_object* v___x_540_; 
v___x_540_ = lean_box(1);
lean_inc(v___x_503_);
v_it_507_ = v___x_540_;
v_startInclusive_508_ = v_currPos_514_;
v_endExclusive_509_ = v___x_503_;
goto v___jp_506_;
}
}
}
else
{
lean_dec(v___x_503_);
lean_dec_ref(v___x_501_);
return v_b_505_;
}
v___jp_506_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
lean_inc_ref(v___x_501_);
v___x_510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_510_, 0, v___x_501_);
lean_ctor_set(v___x_510_, 1, v_startInclusive_508_);
lean_ctor_set(v___x_510_, 2, v_endExclusive_509_);
v___x_511_ = l_String_Slice_toString(v___x_510_);
lean_dec_ref(v___x_510_);
v___x_512_ = lean_array_push(v_b_505_, v___x_511_);
v_a_504_ = v_it_507_;
v_b_505_ = v___x_512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object* v___x_620_, lean_object* v___x_621_, lean_object* v___x_622_, lean_object* v_a_623_, lean_object* v_b_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_620_, v___x_621_, v___x_622_, v_a_623_, v_b_624_);
lean_dec_ref(v___x_621_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object* v_p_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_629_ = l_System_FilePath_normalize(v_p_628_);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_string_utf8_byte_size(v___x_629_);
lean_inc_ref(v___x_629_);
v___x_632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_632_, 0, v___x_629_);
lean_ctor_set(v___x_632_, 1, v___x_630_);
lean_ctor_set(v___x_632_, 2, v___x_631_);
v___x_633_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v___x_632_);
v___x_634_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_635_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_629_, v___x_632_, v___x_631_, v___x_633_, v___x_634_);
lean_dec_ref(v___x_632_);
v___x_636_ = lean_array_to_list(v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object* v___x_637_, lean_object* v___x_638_, lean_object* v___x_639_, lean_object* v_inst_640_, lean_object* v_R_641_, lean_object* v_a_642_, lean_object* v_b_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_637_, v___x_638_, v___x_639_, v_a_642_, v_b_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v___x_647_, lean_object* v_inst_648_, lean_object* v_R_649_, lean_object* v_a_650_, lean_object* v_b_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(v___x_645_, v___x_646_, v___x_647_, v_inst_648_, v_R_649_, v_a_650_, v_b_651_);
lean_dec_ref(v___x_646_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object* v_parts_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_655_ = l_String_intercalate(v___x_654_, v_parts_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object* v_toString_656_){
_start:
{
lean_inc_ref(v_toString_656_);
return v_toString_656_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object* v_toString_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_System_instCoeStringFilePath___lam__0(v_toString_657_);
lean_dec_ref(v_toString_657_);
return v_res_658_;
}
}
static uint32_t _init_l_System_SearchPath_separator(void){
_start:
{
uint8_t v___x_661_; 
v___x_661_ = l_System_Platform_isWindows;
if (v___x_661_ == 0)
{
uint32_t v___x_662_; 
v___x_662_ = 58;
return v___x_662_;
}
else
{
uint32_t v___x_663_; 
v___x_663_ = 59;
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(lean_object* v_s_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0));
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___boxed(lean_object* v_s_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v_s_668_);
lean_dec_ref(v_s_668_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(lean_object* v_s_670_, lean_object* v___x_671_, lean_object* v___x_672_, lean_object* v_a_673_, lean_object* v_b_674_){
_start:
{
lean_object* v_it_676_; lean_object* v_startInclusive_677_; lean_object* v_endExclusive_678_; 
if (lean_obj_tag(v_a_673_) == 0)
{
lean_object* v_currPos_682_; lean_object* v_searcher_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_709_; 
v_currPos_682_ = lean_ctor_get(v_a_673_, 0);
v_searcher_683_ = lean_ctor_get(v_a_673_, 1);
v_isSharedCheck_709_ = !lean_is_exclusive(v_a_673_);
if (v_isSharedCheck_709_ == 0)
{
v___x_685_ = v_a_673_;
v_isShared_686_ = v_isSharedCheck_709_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_searcher_683_);
lean_inc(v_currPos_682_);
lean_dec(v_a_673_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_709_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_startInclusive_687_; lean_object* v_endExclusive_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v_startInclusive_687_ = lean_ctor_get(v___x_671_, 1);
v_endExclusive_688_ = lean_ctor_get(v___x_671_, 2);
v___x_689_ = lean_nat_sub(v_endExclusive_688_, v_startInclusive_687_);
v___x_690_ = lean_nat_dec_eq(v_searcher_683_, v___x_689_);
lean_dec(v___x_689_);
if (v___x_690_ == 0)
{
uint32_t v___x_691_; uint32_t v___x_692_; uint8_t v___x_693_; 
v___x_691_ = l_System_SearchPath_separator;
v___x_692_ = lean_string_utf8_get_fast(v_s_670_, v_searcher_683_);
v___x_693_ = lean_uint32_dec_eq(v___x_692_, v___x_691_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = lean_string_utf8_next_fast(v_s_670_, v_searcher_683_);
lean_dec(v_searcher_683_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_694_);
v___x_696_ = v___x_685_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_currPos_682_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_698_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
v_a_673_ = v___x_696_;
goto _start;
}
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v_slice_702_; lean_object* v_nextIt_704_; 
v___x_699_ = lean_string_utf8_next_fast(v_s_670_, v_searcher_683_);
v___x_700_ = lean_nat_sub(v___x_699_, v_searcher_683_);
v___x_701_ = lean_nat_add(v_searcher_683_, v___x_700_);
lean_dec(v___x_700_);
v_slice_702_ = l_String_Slice_subslice_x21(v___x_671_, v_currPos_682_, v_searcher_683_);
lean_inc(v___x_701_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_701_);
lean_ctor_set(v___x_685_, 0, v___x_701_);
v_nextIt_704_ = v___x_685_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_701_);
v_nextIt_704_ = v_reuseFailAlloc_707_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v_startInclusive_705_; lean_object* v_endExclusive_706_; 
v_startInclusive_705_ = lean_ctor_get(v_slice_702_, 0);
lean_inc(v_startInclusive_705_);
v_endExclusive_706_ = lean_ctor_get(v_slice_702_, 1);
lean_inc(v_endExclusive_706_);
lean_dec_ref(v_slice_702_);
v_it_676_ = v_nextIt_704_;
v_startInclusive_677_ = v_startInclusive_705_;
v_endExclusive_678_ = v_endExclusive_706_;
goto v___jp_675_;
}
}
}
else
{
lean_object* v___x_708_; 
lean_del_object(v___x_685_);
lean_dec(v_searcher_683_);
v___x_708_ = lean_box(1);
lean_inc(v___x_672_);
v_it_676_ = v___x_708_;
v_startInclusive_677_ = v_currPos_682_;
v_endExclusive_678_ = v___x_672_;
goto v___jp_675_;
}
}
}
else
{
lean_dec(v___x_672_);
return v_b_674_;
}
v___jp_675_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_string_utf8_extract(v_s_670_, v_startInclusive_677_, v_endExclusive_678_);
lean_dec(v_endExclusive_678_);
lean_dec(v_startInclusive_677_);
v___x_680_ = lean_array_push(v_b_674_, v___x_679_);
v_a_673_ = v_it_676_;
v_b_674_ = v___x_680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg___boxed(lean_object* v_s_710_, lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v_a_713_, lean_object* v_b_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_710_, v___x_711_, v___x_712_, v_a_713_, v_b_714_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v_s_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object* v_s_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = lean_string_utf8_byte_size(v_s_716_);
lean_inc_ref(v_s_716_);
v___x_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_719_, 0, v_s_716_);
lean_ctor_set(v___x_719_, 1, v___x_717_);
lean_ctor_set(v___x_719_, 2, v___x_718_);
v___x_720_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v___x_719_);
v___x_721_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_722_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_716_, v___x_719_, v___x_718_, v___x_720_, v___x_721_);
lean_dec_ref(v___x_719_);
lean_dec_ref(v_s_716_);
v___x_723_ = lean_array_to_list(v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(lean_object* v_s_724_, lean_object* v___x_725_, lean_object* v___x_726_, lean_object* v_inst_727_, lean_object* v_R_728_, lean_object* v_a_729_, lean_object* v_b_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_724_, v___x_725_, v___x_726_, v_a_729_, v_b_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___boxed(lean_object* v_s_732_, lean_object* v___x_733_, lean_object* v___x_734_, lean_object* v_inst_735_, lean_object* v_R_736_, lean_object* v_a_737_, lean_object* v_b_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(v_s_732_, v___x_733_, v___x_734_, v_inst_735_, v_R_736_, v_a_737_, v_b_738_);
lean_dec_ref(v___x_733_);
lean_dec_ref(v_s_732_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
if (lean_obj_tag(v_a_740_) == 0)
{
lean_object* v___x_742_; 
v___x_742_ = l_List_reverse___redArg(v_a_741_);
return v___x_742_;
}
else
{
lean_object* v_head_743_; lean_object* v_tail_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_752_; 
v_head_743_ = lean_ctor_get(v_a_740_, 0);
v_tail_744_ = lean_ctor_get(v_a_740_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v_a_740_);
if (v_isSharedCheck_752_ == 0)
{
v___x_746_ = v_a_740_;
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_tail_744_);
lean_inc(v_head_743_);
lean_dec(v_a_740_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v_a_741_);
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_head_743_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_a_741_);
v___x_749_ = v_reuseFailAlloc_751_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
v_a_740_ = v_tail_744_;
v_a_741_ = v___x_749_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_System_SearchPath_toString___closed__0(void){
_start:
{
uint32_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = l_System_SearchPath_separator;
v___x_754_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_755_ = lean_string_push(v___x_754_, v___x_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object* v_path_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_757_ = lean_obj_once(&l_System_SearchPath_toString___closed__0, &l_System_SearchPath_toString___closed__0_once, _init_l_System_SearchPath_toString___closed__0);
v___x_758_ = lean_box(0);
v___x_759_ = l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(v_path_756_, v___x_758_);
v___x_760_ = l_String_intercalate(v___x_757_, v___x_759_);
return v___x_760_;
}
}
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_System_FilePath_pathSeparator = _init_l_System_FilePath_pathSeparator();
l_System_FilePath_pathSeparators___closed__0___boxed__const__1 = _init_l_System_FilePath_pathSeparators___closed__0___boxed__const__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__0___boxed__const__1);
l_System_FilePath_pathSeparators___closed__1___boxed__const__1 = _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__1___boxed__const__1);
l_System_FilePath_pathSeparators = _init_l_System_FilePath_pathSeparators();
lean_mark_persistent(l_System_FilePath_pathSeparators);
l_System_FilePath_extSeparator = _init_l_System_FilePath_extSeparator();
l_System_FilePath_exeExtension = _init_l_System_FilePath_exeExtension();
lean_mark_persistent(l_System_FilePath_exeExtension);
l_System_FilePath_isAbsolute___closed__0___boxed__const__1 = _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1();
lean_mark_persistent(l_System_FilePath_isAbsolute___closed__0___boxed__const__1);
l_System_SearchPath_separator = _init_l_System_SearchPath_separator();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_System_FilePath(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_System_FilePath(builtin);
}
#ifdef __cplusplus
}
#endif
