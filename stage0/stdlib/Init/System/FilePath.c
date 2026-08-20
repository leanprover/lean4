// Lean compiler output
// Module: Init.System.FilePath
// Imports: import Init.Data.String.Modify import Init.Data.String.Search public import Init.Data.ToString.Basic import Init.Data.Iterators.Consumers.Collect import Init.System.Platform import Init.Data.String.Length import Init.Data.Iterators.Combinators.Take import Init.Data.Iterators.Consumers.Access
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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_instDecidableEqPos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_next_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_next_x21(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0 = (const lean_object*)&l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00System_FilePath_normalize_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00System_FilePath_normalize_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_System_FilePath_normalize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_FilePath_normalize___closed__0;
static lean_once_cell_t l_System_FilePath_normalize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_System_FilePath_normalize___closed__1;
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
static lean_once_cell_t l_System_FilePath_isAbsolute___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_FilePath_isAbsolute___closed__0;
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object*);
static const lean_string_object l_System_FilePath_fileName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_System_FilePath_fileName___closed__0 = (const lean_object*)&l_System_FilePath_fileName___closed__0_value;
static const lean_string_object l_System_FilePath_fileName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l_System_FilePath_fileName___closed__1 = (const lean_object*)&l_System_FilePath_fileName___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(lean_object* v___x_68_, lean_object* v___x_69_, lean_object* v_a_70_, lean_object* v_b_71_){
_start:
{
lean_object* v_countdown_72_; lean_object* v_inner_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_89_; 
v_countdown_72_ = lean_ctor_get(v_a_70_, 0);
v_inner_73_ = lean_ctor_get(v_a_70_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_a_70_);
if (v_isSharedCheck_89_ == 0)
{
v___x_75_ = v_a_70_;
v_isShared_76_ = v_isSharedCheck_89_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_inner_73_);
lean_inc(v_countdown_72_);
lean_dec(v_a_70_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_89_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_dec_eq(v_countdown_72_, v___x_77_);
if (v___x_78_ == 0)
{
uint8_t v_decide_79_; 
v_decide_79_ = lean_nat_dec_eq(v_inner_73_, v___x_69_);
if (v_decide_79_ == 0)
{
lean_object* v___x_80_; uint32_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_80_ = lean_string_utf8_next_fast(v___x_68_, v_inner_73_);
v___x_81_ = lean_string_utf8_get_fast(v___x_68_, v_inner_73_);
lean_dec(v_inner_73_);
v___x_82_ = lean_nat_sub(v_countdown_72_, v___x_77_);
lean_dec(v_countdown_72_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_80_);
lean_ctor_set(v___x_75_, 0, v___x_82_);
v___x_84_ = v___x_75_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_80_);
v___x_84_ = v_reuseFailAlloc_88_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_box_uint32(v___x_81_);
v___x_86_ = lean_array_push(v_b_71_, v___x_85_);
v_a_70_ = v___x_84_;
v_b_71_ = v___x_86_;
goto _start;
}
}
else
{
lean_del_object(v___x_75_);
lean_dec(v_inner_73_);
lean_dec(v_countdown_72_);
return v_b_71_;
}
}
else
{
lean_del_object(v___x_75_);
lean_dec(v_inner_73_);
lean_dec(v_countdown_72_);
return v_b_71_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg___boxed(lean_object* v___x_90_, lean_object* v___x_91_, lean_object* v_a_92_, lean_object* v_b_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_90_, v___x_91_, v_a_92_, v_b_93_);
lean_dec(v___x_91_);
lean_dec_ref(v___x_90_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(lean_object* v_p_97_){
_start:
{
uint8_t v___x_98_; 
v___x_98_ = l_System_Platform_isWindows;
if (v___x_98_ == 0)
{
return v_p_97_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_string_utf8_byte_size(v_p_97_);
lean_inc_ref(v_p_97_);
v___x_101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_101_, 0, v_p_97_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_100_);
v___x_102_ = l_String_Slice_positions(v___x_101_);
lean_dec_ref_known(v___x_101_, 3);
v___x_103_ = lean_unsigned_to_nat(3u);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
v___x_105_ = ((lean_object*)(l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0));
v___x_106_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v_p_97_, v___x_100_, v___x_104_, v___x_105_);
v___x_107_ = lean_array_to_list(v___x_106_);
if (lean_obj_tag(v___x_107_) == 1)
{
lean_object* v_tail_108_; 
v_tail_108_ = lean_ctor_get(v___x_107_, 1);
lean_inc(v_tail_108_);
if (lean_obj_tag(v_tail_108_) == 1)
{
lean_object* v_head_109_; lean_object* v_head_110_; lean_object* v_tail_111_; uint32_t v___x_112_; uint32_t v___x_113_; uint8_t v___x_114_; 
v_head_109_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_head_109_);
lean_dec_ref_known(v___x_107_, 2);
v_head_110_ = lean_ctor_get(v_tail_108_, 0);
lean_inc(v_head_110_);
v_tail_111_ = lean_ctor_get(v_tail_108_, 1);
lean_inc(v_tail_111_);
lean_dec_ref_known(v_tail_108_, 2);
v___x_112_ = 58;
v___x_113_ = lean_unbox_uint32(v_head_110_);
lean_dec(v_head_110_);
v___x_114_ = lean_uint32_dec_eq(v___x_113_, v___x_112_);
if (v___x_114_ == 0)
{
lean_dec(v_tail_111_);
lean_dec(v_head_109_);
return v_p_97_;
}
else
{
if (lean_obj_tag(v_tail_111_) == 0)
{
uint32_t v___x_115_; uint32_t v___x_116_; uint8_t v___x_117_; 
v___x_115_ = 97;
v___x_116_ = lean_unbox_uint32(v_head_109_);
v___x_117_ = lean_uint32_dec_le(v___x_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_dec(v_head_109_);
return v_p_97_;
}
else
{
uint32_t v___x_118_; uint32_t v___x_119_; uint8_t v___x_120_; 
v___x_118_ = 122;
v___x_119_ = lean_unbox_uint32(v_head_109_);
lean_dec(v_head_109_);
v___x_120_ = lean_uint32_dec_le(v___x_119_, v___x_118_);
if (v___x_120_ == 0)
{
return v_p_97_;
}
else
{
uint32_t v___x_121_; uint8_t v___y_123_; uint8_t v___x_128_; 
v___x_121_ = lean_string_utf8_get(v_p_97_, v___x_99_);
v___x_128_ = lean_uint32_dec_le(v___x_115_, v___x_121_);
if (v___x_128_ == 0)
{
v___y_123_ = v___x_128_;
goto v___jp_122_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = lean_uint32_dec_le(v___x_121_, v___x_118_);
v___y_123_ = v___x_129_;
goto v___jp_122_;
}
v___jp_122_:
{
if (v___y_123_ == 0)
{
lean_object* v___x_124_; 
v___x_124_ = lean_string_utf8_set(v_p_97_, v___x_99_, v___x_121_);
return v___x_124_;
}
else
{
uint32_t v___x_125_; uint32_t v___x_126_; lean_object* v___x_127_; 
v___x_125_ = 4294967264;
v___x_126_ = lean_uint32_add(v___x_121_, v___x_125_);
v___x_127_ = lean_string_utf8_set(v_p_97_, v___x_99_, v___x_126_);
return v___x_127_;
}
}
}
}
}
else
{
lean_dec(v_tail_111_);
lean_dec(v_head_109_);
return v_p_97_;
}
}
}
else
{
lean_dec(v_tail_108_);
lean_dec_ref_known(v___x_107_, 2);
return v_p_97_;
}
}
else
{
lean_dec(v___x_107_);
return v_p_97_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(lean_object* v___x_130_, lean_object* v___x_131_, lean_object* v___x_132_, lean_object* v_inst_133_, lean_object* v_R_134_, lean_object* v_a_135_, lean_object* v_b_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_131_, v___x_132_, v_a_135_, v_b_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___boxed(lean_object* v___x_138_, lean_object* v___x_139_, lean_object* v___x_140_, lean_object* v_inst_141_, lean_object* v_R_142_, lean_object* v_a_143_, lean_object* v_b_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(v___x_138_, v___x_139_, v___x_140_, v_inst_141_, v_R_142_, v_a_143_, v_b_144_);
lean_dec(v___x_140_);
lean_dec_ref(v___x_139_);
lean_dec_ref(v___x_138_);
return v_res_145_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00System_FilePath_normalize_spec__0(uint32_t v_a_146_, lean_object* v_x_147_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
uint8_t v___x_148_; 
v___x_148_ = 0;
return v___x_148_;
}
else
{
lean_object* v_head_149_; lean_object* v_tail_150_; uint32_t v___x_151_; uint8_t v___x_152_; 
v_head_149_ = lean_ctor_get(v_x_147_, 0);
v_tail_150_ = lean_ctor_get(v_x_147_, 1);
v___x_151_ = lean_unbox_uint32(v_head_149_);
v___x_152_ = lean_uint32_dec_eq(v_a_146_, v___x_151_);
if (v___x_152_ == 0)
{
v_x_147_ = v_tail_150_;
goto _start;
}
else
{
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00System_FilePath_normalize_spec__0___boxed(lean_object* v_a_154_, lean_object* v_x_155_){
_start:
{
uint32_t v_a_boxed_156_; uint8_t v_res_157_; lean_object* v_r_158_; 
v_a_boxed_156_ = lean_unbox_uint32(v_a_154_);
lean_dec(v_a_154_);
v_res_157_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v_a_boxed_156_, v_x_155_);
lean_dec(v_x_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1(lean_object* v_s_159_, lean_object* v_p_160_){
_start:
{
uint32_t v___y_162_; lean_object* v___x_167_; uint8_t v_decide_168_; 
v___x_167_ = lean_string_utf8_byte_size(v_s_159_);
v_decide_168_ = lean_nat_dec_eq(v_p_160_, v___x_167_);
if (v_decide_168_ == 0)
{
lean_object* v___x_169_; uint32_t v___x_170_; uint8_t v___x_171_; 
v___x_169_ = l_System_FilePath_pathSeparators;
v___x_170_ = lean_string_utf8_get_fast(v_s_159_, v_p_160_);
v___x_171_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_170_, v___x_169_);
if (v___x_171_ == 0)
{
v___y_162_ = v___x_170_;
goto v___jp_161_;
}
else
{
uint32_t v___x_172_; 
v___x_172_ = l_System_FilePath_pathSeparator;
v___y_162_ = v___x_172_;
goto v___jp_161_;
}
}
else
{
lean_dec(v_p_160_);
return v_s_159_;
}
v___jp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
lean_inc(v_p_160_);
v___x_163_ = lean_string_utf8_set(v_s_159_, v_p_160_, v___y_162_);
v___x_164_ = l_Char_utf8Size(v___y_162_);
v___x_165_ = lean_nat_add(v_p_160_, v___x_164_);
lean_dec(v___x_164_);
lean_dec(v_p_160_);
v_s_159_ = v___x_163_;
v_p_160_ = v___x_165_;
goto _start;
}
}
}
static lean_object* _init_l_System_FilePath_normalize___closed__0(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = l_System_FilePath_pathSeparators;
v___x_174_ = l_List_lengthTR___redArg(v___x_173_);
return v___x_174_;
}
}
static uint8_t _init_l_System_FilePath_normalize___closed__1(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_obj_once(&l_System_FilePath_normalize___closed__0, &l_System_FilePath_normalize___closed__0_once, _init_l_System_FilePath_normalize___closed__0);
v___x_177_ = lean_nat_dec_eq(v___x_176_, v___x_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object* v_p_178_){
_start:
{
lean_object* v_p_179_; uint8_t v___x_180_; 
v_p_179_ = l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(v_p_178_);
v___x_180_ = lean_uint8_once(&l_System_FilePath_normalize___closed__1, &l_System_FilePath_normalize___closed__1_once, _init_l_System_FilePath_normalize___closed__1);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v_p_182_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v_p_182_ = l_String_mapAux___at___00System_FilePath_normalize_spec__1(v_p_179_, v___x_181_);
return v_p_182_;
}
else
{
return v_p_179_;
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
if (lean_obj_tag(v_x_184_) == 0)
{
uint8_t v___x_185_; 
v___x_185_ = 1;
return v___x_185_;
}
else
{
uint8_t v___x_186_; 
v___x_186_ = 0;
return v___x_186_;
}
}
else
{
if (lean_obj_tag(v_x_184_) == 0)
{
uint8_t v___x_187_; 
v___x_187_ = 0;
return v___x_187_;
}
else
{
lean_object* v_val_188_; lean_object* v_val_189_; uint32_t v___x_190_; uint32_t v___x_191_; uint8_t v___x_192_; 
v_val_188_ = lean_ctor_get(v_x_183_, 0);
v_val_189_ = lean_ctor_get(v_x_184_, 0);
v___x_190_ = lean_unbox_uint32(v_val_188_);
v___x_191_ = lean_unbox_uint32(v_val_189_);
v___x_192_ = lean_uint32_dec_eq(v___x_190_, v___x_191_);
return v___x_192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1___boxed(lean_object* v_x_193_, lean_object* v_x_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(v_x_193_, v_x_194_);
lean_dec(v_x_194_);
lean_dec(v_x_193_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(lean_object* v___x_197_, lean_object* v___x_198_, lean_object* v_a_199_, lean_object* v_b_200_){
_start:
{
lean_object* v_str_201_; lean_object* v_startInclusive_202_; lean_object* v_endExclusive_203_; lean_object* v___x_204_; uint8_t v_decide_205_; 
v_str_201_ = lean_ctor_get(v___x_198_, 0);
v_startInclusive_202_ = lean_ctor_get(v___x_198_, 1);
v_endExclusive_203_ = lean_ctor_get(v___x_198_, 2);
v___x_204_ = lean_nat_sub(v_endExclusive_203_, v_startInclusive_202_);
v_decide_205_ = lean_nat_dec_eq(v_a_199_, v___x_204_);
lean_dec(v___x_204_);
if (v_decide_205_ == 0)
{
lean_object* v_zero_206_; uint8_t v_isZero_207_; 
v_zero_206_ = lean_unsigned_to_nat(0u);
v_isZero_207_ = lean_nat_dec_eq(v_b_200_, v_zero_206_);
if (v_isZero_207_ == 1)
{
uint32_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec(v_b_200_);
v___x_208_ = lean_string_utf8_get_fast(v___x_197_, v_a_199_);
lean_dec(v_a_199_);
v___x_209_ = lean_box_uint32(v___x_208_);
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v_one_214_; lean_object* v_n_215_; 
v___x_211_ = lean_nat_add(v_startInclusive_202_, v_a_199_);
lean_dec(v_a_199_);
v___x_212_ = lean_string_utf8_next_fast(v_str_201_, v___x_211_);
lean_dec(v___x_211_);
v___x_213_ = lean_nat_sub(v___x_212_, v_startInclusive_202_);
v_one_214_ = lean_unsigned_to_nat(1u);
v_n_215_ = lean_nat_sub(v_b_200_, v_one_214_);
lean_dec(v_b_200_);
v_a_199_ = v___x_213_;
v_b_200_ = v_n_215_;
goto _start;
}
}
else
{
lean_object* v___x_217_; 
lean_dec(v_b_200_);
lean_dec(v_a_199_);
v___x_217_ = lean_box(0);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg___boxed(lean_object* v___x_218_, lean_object* v___x_219_, lean_object* v_a_220_, lean_object* v_b_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_218_, v___x_219_, v_a_220_, v_b_221_);
lean_dec_ref(v___x_219_);
lean_dec_ref(v___x_218_);
return v_res_222_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_223_; lean_object* v___x_224_; 
v___x_223_ = 58;
v___x_224_ = lean_box_uint32(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object* v_p_227_){
_start:
{
lean_object* v___x_228_; uint32_t v___y_230_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_228_ = l_System_FilePath_pathSeparators;
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_string_utf8_byte_size(v_p_227_);
lean_inc_ref(v_p_227_);
v___x_243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_243_, 0, v_p_227_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_242_);
v___x_244_ = l_String_Slice_Pos_get_x3f(v___x_243_, v___x_241_);
lean_dec_ref_known(v___x_243_, 3);
if (lean_obj_tag(v___x_244_) == 0)
{
uint32_t v___x_245_; 
v___x_245_ = 65;
v___y_230_ = v___x_245_;
goto v___jp_229_;
}
else
{
lean_object* v_val_246_; uint32_t v___x_247_; 
v_val_246_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_val_246_);
lean_dec_ref_known(v___x_244_, 1);
v___x_247_ = lean_unbox_uint32(v_val_246_);
lean_dec(v_val_246_);
v___y_230_ = v___x_247_;
goto v___jp_229_;
}
v___jp_229_:
{
uint8_t v___x_231_; 
v___x_231_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_230_, v___x_228_);
if (v___x_231_ == 0)
{
uint8_t v___x_232_; 
v___x_232_ = l_System_Platform_isWindows;
if (v___x_232_ == 0)
{
lean_dec_ref(v_p_227_);
return v___x_232_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_string_utf8_byte_size(v_p_227_);
lean_inc_ref(v_p_227_);
v___x_235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_235_, 0, v_p_227_);
lean_ctor_set(v___x_235_, 1, v___x_233_);
lean_ctor_set(v___x_235_, 2, v___x_234_);
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = l_String_Slice_positions(v___x_235_);
v___x_238_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v_p_227_, v___x_235_, v___x_237_, v___x_236_);
lean_dec_ref_known(v___x_235_, 3);
lean_dec_ref(v_p_227_);
v___x_239_ = lean_obj_once(&l_System_FilePath_isAbsolute___closed__0, &l_System_FilePath_isAbsolute___closed__0_once, _init_l_System_FilePath_isAbsolute___closed__0);
v___x_240_ = l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(v___x_238_, v___x_239_);
lean_dec(v___x_238_);
return v___x_240_;
}
}
else
{
lean_dec_ref(v_p_227_);
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object* v_p_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_System_FilePath_isAbsolute(v_p_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(lean_object* v___x_251_, lean_object* v___x_252_, lean_object* v_n_253_, lean_object* v_it_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_252_, v___x_251_, v_it_254_, v_n_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object* v___x_256_, lean_object* v___x_257_, lean_object* v_n_258_, lean_object* v_it_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(v___x_256_, v___x_257_, v_n_258_, v_it_259_);
lean_dec_ref(v___x_257_);
lean_dec_ref(v___x_256_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(lean_object* v___x_261_, lean_object* v___x_262_, lean_object* v_inst_263_, lean_object* v_R_264_, lean_object* v_a_265_, lean_object* v_b_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_261_, v___x_262_, v_a_265_, v_b_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___boxed(lean_object* v___x_268_, lean_object* v___x_269_, lean_object* v_inst_270_, lean_object* v_R_271_, lean_object* v_a_272_, lean_object* v_b_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(v___x_268_, v___x_269_, v_inst_270_, v_R_271_, v_a_272_, v_b_273_);
lean_dec_ref(v___x_269_);
lean_dec_ref(v___x_268_);
return v_res_274_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object* v_p_275_){
_start:
{
uint8_t v___x_276_; 
v___x_276_ = l_System_FilePath_isAbsolute(v_p_275_);
if (v___x_276_ == 0)
{
uint8_t v___x_277_; 
v___x_277_ = 1;
return v___x_277_;
}
else
{
uint8_t v___x_278_; 
v___x_278_ = 0;
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object* v_p_279_){
_start:
{
uint8_t v_res_280_; lean_object* v_r_281_; 
v_res_280_ = l_System_FilePath_isRelative(v_p_279_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
static lean_object* _init_l_System_FilePath_join___closed__0(void){
_start:
{
uint32_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = l_System_FilePath_pathSeparator;
v___x_283_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_284_ = lean_string_push(v___x_283_, v___x_282_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object* v_p_285_, lean_object* v_sub_286_){
_start:
{
uint8_t v___x_287_; 
lean_inc_ref(v_sub_286_);
v___x_287_ = l_System_FilePath_isAbsolute(v_sub_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_289_ = lean_string_append(v_p_285_, v___x_288_);
v___x_290_ = lean_string_append(v___x_289_, v_sub_286_);
lean_dec_ref(v_sub_286_);
return v___x_290_;
}
else
{
lean_dec_ref(v_p_285_);
return v_sub_286_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(lean_object* v_s_294_, lean_object* v_a_295_, lean_object* v_b_296_){
_start:
{
lean_object* v___x_297_; uint8_t v_decide_298_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v_decide_298_ = lean_nat_dec_eq(v_a_295_, v___x_297_);
if (v_decide_298_ == 0)
{
lean_object* v_str_299_; lean_object* v_startInclusive_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint32_t v___x_309_; uint8_t v___x_310_; 
v_str_299_ = lean_ctor_get(v_s_294_, 0);
v_startInclusive_300_ = lean_ctor_get(v_s_294_, 1);
v___x_301_ = l_System_FilePath_pathSeparators;
v___x_302_ = lean_nat_add(v_startInclusive_300_, v_a_295_);
lean_inc(v___x_302_);
lean_inc(v_startInclusive_300_);
lean_inc_ref(v_str_299_);
v___x_303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_303_, 0, v_str_299_);
lean_ctor_set(v___x_303_, 1, v_startInclusive_300_);
lean_ctor_set(v___x_303_, 2, v___x_302_);
v___x_304_ = lean_nat_sub(v___x_302_, v_startInclusive_300_);
lean_dec(v___x_302_);
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_sub(v___x_304_, v___x_305_);
lean_dec(v___x_304_);
v___x_307_ = l_String_Slice_posLE(v___x_303_, v___x_306_);
lean_dec_ref_known(v___x_303_, 3);
v___x_308_ = lean_nat_add(v_startInclusive_300_, v___x_307_);
v___x_309_ = lean_string_utf8_get_fast(v_str_299_, v___x_308_);
lean_dec(v___x_308_);
v___x_310_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_309_, v___x_301_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v___x_307_);
v___x_311_ = lean_box(0);
v___x_312_ = lean_nat_sub(v_a_295_, v___x_305_);
lean_dec(v_a_295_);
v___x_313_ = l_String_Slice_posLE(v_s_294_, v___x_312_);
v_a_295_ = v___x_313_;
v_b_296_ = v___x_311_;
goto _start;
}
else
{
lean_object* v___x_315_; 
lean_dec(v_a_295_);
v___x_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_307_);
return v___x_315_;
}
}
else
{
lean_dec(v_a_295_);
lean_inc(v_b_296_);
return v_b_296_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg___boxed(lean_object* v_s_316_, lean_object* v_a_317_, lean_object* v_b_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_316_, v_a_317_, v_b_318_);
lean_dec(v_b_318_);
lean_dec_ref(v_s_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(lean_object* v_s_320_){
_start:
{
lean_object* v_startInclusive_321_; lean_object* v_endExclusive_322_; lean_object* v_searcher_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_startInclusive_321_ = lean_ctor_get(v_s_320_, 1);
v_endExclusive_322_ = lean_ctor_get(v_s_320_, 2);
v_searcher_323_ = lean_nat_sub(v_endExclusive_322_, v_startInclusive_321_);
v___x_324_ = lean_box(0);
v___x_325_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_320_, v_searcher_323_, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___boxed(lean_object* v_s_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v_s_326_);
lean_dec_ref(v_s_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object* v_p_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = lean_string_utf8_byte_size(v_p_328_);
v___x_331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_331_, 0, v_p_328_);
lean_ctor_set(v___x_331_, 1, v___x_329_);
lean_ctor_set(v___x_331_, 2, v___x_330_);
v___x_332_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v___x_331_);
lean_dec_ref_known(v___x_331_, 3);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_box(0);
return v___x_333_;
}
else
{
lean_object* v_val_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_val_334_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_332_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_val_334_);
lean_dec(v___x_332_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_val_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(lean_object* v_s_342_, lean_object* v_inst_343_, lean_object* v_R_344_, lean_object* v_a_345_, lean_object* v_b_346_, lean_object* v_c_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_342_, v_a_345_, v_b_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___boxed(lean_object* v_s_349_, lean_object* v_inst_350_, lean_object* v_R_351_, lean_object* v_a_352_, lean_object* v_b_353_, lean_object* v_c_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(v_s_349_, v_inst_350_, v_R_351_, v_a_352_, v_b_353_, v_c_354_);
lean_dec(v_b_353_);
lean_dec_ref(v_s_349_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(lean_object* v_p_356_){
_start:
{
lean_object* v___x_357_; uint32_t v___y_359_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_357_ = l_System_FilePath_pathSeparators;
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = lean_string_utf8_byte_size(v_p_356_);
lean_inc_ref(v_p_356_);
v___x_373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_373_, 0, v_p_356_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
lean_ctor_set(v___x_373_, 2, v___x_372_);
v___x_374_ = l_String_Slice_Pos_get_x3f(v___x_373_, v___x_371_);
lean_dec_ref_known(v___x_373_, 3);
if (lean_obj_tag(v___x_374_) == 0)
{
uint32_t v___x_375_; 
v___x_375_ = 65;
v___y_359_ = v___x_375_;
goto v___jp_358_;
}
else
{
lean_object* v_val_376_; uint32_t v___x_377_; 
v_val_376_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v___x_374_, 1);
v___x_377_ = lean_unbox_uint32(v_val_376_);
lean_dec(v_val_376_);
v___y_359_ = v___x_377_;
goto v___jp_358_;
}
v___jp_358_:
{
uint8_t v___x_360_; 
v___x_360_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_359_, v___x_357_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_unsigned_to_nat(3u);
v___x_363_ = lean_string_utf8_byte_size(v_p_356_);
v___x_364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_364_, 0, v_p_356_);
lean_ctor_set(v___x_364_, 1, v___x_361_);
lean_ctor_set(v___x_364_, 2, v___x_363_);
v___x_365_ = l_String_Slice_Pos_nextn(v___x_364_, v___x_361_, v___x_362_);
lean_dec_ref_known(v___x_364_, 3);
return v___x_365_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_string_utf8_byte_size(v_p_356_);
v___x_369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_369_, 0, v_p_356_);
lean_ctor_set(v___x_369_, 1, v___x_366_);
lean_ctor_set(v___x_369_, 2, v___x_368_);
v___x_370_ = l_String_Slice_Pos_nextn(v___x_369_, v___x_366_, v___x_367_);
lean_dec_ref_known(v___x_369_, 3);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object* v_p_378_){
_start:
{
lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___x_389_; lean_object* v___y_391_; 
lean_inc_ref(v_p_378_);
v___x_389_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_378_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(0);
v___y_391_ = v___x_411_;
goto v___jp_390_;
}
else
{
lean_object* v_val_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_val_412_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_412_);
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_string_utf8_extract_fast(v_p_378_, v___x_413_, v_val_412_);
lean_dec(v_val_412_);
v___x_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
v___y_391_ = v___x_415_;
goto v___jp_390_;
}
v___jp_379_:
{
lean_object* v___x_384_; uint8_t v___x_385_; 
lean_inc(v___y_380_);
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v___y_380_);
v___x_385_ = l_Option_instDecidableEq___redArg(v___y_381_, v___y_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_dec(v___y_380_);
lean_dec_ref(v_p_378_);
return v___y_382_;
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v___y_382_);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_string_utf8_extract_fast(v_p_378_, v___x_386_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v_p_378_);
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
v___jp_390_:
{
uint8_t v___x_392_; 
lean_inc_ref(v_p_378_);
v___x_392_ = l_System_FilePath_isAbsolute(v_p_378_);
if (v___x_392_ == 0)
{
lean_dec(v___x_389_);
lean_dec_ref(v_p_378_);
return v___y_391_;
}
else
{
lean_object* v_afterRootDirectory_393_; lean_object* v___x_394_; uint8_t v_decide_395_; 
lean_inc_ref(v_p_378_);
v_afterRootDirectory_393_ = l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(v_p_378_);
v___x_394_ = lean_string_utf8_byte_size(v_p_378_);
v_decide_395_ = lean_nat_dec_eq(v_afterRootDirectory_393_, v___x_394_);
if (v_decide_395_ == 0)
{
lean_object* v___x_396_; 
lean_inc_ref(v_p_378_);
v___x_396_ = lean_alloc_closure((void*)(l_String_instDecidableEqPos___boxed), 3, 1);
lean_closure_set(v___x_396_, 0, v_p_378_);
if (lean_obj_tag(v___x_389_) == 0)
{
v___y_380_ = v_afterRootDirectory_393_;
v___y_381_ = v___x_396_;
v___y_382_ = v___y_391_;
v___y_383_ = v___x_389_;
goto v___jp_379_;
}
else
{
lean_object* v_val_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_val_397_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_397_);
lean_dec_ref_known(v___x_389_, 1);
v___x_398_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_p_378_);
v___x_399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_399_, 0, v_p_378_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
lean_ctor_set(v___x_399_, 2, v___x_394_);
v___x_400_ = l_String_Slice_Pos_next_x3f(v___x_399_, v_val_397_);
lean_dec(v_val_397_);
lean_dec_ref_known(v___x_399_, 3);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; 
v___x_401_ = lean_box(0);
v___y_380_ = v_afterRootDirectory_393_;
v___y_381_ = v___x_396_;
v___y_382_ = v___y_391_;
v___y_383_ = v___x_401_;
goto v___jp_379_;
}
else
{
lean_object* v_val_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
v_val_402_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_400_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_val_402_);
lean_dec(v___x_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_val_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
v___y_380_ = v_afterRootDirectory_393_;
v___y_381_ = v___x_396_;
v___y_382_ = v___y_391_;
v___y_383_ = v___x_407_;
goto v___jp_379_;
}
}
}
}
}
else
{
lean_object* v___x_410_; 
lean_dec(v_afterRootDirectory_393_);
lean_dec(v___y_391_);
lean_dec(v___x_389_);
lean_dec_ref(v_p_378_);
v___x_410_ = lean_box(0);
return v___x_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object* v_p_418_){
_start:
{
lean_object* v___y_420_; lean_object* v___x_432_; 
lean_inc_ref(v_p_418_);
v___x_432_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_418_);
if (lean_obj_tag(v___x_432_) == 0)
{
v___y_420_ = v_p_418_;
goto v___jp_419_;
}
else
{
lean_object* v_val_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_val_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_val_433_);
lean_dec_ref_known(v___x_432_, 1);
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_string_utf8_byte_size(v_p_418_);
lean_inc_ref(v_p_418_);
v___x_436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_436_, 0, v_p_418_);
lean_ctor_set(v___x_436_, 1, v___x_434_);
lean_ctor_set(v___x_436_, 2, v___x_435_);
v___x_437_ = l_String_Slice_Pos_next_x21(v___x_436_, v_val_433_);
lean_dec(v_val_433_);
lean_dec_ref_known(v___x_436_, 3);
v___x_438_ = lean_string_utf8_extract_fast(v_p_418_, v___x_437_, v___x_435_);
lean_dec(v___x_437_);
lean_dec_ref(v_p_418_);
v___y_420_ = v___x_438_;
goto v___jp_419_;
}
v___jp_419_:
{
lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_421_ = lean_string_utf8_byte_size(v___y_420_);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_nat_dec_eq(v___x_421_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_425_ = lean_string_dec_eq(v___y_420_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
v___x_427_ = lean_string_dec_eq(v___y_420_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
v___x_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_428_, 0, v___y_420_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; 
lean_dec_ref(v___y_420_);
v___x_429_ = lean_box(0);
return v___x_429_;
}
}
else
{
lean_object* v___x_430_; 
lean_dec_ref(v___y_420_);
v___x_430_ = lean_box(0);
return v___x_430_;
}
}
else
{
lean_object* v___x_431_; 
lean_dec_ref(v___y_420_);
v___x_431_ = lean_box(0);
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(lean_object* v_s_439_, lean_object* v_a_440_, lean_object* v_b_441_){
_start:
{
lean_object* v___x_442_; uint8_t v_decide_443_; 
v___x_442_ = lean_unsigned_to_nat(0u);
v_decide_443_ = lean_nat_dec_eq(v_a_440_, v___x_442_);
if (v_decide_443_ == 0)
{
lean_object* v_str_444_; lean_object* v_startInclusive_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint32_t v___x_453_; uint32_t v___x_454_; uint8_t v___x_455_; 
v_str_444_ = lean_ctor_get(v_s_439_, 0);
v_startInclusive_445_ = lean_ctor_get(v_s_439_, 1);
v___x_446_ = lean_nat_add(v_startInclusive_445_, v_a_440_);
lean_inc(v___x_446_);
lean_inc(v_startInclusive_445_);
lean_inc_ref(v_str_444_);
v___x_447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_447_, 0, v_str_444_);
lean_ctor_set(v___x_447_, 1, v_startInclusive_445_);
lean_ctor_set(v___x_447_, 2, v___x_446_);
v___x_448_ = lean_nat_sub(v___x_446_, v_startInclusive_445_);
lean_dec(v___x_446_);
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_nat_sub(v___x_448_, v___x_449_);
lean_dec(v___x_448_);
v___x_451_ = l_String_Slice_posLE(v___x_447_, v___x_450_);
lean_dec_ref_known(v___x_447_, 3);
v___x_452_ = lean_nat_add(v_startInclusive_445_, v___x_451_);
v___x_453_ = lean_string_utf8_get_fast(v_str_444_, v___x_452_);
lean_dec(v___x_452_);
v___x_454_ = 46;
v___x_455_ = lean_uint32_dec_eq(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v___x_451_);
v___x_456_ = lean_box(0);
v___x_457_ = lean_nat_sub(v_a_440_, v___x_449_);
lean_dec(v_a_440_);
v___x_458_ = l_String_Slice_posLE(v_s_439_, v___x_457_);
v_a_440_ = v___x_458_;
v_b_441_ = v___x_456_;
goto _start;
}
else
{
lean_object* v___x_460_; 
lean_dec(v_a_440_);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_451_);
return v___x_460_;
}
}
else
{
lean_dec(v_a_440_);
lean_inc(v_b_441_);
return v_b_441_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg___boxed(lean_object* v_s_461_, lean_object* v_a_462_, lean_object* v_b_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_461_, v_a_462_, v_b_463_);
lean_dec(v_b_463_);
lean_dec_ref(v_s_461_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(lean_object* v_s_465_){
_start:
{
lean_object* v_startInclusive_466_; lean_object* v_endExclusive_467_; lean_object* v_searcher_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_startInclusive_466_ = lean_ctor_get(v_s_465_, 1);
v_endExclusive_467_ = lean_ctor_get(v_s_465_, 2);
v_searcher_468_ = lean_nat_sub(v_endExclusive_467_, v_startInclusive_466_);
v___x_469_ = lean_box(0);
v___x_470_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_465_, v_searcher_468_, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0___boxed(lean_object* v_s_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v_s_471_);
lean_dec_ref(v_s_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object* v_p_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_System_FilePath_fileName(v_p_473_);
if (lean_obj_tag(v___x_474_) == 0)
{
return v___x_474_;
}
else
{
lean_object* v_val_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_val_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc_n(v_val_475_, 2);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_string_utf8_byte_size(v_val_475_);
v___x_478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_478_, 0, v_val_475_);
lean_ctor_set(v___x_478_, 1, v___x_476_);
lean_ctor_set(v___x_478_, 2, v___x_477_);
v___x_479_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_478_);
lean_dec_ref_known(v___x_478_, 3);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_dec(v_val_475_);
return v___x_474_;
}
else
{
lean_object* v_val_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_489_; 
v_val_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_489_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_489_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_val_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_489_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
uint8_t v___x_484_; 
v___x_484_ = lean_nat_dec_eq(v_val_480_, v___x_476_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_487_; 
lean_dec_ref_known(v___x_474_, 1);
v___x_485_ = lean_string_utf8_extract(v_val_475_, v___x_476_, v_val_480_);
lean_dec(v_val_480_);
lean_dec(v_val_475_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_485_);
v___x_487_ = v___x_482_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
else
{
lean_del_object(v___x_482_);
lean_dec(v_val_480_);
lean_dec(v_val_475_);
return v___x_474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(lean_object* v_s_490_, lean_object* v_inst_491_, lean_object* v_R_492_, lean_object* v_a_493_, lean_object* v_b_494_, lean_object* v_c_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_490_, v_a_493_, v_b_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___boxed(lean_object* v_s_497_, lean_object* v_inst_498_, lean_object* v_R_499_, lean_object* v_a_500_, lean_object* v_b_501_, lean_object* v_c_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(v_s_497_, v_inst_498_, v_R_499_, v_a_500_, v_b_501_, v_c_502_);
lean_dec(v_b_501_);
lean_dec_ref(v_s_497_);
return v_res_503_;
}
}
static lean_object* _init_l_System_FilePath_extension___closed__0(void){
_start:
{
uint32_t v___x_504_; lean_object* v___x_505_; 
v___x_504_ = 46;
v___x_505_ = l_Char_utf8Size(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object* v_p_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_System_FilePath_fileName(v_p_506_);
if (lean_obj_tag(v___x_507_) == 0)
{
return v___x_507_;
}
else
{
lean_object* v_val_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_val_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc_n(v_val_508_, 2);
lean_dec_ref_known(v___x_507_, 1);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = lean_string_utf8_byte_size(v_val_508_);
v___x_511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_511_, 0, v_val_508_);
lean_ctor_set(v___x_511_, 1, v___x_509_);
lean_ctor_set(v___x_511_, 2, v___x_510_);
v___x_512_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_511_);
lean_dec_ref_known(v___x_511_, 3);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v___x_513_; 
lean_dec(v_val_508_);
v___x_513_ = lean_box(0);
return v___x_513_;
}
else
{
lean_object* v_val_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_526_; 
v_val_514_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_526_ == 0)
{
v___x_516_ = v___x_512_;
v_isShared_517_ = v_isSharedCheck_526_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_val_514_);
lean_dec(v___x_512_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_526_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
uint8_t v___x_518_; 
v___x_518_ = lean_nat_dec_eq(v_val_514_, v___x_509_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_519_ = lean_obj_once(&l_System_FilePath_extension___closed__0, &l_System_FilePath_extension___closed__0_once, _init_l_System_FilePath_extension___closed__0);
v___x_520_ = lean_nat_add(v_val_514_, v___x_519_);
lean_dec(v_val_514_);
v___x_521_ = lean_string_utf8_extract(v_val_508_, v___x_520_, v___x_510_);
lean_dec(v___x_520_);
lean_dec(v_val_508_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_521_);
v___x_523_ = v___x_516_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
else
{
lean_object* v___x_525_; 
lean_del_object(v___x_516_);
lean_dec(v_val_514_);
lean_dec(v_val_508_);
v___x_525_ = lean_box(0);
return v___x_525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object* v_p_527_, lean_object* v_fname_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_System_FilePath_parent(v_p_527_);
if (lean_obj_tag(v___x_529_) == 0)
{
return v_fname_528_;
}
else
{
lean_object* v_val_530_; lean_object* v___x_531_; 
v_val_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_val_530_);
lean_dec_ref_known(v___x_529_, 1);
v___x_531_ = l_System_FilePath_join(v_val_530_, v_fname_528_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object* v_p_532_, lean_object* v_ext_533_){
_start:
{
lean_object* v___x_534_; 
lean_inc_ref(v_p_532_);
v___x_534_ = l_System_FilePath_fileName(v_p_532_);
if (lean_obj_tag(v___x_534_) == 0)
{
return v_p_532_;
}
else
{
lean_object* v_val_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_val_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_val_535_);
lean_dec_ref_known(v___x_534_, 1);
v___x_536_ = lean_string_utf8_byte_size(v_ext_533_);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = lean_nat_dec_eq(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_539_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_540_ = lean_string_append(v_val_535_, v___x_539_);
v___x_541_ = lean_string_append(v___x_540_, v_ext_533_);
v___x_542_ = l_System_FilePath_withFileName(v_p_532_, v___x_541_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = l_System_FilePath_withFileName(v_p_532_, v_val_535_);
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object* v_p_544_, lean_object* v_ext_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_System_FilePath_addExtension(v_p_544_, v_ext_545_);
lean_dec_ref(v_ext_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object* v_p_547_, lean_object* v_ext_548_){
_start:
{
lean_object* v___x_549_; 
lean_inc_ref(v_p_547_);
v___x_549_ = l_System_FilePath_fileStem(v_p_547_);
if (lean_obj_tag(v___x_549_) == 0)
{
return v_p_547_;
}
else
{
lean_object* v_val_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v_val_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v___x_549_, 1);
v___x_551_ = lean_string_utf8_byte_size(v_ext_548_);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_nat_dec_eq(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_554_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_555_ = lean_string_append(v_val_550_, v___x_554_);
v___x_556_ = lean_string_append(v___x_555_, v_ext_548_);
v___x_557_ = l_System_FilePath_withFileName(v_p_547_, v___x_556_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; 
v___x_558_ = l_System_FilePath_withFileName(v_p_547_, v_val_550_);
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object* v_p_559_, lean_object* v_ext_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_System_FilePath_withExtension(v_p_559_, v_ext_560_);
lean_dec_ref(v_ext_560_);
return v_res_561_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_563_ = lean_string_utf8_byte_size(v___x_562_);
return v___x_563_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
v___x_566_ = lean_nat_dec_eq(v___x_565_, v___x_564_);
return v___x_566_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
lean_ctor_set(v___x_570_, 2, v___x_567_);
return v___x_570_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2);
v___x_572_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3);
v___x_575_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2);
v___x_576_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_574_);
lean_ctor_set(v___x_576_, 2, v___x_573_);
lean_ctor_set(v___x_576_, 3, v___x_573_);
return v___x_576_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4);
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v___x_577_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(lean_object* v_s_585_){
_start:
{
uint8_t v___x_586_; 
v___x_586_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
v___x_587_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5);
return v___x_587_;
}
else
{
lean_object* v___x_588_; 
v___x_588_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7));
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(lean_object* v_s_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v_s_589_);
lean_dec_ref(v_s_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object* v___x_591_, lean_object* v___x_592_, lean_object* v___x_593_, lean_object* v_a_594_, lean_object* v_b_595_){
_start:
{
lean_object* v_it_597_; lean_object* v_startInclusive_598_; lean_object* v_endExclusive_599_; 
if (lean_obj_tag(v_a_594_) == 0)
{
lean_object* v_currPos_604_; lean_object* v_searcher_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_711_; 
v_currPos_604_ = lean_ctor_get(v_a_594_, 0);
v_searcher_605_ = lean_ctor_get(v_a_594_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_a_594_);
if (v_isSharedCheck_711_ == 0)
{
v___x_607_ = v_a_594_;
v_isShared_608_ = v_isSharedCheck_711_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_searcher_605_);
lean_inc(v_currPos_604_);
lean_dec(v_a_594_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_711_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_it_610_; lean_object* v_it_616_; lean_object* v_startPos_617_; lean_object* v_endPos_618_; 
switch(lean_obj_tag(v_searcher_605_))
{
case 0:
{
lean_object* v_pos_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_643_; 
lean_del_object(v___x_607_);
v_pos_631_ = lean_ctor_get(v_searcher_605_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v_searcher_605_);
if (v_isSharedCheck_643_ == 0)
{
v___x_633_ = v_searcher_605_;
v_isShared_634_ = v_isSharedCheck_643_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_pos_631_);
lean_dec(v_searcher_605_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_643_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v_startInclusive_635_; lean_object* v_endExclusive_636_; lean_object* v___x_637_; uint8_t v_decide_638_; 
v_startInclusive_635_ = lean_ctor_get(v___x_592_, 1);
v_endExclusive_636_ = lean_ctor_get(v___x_592_, 2);
v___x_637_ = lean_nat_sub(v_endExclusive_636_, v_startInclusive_635_);
v_decide_638_ = lean_nat_dec_eq(v_pos_631_, v___x_637_);
lean_dec(v___x_637_);
if (v_decide_638_ == 0)
{
lean_object* v___x_640_; 
lean_inc(v_pos_631_);
if (v_isShared_634_ == 0)
{
lean_ctor_set_tag(v___x_633_, 1);
v___x_640_ = v___x_633_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_pos_631_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_inc(v_pos_631_);
v_it_616_ = v___x_640_;
v_startPos_617_ = v_pos_631_;
v_endPos_618_ = v_pos_631_;
goto v___jp_615_;
}
}
else
{
lean_object* v___x_642_; 
lean_del_object(v___x_633_);
v___x_642_ = lean_box(3);
lean_inc(v_pos_631_);
v_it_616_ = v___x_642_;
v_startPos_617_ = v_pos_631_;
v_endPos_618_ = v_pos_631_;
goto v___jp_615_;
}
}
}
case 1:
{
lean_object* v_pos_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_652_; 
v_pos_644_ = lean_ctor_get(v_searcher_605_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v_searcher_605_);
if (v_isSharedCheck_652_ == 0)
{
v___x_646_ = v_searcher_605_;
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_pos_644_);
lean_dec(v_searcher_605_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = lean_string_utf8_next_fast(v___x_591_, v_pos_644_);
lean_dec(v_pos_644_);
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 0);
lean_ctor_set(v___x_646_, 0, v___x_648_);
v___x_650_ = v___x_646_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
v_it_610_ = v___x_650_;
goto v___jp_609_;
}
}
}
case 2:
{
lean_object* v_needle_653_; lean_object* v_table_654_; lean_object* v_stackPos_655_; lean_object* v_needlePos_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_710_; 
v_needle_653_ = lean_ctor_get(v_searcher_605_, 0);
v_table_654_ = lean_ctor_get(v_searcher_605_, 1);
v_stackPos_655_ = lean_ctor_get(v_searcher_605_, 2);
v_needlePos_656_ = lean_ctor_get(v_searcher_605_, 3);
v_isSharedCheck_710_ = !lean_is_exclusive(v_searcher_605_);
if (v_isSharedCheck_710_ == 0)
{
v___x_658_ = v_searcher_605_;
v_isShared_659_ = v_isSharedCheck_710_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_needlePos_656_);
lean_inc(v_stackPos_655_);
lean_inc(v_table_654_);
lean_inc(v_needle_653_);
lean_dec(v_searcher_605_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_710_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_str_660_; lean_object* v_startInclusive_661_; lean_object* v_endExclusive_662_; lean_object* v_basePos_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_str_660_ = lean_ctor_get(v_needle_653_, 0);
v_startInclusive_661_ = lean_ctor_get(v_needle_653_, 1);
v_endExclusive_662_ = lean_ctor_get(v_needle_653_, 2);
v_basePos_663_ = lean_nat_sub(v_stackPos_655_, v_needlePos_656_);
v___x_664_ = lean_nat_sub(v_endExclusive_662_, v_startInclusive_661_);
v___x_665_ = lean_nat_add(v_basePos_663_, v___x_664_);
v___x_666_ = lean_nat_dec_le(v___x_665_, v___x_593_);
lean_dec(v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
lean_dec(v___x_664_);
lean_del_object(v___x_658_);
lean_dec(v_needlePos_656_);
lean_dec(v_stackPos_655_);
lean_dec_ref(v_table_654_);
lean_dec_ref(v_needle_653_);
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_nat_add(v_basePos_663_, v___x_667_);
lean_dec(v_basePos_663_);
v___x_669_ = lean_nat_dec_le(v___x_668_, v___x_593_);
lean_dec(v___x_668_);
if (v___x_669_ == 0)
{
lean_del_object(v___x_607_);
goto v___jp_629_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = lean_box(3);
v_it_610_ = v___x_670_;
goto v___jp_609_;
}
}
else
{
uint8_t v_stackByte_671_; lean_object* v___x_672_; uint8_t v_patByte_673_; uint8_t v___x_674_; 
lean_dec(v_basePos_663_);
lean_inc(v_stackPos_655_);
v_stackByte_671_ = lean_string_get_byte_fast(v___x_591_, v_stackPos_655_);
v___x_672_ = lean_nat_add(v_startInclusive_661_, v_needlePos_656_);
v_patByte_673_ = lean_string_get_byte_fast(v_str_660_, v___x_672_);
v___x_674_ = lean_uint8_dec_eq(v_stackByte_671_, v_patByte_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; uint8_t v_decide_676_; 
lean_dec(v___x_664_);
v___x_675_ = lean_unsigned_to_nat(0u);
v_decide_676_ = lean_nat_dec_eq(v_needlePos_656_, v___x_675_);
if (v_decide_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_newNeedlePos_679_; uint8_t v___x_680_; 
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = lean_nat_sub(v_needlePos_656_, v___x_677_);
lean_dec(v_needlePos_656_);
v_newNeedlePos_679_ = lean_array_fget_borrowed(v_table_654_, v___x_678_);
lean_dec(v___x_678_);
v___x_680_ = lean_nat_dec_eq(v_newNeedlePos_679_, v___x_675_);
if (v___x_680_ == 0)
{
lean_object* v___x_682_; 
lean_inc(v_newNeedlePos_679_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 3, v_newNeedlePos_679_);
v___x_682_ = v___x_658_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_needle_653_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_table_654_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_stackPos_655_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v_newNeedlePos_679_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
v_it_610_ = v___x_682_;
goto v___jp_609_;
}
}
else
{
lean_object* v_nextStackPos_684_; lean_object* v___x_686_; 
v_nextStackPos_684_ = l_String_Slice_posGE___redArg(v___x_592_, v_stackPos_655_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 3, v___x_675_);
lean_ctor_set(v___x_658_, 2, v_nextStackPos_684_);
v___x_686_ = v___x_658_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_needle_653_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_table_654_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_nextStackPos_684_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v___x_675_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
v_it_610_ = v___x_686_;
goto v___jp_609_;
}
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_nextStackPos_690_; lean_object* v___x_692_; 
lean_dec(v_needlePos_656_);
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = lean_nat_add(v_stackPos_655_, v___x_688_);
lean_dec(v_stackPos_655_);
v_nextStackPos_690_ = l_String_Slice_posGE___redArg(v___x_592_, v___x_689_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 3, v___x_675_);
lean_ctor_set(v___x_658_, 2, v_nextStackPos_690_);
v___x_692_ = v___x_658_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_needle_653_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_table_654_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_nextStackPos_690_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v___x_675_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
v_it_610_ = v___x_692_;
goto v___jp_609_;
}
}
}
else
{
lean_object* v___x_694_; lean_object* v_nextStackPos_695_; lean_object* v_nextNeedlePos_696_; uint8_t v_decide_697_; 
lean_del_object(v___x_607_);
v___x_694_ = lean_unsigned_to_nat(1u);
v_nextStackPos_695_ = lean_nat_add(v_stackPos_655_, v___x_694_);
lean_dec(v_stackPos_655_);
v_nextNeedlePos_696_ = lean_nat_add(v_needlePos_656_, v___x_694_);
lean_dec(v_needlePos_656_);
v_decide_697_ = lean_nat_dec_eq(v_nextNeedlePos_696_, v___x_664_);
lean_dec(v___x_664_);
if (v_decide_697_ == 0)
{
lean_object* v___x_699_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 3, v_nextNeedlePos_696_);
lean_ctor_set(v___x_658_, 2, v_nextStackPos_695_);
v___x_699_ = v___x_658_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_needle_653_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_table_654_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_nextStackPos_695_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_nextNeedlePos_696_);
v___x_699_ = v_reuseFailAlloc_702_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; 
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v_currPos_604_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v_a_594_ = v___x_700_;
goto _start;
}
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_703_ = lean_nat_sub(v_nextStackPos_695_, v_nextNeedlePos_696_);
lean_dec(v_nextNeedlePos_696_);
v___x_704_ = l_String_Slice_pos_x21(v___x_592_, v___x_703_);
lean_dec(v___x_703_);
v___x_705_ = l_String_Slice_pos_x21(v___x_592_, v_nextStackPos_695_);
v___x_706_ = lean_unsigned_to_nat(0u);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 3, v___x_706_);
lean_ctor_set(v___x_658_, 2, v_nextStackPos_695_);
v___x_708_ = v___x_658_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_needle_653_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_table_654_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_nextStackPos_695_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
v_it_616_ = v___x_708_;
v_startPos_617_ = v___x_704_;
v_endPos_618_ = v___x_705_;
goto v___jp_615_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_607_);
goto v___jp_629_;
}
}
v___jp_609_:
{
lean_object* v___x_612_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v_it_610_);
v___x_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_currPos_604_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_it_610_);
v___x_612_ = v_reuseFailAlloc_614_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
v_a_594_ = v___x_612_;
goto _start;
}
}
v___jp_615_:
{
lean_object* v_slice_619_; lean_object* v_startInclusive_620_; lean_object* v_endExclusive_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
v_slice_619_ = l_String_Slice_subslice_x21(v___x_592_, v_currPos_604_, v_startPos_617_);
v_startInclusive_620_ = lean_ctor_get(v_slice_619_, 0);
v_endExclusive_621_ = lean_ctor_get(v_slice_619_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_slice_619_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v_slice_619_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_endExclusive_621_);
lean_inc(v_startInclusive_620_);
lean_dec(v_slice_619_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_nextIt_626_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v_it_616_);
lean_ctor_set(v___x_623_, 0, v_endPos_618_);
v_nextIt_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_endPos_618_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_it_616_);
v_nextIt_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
v_it_597_ = v_nextIt_626_;
v_startInclusive_598_ = v_startInclusive_620_;
v_endExclusive_599_ = v_endExclusive_621_;
goto v___jp_596_;
}
}
}
v___jp_629_:
{
lean_object* v___x_630_; 
v___x_630_ = lean_box(1);
lean_inc(v___x_593_);
v_it_597_ = v___x_630_;
v_startInclusive_598_ = v_currPos_604_;
v_endExclusive_599_ = v___x_593_;
goto v___jp_596_;
}
}
}
else
{
lean_dec(v___x_593_);
lean_dec_ref(v___x_591_);
return v_b_595_;
}
v___jp_596_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_inc_ref(v___x_591_);
v___x_600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_600_, 0, v___x_591_);
lean_ctor_set(v___x_600_, 1, v_startInclusive_598_);
lean_ctor_set(v___x_600_, 2, v_endExclusive_599_);
v___x_601_ = l_String_Slice_toString(v___x_600_);
lean_dec_ref_known(v___x_600_, 3);
v___x_602_ = lean_array_push(v_b_595_, v___x_601_);
v_a_594_ = v_it_597_;
v_b_595_ = v___x_602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object* v___x_712_, lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v_a_715_, lean_object* v_b_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_712_, v___x_713_, v___x_714_, v_a_715_, v_b_716_);
lean_dec_ref(v___x_713_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object* v_p_720_){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_721_ = l_System_FilePath_normalize(v_p_720_);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_string_utf8_byte_size(v___x_721_);
lean_inc_ref(v___x_721_);
v___x_724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_724_, 0, v___x_721_);
lean_ctor_set(v___x_724_, 1, v___x_722_);
lean_ctor_set(v___x_724_, 2, v___x_723_);
v___x_725_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v___x_724_);
v___x_726_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_727_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_721_, v___x_724_, v___x_723_, v___x_725_, v___x_726_);
lean_dec_ref_known(v___x_724_, 3);
v___x_728_ = lean_array_to_list(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object* v___x_729_, lean_object* v___x_730_, lean_object* v___x_731_, lean_object* v_inst_732_, lean_object* v_R_733_, lean_object* v_a_734_, lean_object* v_b_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_729_, v___x_730_, v___x_731_, v_a_734_, v_b_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object* v___x_737_, lean_object* v___x_738_, lean_object* v___x_739_, lean_object* v_inst_740_, lean_object* v_R_741_, lean_object* v_a_742_, lean_object* v_b_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(v___x_737_, v___x_738_, v___x_739_, v_inst_740_, v_R_741_, v_a_742_, v_b_743_);
lean_dec_ref(v___x_738_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object* v_parts_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_747_ = l_String_intercalate(v___x_746_, v_parts_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object* v_toString_748_){
_start:
{
lean_inc_ref(v_toString_748_);
return v_toString_748_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object* v_toString_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_System_instCoeStringFilePath___lam__0(v_toString_749_);
lean_dec_ref(v_toString_749_);
return v_res_750_;
}
}
static uint32_t _init_l_System_SearchPath_separator(void){
_start:
{
uint8_t v___x_753_; 
v___x_753_ = l_System_Platform_isWindows;
if (v___x_753_ == 0)
{
uint32_t v___x_754_; 
v___x_754_ = 58;
return v___x_754_;
}
else
{
uint32_t v___x_755_; 
v___x_755_ = 59;
return v___x_755_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(lean_object* v_s_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0));
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___boxed(lean_object* v_s_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v_s_760_);
lean_dec_ref(v_s_760_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(lean_object* v_s_762_, lean_object* v___x_763_, lean_object* v___x_764_, lean_object* v_a_765_, lean_object* v_b_766_){
_start:
{
lean_object* v_it_768_; lean_object* v_startInclusive_769_; lean_object* v_endExclusive_770_; 
if (lean_obj_tag(v_a_765_) == 0)
{
lean_object* v_currPos_774_; lean_object* v_searcher_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_798_; 
v_currPos_774_ = lean_ctor_get(v_a_765_, 0);
v_searcher_775_ = lean_ctor_get(v_a_765_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_a_765_);
if (v_isSharedCheck_798_ == 0)
{
v___x_777_ = v_a_765_;
v_isShared_778_ = v_isSharedCheck_798_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_searcher_775_);
lean_inc(v_currPos_774_);
lean_dec(v_a_765_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_798_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
uint8_t v_decide_779_; 
v_decide_779_ = lean_nat_dec_eq(v_searcher_775_, v___x_764_);
if (v_decide_779_ == 0)
{
uint32_t v___x_780_; uint32_t v___x_781_; uint8_t v___x_782_; 
v___x_780_ = l_System_SearchPath_separator;
v___x_781_ = lean_string_utf8_get_fast(v_s_762_, v_searcher_775_);
v___x_782_ = lean_uint32_dec_eq(v___x_781_, v___x_780_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = lean_string_utf8_next_fast(v_s_762_, v_searcher_775_);
lean_dec(v_searcher_775_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_783_);
v___x_785_ = v___x_777_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_currPos_774_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v___x_783_);
v___x_785_ = v_reuseFailAlloc_787_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
v_a_765_ = v___x_785_;
goto _start;
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v_slice_791_; lean_object* v_nextIt_793_; 
v___x_788_ = lean_string_utf8_next_fast(v_s_762_, v_searcher_775_);
v___x_789_ = lean_nat_sub(v___x_788_, v_searcher_775_);
v___x_790_ = lean_nat_add(v_searcher_775_, v___x_789_);
lean_dec(v___x_789_);
v_slice_791_ = l_String_Slice_subslice_x21(v___x_763_, v_currPos_774_, v_searcher_775_);
lean_inc(v___x_790_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_790_);
lean_ctor_set(v___x_777_, 0, v___x_790_);
v_nextIt_793_ = v___x_777_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_790_);
v_nextIt_793_ = v_reuseFailAlloc_796_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v_startInclusive_794_; lean_object* v_endExclusive_795_; 
v_startInclusive_794_ = lean_ctor_get(v_slice_791_, 0);
lean_inc(v_startInclusive_794_);
v_endExclusive_795_ = lean_ctor_get(v_slice_791_, 1);
lean_inc(v_endExclusive_795_);
lean_dec_ref(v_slice_791_);
v_it_768_ = v_nextIt_793_;
v_startInclusive_769_ = v_startInclusive_794_;
v_endExclusive_770_ = v_endExclusive_795_;
goto v___jp_767_;
}
}
}
else
{
lean_object* v___x_797_; 
lean_del_object(v___x_777_);
lean_dec(v_searcher_775_);
v___x_797_ = lean_box(1);
lean_inc(v___x_764_);
v_it_768_ = v___x_797_;
v_startInclusive_769_ = v_currPos_774_;
v_endExclusive_770_ = v___x_764_;
goto v___jp_767_;
}
}
}
else
{
lean_dec(v___x_764_);
return v_b_766_;
}
v___jp_767_:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_string_utf8_extract_fast(v_s_762_, v_startInclusive_769_, v_endExclusive_770_);
lean_dec(v_endExclusive_770_);
lean_dec(v_startInclusive_769_);
v___x_772_ = lean_array_push(v_b_766_, v___x_771_);
v_a_765_ = v_it_768_;
v_b_766_ = v___x_772_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg___boxed(lean_object* v_s_799_, lean_object* v___x_800_, lean_object* v___x_801_, lean_object* v_a_802_, lean_object* v_b_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_799_, v___x_800_, v___x_801_, v_a_802_, v_b_803_);
lean_dec_ref(v___x_800_);
lean_dec_ref(v_s_799_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object* v_s_805_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = lean_string_utf8_byte_size(v_s_805_);
lean_inc_ref(v_s_805_);
v___x_808_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_808_, 0, v_s_805_);
lean_ctor_set(v___x_808_, 1, v___x_806_);
lean_ctor_set(v___x_808_, 2, v___x_807_);
v___x_809_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v___x_808_);
v___x_810_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_811_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_805_, v___x_808_, v___x_807_, v___x_809_, v___x_810_);
lean_dec_ref_known(v___x_808_, 3);
lean_dec_ref(v_s_805_);
v___x_812_ = lean_array_to_list(v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(lean_object* v_s_813_, lean_object* v___x_814_, lean_object* v___x_815_, lean_object* v_inst_816_, lean_object* v_R_817_, lean_object* v_a_818_, lean_object* v_b_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_813_, v___x_814_, v___x_815_, v_a_818_, v_b_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___boxed(lean_object* v_s_821_, lean_object* v___x_822_, lean_object* v___x_823_, lean_object* v_inst_824_, lean_object* v_R_825_, lean_object* v_a_826_, lean_object* v_b_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(v_s_821_, v___x_822_, v___x_823_, v_inst_824_, v_R_825_, v_a_826_, v_b_827_);
lean_dec_ref(v___x_822_);
lean_dec_ref(v_s_821_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
if (lean_obj_tag(v_a_829_) == 0)
{
lean_object* v___x_831_; 
v___x_831_ = l_List_reverse___redArg(v_a_830_);
return v___x_831_;
}
else
{
lean_object* v_head_832_; lean_object* v_tail_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_841_; 
v_head_832_ = lean_ctor_get(v_a_829_, 0);
v_tail_833_ = lean_ctor_get(v_a_829_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_a_829_);
if (v_isSharedCheck_841_ == 0)
{
v___x_835_ = v_a_829_;
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_tail_833_);
lean_inc(v_head_832_);
lean_dec(v_a_829_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v_a_830_);
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_head_832_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_a_830_);
v___x_838_ = v_reuseFailAlloc_840_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
v_a_829_ = v_tail_833_;
v_a_830_ = v___x_838_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_System_SearchPath_toString___closed__0(void){
_start:
{
uint32_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = l_System_SearchPath_separator;
v___x_843_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_844_ = lean_string_push(v___x_843_, v___x_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object* v_path_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_846_ = lean_obj_once(&l_System_SearchPath_toString___closed__0, &l_System_SearchPath_toString___closed__0_once, _init_l_System_SearchPath_toString___closed__0);
v___x_847_ = lean_box(0);
v___x_848_ = l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(v_path_845_, v___x_847_);
v___x_849_ = l_String_intercalate(v___x_846_, v___x_848_);
return v___x_849_;
}
}
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
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
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_Take(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin);
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
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Access(builtin);
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
