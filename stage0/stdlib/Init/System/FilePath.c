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
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0 = (const lean_object*)&l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0_value;
static const lean_array_object l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__1 = (const lean_object*)&l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__1_value;
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
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__6 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__6_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__6_value)}};
static const lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__7 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0;
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0;
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
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(lean_object* v_p_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = l_System_Platform_isWindows;
if (v___x_101_ == 0)
{
return v_p_100_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_string_utf8_byte_size(v_p_100_);
v___x_104_ = ((lean_object*)(l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0));
v___x_105_ = ((lean_object*)(l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__1));
v___x_106_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v_p_100_, v___x_103_, v___x_104_, v___x_105_);
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
return v_p_100_;
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
return v_p_100_;
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
return v_p_100_;
}
else
{
uint32_t v___x_121_; uint8_t v___y_123_; uint8_t v___x_128_; 
v___x_121_ = lean_string_utf8_get(v_p_100_, v___x_102_);
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
v___x_124_ = lean_string_utf8_set(v_p_100_, v___x_102_, v___x_121_);
return v___x_124_;
}
else
{
uint32_t v___x_125_; uint32_t v___x_126_; lean_object* v___x_127_; 
v___x_125_ = 4294967264;
v___x_126_ = lean_uint32_add(v___x_121_, v___x_125_);
v___x_127_ = lean_string_utf8_set(v_p_100_, v___x_102_, v___x_126_);
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
return v_p_100_;
}
}
}
else
{
lean_dec_ref_known(v___x_107_, 2);
lean_dec(v_tail_108_);
return v_p_100_;
}
}
else
{
lean_dec(v___x_107_);
return v_p_100_;
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
lean_object* v___x_228_; uint32_t v___y_230_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_228_ = l_System_FilePath_pathSeparators;
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_string_utf8_byte_size(v_p_227_);
lean_inc_ref(v_p_227_);
v___x_242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_242_, 0, v_p_227_);
lean_ctor_set(v___x_242_, 1, v___x_240_);
lean_ctor_set(v___x_242_, 2, v___x_241_);
v___x_243_ = l_String_Slice_Pos_get_x3f(v___x_242_, v___x_240_);
lean_dec_ref_known(v___x_242_, 3);
if (lean_obj_tag(v___x_243_) == 0)
{
uint32_t v___x_244_; 
v___x_244_ = 65;
v___y_230_ = v___x_244_;
goto v___jp_229_;
}
else
{
lean_object* v_val_245_; uint32_t v___x_246_; 
v_val_245_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_val_245_);
lean_dec_ref_known(v___x_243_, 1);
v___x_246_ = lean_unbox_uint32(v_val_245_);
lean_dec(v_val_245_);
v___y_230_ = v___x_246_;
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
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_string_utf8_byte_size(v_p_227_);
lean_inc_ref(v_p_227_);
v___x_235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_235_, 0, v_p_227_);
lean_ctor_set(v___x_235_, 1, v___x_233_);
lean_ctor_set(v___x_235_, 2, v___x_234_);
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v_p_227_, v___x_235_, v___x_233_, v___x_236_);
lean_dec_ref_known(v___x_235_, 3);
lean_dec_ref(v_p_227_);
v___x_238_ = lean_obj_once(&l_System_FilePath_isAbsolute___closed__0, &l_System_FilePath_isAbsolute___closed__0_once, _init_l_System_FilePath_isAbsolute___closed__0);
v___x_239_ = l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(v___x_237_, v___x_238_);
lean_dec(v___x_237_);
return v___x_239_;
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
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object* v_p_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_System_FilePath_isAbsolute(v_p_247_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(lean_object* v___x_250_, lean_object* v___x_251_, lean_object* v_n_252_, lean_object* v_it_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_251_, v___x_250_, v_it_253_, v_n_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object* v___x_255_, lean_object* v___x_256_, lean_object* v_n_257_, lean_object* v_it_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(v___x_255_, v___x_256_, v_n_257_, v_it_258_);
lean_dec_ref(v___x_256_);
lean_dec_ref(v___x_255_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(lean_object* v___x_260_, lean_object* v___x_261_, lean_object* v_inst_262_, lean_object* v_R_263_, lean_object* v_a_264_, lean_object* v_b_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_260_, v___x_261_, v_a_264_, v_b_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___boxed(lean_object* v___x_267_, lean_object* v___x_268_, lean_object* v_inst_269_, lean_object* v_R_270_, lean_object* v_a_271_, lean_object* v_b_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(v___x_267_, v___x_268_, v_inst_269_, v_R_270_, v_a_271_, v_b_272_);
lean_dec_ref(v___x_268_);
lean_dec_ref(v___x_267_);
return v_res_273_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object* v_p_274_){
_start:
{
uint8_t v___x_275_; 
v___x_275_ = l_System_FilePath_isAbsolute(v_p_274_);
if (v___x_275_ == 0)
{
uint8_t v___x_276_; 
v___x_276_ = 1;
return v___x_276_;
}
else
{
uint8_t v___x_277_; 
v___x_277_ = 0;
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object* v_p_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_System_FilePath_isRelative(v_p_278_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
static lean_object* _init_l_System_FilePath_join___closed__0(void){
_start:
{
uint32_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = l_System_FilePath_pathSeparator;
v___x_282_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_283_ = lean_string_push(v___x_282_, v___x_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object* v_p_284_, lean_object* v_sub_285_){
_start:
{
uint8_t v___x_286_; 
lean_inc_ref(v_sub_285_);
v___x_286_ = l_System_FilePath_isAbsolute(v_sub_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_288_ = lean_string_append(v_p_284_, v___x_287_);
v___x_289_ = lean_string_append(v___x_288_, v_sub_285_);
lean_dec_ref(v_sub_285_);
return v___x_289_;
}
else
{
lean_dec_ref(v_p_284_);
return v_sub_285_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(lean_object* v_s_293_, lean_object* v_a_294_, lean_object* v_b_295_){
_start:
{
lean_object* v___x_296_; uint8_t v_decide_297_; 
v___x_296_ = lean_unsigned_to_nat(0u);
v_decide_297_ = lean_nat_dec_eq(v_a_294_, v___x_296_);
if (v_decide_297_ == 0)
{
lean_object* v_str_298_; lean_object* v_startInclusive_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint32_t v___x_308_; uint8_t v___x_309_; 
v_str_298_ = lean_ctor_get(v_s_293_, 0);
v_startInclusive_299_ = lean_ctor_get(v_s_293_, 1);
v___x_300_ = l_System_FilePath_pathSeparators;
v___x_301_ = lean_nat_add(v_startInclusive_299_, v_a_294_);
lean_inc(v___x_301_);
lean_inc(v_startInclusive_299_);
lean_inc_ref(v_str_298_);
v___x_302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_302_, 0, v_str_298_);
lean_ctor_set(v___x_302_, 1, v_startInclusive_299_);
lean_ctor_set(v___x_302_, 2, v___x_301_);
v___x_303_ = lean_nat_sub(v___x_301_, v_startInclusive_299_);
lean_dec(v___x_301_);
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = lean_nat_sub(v___x_303_, v___x_304_);
lean_dec(v___x_303_);
v___x_306_ = l_String_Slice_posLE(v___x_302_, v___x_305_);
lean_dec_ref_known(v___x_302_, 3);
v___x_307_ = lean_nat_add(v_startInclusive_299_, v___x_306_);
v___x_308_ = lean_string_utf8_get_fast(v_str_298_, v___x_307_);
lean_dec(v___x_307_);
v___x_309_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_308_, v___x_300_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v___x_306_);
v___x_310_ = lean_box(0);
v___x_311_ = lean_nat_sub(v_a_294_, v___x_304_);
lean_dec(v_a_294_);
v___x_312_ = l_String_Slice_posLE(v_s_293_, v___x_311_);
v_a_294_ = v___x_312_;
v_b_295_ = v___x_310_;
goto _start;
}
else
{
lean_object* v___x_314_; 
lean_dec(v_a_294_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_306_);
return v___x_314_;
}
}
else
{
lean_dec(v_a_294_);
lean_inc(v_b_295_);
return v_b_295_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg___boxed(lean_object* v_s_315_, lean_object* v_a_316_, lean_object* v_b_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_315_, v_a_316_, v_b_317_);
lean_dec(v_b_317_);
lean_dec_ref(v_s_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(lean_object* v_s_319_){
_start:
{
lean_object* v_startInclusive_320_; lean_object* v_endExclusive_321_; lean_object* v_searcher_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_startInclusive_320_ = lean_ctor_get(v_s_319_, 1);
v_endExclusive_321_ = lean_ctor_get(v_s_319_, 2);
v_searcher_322_ = lean_nat_sub(v_endExclusive_321_, v_startInclusive_320_);
v___x_323_ = lean_box(0);
v___x_324_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_319_, v_searcher_322_, v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___boxed(lean_object* v_s_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v_s_325_);
lean_dec_ref(v_s_325_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object* v_p_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_string_utf8_byte_size(v_p_327_);
v___x_330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_330_, 0, v_p_327_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
lean_ctor_set(v___x_330_, 2, v___x_329_);
v___x_331_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v___x_330_);
lean_dec_ref_known(v___x_330_, 3);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v___x_332_; 
v___x_332_ = lean_box(0);
return v___x_332_;
}
else
{
lean_object* v_val_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
v_val_333_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_331_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_val_333_);
lean_dec(v___x_331_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_val_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(lean_object* v_s_341_, lean_object* v_inst_342_, lean_object* v_R_343_, lean_object* v_a_344_, lean_object* v_b_345_, lean_object* v_c_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_341_, v_a_344_, v_b_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___boxed(lean_object* v_s_348_, lean_object* v_inst_349_, lean_object* v_R_350_, lean_object* v_a_351_, lean_object* v_b_352_, lean_object* v_c_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(v_s_348_, v_inst_349_, v_R_350_, v_a_351_, v_b_352_, v_c_353_);
lean_dec(v_b_352_);
lean_dec_ref(v_s_348_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(lean_object* v_p_355_){
_start:
{
lean_object* v___x_356_; uint32_t v___y_358_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_356_ = l_System_FilePath_pathSeparators;
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = lean_string_utf8_byte_size(v_p_355_);
lean_inc_ref(v_p_355_);
v___x_372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_372_, 0, v_p_355_);
lean_ctor_set(v___x_372_, 1, v___x_370_);
lean_ctor_set(v___x_372_, 2, v___x_371_);
v___x_373_ = l_String_Slice_Pos_get_x3f(v___x_372_, v___x_370_);
lean_dec_ref_known(v___x_372_, 3);
if (lean_obj_tag(v___x_373_) == 0)
{
uint32_t v___x_374_; 
v___x_374_ = 65;
v___y_358_ = v___x_374_;
goto v___jp_357_;
}
else
{
lean_object* v_val_375_; uint32_t v___x_376_; 
v_val_375_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_val_375_);
lean_dec_ref_known(v___x_373_, 1);
v___x_376_ = lean_unbox_uint32(v_val_375_);
lean_dec(v_val_375_);
v___y_358_ = v___x_376_;
goto v___jp_357_;
}
v___jp_357_:
{
uint8_t v___x_359_; 
v___x_359_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_358_, v___x_356_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_unsigned_to_nat(3u);
v___x_362_ = lean_string_utf8_byte_size(v_p_355_);
v___x_363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_363_, 0, v_p_355_);
lean_ctor_set(v___x_363_, 1, v___x_360_);
lean_ctor_set(v___x_363_, 2, v___x_362_);
v___x_364_ = l_String_Slice_Pos_nextn(v___x_363_, v___x_360_, v___x_361_);
lean_dec_ref_known(v___x_363_, 3);
return v___x_364_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = lean_string_utf8_byte_size(v_p_355_);
v___x_368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_368_, 0, v_p_355_);
lean_ctor_set(v___x_368_, 1, v___x_365_);
lean_ctor_set(v___x_368_, 2, v___x_367_);
v___x_369_ = l_String_Slice_Pos_nextn(v___x_368_, v___x_365_, v___x_366_);
lean_dec_ref_known(v___x_368_, 3);
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object* v_p_377_){
_start:
{
lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___x_388_; lean_object* v___y_390_; 
lean_inc_ref(v_p_377_);
v___x_388_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_377_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v___x_410_; 
v___x_410_ = lean_box(0);
v___y_390_ = v___x_410_;
goto v___jp_389_;
}
else
{
lean_object* v_val_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_val_411_ = lean_ctor_get(v___x_388_, 0);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_string_utf8_extract_fast(v_p_377_, v___x_412_, v_val_411_);
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
v___y_390_ = v___x_414_;
goto v___jp_389_;
}
v___jp_378_:
{
lean_object* v___x_383_; uint8_t v___x_384_; 
lean_inc(v___y_380_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___y_380_);
v___x_384_ = l_Option_instDecidableEq___redArg(v___y_381_, v___y_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_dec(v___y_380_);
lean_dec_ref(v_p_377_);
return v___y_379_;
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v___y_379_);
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_string_utf8_extract_fast(v_p_377_, v___x_385_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v_p_377_);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
v___jp_389_:
{
uint8_t v___x_391_; 
lean_inc_ref(v_p_377_);
v___x_391_ = l_System_FilePath_isAbsolute(v_p_377_);
if (v___x_391_ == 0)
{
lean_dec(v___x_388_);
lean_dec_ref(v_p_377_);
return v___y_390_;
}
else
{
lean_object* v_afterRootDirectory_392_; lean_object* v___x_393_; uint8_t v_decide_394_; 
lean_inc_ref(v_p_377_);
v_afterRootDirectory_392_ = l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(v_p_377_);
v___x_393_ = lean_string_utf8_byte_size(v_p_377_);
v_decide_394_ = lean_nat_dec_eq(v_afterRootDirectory_392_, v___x_393_);
if (v_decide_394_ == 0)
{
lean_object* v___x_395_; 
lean_inc_ref(v_p_377_);
v___x_395_ = lean_alloc_closure((void*)(l_String_instDecidableEqPos___boxed), 3, 1);
lean_closure_set(v___x_395_, 0, v_p_377_);
if (lean_obj_tag(v___x_388_) == 0)
{
v___y_379_ = v___y_390_;
v___y_380_ = v_afterRootDirectory_392_;
v___y_381_ = v___x_395_;
v___y_382_ = v___x_388_;
goto v___jp_378_;
}
else
{
lean_object* v_val_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_val_396_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v___x_388_, 1);
v___x_397_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_p_377_);
v___x_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_398_, 0, v_p_377_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
lean_ctor_set(v___x_398_, 2, v___x_393_);
v___x_399_ = l_String_Slice_Pos_next_x3f(v___x_398_, v_val_396_);
lean_dec(v_val_396_);
lean_dec_ref_known(v___x_398_, 3);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v___x_400_; 
v___x_400_ = lean_box(0);
v___y_379_ = v___y_390_;
v___y_380_ = v_afterRootDirectory_392_;
v___y_381_ = v___x_395_;
v___y_382_ = v___x_400_;
goto v___jp_378_;
}
else
{
lean_object* v_val_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
v_val_401_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_399_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_val_401_);
lean_dec(v___x_399_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_val_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
v___y_379_ = v___y_390_;
v___y_380_ = v_afterRootDirectory_392_;
v___y_381_ = v___x_395_;
v___y_382_ = v___x_406_;
goto v___jp_378_;
}
}
}
}
}
else
{
lean_object* v___x_409_; 
lean_dec(v_afterRootDirectory_392_);
lean_dec(v___y_390_);
lean_dec(v___x_388_);
lean_dec_ref(v_p_377_);
v___x_409_ = lean_box(0);
return v___x_409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object* v_p_417_){
_start:
{
lean_object* v___y_419_; lean_object* v___x_431_; 
lean_inc_ref(v_p_417_);
v___x_431_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_417_);
if (lean_obj_tag(v___x_431_) == 0)
{
v___y_419_ = v_p_417_;
goto v___jp_418_;
}
else
{
lean_object* v_val_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_val_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_val_432_);
lean_dec_ref_known(v___x_431_, 1);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_string_utf8_byte_size(v_p_417_);
lean_inc_ref(v_p_417_);
v___x_435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_435_, 0, v_p_417_);
lean_ctor_set(v___x_435_, 1, v___x_433_);
lean_ctor_set(v___x_435_, 2, v___x_434_);
v___x_436_ = l_String_Slice_Pos_next_x21(v___x_435_, v_val_432_);
lean_dec(v_val_432_);
lean_dec_ref_known(v___x_435_, 3);
v___x_437_ = lean_string_utf8_extract_fast(v_p_417_, v___x_436_, v___x_434_);
lean_dec(v___x_436_);
lean_dec_ref(v_p_417_);
v___y_419_ = v___x_437_;
goto v___jp_418_;
}
v___jp_418_:
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_420_ = lean_string_utf8_byte_size(v___y_419_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_nat_dec_eq(v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_424_ = lean_string_dec_eq(v___y_419_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
v___x_426_ = lean_string_dec_eq(v___y_419_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v___y_419_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; 
lean_dec_ref(v___y_419_);
v___x_428_ = lean_box(0);
return v___x_428_;
}
}
else
{
lean_object* v___x_429_; 
lean_dec_ref(v___y_419_);
v___x_429_ = lean_box(0);
return v___x_429_;
}
}
else
{
lean_object* v___x_430_; 
lean_dec_ref(v___y_419_);
v___x_430_ = lean_box(0);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(lean_object* v_s_438_, lean_object* v_a_439_, lean_object* v_b_440_){
_start:
{
lean_object* v___x_441_; uint8_t v_decide_442_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v_decide_442_ = lean_nat_dec_eq(v_a_439_, v___x_441_);
if (v_decide_442_ == 0)
{
lean_object* v_str_443_; lean_object* v_startInclusive_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint32_t v___x_452_; uint32_t v___x_453_; uint8_t v___x_454_; 
v_str_443_ = lean_ctor_get(v_s_438_, 0);
v_startInclusive_444_ = lean_ctor_get(v_s_438_, 1);
v___x_445_ = lean_nat_add(v_startInclusive_444_, v_a_439_);
lean_inc(v___x_445_);
lean_inc(v_startInclusive_444_);
lean_inc_ref(v_str_443_);
v___x_446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_446_, 0, v_str_443_);
lean_ctor_set(v___x_446_, 1, v_startInclusive_444_);
lean_ctor_set(v___x_446_, 2, v___x_445_);
v___x_447_ = lean_nat_sub(v___x_445_, v_startInclusive_444_);
lean_dec(v___x_445_);
v___x_448_ = lean_unsigned_to_nat(1u);
v___x_449_ = lean_nat_sub(v___x_447_, v___x_448_);
lean_dec(v___x_447_);
v___x_450_ = l_String_Slice_posLE(v___x_446_, v___x_449_);
lean_dec_ref_known(v___x_446_, 3);
v___x_451_ = lean_nat_add(v_startInclusive_444_, v___x_450_);
v___x_452_ = lean_string_utf8_get_fast(v_str_443_, v___x_451_);
lean_dec(v___x_451_);
v___x_453_ = 46;
v___x_454_ = lean_uint32_dec_eq(v___x_452_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v___x_450_);
v___x_455_ = lean_box(0);
v___x_456_ = lean_nat_sub(v_a_439_, v___x_448_);
lean_dec(v_a_439_);
v___x_457_ = l_String_Slice_posLE(v_s_438_, v___x_456_);
v_a_439_ = v___x_457_;
v_b_440_ = v___x_455_;
goto _start;
}
else
{
lean_object* v___x_459_; 
lean_dec(v_a_439_);
v___x_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_450_);
return v___x_459_;
}
}
else
{
lean_dec(v_a_439_);
lean_inc(v_b_440_);
return v_b_440_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg___boxed(lean_object* v_s_460_, lean_object* v_a_461_, lean_object* v_b_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_460_, v_a_461_, v_b_462_);
lean_dec(v_b_462_);
lean_dec_ref(v_s_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(lean_object* v_s_464_){
_start:
{
lean_object* v_startInclusive_465_; lean_object* v_endExclusive_466_; lean_object* v_searcher_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_startInclusive_465_ = lean_ctor_get(v_s_464_, 1);
v_endExclusive_466_ = lean_ctor_get(v_s_464_, 2);
v_searcher_467_ = lean_nat_sub(v_endExclusive_466_, v_startInclusive_465_);
v___x_468_ = lean_box(0);
v___x_469_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_464_, v_searcher_467_, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0___boxed(lean_object* v_s_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v_s_470_);
lean_dec_ref(v_s_470_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object* v_p_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_System_FilePath_fileName(v_p_472_);
if (lean_obj_tag(v___x_473_) == 0)
{
return v___x_473_;
}
else
{
lean_object* v_val_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_val_474_ = lean_ctor_get(v___x_473_, 0);
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_string_utf8_byte_size(v_val_474_);
lean_inc(v_val_474_);
v___x_477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_477_, 0, v_val_474_);
lean_ctor_set(v___x_477_, 1, v___x_475_);
lean_ctor_set(v___x_477_, 2, v___x_476_);
v___x_478_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_477_);
lean_dec_ref_known(v___x_477_, 3);
if (lean_obj_tag(v___x_478_) == 0)
{
return v___x_473_;
}
else
{
lean_object* v_val_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_488_; 
v_val_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_488_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_488_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_val_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_488_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
uint8_t v___x_483_; 
v___x_483_ = lean_nat_dec_eq(v_val_479_, v___x_475_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_486_; 
lean_inc(v_val_474_);
lean_dec_ref_known(v___x_473_, 1);
v___x_484_ = lean_string_utf8_extract(v_val_474_, v___x_475_, v_val_479_);
lean_dec(v_val_479_);
lean_dec(v_val_474_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_484_);
v___x_486_ = v___x_481_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
else
{
lean_del_object(v___x_481_);
lean_dec(v_val_479_);
return v___x_473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(lean_object* v_s_489_, lean_object* v_inst_490_, lean_object* v_R_491_, lean_object* v_a_492_, lean_object* v_b_493_, lean_object* v_c_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_489_, v_a_492_, v_b_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___boxed(lean_object* v_s_496_, lean_object* v_inst_497_, lean_object* v_R_498_, lean_object* v_a_499_, lean_object* v_b_500_, lean_object* v_c_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(v_s_496_, v_inst_497_, v_R_498_, v_a_499_, v_b_500_, v_c_501_);
lean_dec(v_b_500_);
lean_dec_ref(v_s_496_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object* v_p_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_System_FilePath_fileName(v_p_503_);
if (lean_obj_tag(v___x_504_) == 0)
{
return v___x_504_;
}
else
{
lean_object* v_val_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_val_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc_n(v_val_505_, 2);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_string_utf8_byte_size(v_val_505_);
v___x_508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_508_, 0, v_val_505_);
lean_ctor_set(v___x_508_, 1, v___x_506_);
lean_ctor_set(v___x_508_, 2, v___x_507_);
v___x_509_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_508_);
lean_dec_ref_known(v___x_508_, 3);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v___x_510_; 
lean_dec(v_val_505_);
v___x_510_ = lean_box(0);
return v___x_510_;
}
else
{
lean_object* v_val_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_523_; 
v_val_511_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_523_ == 0)
{
v___x_513_ = v___x_509_;
v_isShared_514_ = v_isSharedCheck_523_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_val_511_);
lean_dec(v___x_509_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_523_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
uint8_t v___x_515_; 
v___x_515_ = lean_nat_dec_eq(v_val_511_, v___x_506_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_val_511_, v___x_516_);
lean_dec(v_val_511_);
v___x_518_ = lean_string_utf8_extract(v_val_505_, v___x_517_, v___x_507_);
lean_dec(v___x_517_);
lean_dec(v_val_505_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_518_);
v___x_520_ = v___x_513_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
else
{
lean_object* v___x_522_; 
lean_del_object(v___x_513_);
lean_dec(v_val_511_);
lean_dec(v_val_505_);
v___x_522_ = lean_box(0);
return v___x_522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object* v_p_524_, lean_object* v_fname_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_System_FilePath_parent(v_p_524_);
if (lean_obj_tag(v___x_526_) == 0)
{
return v_fname_525_;
}
else
{
lean_object* v_val_527_; lean_object* v___x_528_; 
v_val_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_val_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = l_System_FilePath_join(v_val_527_, v_fname_525_);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object* v_p_529_, lean_object* v_ext_530_){
_start:
{
lean_object* v___x_531_; 
lean_inc_ref(v_p_529_);
v___x_531_ = l_System_FilePath_fileName(v_p_529_);
if (lean_obj_tag(v___x_531_) == 0)
{
return v_p_529_;
}
else
{
lean_object* v_val_532_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v_val_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_val_532_);
lean_dec_ref_known(v___x_531_, 1);
v___x_533_ = lean_string_utf8_byte_size(v_ext_530_);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = lean_nat_dec_eq(v___x_533_, v___x_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_536_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_537_ = lean_string_append(v_val_532_, v___x_536_);
v___x_538_ = lean_string_append(v___x_537_, v_ext_530_);
v___x_539_ = l_System_FilePath_withFileName(v_p_529_, v___x_538_);
return v___x_539_;
}
else
{
lean_object* v___x_540_; 
v___x_540_ = l_System_FilePath_withFileName(v_p_529_, v_val_532_);
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object* v_p_541_, lean_object* v_ext_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_System_FilePath_addExtension(v_p_541_, v_ext_542_);
lean_dec_ref(v_ext_542_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object* v_p_544_, lean_object* v_ext_545_){
_start:
{
lean_object* v___x_546_; 
lean_inc_ref(v_p_544_);
v___x_546_ = l_System_FilePath_fileStem(v_p_544_);
if (lean_obj_tag(v___x_546_) == 0)
{
return v_p_544_;
}
else
{
lean_object* v_val_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_val_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = lean_string_utf8_byte_size(v_ext_545_);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_nat_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_551_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_552_ = lean_string_append(v_val_547_, v___x_551_);
v___x_553_ = lean_string_append(v___x_552_, v_ext_545_);
v___x_554_ = l_System_FilePath_withFileName(v_p_544_, v___x_553_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = l_System_FilePath_withFileName(v_p_544_, v_val_547_);
return v___x_555_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object* v_p_556_, lean_object* v_ext_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_System_FilePath_withExtension(v_p_556_, v_ext_557_);
lean_dec_ref(v_ext_557_);
return v_res_558_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_560_ = lean_string_utf8_byte_size(v___x_559_);
return v___x_560_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0);
v___x_563_ = lean_nat_dec_eq(v___x_562_, v___x_561_);
return v___x_563_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_564_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_567_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v___x_565_);
lean_ctor_set(v___x_567_, 2, v___x_564_);
return v___x_567_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2);
v___x_569_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3);
v___x_572_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2);
v___x_573_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_571_);
lean_ctor_set(v___x_573_, 2, v___x_570_);
lean_ctor_set(v___x_573_, 3, v___x_570_);
return v___x_573_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4);
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg(){
_start:
{
uint8_t v___x_583_; 
v___x_583_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5);
return v___x_584_;
}
else
{
lean_object* v___x_585_; 
v___x_585_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__7));
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___boxed(lean_object* v___dummy_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg();
return v_res_587_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0(void){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg();
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(lean_object* v_s_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(lean_object* v_s_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v_s_591_);
lean_dec_ref(v_s_591_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object* v___x_593_, lean_object* v___x_594_, lean_object* v___x_595_, lean_object* v_a_596_, lean_object* v_b_597_){
_start:
{
lean_object* v_it_599_; lean_object* v_startInclusive_600_; lean_object* v_endExclusive_601_; 
if (lean_obj_tag(v_a_596_) == 0)
{
lean_object* v_currPos_606_; lean_object* v_searcher_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_713_; 
v_currPos_606_ = lean_ctor_get(v_a_596_, 0);
v_searcher_607_ = lean_ctor_get(v_a_596_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_a_596_);
if (v_isSharedCheck_713_ == 0)
{
v___x_609_ = v_a_596_;
v_isShared_610_ = v_isSharedCheck_713_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_searcher_607_);
lean_inc(v_currPos_606_);
lean_dec(v_a_596_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_713_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v_it_612_; lean_object* v_it_618_; lean_object* v_startPos_619_; lean_object* v_endPos_620_; 
switch(lean_obj_tag(v_searcher_607_))
{
case 0:
{
lean_object* v_pos_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_645_; 
lean_del_object(v___x_609_);
v_pos_633_ = lean_ctor_get(v_searcher_607_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v_searcher_607_);
if (v_isSharedCheck_645_ == 0)
{
v___x_635_ = v_searcher_607_;
v_isShared_636_ = v_isSharedCheck_645_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_pos_633_);
lean_dec(v_searcher_607_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_645_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_startInclusive_637_; lean_object* v_endExclusive_638_; lean_object* v___x_639_; uint8_t v_decide_640_; 
v_startInclusive_637_ = lean_ctor_get(v___x_594_, 1);
v_endExclusive_638_ = lean_ctor_get(v___x_594_, 2);
v___x_639_ = lean_nat_sub(v_endExclusive_638_, v_startInclusive_637_);
v_decide_640_ = lean_nat_dec_eq(v_pos_633_, v___x_639_);
lean_dec(v___x_639_);
if (v_decide_640_ == 0)
{
lean_object* v___x_642_; 
lean_inc(v_pos_633_);
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 1);
v___x_642_ = v___x_635_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_pos_633_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_inc(v_pos_633_);
v_it_618_ = v___x_642_;
v_startPos_619_ = v_pos_633_;
v_endPos_620_ = v_pos_633_;
goto v___jp_617_;
}
}
else
{
lean_object* v___x_644_; 
lean_del_object(v___x_635_);
v___x_644_ = lean_box(3);
lean_inc(v_pos_633_);
v_it_618_ = v___x_644_;
v_startPos_619_ = v_pos_633_;
v_endPos_620_ = v_pos_633_;
goto v___jp_617_;
}
}
}
case 1:
{
lean_object* v_pos_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_pos_646_ = lean_ctor_get(v_searcher_607_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v_searcher_607_);
if (v_isSharedCheck_654_ == 0)
{
v___x_648_ = v_searcher_607_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_pos_646_);
lean_dec(v_searcher_607_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_string_utf8_next_fast(v___x_593_, v_pos_646_);
lean_dec(v_pos_646_);
if (v_isShared_649_ == 0)
{
lean_ctor_set_tag(v___x_648_, 0);
lean_ctor_set(v___x_648_, 0, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
v_it_612_ = v___x_652_;
goto v___jp_611_;
}
}
}
case 2:
{
lean_object* v_needle_655_; lean_object* v_table_656_; lean_object* v_stackPos_657_; lean_object* v_needlePos_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_712_; 
v_needle_655_ = lean_ctor_get(v_searcher_607_, 0);
v_table_656_ = lean_ctor_get(v_searcher_607_, 1);
v_stackPos_657_ = lean_ctor_get(v_searcher_607_, 2);
v_needlePos_658_ = lean_ctor_get(v_searcher_607_, 3);
v_isSharedCheck_712_ = !lean_is_exclusive(v_searcher_607_);
if (v_isSharedCheck_712_ == 0)
{
v___x_660_ = v_searcher_607_;
v_isShared_661_ = v_isSharedCheck_712_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_needlePos_658_);
lean_inc(v_stackPos_657_);
lean_inc(v_table_656_);
lean_inc(v_needle_655_);
lean_dec(v_searcher_607_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_712_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_str_662_; lean_object* v_startInclusive_663_; lean_object* v_endExclusive_664_; lean_object* v_basePos_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_str_662_ = lean_ctor_get(v_needle_655_, 0);
v_startInclusive_663_ = lean_ctor_get(v_needle_655_, 1);
v_endExclusive_664_ = lean_ctor_get(v_needle_655_, 2);
v_basePos_665_ = lean_nat_sub(v_stackPos_657_, v_needlePos_658_);
v___x_666_ = lean_nat_sub(v_endExclusive_664_, v_startInclusive_663_);
v___x_667_ = lean_nat_add(v_basePos_665_, v___x_666_);
v___x_668_ = lean_nat_dec_le(v___x_667_, v___x_595_);
lean_dec(v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
lean_dec(v___x_666_);
lean_del_object(v___x_660_);
lean_dec(v_needlePos_658_);
lean_dec(v_stackPos_657_);
lean_dec_ref(v_table_656_);
lean_dec_ref(v_needle_655_);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_add(v_basePos_665_, v___x_669_);
lean_dec(v_basePos_665_);
v___x_671_ = lean_nat_dec_le(v___x_670_, v___x_595_);
lean_dec(v___x_670_);
if (v___x_671_ == 0)
{
lean_del_object(v___x_609_);
goto v___jp_631_;
}
else
{
lean_object* v___x_672_; 
v___x_672_ = lean_box(3);
v_it_612_ = v___x_672_;
goto v___jp_611_;
}
}
else
{
uint8_t v_stackByte_673_; lean_object* v___x_674_; uint8_t v_patByte_675_; uint8_t v___x_676_; 
lean_dec(v_basePos_665_);
lean_inc(v_stackPos_657_);
v_stackByte_673_ = lean_string_get_byte_fast(v___x_593_, v_stackPos_657_);
v___x_674_ = lean_nat_add(v_startInclusive_663_, v_needlePos_658_);
v_patByte_675_ = lean_string_get_byte_fast(v_str_662_, v___x_674_);
v___x_676_ = lean_uint8_dec_eq(v_stackByte_673_, v_patByte_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; uint8_t v_decide_678_; 
lean_dec(v___x_666_);
v___x_677_ = lean_unsigned_to_nat(0u);
v_decide_678_ = lean_nat_dec_eq(v_needlePos_658_, v___x_677_);
if (v_decide_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v_newNeedlePos_681_; uint8_t v___x_682_; 
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_nat_sub(v_needlePos_658_, v___x_679_);
lean_dec(v_needlePos_658_);
v_newNeedlePos_681_ = lean_array_fget_borrowed(v_table_656_, v___x_680_);
lean_dec(v___x_680_);
v___x_682_ = lean_nat_dec_eq(v_newNeedlePos_681_, v___x_677_);
if (v___x_682_ == 0)
{
lean_object* v___x_684_; 
lean_inc(v_newNeedlePos_681_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 3, v_newNeedlePos_681_);
v___x_684_ = v___x_660_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_needle_655_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_table_656_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_stackPos_657_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_newNeedlePos_681_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
v_it_612_ = v___x_684_;
goto v___jp_611_;
}
}
else
{
lean_object* v_nextStackPos_686_; lean_object* v___x_688_; 
v_nextStackPos_686_ = l_String_Slice_posGE___redArg(v___x_594_, v_stackPos_657_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 3, v___x_677_);
lean_ctor_set(v___x_660_, 2, v_nextStackPos_686_);
v___x_688_ = v___x_660_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_needle_655_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_table_656_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v_nextStackPos_686_);
lean_ctor_set(v_reuseFailAlloc_689_, 3, v___x_677_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v_it_612_ = v___x_688_;
goto v___jp_611_;
}
}
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_nextStackPos_692_; lean_object* v___x_694_; 
lean_dec(v_needlePos_658_);
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_add(v_stackPos_657_, v___x_690_);
lean_dec(v_stackPos_657_);
v_nextStackPos_692_ = l_String_Slice_posGE___redArg(v___x_594_, v___x_691_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 3, v___x_677_);
lean_ctor_set(v___x_660_, 2, v_nextStackPos_692_);
v___x_694_ = v___x_660_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_needle_655_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_table_656_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_nextStackPos_692_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v___x_677_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
v_it_612_ = v___x_694_;
goto v___jp_611_;
}
}
}
else
{
lean_object* v___x_696_; lean_object* v_nextStackPos_697_; lean_object* v_nextNeedlePos_698_; uint8_t v_decide_699_; 
lean_del_object(v___x_609_);
v___x_696_ = lean_unsigned_to_nat(1u);
v_nextStackPos_697_ = lean_nat_add(v_stackPos_657_, v___x_696_);
lean_dec(v_stackPos_657_);
v_nextNeedlePos_698_ = lean_nat_add(v_needlePos_658_, v___x_696_);
lean_dec(v_needlePos_658_);
v_decide_699_ = lean_nat_dec_eq(v_nextNeedlePos_698_, v___x_666_);
lean_dec(v___x_666_);
if (v_decide_699_ == 0)
{
lean_object* v___x_701_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 3, v_nextNeedlePos_698_);
lean_ctor_set(v___x_660_, 2, v_nextStackPos_697_);
v___x_701_ = v___x_660_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_needle_655_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_table_656_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_nextStackPos_697_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_nextNeedlePos_698_);
v___x_701_ = v_reuseFailAlloc_704_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_currPos_606_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v_a_596_ = v___x_702_;
goto _start;
}
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_705_ = lean_nat_sub(v_nextStackPos_697_, v_nextNeedlePos_698_);
lean_dec(v_nextNeedlePos_698_);
v___x_706_ = l_String_Slice_pos_x21(v___x_594_, v___x_705_);
lean_dec(v___x_705_);
v___x_707_ = l_String_Slice_pos_x21(v___x_594_, v_nextStackPos_697_);
v___x_708_ = lean_unsigned_to_nat(0u);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 3, v___x_708_);
lean_ctor_set(v___x_660_, 2, v_nextStackPos_697_);
v___x_710_ = v___x_660_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_needle_655_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_table_656_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_nextStackPos_697_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
v_it_618_ = v___x_710_;
v_startPos_619_ = v___x_706_;
v_endPos_620_ = v___x_707_;
goto v___jp_617_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_609_);
goto v___jp_631_;
}
}
v___jp_611_:
{
lean_object* v___x_614_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v_it_612_);
v___x_614_ = v___x_609_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_currPos_606_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_it_612_);
v___x_614_ = v_reuseFailAlloc_616_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
v_a_596_ = v___x_614_;
goto _start;
}
}
v___jp_617_:
{
lean_object* v_slice_621_; lean_object* v_startInclusive_622_; lean_object* v_endExclusive_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_slice_621_ = l_String_Slice_subslice_x21(v___x_594_, v_currPos_606_, v_startPos_619_);
v_startInclusive_622_ = lean_ctor_get(v_slice_621_, 0);
v_endExclusive_623_ = lean_ctor_get(v_slice_621_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_slice_621_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v_slice_621_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_endExclusive_623_);
lean_inc(v_startInclusive_622_);
lean_dec(v_slice_621_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v_nextIt_628_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v_it_618_);
lean_ctor_set(v___x_625_, 0, v_endPos_620_);
v_nextIt_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_endPos_620_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_it_618_);
v_nextIt_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v_it_599_ = v_nextIt_628_;
v_startInclusive_600_ = v_startInclusive_622_;
v_endExclusive_601_ = v_endExclusive_623_;
goto v___jp_598_;
}
}
}
v___jp_631_:
{
lean_object* v___x_632_; 
v___x_632_ = lean_box(1);
lean_inc(v___x_595_);
v_it_599_ = v___x_632_;
v_startInclusive_600_ = v_currPos_606_;
v_endExclusive_601_ = v___x_595_;
goto v___jp_598_;
}
}
}
else
{
lean_dec(v___x_595_);
lean_dec_ref(v___x_593_);
return v_b_597_;
}
v___jp_598_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
lean_inc_ref(v___x_593_);
v___x_602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_602_, 0, v___x_593_);
lean_ctor_set(v___x_602_, 1, v_startInclusive_600_);
lean_ctor_set(v___x_602_, 2, v_endExclusive_601_);
v___x_603_ = l_String_Slice_toString(v___x_602_);
lean_dec_ref_known(v___x_602_, 3);
v___x_604_ = lean_array_push(v_b_597_, v___x_603_);
v_a_596_ = v_it_599_;
v_b_597_ = v___x_604_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object* v___x_714_, lean_object* v___x_715_, lean_object* v___x_716_, lean_object* v_a_717_, lean_object* v_b_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_714_, v___x_715_, v___x_716_, v_a_717_, v_b_718_);
lean_dec_ref(v___x_715_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object* v_p_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_723_ = l_System_FilePath_normalize(v_p_722_);
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_string_utf8_byte_size(v___x_723_);
lean_inc_ref(v___x_723_);
v___x_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_726_, 0, v___x_723_);
lean_ctor_set(v___x_726_, 1, v___x_724_);
lean_ctor_set(v___x_726_, 2, v___x_725_);
v___x_727_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
v___x_728_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_729_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_723_, v___x_726_, v___x_725_, v___x_727_, v___x_728_);
lean_dec_ref_known(v___x_726_, 3);
v___x_730_ = lean_array_to_list(v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object* v___x_731_, lean_object* v___x_732_, lean_object* v___x_733_, lean_object* v_inst_734_, lean_object* v_R_735_, lean_object* v_a_736_, lean_object* v_b_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_731_, v___x_732_, v___x_733_, v_a_736_, v_b_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object* v___x_739_, lean_object* v___x_740_, lean_object* v___x_741_, lean_object* v_inst_742_, lean_object* v_R_743_, lean_object* v_a_744_, lean_object* v_b_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(v___x_739_, v___x_740_, v___x_741_, v_inst_742_, v_R_743_, v_a_744_, v_b_745_);
lean_dec_ref(v___x_740_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object* v_parts_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_749_ = l_String_intercalate(v___x_748_, v_parts_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object* v_toString_750_){
_start:
{
lean_inc_ref(v_toString_750_);
return v_toString_750_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object* v_toString_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_System_instCoeStringFilePath___lam__0(v_toString_751_);
lean_dec_ref(v_toString_751_);
return v_res_752_;
}
}
static uint32_t _init_l_System_SearchPath_separator(void){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = l_System_Platform_isWindows;
if (v___x_755_ == 0)
{
uint32_t v___x_756_; 
v___x_756_ = 58;
return v___x_756_;
}
else
{
uint32_t v___x_757_; 
v___x_757_ = 59;
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___closed__0));
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___boxed(lean_object* v___dummy_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg();
return v_res_763_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0(void){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg();
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(lean_object* v_s_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___boxed(lean_object* v_s_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v_s_767_);
lean_dec_ref(v_s_767_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(lean_object* v_s_769_, lean_object* v___x_770_, lean_object* v___x_771_, lean_object* v_a_772_, lean_object* v_b_773_){
_start:
{
lean_object* v_it_775_; lean_object* v_startInclusive_776_; lean_object* v_endExclusive_777_; 
if (lean_obj_tag(v_a_772_) == 0)
{
lean_object* v_currPos_781_; lean_object* v_searcher_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_805_; 
v_currPos_781_ = lean_ctor_get(v_a_772_, 0);
v_searcher_782_ = lean_ctor_get(v_a_772_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v_a_772_);
if (v_isSharedCheck_805_ == 0)
{
v___x_784_ = v_a_772_;
v_isShared_785_ = v_isSharedCheck_805_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_searcher_782_);
lean_inc(v_currPos_781_);
lean_dec(v_a_772_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_805_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
uint8_t v_decide_786_; 
v_decide_786_ = lean_nat_dec_eq(v_searcher_782_, v___x_771_);
if (v_decide_786_ == 0)
{
uint32_t v___x_787_; uint32_t v___x_788_; uint8_t v___x_789_; 
v___x_787_ = l_System_SearchPath_separator;
v___x_788_ = lean_string_utf8_get_fast(v_s_769_, v_searcher_782_);
v___x_789_ = lean_uint32_dec_eq(v___x_788_, v___x_787_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = lean_string_utf8_next_fast(v_s_769_, v_searcher_782_);
lean_dec(v_searcher_782_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_790_);
v___x_792_ = v___x_784_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_currPos_781_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_790_);
v___x_792_ = v_reuseFailAlloc_794_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v_a_772_ = v___x_792_;
goto _start;
}
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_slice_798_; lean_object* v_nextIt_800_; 
v___x_795_ = lean_string_utf8_next_fast(v_s_769_, v_searcher_782_);
v___x_796_ = lean_nat_sub(v___x_795_, v_searcher_782_);
v___x_797_ = lean_nat_add(v_searcher_782_, v___x_796_);
lean_dec(v___x_796_);
v_slice_798_ = l_String_Slice_subslice_x21(v___x_770_, v_currPos_781_, v_searcher_782_);
lean_inc(v___x_797_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_797_);
lean_ctor_set(v___x_784_, 0, v___x_797_);
v_nextIt_800_ = v___x_784_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v___x_797_);
v_nextIt_800_ = v_reuseFailAlloc_803_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v_startInclusive_801_; lean_object* v_endExclusive_802_; 
v_startInclusive_801_ = lean_ctor_get(v_slice_798_, 0);
lean_inc(v_startInclusive_801_);
v_endExclusive_802_ = lean_ctor_get(v_slice_798_, 1);
lean_inc(v_endExclusive_802_);
lean_dec_ref(v_slice_798_);
v_it_775_ = v_nextIt_800_;
v_startInclusive_776_ = v_startInclusive_801_;
v_endExclusive_777_ = v_endExclusive_802_;
goto v___jp_774_;
}
}
}
else
{
lean_object* v___x_804_; 
lean_del_object(v___x_784_);
lean_dec(v_searcher_782_);
v___x_804_ = lean_box(1);
lean_inc(v___x_771_);
v_it_775_ = v___x_804_;
v_startInclusive_776_ = v_currPos_781_;
v_endExclusive_777_ = v___x_771_;
goto v___jp_774_;
}
}
}
else
{
lean_dec(v___x_771_);
return v_b_773_;
}
v___jp_774_:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_string_utf8_extract_fast(v_s_769_, v_startInclusive_776_, v_endExclusive_777_);
lean_dec(v_endExclusive_777_);
lean_dec(v_startInclusive_776_);
v___x_779_ = lean_array_push(v_b_773_, v___x_778_);
v_a_772_ = v_it_775_;
v_b_773_ = v___x_779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg___boxed(lean_object* v_s_806_, lean_object* v___x_807_, lean_object* v___x_808_, lean_object* v_a_809_, lean_object* v_b_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_806_, v___x_807_, v___x_808_, v_a_809_, v_b_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref(v_s_806_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object* v_s_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = lean_string_utf8_byte_size(v_s_812_);
lean_inc_ref(v_s_812_);
v___x_815_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_815_, 0, v_s_812_);
lean_ctor_set(v___x_815_, 1, v___x_813_);
lean_ctor_set(v___x_815_, 2, v___x_814_);
v___x_816_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0);
v___x_817_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_818_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_812_, v___x_815_, v___x_814_, v___x_816_, v___x_817_);
lean_dec_ref_known(v___x_815_, 3);
lean_dec_ref(v_s_812_);
v___x_819_ = lean_array_to_list(v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(lean_object* v_s_820_, lean_object* v___x_821_, lean_object* v___x_822_, lean_object* v_inst_823_, lean_object* v_R_824_, lean_object* v_a_825_, lean_object* v_b_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_820_, v___x_821_, v___x_822_, v_a_825_, v_b_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___boxed(lean_object* v_s_828_, lean_object* v___x_829_, lean_object* v___x_830_, lean_object* v_inst_831_, lean_object* v_R_832_, lean_object* v_a_833_, lean_object* v_b_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(v_s_828_, v___x_829_, v___x_830_, v_inst_831_, v_R_832_, v_a_833_, v_b_834_);
lean_dec_ref(v___x_829_);
lean_dec_ref(v_s_828_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
if (lean_obj_tag(v_a_836_) == 0)
{
lean_object* v___x_838_; 
v___x_838_ = l_List_reverse___redArg(v_a_837_);
return v___x_838_;
}
else
{
lean_object* v_head_839_; lean_object* v_tail_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_848_; 
v_head_839_ = lean_ctor_get(v_a_836_, 0);
v_tail_840_ = lean_ctor_get(v_a_836_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_a_836_);
if (v_isSharedCheck_848_ == 0)
{
v___x_842_ = v_a_836_;
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_tail_840_);
lean_inc(v_head_839_);
lean_dec(v_a_836_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v_a_837_);
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_head_839_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_a_837_);
v___x_845_ = v_reuseFailAlloc_847_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
v_a_836_ = v_tail_840_;
v_a_837_ = v___x_845_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_System_SearchPath_toString___closed__0(void){
_start:
{
uint32_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = l_System_SearchPath_separator;
v___x_850_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_851_ = lean_string_push(v___x_850_, v___x_849_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object* v_path_852_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_853_ = lean_obj_once(&l_System_SearchPath_toString___closed__0, &l_System_SearchPath_toString___closed__0_once, _init_l_System_SearchPath_toString___closed__0);
v___x_854_ = lean_box(0);
v___x_855_ = l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(v_path_852_, v___x_854_);
v___x_856_ = l_String_intercalate(v___x_853_, v___x_855_);
return v___x_856_;
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
