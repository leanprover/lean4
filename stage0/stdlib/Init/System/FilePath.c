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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1___boxed(lean_object*, lean_object*);
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
uint32_t v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_string_utf8_get(v_p_100_, v___x_102_);
v___x_122_ = lean_uint32_dec_le(v___x_115_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_string_utf8_set(v_p_100_, v___x_102_, v___x_121_);
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = lean_uint32_dec_le(v___x_121_, v___x_118_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_string_utf8_set(v_p_100_, v___x_102_, v___x_121_);
return v___x_125_;
}
else
{
uint32_t v___x_126_; uint32_t v___x_127_; lean_object* v___x_128_; 
v___x_126_ = 4294967264;
v___x_127_ = lean_uint32_add(v___x_121_, v___x_126_);
v___x_128_ = lean_string_utf8_set(v_p_100_, v___x_102_, v___x_127_);
return v___x_128_;
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(lean_object* v___x_129_, lean_object* v___x_130_, lean_object* v___x_131_, lean_object* v_inst_132_, lean_object* v_R_133_, lean_object* v_a_134_, lean_object* v_b_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_130_, v___x_131_, v_a_134_, v_b_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___boxed(lean_object* v___x_137_, lean_object* v___x_138_, lean_object* v___x_139_, lean_object* v_inst_140_, lean_object* v_R_141_, lean_object* v_a_142_, lean_object* v_b_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(v___x_137_, v___x_138_, v___x_139_, v_inst_140_, v_R_141_, v_a_142_, v_b_143_);
lean_dec(v___x_139_);
lean_dec_ref(v___x_138_);
lean_dec_ref(v___x_137_);
return v_res_144_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00System_FilePath_normalize_spec__0(uint32_t v_a_145_, lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
uint8_t v___x_147_; 
v___x_147_ = 0;
return v___x_147_;
}
else
{
lean_object* v_head_148_; lean_object* v_tail_149_; uint32_t v___x_150_; uint8_t v___x_151_; 
v_head_148_ = lean_ctor_get(v_x_146_, 0);
v_tail_149_ = lean_ctor_get(v_x_146_, 1);
v___x_150_ = lean_unbox_uint32(v_head_148_);
v___x_151_ = lean_uint32_dec_eq(v_a_145_, v___x_150_);
if (v___x_151_ == 0)
{
v_x_146_ = v_tail_149_;
goto _start;
}
else
{
return v___x_151_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00System_FilePath_normalize_spec__0___boxed(lean_object* v_a_153_, lean_object* v_x_154_){
_start:
{
uint32_t v_a_boxed_155_; uint8_t v_res_156_; lean_object* v_r_157_; 
v_a_boxed_155_ = lean_unbox_uint32(v_a_153_);
lean_dec(v_a_153_);
v_res_156_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v_a_boxed_155_, v_x_154_);
lean_dec(v_x_154_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1(lean_object* v_s_158_, lean_object* v_p_159_){
_start:
{
uint32_t v___y_161_; lean_object* v___x_166_; uint8_t v_decide_167_; 
v___x_166_ = lean_string_utf8_byte_size(v_s_158_);
v_decide_167_ = lean_nat_dec_eq(v_p_159_, v___x_166_);
if (v_decide_167_ == 0)
{
lean_object* v___x_168_; uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_168_ = l_System_FilePath_pathSeparators;
v___x_169_ = lean_string_utf8_get_fast(v_s_158_, v_p_159_);
v___x_170_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_169_, v___x_168_);
if (v___x_170_ == 0)
{
v___y_161_ = v___x_169_;
goto v___jp_160_;
}
else
{
uint32_t v___x_171_; 
v___x_171_ = l_System_FilePath_pathSeparator;
v___y_161_ = v___x_171_;
goto v___jp_160_;
}
}
else
{
lean_dec(v_p_159_);
return v_s_158_;
}
v___jp_160_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
lean_inc(v_p_159_);
v___x_162_ = lean_string_utf8_set(v_s_158_, v_p_159_, v___y_161_);
v___x_163_ = l_Char_utf8Size(v___y_161_);
v___x_164_ = lean_nat_add(v_p_159_, v___x_163_);
lean_dec(v___x_163_);
lean_dec(v_p_159_);
v_s_158_ = v___x_162_;
v_p_159_ = v___x_164_;
goto _start;
}
}
}
static lean_object* _init_l_System_FilePath_normalize___closed__0(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = l_System_FilePath_pathSeparators;
v___x_173_ = l_List_lengthTR___redArg(v___x_172_);
return v___x_173_;
}
}
static uint8_t _init_l_System_FilePath_normalize___closed__1(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_obj_once(&l_System_FilePath_normalize___closed__0, &l_System_FilePath_normalize___closed__0_once, _init_l_System_FilePath_normalize___closed__0);
v___x_176_ = lean_nat_dec_eq(v___x_175_, v___x_174_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object* v_p_177_){
_start:
{
lean_object* v_p_178_; uint8_t v___x_179_; 
v_p_178_ = l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(v_p_177_);
v___x_179_ = lean_uint8_once(&l_System_FilePath_normalize___closed__1, &l_System_FilePath_normalize___closed__1_once, _init_l_System_FilePath_normalize___closed__1);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v_p_181_; 
v___x_180_ = lean_unsigned_to_nat(0u);
v_p_181_ = l_String_mapAux___at___00System_FilePath_normalize_spec__1(v_p_178_, v___x_180_);
return v_p_181_;
}
else
{
return v_p_178_;
}
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1(lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_182_) == 0)
{
if (lean_obj_tag(v_x_183_) == 0)
{
uint8_t v___x_184_; 
v___x_184_ = 1;
return v___x_184_;
}
else
{
uint8_t v___x_185_; 
v___x_185_ = 0;
return v___x_185_;
}
}
else
{
if (lean_obj_tag(v_x_183_) == 0)
{
uint8_t v___x_186_; 
v___x_186_ = 0;
return v___x_186_;
}
else
{
lean_object* v_val_187_; lean_object* v_val_188_; uint32_t v___x_189_; uint32_t v___x_190_; uint8_t v___x_191_; 
v_val_187_ = lean_ctor_get(v_x_182_, 0);
v_val_188_ = lean_ctor_get(v_x_183_, 0);
v___x_189_ = lean_unbox_uint32(v_val_187_);
v___x_190_ = lean_unbox_uint32(v_val_188_);
v___x_191_ = lean_uint32_dec_eq(v___x_189_, v___x_190_);
return v___x_191_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1___boxed(lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1(v_x_192_, v_x_193_);
lean_dec(v_x_193_);
lean_dec(v_x_192_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(lean_object* v___x_196_, lean_object* v___x_197_, lean_object* v_a_198_, lean_object* v_b_199_){
_start:
{
lean_object* v_str_200_; lean_object* v_startInclusive_201_; lean_object* v_endExclusive_202_; lean_object* v___x_203_; uint8_t v_decide_204_; 
v_str_200_ = lean_ctor_get(v___x_197_, 0);
v_startInclusive_201_ = lean_ctor_get(v___x_197_, 1);
v_endExclusive_202_ = lean_ctor_get(v___x_197_, 2);
v___x_203_ = lean_nat_sub(v_endExclusive_202_, v_startInclusive_201_);
v_decide_204_ = lean_nat_dec_eq(v_a_198_, v___x_203_);
lean_dec(v___x_203_);
if (v_decide_204_ == 0)
{
lean_object* v_zero_205_; uint8_t v_isZero_206_; 
v_zero_205_ = lean_unsigned_to_nat(0u);
v_isZero_206_ = lean_nat_dec_eq(v_b_199_, v_zero_205_);
if (v_isZero_206_ == 1)
{
uint32_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec(v_b_199_);
v___x_207_ = lean_string_utf8_get_fast(v___x_196_, v_a_198_);
lean_dec(v_a_198_);
v___x_208_ = lean_box_uint32(v___x_207_);
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_one_213_; lean_object* v_n_214_; 
v___x_210_ = lean_nat_add(v_startInclusive_201_, v_a_198_);
lean_dec(v_a_198_);
v___x_211_ = lean_string_utf8_next_fast(v_str_200_, v___x_210_);
lean_dec(v___x_210_);
v___x_212_ = lean_nat_sub(v___x_211_, v_startInclusive_201_);
v_one_213_ = lean_unsigned_to_nat(1u);
v_n_214_ = lean_nat_sub(v_b_199_, v_one_213_);
lean_dec(v_b_199_);
v_a_198_ = v___x_212_;
v_b_199_ = v_n_214_;
goto _start;
}
}
else
{
lean_object* v___x_216_; 
lean_dec(v_b_199_);
lean_dec(v_a_198_);
v___x_216_ = lean_box(0);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg___boxed(lean_object* v___x_217_, lean_object* v___x_218_, lean_object* v_a_219_, lean_object* v_b_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_217_, v___x_218_, v_a_219_, v_b_220_);
lean_dec_ref(v___x_218_);
lean_dec_ref(v___x_217_);
return v_res_221_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_222_; lean_object* v___x_223_; 
v___x_222_ = 58;
v___x_223_ = lean_box_uint32(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object* v_p_226_){
_start:
{
lean_object* v___x_227_; uint32_t v___y_229_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_227_ = l_System_FilePath_pathSeparators;
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_string_utf8_byte_size(v_p_226_);
lean_inc_ref(v_p_226_);
v___x_241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_241_, 0, v_p_226_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_240_);
v___x_242_ = l_String_Slice_Pos_get_x3f(v___x_241_, v___x_239_);
lean_dec_ref_known(v___x_241_, 3);
if (lean_obj_tag(v___x_242_) == 0)
{
uint32_t v___x_243_; 
v___x_243_ = 65;
v___y_229_ = v___x_243_;
goto v___jp_228_;
}
else
{
lean_object* v_val_244_; uint32_t v___x_245_; 
v_val_244_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_val_244_);
lean_dec_ref_known(v___x_242_, 1);
v___x_245_ = lean_unbox_uint32(v_val_244_);
lean_dec(v_val_244_);
v___y_229_ = v___x_245_;
goto v___jp_228_;
}
v___jp_228_:
{
uint8_t v___x_230_; 
v___x_230_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_229_, v___x_227_);
if (v___x_230_ == 0)
{
uint8_t v___x_231_; 
v___x_231_ = l_System_Platform_isWindows;
if (v___x_231_ == 0)
{
lean_dec_ref(v_p_226_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_string_utf8_byte_size(v_p_226_);
lean_inc_ref(v_p_226_);
v___x_234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_234_, 0, v_p_226_);
lean_ctor_set(v___x_234_, 1, v___x_232_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v_p_226_, v___x_234_, v___x_232_, v___x_235_);
lean_dec_ref_known(v___x_234_, 3);
lean_dec_ref(v_p_226_);
v___x_237_ = lean_obj_once(&l_System_FilePath_isAbsolute___closed__0, &l_System_FilePath_isAbsolute___closed__0_once, _init_l_System_FilePath_isAbsolute___closed__0);
v___x_238_ = l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1(v___x_236_, v___x_237_);
lean_dec(v___x_236_);
return v___x_238_;
}
}
else
{
lean_dec_ref(v_p_226_);
return v___x_230_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object* v_p_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_System_FilePath_isAbsolute(v_p_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(lean_object* v___x_249_, lean_object* v___x_250_, lean_object* v_n_251_, lean_object* v_it_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_250_, v___x_249_, v_it_252_, v_n_251_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object* v___x_254_, lean_object* v___x_255_, lean_object* v_n_256_, lean_object* v_it_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(v___x_254_, v___x_255_, v_n_256_, v_it_257_);
lean_dec_ref(v___x_255_);
lean_dec_ref(v___x_254_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(lean_object* v___x_259_, lean_object* v___x_260_, lean_object* v_inst_261_, lean_object* v_R_262_, lean_object* v_a_263_, lean_object* v_b_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_259_, v___x_260_, v_a_263_, v_b_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___boxed(lean_object* v___x_266_, lean_object* v___x_267_, lean_object* v_inst_268_, lean_object* v_R_269_, lean_object* v_a_270_, lean_object* v_b_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(v___x_266_, v___x_267_, v_inst_268_, v_R_269_, v_a_270_, v_b_271_);
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_266_);
return v_res_272_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object* v_p_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = l_System_FilePath_isAbsolute(v_p_273_);
if (v___x_274_ == 0)
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
}
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object* v_p_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_System_FilePath_isRelative(v_p_277_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
static lean_object* _init_l_System_FilePath_join___closed__0(void){
_start:
{
uint32_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = l_System_FilePath_pathSeparator;
v___x_281_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_282_ = lean_string_push(v___x_281_, v___x_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object* v_p_283_, lean_object* v_sub_284_){
_start:
{
uint8_t v___x_285_; 
lean_inc_ref(v_sub_284_);
v___x_285_ = l_System_FilePath_isAbsolute(v_sub_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_287_ = lean_string_append(v_p_283_, v___x_286_);
v___x_288_ = lean_string_append(v___x_287_, v_sub_284_);
lean_dec_ref(v_sub_284_);
return v___x_288_;
}
else
{
lean_dec_ref(v_p_283_);
return v_sub_284_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(lean_object* v_s_292_, lean_object* v_a_293_, lean_object* v_b_294_){
_start:
{
lean_object* v___x_295_; uint8_t v_decide_296_; 
v___x_295_ = lean_unsigned_to_nat(0u);
v_decide_296_ = lean_nat_dec_eq(v_a_293_, v___x_295_);
if (v_decide_296_ == 0)
{
lean_object* v_str_297_; lean_object* v_startInclusive_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint32_t v___x_307_; uint8_t v___x_308_; 
v_str_297_ = lean_ctor_get(v_s_292_, 0);
v_startInclusive_298_ = lean_ctor_get(v_s_292_, 1);
v___x_299_ = l_System_FilePath_pathSeparators;
v___x_300_ = lean_nat_add(v_startInclusive_298_, v_a_293_);
lean_inc(v___x_300_);
lean_inc(v_startInclusive_298_);
lean_inc_ref(v_str_297_);
v___x_301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_301_, 0, v_str_297_);
lean_ctor_set(v___x_301_, 1, v_startInclusive_298_);
lean_ctor_set(v___x_301_, 2, v___x_300_);
v___x_302_ = lean_nat_sub(v___x_300_, v_startInclusive_298_);
lean_dec(v___x_300_);
v___x_303_ = lean_unsigned_to_nat(1u);
v___x_304_ = lean_nat_sub(v___x_302_, v___x_303_);
lean_dec(v___x_302_);
v___x_305_ = l_String_Slice_posLE(v___x_301_, v___x_304_);
lean_dec_ref_known(v___x_301_, 3);
v___x_306_ = lean_nat_add(v_startInclusive_298_, v___x_305_);
v___x_307_ = lean_string_utf8_get_fast(v_str_297_, v___x_306_);
lean_dec(v___x_306_);
v___x_308_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_307_, v___x_299_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v___x_305_);
v___x_309_ = lean_box(0);
v___x_310_ = lean_nat_sub(v_a_293_, v___x_303_);
lean_dec(v_a_293_);
v___x_311_ = l_String_Slice_posLE(v_s_292_, v___x_310_);
v_a_293_ = v___x_311_;
v_b_294_ = v___x_309_;
goto _start;
}
else
{
lean_object* v___x_313_; 
lean_dec(v_a_293_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_305_);
return v___x_313_;
}
}
else
{
lean_dec(v_a_293_);
lean_inc(v_b_294_);
return v_b_294_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg___boxed(lean_object* v_s_314_, lean_object* v_a_315_, lean_object* v_b_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_314_, v_a_315_, v_b_316_);
lean_dec(v_b_316_);
lean_dec_ref(v_s_314_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(lean_object* v_s_318_){
_start:
{
lean_object* v_startInclusive_319_; lean_object* v_endExclusive_320_; lean_object* v_searcher_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_startInclusive_319_ = lean_ctor_get(v_s_318_, 1);
v_endExclusive_320_ = lean_ctor_get(v_s_318_, 2);
v_searcher_321_ = lean_nat_sub(v_endExclusive_320_, v_startInclusive_319_);
v___x_322_ = lean_box(0);
v___x_323_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_318_, v_searcher_321_, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___boxed(lean_object* v_s_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v_s_324_);
lean_dec_ref(v_s_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object* v_p_326_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_string_utf8_byte_size(v_p_326_);
v___x_329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_329_, 0, v_p_326_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
lean_ctor_set(v___x_329_, 2, v___x_328_);
v___x_330_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v___x_329_);
lean_dec_ref_known(v___x_329_, 3);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v___x_331_; 
v___x_331_ = lean_box(0);
return v___x_331_;
}
else
{
lean_object* v_val_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
v_val_332_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_330_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_val_332_);
lean_dec(v___x_330_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_val_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(lean_object* v_s_340_, lean_object* v_inst_341_, lean_object* v_R_342_, lean_object* v_a_343_, lean_object* v_b_344_, lean_object* v_c_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_340_, v_a_343_, v_b_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___boxed(lean_object* v_s_347_, lean_object* v_inst_348_, lean_object* v_R_349_, lean_object* v_a_350_, lean_object* v_b_351_, lean_object* v_c_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(v_s_347_, v_inst_348_, v_R_349_, v_a_350_, v_b_351_, v_c_352_);
lean_dec(v_b_351_);
lean_dec_ref(v_s_347_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(lean_object* v_p_354_){
_start:
{
lean_object* v___x_355_; uint32_t v___y_357_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_355_ = l_System_FilePath_pathSeparators;
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = lean_string_utf8_byte_size(v_p_354_);
lean_inc_ref(v_p_354_);
v___x_371_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_371_, 0, v_p_354_);
lean_ctor_set(v___x_371_, 1, v___x_369_);
lean_ctor_set(v___x_371_, 2, v___x_370_);
v___x_372_ = l_String_Slice_Pos_get_x3f(v___x_371_, v___x_369_);
lean_dec_ref_known(v___x_371_, 3);
if (lean_obj_tag(v___x_372_) == 0)
{
uint32_t v___x_373_; 
v___x_373_ = 65;
v___y_357_ = v___x_373_;
goto v___jp_356_;
}
else
{
lean_object* v_val_374_; uint32_t v___x_375_; 
v_val_374_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v___x_372_, 1);
v___x_375_ = lean_unbox_uint32(v_val_374_);
lean_dec(v_val_374_);
v___y_357_ = v___x_375_;
goto v___jp_356_;
}
v___jp_356_:
{
uint8_t v___x_358_; 
v___x_358_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_357_, v___x_355_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_unsigned_to_nat(3u);
v___x_361_ = lean_string_utf8_byte_size(v_p_354_);
v___x_362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_362_, 0, v_p_354_);
lean_ctor_set(v___x_362_, 1, v___x_359_);
lean_ctor_set(v___x_362_, 2, v___x_361_);
v___x_363_ = l_String_Slice_Pos_nextn(v___x_362_, v___x_359_, v___x_360_);
lean_dec_ref_known(v___x_362_, 3);
return v___x_363_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = lean_string_utf8_byte_size(v_p_354_);
v___x_367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_367_, 0, v_p_354_);
lean_ctor_set(v___x_367_, 1, v___x_364_);
lean_ctor_set(v___x_367_, 2, v___x_366_);
v___x_368_ = l_String_Slice_Pos_nextn(v___x_367_, v___x_364_, v___x_365_);
lean_dec_ref_known(v___x_367_, 3);
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object* v_p_376_){
_start:
{
lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___x_387_; lean_object* v___y_389_; 
lean_inc_ref(v_p_376_);
v___x_387_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_376_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v___x_409_; 
v___x_409_ = lean_box(0);
v___y_389_ = v___x_409_;
goto v___jp_388_;
}
else
{
lean_object* v_val_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_val_410_ = lean_ctor_get(v___x_387_, 0);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_string_utf8_extract_fast(v_p_376_, v___x_411_, v_val_410_);
v___x_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
v___y_389_ = v___x_413_;
goto v___jp_388_;
}
v___jp_377_:
{
lean_object* v___x_382_; uint8_t v___x_383_; 
lean_inc(v___y_380_);
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v___y_380_);
v___x_383_ = l_Option_instDecidableEq___redArg(v___y_378_, v___y_381_, v___x_382_);
if (v___x_383_ == 0)
{
lean_dec(v___y_380_);
lean_dec_ref(v_p_376_);
return v___y_379_;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v___y_379_);
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_string_utf8_extract_fast(v_p_376_, v___x_384_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v_p_376_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
v___jp_388_:
{
uint8_t v___x_390_; 
lean_inc_ref(v_p_376_);
v___x_390_ = l_System_FilePath_isAbsolute(v_p_376_);
if (v___x_390_ == 0)
{
lean_dec(v___x_387_);
lean_dec_ref(v_p_376_);
return v___y_389_;
}
else
{
lean_object* v_afterRootDirectory_391_; lean_object* v___x_392_; uint8_t v_decide_393_; 
lean_inc_ref(v_p_376_);
v_afterRootDirectory_391_ = l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(v_p_376_);
v___x_392_ = lean_string_utf8_byte_size(v_p_376_);
v_decide_393_ = lean_nat_dec_eq(v_afterRootDirectory_391_, v___x_392_);
if (v_decide_393_ == 0)
{
lean_object* v___x_394_; 
lean_inc_ref(v_p_376_);
v___x_394_ = lean_alloc_closure((void*)(l_String_instDecidableEqPos___boxed), 3, 1);
lean_closure_set(v___x_394_, 0, v_p_376_);
if (lean_obj_tag(v___x_387_) == 0)
{
v___y_378_ = v___x_394_;
v___y_379_ = v___y_389_;
v___y_380_ = v_afterRootDirectory_391_;
v___y_381_ = v___x_387_;
goto v___jp_377_;
}
else
{
lean_object* v_val_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_val_395_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v___x_387_, 1);
v___x_396_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_p_376_);
v___x_397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_397_, 0, v_p_376_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
lean_ctor_set(v___x_397_, 2, v___x_392_);
v___x_398_ = l_String_Slice_Pos_next_x3f(v___x_397_, v_val_395_);
lean_dec(v_val_395_);
lean_dec_ref_known(v___x_397_, 3);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(0);
v___y_378_ = v___x_394_;
v___y_379_ = v___y_389_;
v___y_380_ = v_afterRootDirectory_391_;
v___y_381_ = v___x_399_;
goto v___jp_377_;
}
else
{
lean_object* v_val_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
v_val_400_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_398_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_val_400_);
lean_dec(v___x_398_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_val_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
v___y_378_ = v___x_394_;
v___y_379_ = v___y_389_;
v___y_380_ = v_afterRootDirectory_391_;
v___y_381_ = v___x_405_;
goto v___jp_377_;
}
}
}
}
}
else
{
lean_object* v___x_408_; 
lean_dec(v_afterRootDirectory_391_);
lean_dec(v___y_389_);
lean_dec(v___x_387_);
lean_dec_ref(v_p_376_);
v___x_408_ = lean_box(0);
return v___x_408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object* v_p_416_){
_start:
{
lean_object* v___y_418_; lean_object* v___x_430_; 
lean_inc_ref(v_p_416_);
v___x_430_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_416_);
if (lean_obj_tag(v___x_430_) == 0)
{
v___y_418_ = v_p_416_;
goto v___jp_417_;
}
else
{
lean_object* v_val_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_val_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_val_431_);
lean_dec_ref_known(v___x_430_, 1);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_string_utf8_byte_size(v_p_416_);
lean_inc_ref(v_p_416_);
v___x_434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_434_, 0, v_p_416_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
lean_ctor_set(v___x_434_, 2, v___x_433_);
v___x_435_ = l_String_Slice_Pos_next_x21(v___x_434_, v_val_431_);
lean_dec(v_val_431_);
lean_dec_ref_known(v___x_434_, 3);
v___x_436_ = lean_string_utf8_extract_fast(v_p_416_, v___x_435_, v___x_433_);
lean_dec(v___x_435_);
lean_dec_ref(v_p_416_);
v___y_418_ = v___x_436_;
goto v___jp_417_;
}
v___jp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_419_ = lean_string_utf8_byte_size(v___y_418_);
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_nat_dec_eq(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_423_ = lean_string_dec_eq(v___y_418_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
v___x_425_ = lean_string_dec_eq(v___y_418_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v___y_418_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; 
lean_dec_ref(v___y_418_);
v___x_427_ = lean_box(0);
return v___x_427_;
}
}
else
{
lean_object* v___x_428_; 
lean_dec_ref(v___y_418_);
v___x_428_ = lean_box(0);
return v___x_428_;
}
}
else
{
lean_object* v___x_429_; 
lean_dec_ref(v___y_418_);
v___x_429_ = lean_box(0);
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(lean_object* v_s_437_, lean_object* v_a_438_, lean_object* v_b_439_){
_start:
{
lean_object* v___x_440_; uint8_t v_decide_441_; 
v___x_440_ = lean_unsigned_to_nat(0u);
v_decide_441_ = lean_nat_dec_eq(v_a_438_, v___x_440_);
if (v_decide_441_ == 0)
{
lean_object* v_str_442_; lean_object* v_startInclusive_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint32_t v___x_451_; uint32_t v___x_452_; uint8_t v___x_453_; 
v_str_442_ = lean_ctor_get(v_s_437_, 0);
v_startInclusive_443_ = lean_ctor_get(v_s_437_, 1);
v___x_444_ = lean_nat_add(v_startInclusive_443_, v_a_438_);
lean_inc(v___x_444_);
lean_inc(v_startInclusive_443_);
lean_inc_ref(v_str_442_);
v___x_445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_445_, 0, v_str_442_);
lean_ctor_set(v___x_445_, 1, v_startInclusive_443_);
lean_ctor_set(v___x_445_, 2, v___x_444_);
v___x_446_ = lean_nat_sub(v___x_444_, v_startInclusive_443_);
lean_dec(v___x_444_);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_sub(v___x_446_, v___x_447_);
lean_dec(v___x_446_);
v___x_449_ = l_String_Slice_posLE(v___x_445_, v___x_448_);
lean_dec_ref_known(v___x_445_, 3);
v___x_450_ = lean_nat_add(v_startInclusive_443_, v___x_449_);
v___x_451_ = lean_string_utf8_get_fast(v_str_442_, v___x_450_);
lean_dec(v___x_450_);
v___x_452_ = 46;
v___x_453_ = lean_uint32_dec_eq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v___x_449_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_nat_sub(v_a_438_, v___x_447_);
lean_dec(v_a_438_);
v___x_456_ = l_String_Slice_posLE(v_s_437_, v___x_455_);
v_a_438_ = v___x_456_;
v_b_439_ = v___x_454_;
goto _start;
}
else
{
lean_object* v___x_458_; 
lean_dec(v_a_438_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_449_);
return v___x_458_;
}
}
else
{
lean_dec(v_a_438_);
lean_inc(v_b_439_);
return v_b_439_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg___boxed(lean_object* v_s_459_, lean_object* v_a_460_, lean_object* v_b_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_459_, v_a_460_, v_b_461_);
lean_dec(v_b_461_);
lean_dec_ref(v_s_459_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(lean_object* v_s_463_){
_start:
{
lean_object* v_startInclusive_464_; lean_object* v_endExclusive_465_; lean_object* v_searcher_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_startInclusive_464_ = lean_ctor_get(v_s_463_, 1);
v_endExclusive_465_ = lean_ctor_get(v_s_463_, 2);
v_searcher_466_ = lean_nat_sub(v_endExclusive_465_, v_startInclusive_464_);
v___x_467_ = lean_box(0);
v___x_468_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_463_, v_searcher_466_, v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0___boxed(lean_object* v_s_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v_s_469_);
lean_dec_ref(v_s_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object* v_p_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_System_FilePath_fileName(v_p_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
return v___x_472_;
}
else
{
lean_object* v_val_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_val_473_ = lean_ctor_get(v___x_472_, 0);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_string_utf8_byte_size(v_val_473_);
lean_inc(v_val_473_);
v___x_476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_476_, 0, v_val_473_);
lean_ctor_set(v___x_476_, 1, v___x_474_);
lean_ctor_set(v___x_476_, 2, v___x_475_);
v___x_477_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_476_);
lean_dec_ref_known(v___x_476_, 3);
if (lean_obj_tag(v___x_477_) == 0)
{
return v___x_472_;
}
else
{
lean_object* v_val_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_487_; 
v_val_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_487_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_val_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint8_t v___x_482_; 
v___x_482_ = lean_nat_dec_eq(v_val_478_, v___x_474_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_inc(v_val_473_);
lean_dec_ref_known(v___x_472_, 1);
v___x_483_ = lean_string_utf8_extract(v_val_473_, v___x_474_, v_val_478_);
lean_dec(v_val_478_);
lean_dec(v_val_473_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_483_);
v___x_485_ = v___x_480_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
else
{
lean_del_object(v___x_480_);
lean_dec(v_val_478_);
return v___x_472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(lean_object* v_s_488_, lean_object* v_inst_489_, lean_object* v_R_490_, lean_object* v_a_491_, lean_object* v_b_492_, lean_object* v_c_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_488_, v_a_491_, v_b_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___boxed(lean_object* v_s_495_, lean_object* v_inst_496_, lean_object* v_R_497_, lean_object* v_a_498_, lean_object* v_b_499_, lean_object* v_c_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(v_s_495_, v_inst_496_, v_R_497_, v_a_498_, v_b_499_, v_c_500_);
lean_dec(v_b_499_);
lean_dec_ref(v_s_495_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object* v_p_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_System_FilePath_fileName(v_p_502_);
if (lean_obj_tag(v___x_503_) == 0)
{
return v___x_503_;
}
else
{
lean_object* v_val_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_val_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc_n(v_val_504_, 2);
lean_dec_ref_known(v___x_503_, 1);
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_string_utf8_byte_size(v_val_504_);
v___x_507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_507_, 0, v_val_504_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
lean_ctor_set(v___x_507_, 2, v___x_506_);
v___x_508_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_507_);
lean_dec_ref_known(v___x_507_, 3);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v___x_509_; 
lean_dec(v_val_504_);
v___x_509_ = lean_box(0);
return v___x_509_;
}
else
{
lean_object* v_val_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_522_; 
v_val_510_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_522_ == 0)
{
v___x_512_ = v___x_508_;
v_isShared_513_ = v_isSharedCheck_522_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_val_510_);
lean_dec(v___x_508_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_522_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
uint8_t v___x_514_; 
v___x_514_ = lean_nat_dec_eq(v_val_510_, v___x_505_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_add(v_val_510_, v___x_515_);
lean_dec(v_val_510_);
v___x_517_ = lean_string_utf8_extract(v_val_504_, v___x_516_, v___x_506_);
lean_dec(v___x_516_);
lean_dec(v_val_504_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_517_);
v___x_519_ = v___x_512_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
else
{
lean_object* v___x_521_; 
lean_del_object(v___x_512_);
lean_dec(v_val_510_);
lean_dec(v_val_504_);
v___x_521_ = lean_box(0);
return v___x_521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object* v_p_523_, lean_object* v_fname_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_System_FilePath_parent(v_p_523_);
if (lean_obj_tag(v___x_525_) == 0)
{
return v_fname_524_;
}
else
{
lean_object* v_val_526_; lean_object* v___x_527_; 
v_val_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_val_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = l_System_FilePath_join(v_val_526_, v_fname_524_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object* v_p_528_, lean_object* v_ext_529_){
_start:
{
lean_object* v___x_530_; 
lean_inc_ref(v_p_528_);
v___x_530_ = l_System_FilePath_fileName(v_p_528_);
if (lean_obj_tag(v___x_530_) == 0)
{
return v_p_528_;
}
else
{
lean_object* v_val_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_val_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_val_531_);
lean_dec_ref_known(v___x_530_, 1);
v___x_532_ = lean_string_utf8_byte_size(v_ext_529_);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_nat_dec_eq(v___x_532_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_535_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_536_ = lean_string_append(v_val_531_, v___x_535_);
v___x_537_ = lean_string_append(v___x_536_, v_ext_529_);
v___x_538_ = l_System_FilePath_withFileName(v_p_528_, v___x_537_);
return v___x_538_;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = l_System_FilePath_withFileName(v_p_528_, v_val_531_);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object* v_p_540_, lean_object* v_ext_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_System_FilePath_addExtension(v_p_540_, v_ext_541_);
lean_dec_ref(v_ext_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object* v_p_543_, lean_object* v_ext_544_){
_start:
{
lean_object* v___x_545_; 
lean_inc_ref(v_p_543_);
v___x_545_ = l_System_FilePath_fileStem(v_p_543_);
if (lean_obj_tag(v___x_545_) == 0)
{
return v_p_543_;
}
else
{
lean_object* v_val_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_val_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_545_, 1);
v___x_547_ = lean_string_utf8_byte_size(v_ext_544_);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_nat_dec_eq(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_550_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_551_ = lean_string_append(v_val_546_, v___x_550_);
v___x_552_ = lean_string_append(v___x_551_, v_ext_544_);
v___x_553_ = l_System_FilePath_withFileName(v_p_543_, v___x_552_);
return v___x_553_;
}
else
{
lean_object* v___x_554_; 
v___x_554_ = l_System_FilePath_withFileName(v_p_543_, v_val_546_);
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object* v_p_555_, lean_object* v_ext_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_System_FilePath_withExtension(v_p_555_, v_ext_556_);
lean_dec_ref(v_ext_556_);
return v_res_557_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_559_ = lean_string_utf8_byte_size(v___x_558_);
return v___x_559_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0);
v___x_562_ = lean_nat_dec_eq(v___x_561_, v___x_560_);
return v___x_562_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_563_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0);
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_564_);
lean_ctor_set(v___x_566_, 2, v___x_563_);
return v___x_566_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2);
v___x_568_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3);
v___x_571_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2);
v___x_572_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v___x_570_);
lean_ctor_set(v___x_572_, 2, v___x_569_);
lean_ctor_set(v___x_572_, 3, v___x_569_);
return v___x_572_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg(){
_start:
{
uint8_t v___x_582_; 
v___x_582_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
v___x_583_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5);
return v___x_583_;
}
else
{
lean_object* v___x_584_; 
v___x_584_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__7));
return v___x_584_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___boxed(lean_object* v___dummy_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg();
return v_res_586_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0(void){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg();
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(lean_object* v_s_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(lean_object* v_s_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v_s_590_);
lean_dec_ref(v_s_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object* v___x_592_, lean_object* v___x_593_, lean_object* v___x_594_, lean_object* v_a_595_, lean_object* v_b_596_){
_start:
{
lean_object* v_it_598_; lean_object* v_startInclusive_599_; lean_object* v_endExclusive_600_; 
if (lean_obj_tag(v_a_595_) == 0)
{
lean_object* v_currPos_605_; lean_object* v_searcher_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_712_; 
v_currPos_605_ = lean_ctor_get(v_a_595_, 0);
v_searcher_606_ = lean_ctor_get(v_a_595_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_a_595_);
if (v_isSharedCheck_712_ == 0)
{
v___x_608_ = v_a_595_;
v_isShared_609_ = v_isSharedCheck_712_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_searcher_606_);
lean_inc(v_currPos_605_);
lean_dec(v_a_595_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_712_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_it_611_; lean_object* v_it_617_; lean_object* v_startPos_618_; lean_object* v_endPos_619_; 
switch(lean_obj_tag(v_searcher_606_))
{
case 0:
{
lean_object* v_pos_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_644_; 
lean_del_object(v___x_608_);
v_pos_632_ = lean_ctor_get(v_searcher_606_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v_searcher_606_);
if (v_isSharedCheck_644_ == 0)
{
v___x_634_ = v_searcher_606_;
v_isShared_635_ = v_isSharedCheck_644_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_pos_632_);
lean_dec(v_searcher_606_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_644_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v_startInclusive_636_; lean_object* v_endExclusive_637_; lean_object* v___x_638_; uint8_t v_decide_639_; 
v_startInclusive_636_ = lean_ctor_get(v___x_593_, 1);
v_endExclusive_637_ = lean_ctor_get(v___x_593_, 2);
v___x_638_ = lean_nat_sub(v_endExclusive_637_, v_startInclusive_636_);
v_decide_639_ = lean_nat_dec_eq(v_pos_632_, v___x_638_);
lean_dec(v___x_638_);
if (v_decide_639_ == 0)
{
lean_object* v___x_641_; 
lean_inc(v_pos_632_);
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 1);
v___x_641_ = v___x_634_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_pos_632_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_inc(v_pos_632_);
v_it_617_ = v___x_641_;
v_startPos_618_ = v_pos_632_;
v_endPos_619_ = v_pos_632_;
goto v___jp_616_;
}
}
else
{
lean_object* v___x_643_; 
lean_del_object(v___x_634_);
v___x_643_ = lean_box(3);
lean_inc(v_pos_632_);
v_it_617_ = v___x_643_;
v_startPos_618_ = v_pos_632_;
v_endPos_619_ = v_pos_632_;
goto v___jp_616_;
}
}
}
case 1:
{
lean_object* v_pos_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_653_; 
v_pos_645_ = lean_ctor_get(v_searcher_606_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_searcher_606_);
if (v_isSharedCheck_653_ == 0)
{
v___x_647_ = v_searcher_606_;
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_pos_645_);
lean_dec(v_searcher_606_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = lean_string_utf8_next_fast(v___x_592_, v_pos_645_);
lean_dec(v_pos_645_);
if (v_isShared_648_ == 0)
{
lean_ctor_set_tag(v___x_647_, 0);
lean_ctor_set(v___x_647_, 0, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
v_it_611_ = v___x_651_;
goto v___jp_610_;
}
}
}
case 2:
{
lean_object* v_needle_654_; lean_object* v_table_655_; lean_object* v_stackPos_656_; lean_object* v_needlePos_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_711_; 
v_needle_654_ = lean_ctor_get(v_searcher_606_, 0);
v_table_655_ = lean_ctor_get(v_searcher_606_, 1);
v_stackPos_656_ = lean_ctor_get(v_searcher_606_, 2);
v_needlePos_657_ = lean_ctor_get(v_searcher_606_, 3);
v_isSharedCheck_711_ = !lean_is_exclusive(v_searcher_606_);
if (v_isSharedCheck_711_ == 0)
{
v___x_659_ = v_searcher_606_;
v_isShared_660_ = v_isSharedCheck_711_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_needlePos_657_);
lean_inc(v_stackPos_656_);
lean_inc(v_table_655_);
lean_inc(v_needle_654_);
lean_dec(v_searcher_606_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_711_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_str_661_; lean_object* v_startInclusive_662_; lean_object* v_endExclusive_663_; lean_object* v_basePos_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_str_661_ = lean_ctor_get(v_needle_654_, 0);
v_startInclusive_662_ = lean_ctor_get(v_needle_654_, 1);
v_endExclusive_663_ = lean_ctor_get(v_needle_654_, 2);
v_basePos_664_ = lean_nat_sub(v_stackPos_656_, v_needlePos_657_);
v___x_665_ = lean_nat_sub(v_endExclusive_663_, v_startInclusive_662_);
v___x_666_ = lean_nat_add(v_basePos_664_, v___x_665_);
v___x_667_ = lean_nat_dec_le(v___x_666_, v___x_594_);
lean_dec(v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
lean_dec(v___x_665_);
lean_del_object(v___x_659_);
lean_dec(v_needlePos_657_);
lean_dec(v_stackPos_656_);
lean_dec_ref(v_table_655_);
lean_dec_ref(v_needle_654_);
v___x_668_ = lean_unsigned_to_nat(1u);
v___x_669_ = lean_nat_add(v_basePos_664_, v___x_668_);
lean_dec(v_basePos_664_);
v___x_670_ = lean_nat_dec_le(v___x_669_, v___x_594_);
lean_dec(v___x_669_);
if (v___x_670_ == 0)
{
lean_del_object(v___x_608_);
goto v___jp_630_;
}
else
{
lean_object* v___x_671_; 
v___x_671_ = lean_box(3);
v_it_611_ = v___x_671_;
goto v___jp_610_;
}
}
else
{
uint8_t v_stackByte_672_; lean_object* v___x_673_; uint8_t v_patByte_674_; uint8_t v___x_675_; 
lean_dec(v_basePos_664_);
lean_inc(v_stackPos_656_);
v_stackByte_672_ = lean_string_get_byte_fast(v___x_592_, v_stackPos_656_);
v___x_673_ = lean_nat_add(v_startInclusive_662_, v_needlePos_657_);
v_patByte_674_ = lean_string_get_byte_fast(v_str_661_, v___x_673_);
v___x_675_ = lean_uint8_dec_eq(v_stackByte_672_, v_patByte_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; uint8_t v_decide_677_; 
lean_dec(v___x_665_);
v___x_676_ = lean_unsigned_to_nat(0u);
v_decide_677_ = lean_nat_dec_eq(v_needlePos_657_, v___x_676_);
if (v_decide_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v_newNeedlePos_680_; uint8_t v___x_681_; 
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_nat_sub(v_needlePos_657_, v___x_678_);
lean_dec(v_needlePos_657_);
v_newNeedlePos_680_ = lean_array_fget_borrowed(v_table_655_, v___x_679_);
lean_dec(v___x_679_);
v___x_681_ = lean_nat_dec_eq(v_newNeedlePos_680_, v___x_676_);
if (v___x_681_ == 0)
{
lean_object* v___x_683_; 
lean_inc(v_newNeedlePos_680_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 3, v_newNeedlePos_680_);
v___x_683_ = v___x_659_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_needle_654_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_table_655_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v_stackPos_656_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v_newNeedlePos_680_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
v_it_611_ = v___x_683_;
goto v___jp_610_;
}
}
else
{
lean_object* v_nextStackPos_685_; lean_object* v___x_687_; 
v_nextStackPos_685_ = l_String_Slice_posGE___redArg(v___x_593_, v_stackPos_656_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 3, v___x_676_);
lean_ctor_set(v___x_659_, 2, v_nextStackPos_685_);
v___x_687_ = v___x_659_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_needle_654_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_table_655_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_nextStackPos_685_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v___x_676_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
v_it_611_ = v___x_687_;
goto v___jp_610_;
}
}
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v_nextStackPos_691_; lean_object* v___x_693_; 
lean_dec(v_needlePos_657_);
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = lean_nat_add(v_stackPos_656_, v___x_689_);
lean_dec(v_stackPos_656_);
v_nextStackPos_691_ = l_String_Slice_posGE___redArg(v___x_593_, v___x_690_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 3, v___x_676_);
lean_ctor_set(v___x_659_, 2, v_nextStackPos_691_);
v___x_693_ = v___x_659_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_needle_654_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_table_655_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_nextStackPos_691_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v___x_676_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
v_it_611_ = v___x_693_;
goto v___jp_610_;
}
}
}
else
{
lean_object* v___x_695_; lean_object* v_nextStackPos_696_; lean_object* v_nextNeedlePos_697_; uint8_t v_decide_698_; 
lean_del_object(v___x_608_);
v___x_695_ = lean_unsigned_to_nat(1u);
v_nextStackPos_696_ = lean_nat_add(v_stackPos_656_, v___x_695_);
lean_dec(v_stackPos_656_);
v_nextNeedlePos_697_ = lean_nat_add(v_needlePos_657_, v___x_695_);
lean_dec(v_needlePos_657_);
v_decide_698_ = lean_nat_dec_eq(v_nextNeedlePos_697_, v___x_665_);
lean_dec(v___x_665_);
if (v_decide_698_ == 0)
{
lean_object* v___x_700_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 3, v_nextNeedlePos_697_);
lean_ctor_set(v___x_659_, 2, v_nextStackPos_696_);
v___x_700_ = v___x_659_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_needle_654_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_table_655_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_nextStackPos_696_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_nextNeedlePos_697_);
v___x_700_ = v_reuseFailAlloc_703_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_currPos_605_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v_a_595_ = v___x_701_;
goto _start;
}
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_704_ = lean_nat_sub(v_nextStackPos_696_, v_nextNeedlePos_697_);
lean_dec(v_nextNeedlePos_697_);
v___x_705_ = l_String_Slice_pos_x21(v___x_593_, v___x_704_);
lean_dec(v___x_704_);
v___x_706_ = l_String_Slice_pos_x21(v___x_593_, v_nextStackPos_696_);
v___x_707_ = lean_unsigned_to_nat(0u);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 3, v___x_707_);
lean_ctor_set(v___x_659_, 2, v_nextStackPos_696_);
v___x_709_ = v___x_659_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_needle_654_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_table_655_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_nextStackPos_696_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
v_it_617_ = v___x_709_;
v_startPos_618_ = v___x_705_;
v_endPos_619_ = v___x_706_;
goto v___jp_616_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_608_);
goto v___jp_630_;
}
}
v___jp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v_it_611_);
v___x_613_ = v___x_608_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_currPos_605_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_it_611_);
v___x_613_ = v_reuseFailAlloc_615_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
v_a_595_ = v___x_613_;
goto _start;
}
}
v___jp_616_:
{
lean_object* v_slice_620_; lean_object* v_startInclusive_621_; lean_object* v_endExclusive_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
v_slice_620_ = l_String_Slice_subslice_x21(v___x_593_, v_currPos_605_, v_startPos_618_);
v_startInclusive_621_ = lean_ctor_get(v_slice_620_, 0);
v_endExclusive_622_ = lean_ctor_get(v_slice_620_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_slice_620_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v_slice_620_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_endExclusive_622_);
lean_inc(v_startInclusive_621_);
lean_dec(v_slice_620_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v_nextIt_627_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v_it_617_);
lean_ctor_set(v___x_624_, 0, v_endPos_619_);
v_nextIt_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_endPos_619_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_it_617_);
v_nextIt_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
v_it_598_ = v_nextIt_627_;
v_startInclusive_599_ = v_startInclusive_621_;
v_endExclusive_600_ = v_endExclusive_622_;
goto v___jp_597_;
}
}
}
v___jp_630_:
{
lean_object* v___x_631_; 
v___x_631_ = lean_box(1);
lean_inc(v___x_594_);
v_it_598_ = v___x_631_;
v_startInclusive_599_ = v_currPos_605_;
v_endExclusive_600_ = v___x_594_;
goto v___jp_597_;
}
}
}
else
{
lean_dec(v___x_594_);
lean_dec_ref(v___x_592_);
return v_b_596_;
}
v___jp_597_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_inc_ref(v___x_592_);
v___x_601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_601_, 0, v___x_592_);
lean_ctor_set(v___x_601_, 1, v_startInclusive_599_);
lean_ctor_set(v___x_601_, 2, v_endExclusive_600_);
v___x_602_ = l_String_Slice_toString(v___x_601_);
lean_dec_ref_known(v___x_601_, 3);
v___x_603_ = lean_array_push(v_b_596_, v___x_602_);
v_a_595_ = v_it_598_;
v_b_596_ = v___x_603_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v___x_715_, lean_object* v_a_716_, lean_object* v_b_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_713_, v___x_714_, v___x_715_, v_a_716_, v_b_717_);
lean_dec_ref(v___x_714_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object* v_p_721_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_722_ = l_System_FilePath_normalize(v_p_721_);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_string_utf8_byte_size(v___x_722_);
lean_inc_ref(v___x_722_);
v___x_725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_725_, 0, v___x_722_);
lean_ctor_set(v___x_725_, 1, v___x_723_);
lean_ctor_set(v___x_725_, 2, v___x_724_);
v___x_726_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
v___x_727_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_728_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_722_, v___x_725_, v___x_724_, v___x_726_, v___x_727_);
lean_dec_ref_known(v___x_725_, 3);
v___x_729_ = lean_array_to_list(v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object* v___x_730_, lean_object* v___x_731_, lean_object* v___x_732_, lean_object* v_inst_733_, lean_object* v_R_734_, lean_object* v_a_735_, lean_object* v_b_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_730_, v___x_731_, v___x_732_, v_a_735_, v_b_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object* v___x_738_, lean_object* v___x_739_, lean_object* v___x_740_, lean_object* v_inst_741_, lean_object* v_R_742_, lean_object* v_a_743_, lean_object* v_b_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(v___x_738_, v___x_739_, v___x_740_, v_inst_741_, v_R_742_, v_a_743_, v_b_744_);
lean_dec_ref(v___x_739_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object* v_parts_746_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_748_ = l_String_intercalate(v___x_747_, v_parts_746_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object* v_toString_749_){
_start:
{
lean_inc_ref(v_toString_749_);
return v_toString_749_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object* v_toString_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_System_instCoeStringFilePath___lam__0(v_toString_750_);
lean_dec_ref(v_toString_750_);
return v_res_751_;
}
}
static uint32_t _init_l_System_SearchPath_separator(void){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = l_System_Platform_isWindows;
if (v___x_754_ == 0)
{
uint32_t v___x_755_; 
v___x_755_ = 58;
return v___x_755_;
}
else
{
uint32_t v___x_756_; 
v___x_756_ = 59;
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___closed__0));
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___boxed(lean_object* v___dummy_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg();
return v_res_762_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0(void){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg();
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(lean_object* v_s_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___boxed(lean_object* v_s_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v_s_766_);
lean_dec_ref(v_s_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(lean_object* v_s_768_, lean_object* v___x_769_, lean_object* v___x_770_, lean_object* v_a_771_, lean_object* v_b_772_){
_start:
{
lean_object* v_it_774_; lean_object* v_startInclusive_775_; lean_object* v_endExclusive_776_; 
if (lean_obj_tag(v_a_771_) == 0)
{
lean_object* v_currPos_780_; lean_object* v_searcher_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_804_; 
v_currPos_780_ = lean_ctor_get(v_a_771_, 0);
v_searcher_781_ = lean_ctor_get(v_a_771_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_a_771_);
if (v_isSharedCheck_804_ == 0)
{
v___x_783_ = v_a_771_;
v_isShared_784_ = v_isSharedCheck_804_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_searcher_781_);
lean_inc(v_currPos_780_);
lean_dec(v_a_771_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_804_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
uint8_t v_decide_785_; 
v_decide_785_ = lean_nat_dec_eq(v_searcher_781_, v___x_770_);
if (v_decide_785_ == 0)
{
uint32_t v___x_786_; uint32_t v___x_787_; uint8_t v___x_788_; 
v___x_786_ = l_System_SearchPath_separator;
v___x_787_ = lean_string_utf8_get_fast(v_s_768_, v_searcher_781_);
v___x_788_ = lean_uint32_dec_eq(v___x_787_, v___x_786_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = lean_string_utf8_next_fast(v_s_768_, v_searcher_781_);
lean_dec(v_searcher_781_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_789_);
v___x_791_ = v___x_783_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_currPos_780_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_789_);
v___x_791_ = v_reuseFailAlloc_793_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
v_a_771_ = v___x_791_;
goto _start;
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_slice_797_; lean_object* v_nextIt_799_; 
v___x_794_ = lean_string_utf8_next_fast(v_s_768_, v_searcher_781_);
v___x_795_ = lean_nat_sub(v___x_794_, v_searcher_781_);
v___x_796_ = lean_nat_add(v_searcher_781_, v___x_795_);
lean_dec(v___x_795_);
v_slice_797_ = l_String_Slice_subslice_x21(v___x_769_, v_currPos_780_, v_searcher_781_);
lean_inc(v___x_796_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_796_);
lean_ctor_set(v___x_783_, 0, v___x_796_);
v_nextIt_799_ = v___x_783_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___x_796_);
v_nextIt_799_ = v_reuseFailAlloc_802_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v_startInclusive_800_; lean_object* v_endExclusive_801_; 
v_startInclusive_800_ = lean_ctor_get(v_slice_797_, 0);
lean_inc(v_startInclusive_800_);
v_endExclusive_801_ = lean_ctor_get(v_slice_797_, 1);
lean_inc(v_endExclusive_801_);
lean_dec_ref(v_slice_797_);
v_it_774_ = v_nextIt_799_;
v_startInclusive_775_ = v_startInclusive_800_;
v_endExclusive_776_ = v_endExclusive_801_;
goto v___jp_773_;
}
}
}
else
{
lean_object* v___x_803_; 
lean_del_object(v___x_783_);
lean_dec(v_searcher_781_);
v___x_803_ = lean_box(1);
lean_inc(v___x_770_);
v_it_774_ = v___x_803_;
v_startInclusive_775_ = v_currPos_780_;
v_endExclusive_776_ = v___x_770_;
goto v___jp_773_;
}
}
}
else
{
lean_dec(v___x_770_);
return v_b_772_;
}
v___jp_773_:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_string_utf8_extract_fast(v_s_768_, v_startInclusive_775_, v_endExclusive_776_);
lean_dec(v_endExclusive_776_);
lean_dec(v_startInclusive_775_);
v___x_778_ = lean_array_push(v_b_772_, v___x_777_);
v_a_771_ = v_it_774_;
v_b_772_ = v___x_778_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg___boxed(lean_object* v_s_805_, lean_object* v___x_806_, lean_object* v___x_807_, lean_object* v_a_808_, lean_object* v_b_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_805_, v___x_806_, v___x_807_, v_a_808_, v_b_809_);
lean_dec_ref(v___x_806_);
lean_dec_ref(v_s_805_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object* v_s_811_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = lean_string_utf8_byte_size(v_s_811_);
lean_inc_ref(v_s_811_);
v___x_814_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_814_, 0, v_s_811_);
lean_ctor_set(v___x_814_, 1, v___x_812_);
lean_ctor_set(v___x_814_, 2, v___x_813_);
v___x_815_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0);
v___x_816_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_817_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_811_, v___x_814_, v___x_813_, v___x_815_, v___x_816_);
lean_dec_ref_known(v___x_814_, 3);
lean_dec_ref(v_s_811_);
v___x_818_ = lean_array_to_list(v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(lean_object* v_s_819_, lean_object* v___x_820_, lean_object* v___x_821_, lean_object* v_inst_822_, lean_object* v_R_823_, lean_object* v_a_824_, lean_object* v_b_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_819_, v___x_820_, v___x_821_, v_a_824_, v_b_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___boxed(lean_object* v_s_827_, lean_object* v___x_828_, lean_object* v___x_829_, lean_object* v_inst_830_, lean_object* v_R_831_, lean_object* v_a_832_, lean_object* v_b_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(v_s_827_, v___x_828_, v___x_829_, v_inst_830_, v_R_831_, v_a_832_, v_b_833_);
lean_dec_ref(v___x_828_);
lean_dec_ref(v_s_827_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
if (lean_obj_tag(v_a_835_) == 0)
{
lean_object* v___x_837_; 
v___x_837_ = l_List_reverse___redArg(v_a_836_);
return v___x_837_;
}
else
{
lean_object* v_head_838_; lean_object* v_tail_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_847_; 
v_head_838_ = lean_ctor_get(v_a_835_, 0);
v_tail_839_ = lean_ctor_get(v_a_835_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v_a_835_);
if (v_isSharedCheck_847_ == 0)
{
v___x_841_ = v_a_835_;
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_tail_839_);
lean_inc(v_head_838_);
lean_dec(v_a_835_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v_a_836_);
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_head_838_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_a_836_);
v___x_844_ = v_reuseFailAlloc_846_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
v_a_835_ = v_tail_839_;
v_a_836_ = v___x_844_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_System_SearchPath_toString___closed__0(void){
_start:
{
uint32_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = l_System_SearchPath_separator;
v___x_849_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_850_ = lean_string_push(v___x_849_, v___x_848_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object* v_path_851_){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_852_ = lean_obj_once(&l_System_SearchPath_toString___closed__0, &l_System_SearchPath_toString___closed__0_once, _init_l_System_SearchPath_toString___closed__0);
v___x_853_ = lean_box(0);
v___x_854_ = l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(v_path_851_, v___x_853_);
v___x_855_ = l_String_intercalate(v___x_852_, v___x_854_);
return v___x_855_;
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
