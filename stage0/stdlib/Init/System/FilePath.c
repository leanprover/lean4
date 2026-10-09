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
uint8_t l_System_instDecidableEqFilePath_decEq(lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_string_dec_eq(v_x_4_, v_x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_System_instDecidableEqFilePath_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4_ = stack[0].m_obj;
lean_object* v_x_5_ = stack[1].m_obj;
uint8_t v_res_7_;
v_res_7_ = l_System_instDecidableEqFilePath_decEq(v_x_4_, v_x_5_);
stack->m_num = v_res_7_;
}
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath_decEq___boxed(lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_System_instDecidableEqFilePath_decEq(v_x_8_, v_x_9_);
lean_dec_ref(v_x_9_);
lean_dec_ref(v_x_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
uint8_t l_System_instDecidableEqFilePath(lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
uint8_t v___x_14_; 
v___x_14_ = lean_string_dec_eq(v_x_12_, v_x_13_);
return v___x_14_;
}
}
LEAN_EXPORT void l_System_instDecidableEqFilePath_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_12_ = stack[0].m_obj;
lean_object* v_x_13_ = stack[1].m_obj;
uint8_t v_res_15_;
v_res_15_ = l_System_instDecidableEqFilePath(v_x_12_, v_x_13_);
stack->m_num = v_res_15_;
}
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_System_instDecidableEqFilePath(v_x_16_, v_x_17_);
lean_dec_ref(v_x_17_);
lean_dec_ref(v_x_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
uint64_t l_System_instHashableFilePath_hash(lean_object* v_x_20_){
_start:
{
uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; 
v___x_21_ = 0ULL;
v___x_22_ = lean_string_hash(v_x_20_);
v___x_23_ = lean_uint64_mix_hash(v___x_21_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT void l_System_instHashableFilePath_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_20_ = stack[0].m_obj;
uint64_t v_res_24_;
v_res_24_ = l_System_instHashableFilePath_hash(v_x_20_);
stack->m_num = v_res_24_;
}
LEAN_EXPORT lean_object* l_System_instHashableFilePath_hash___boxed(lean_object* v_x_25_){
_start:
{
uint64_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_System_instHashableFilePath_hash(v_x_25_);
lean_dec_ref(v_x_25_);
v_r_27_ = lean_box_uint64(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0(lean_object* v_p_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_35_ = ((lean_object*)(l_System_instReprFilePath___lam__0___closed__1));
v___x_36_ = l_String_quote(v_p_33_);
v___x_37_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
v___x_38_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_35_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
v___x_39_ = l_Repr_addAppParen(v___x_38_, v___y_34_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0___boxed(lean_object* v_p_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_System_instReprFilePath___lam__0(v_p_40_, v___y_41_);
lean_dec(v___y_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0(lean_object* v_p_45_){
_start:
{
lean_inc_ref(v_p_45_);
return v_p_45_;
}
}
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0___boxed(lean_object* v_p_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_System_instToStringFilePath___lam__0(v_p_46_);
lean_dec_ref(v_p_46_);
return v_res_47_;
}
}
static uint32_t _init_l_System_FilePath_pathSeparator(void){
_start:
{
uint8_t v___x_50_; 
v___x_50_ = l_System_Platform_isWindows;
if (v___x_50_ == 0)
{
uint32_t v___x_51_; 
v___x_51_ = 47;
return v___x_51_;
}
else
{
uint32_t v___x_52_; 
v___x_52_ = 92;
return v___x_52_;
}
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_53_; lean_object* v___x_54_; 
v___x_53_ = 47;
v___x_54_ = lean_box_uint32(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__0(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_box(0);
v___x_56_ = l_System_FilePath_pathSeparators___closed__0___boxed__const__1;
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_58_; lean_object* v___x_59_; 
v___x_58_ = 92;
v___x_59_ = lean_box_uint32(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__1(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_System_FilePath_pathSeparators___closed__0, &l_System_FilePath_pathSeparators___closed__0_once, _init_l_System_FilePath_pathSeparators___closed__0);
v___x_61_ = l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = l_System_Platform_isWindows;
if (v___x_63_ == 0)
{
lean_object* v___x_64_; 
v___x_64_ = lean_obj_once(&l_System_FilePath_pathSeparators___closed__0, &l_System_FilePath_pathSeparators___closed__0_once, _init_l_System_FilePath_pathSeparators___closed__0);
return v___x_64_;
}
else
{
lean_object* v___x_65_; 
v___x_65_ = lean_obj_once(&l_System_FilePath_pathSeparators___closed__1, &l_System_FilePath_pathSeparators___closed__1_once, _init_l_System_FilePath_pathSeparators___closed__1);
return v___x_65_;
}
}
}
static uint32_t _init_l_System_FilePath_extSeparator(void){
_start:
{
uint32_t v___x_66_; 
v___x_66_ = 46;
return v___x_66_;
}
}
static lean_object* _init_l_System_FilePath_exeExtension(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = l_System_Platform_isWindows;
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
v___x_69_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
return v___x_69_;
}
else
{
lean_object* v___x_70_; 
v___x_70_ = ((lean_object*)(l_System_FilePath_exeExtension___closed__0));
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(lean_object* v___x_71_, lean_object* v___x_72_, lean_object* v_a_73_, lean_object* v_b_74_){
_start:
{
lean_object* v_countdown_75_; lean_object* v_inner_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_92_; 
v_countdown_75_ = lean_ctor_get(v_a_73_, 0);
v_inner_76_ = lean_ctor_get(v_a_73_, 1);
v_isSharedCheck_92_ = !lean_is_exclusive(v_a_73_);
if (v_isSharedCheck_92_ == 0)
{
v___x_78_ = v_a_73_;
v_isShared_79_ = v_isSharedCheck_92_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_inner_76_);
lean_inc(v_countdown_75_);
lean_dec(v_a_73_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_92_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_dec_eq(v_countdown_75_, v___x_80_);
if (v___x_81_ == 0)
{
uint8_t v_decide_82_; 
v_decide_82_ = lean_nat_dec_eq(v_inner_76_, v___x_72_);
if (v_decide_82_ == 0)
{
lean_object* v___x_83_; uint32_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_83_ = lean_string_utf8_next_fast(v___x_71_, v_inner_76_);
v___x_84_ = lean_string_utf8_get_fast(v___x_71_, v_inner_76_);
lean_dec(v_inner_76_);
v___x_85_ = lean_nat_sub(v_countdown_75_, v___x_80_);
lean_dec(v_countdown_75_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___x_83_);
lean_ctor_set(v___x_78_, 0, v___x_85_);
v___x_87_ = v___x_78_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___x_83_);
v___x_87_ = v_reuseFailAlloc_91_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_box_uint32(v___x_84_);
v___x_89_ = lean_array_push(v_b_74_, v___x_88_);
v_a_73_ = v___x_87_;
v_b_74_ = v___x_89_;
goto _start;
}
}
else
{
lean_del_object(v___x_78_);
lean_dec(v_inner_76_);
lean_dec(v_countdown_75_);
return v_b_74_;
}
}
else
{
lean_del_object(v___x_78_);
lean_dec(v_inner_76_);
lean_dec(v_countdown_75_);
return v_b_74_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg___boxed(lean_object* v___x_93_, lean_object* v___x_94_, lean_object* v_a_95_, lean_object* v_b_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_93_, v___x_94_, v_a_95_, v_b_96_);
lean_dec(v___x_94_);
lean_dec_ref(v___x_93_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(lean_object* v_p_103_){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = l_System_Platform_isWindows;
if (v___x_104_ == 0)
{
return v_p_103_;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_string_utf8_byte_size(v_p_103_);
v___x_107_ = ((lean_object*)(l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0));
v___x_108_ = ((lean_object*)(l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__1));
v___x_109_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v_p_103_, v___x_106_, v___x_107_, v___x_108_);
v___x_110_ = lean_array_to_list(v___x_109_);
if (lean_obj_tag(v___x_110_) == 1)
{
lean_object* v_tail_111_; 
v_tail_111_ = lean_ctor_get(v___x_110_, 1);
lean_inc(v_tail_111_);
if (lean_obj_tag(v_tail_111_) == 1)
{
lean_object* v_head_112_; lean_object* v_head_113_; lean_object* v_tail_114_; uint32_t v___x_115_; uint32_t v___x_116_; uint8_t v___x_117_; 
v_head_112_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_head_112_);
lean_dec_ref_known(v___x_110_, 2);
v_head_113_ = lean_ctor_get(v_tail_111_, 0);
lean_inc(v_head_113_);
v_tail_114_ = lean_ctor_get(v_tail_111_, 1);
lean_inc(v_tail_114_);
lean_dec_ref_known(v_tail_111_, 2);
v___x_115_ = 58;
v___x_116_ = lean_unbox_uint32(v_head_113_);
lean_dec(v_head_113_);
v___x_117_ = lean_uint32_dec_eq(v___x_116_, v___x_115_);
if (v___x_117_ == 0)
{
lean_dec(v_tail_114_);
lean_dec(v_head_112_);
return v_p_103_;
}
else
{
if (lean_obj_tag(v_tail_114_) == 0)
{
uint32_t v___x_118_; uint32_t v___x_119_; uint8_t v___x_120_; 
v___x_118_ = 97;
v___x_119_ = lean_unbox_uint32(v_head_112_);
v___x_120_ = lean_uint32_dec_le(v___x_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_dec(v_head_112_);
return v_p_103_;
}
else
{
uint32_t v___x_121_; uint32_t v___x_122_; uint8_t v___x_123_; 
v___x_121_ = 122;
v___x_122_ = lean_unbox_uint32(v_head_112_);
lean_dec(v_head_112_);
v___x_123_ = lean_uint32_dec_le(v___x_122_, v___x_121_);
if (v___x_123_ == 0)
{
return v_p_103_;
}
else
{
uint32_t v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_string_utf8_get(v_p_103_, v___x_105_);
v___x_125_ = lean_uint32_dec_le(v___x_118_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = lean_string_utf8_set(v_p_103_, v___x_105_, v___x_124_);
return v___x_126_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = lean_uint32_dec_le(v___x_124_, v___x_121_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_string_utf8_set(v_p_103_, v___x_105_, v___x_124_);
return v___x_128_;
}
else
{
uint32_t v___x_129_; uint32_t v___x_130_; lean_object* v___x_131_; 
v___x_129_ = 4294967264;
v___x_130_ = lean_uint32_add(v___x_124_, v___x_129_);
v___x_131_ = lean_string_utf8_set(v_p_103_, v___x_105_, v___x_130_);
return v___x_131_;
}
}
}
}
}
else
{
lean_dec(v_tail_114_);
lean_dec(v_head_112_);
return v_p_103_;
}
}
}
else
{
lean_dec_ref_known(v___x_110_, 2);
lean_dec(v_tail_111_);
return v_p_103_;
}
}
else
{
lean_dec(v___x_110_);
return v_p_103_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(lean_object* v___x_132_, lean_object* v___x_133_, lean_object* v___x_134_, lean_object* v_inst_135_, lean_object* v_R_136_, lean_object* v_a_137_, lean_object* v_b_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_133_, v___x_134_, v_a_137_, v_b_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___boxed(lean_object* v___x_140_, lean_object* v___x_141_, lean_object* v___x_142_, lean_object* v_inst_143_, lean_object* v_R_144_, lean_object* v_a_145_, lean_object* v_b_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(v___x_140_, v___x_141_, v___x_142_, v_inst_143_, v_R_144_, v_a_145_, v_b_146_);
lean_dec(v___x_142_);
lean_dec_ref(v___x_141_);
lean_dec_ref(v___x_140_);
return v_res_147_;
}
}
uint8_t l_List_elem___at___00System_FilePath_normalize_spec__0(uint32_t v_a_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
else
{
lean_object* v_head_151_; lean_object* v_tail_152_; uint32_t v___x_153_; uint8_t v___x_154_; 
v_head_151_ = lean_ctor_get(v_x_149_, 0);
v_tail_152_ = lean_ctor_get(v_x_149_, 1);
v___x_153_ = lean_unbox_uint32(v_head_151_);
v___x_154_ = lean_uint32_dec_eq(v_a_148_, v___x_153_);
if (v___x_154_ == 0)
{
v_x_149_ = v_tail_152_;
goto _start;
}
else
{
return v___x_154_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00System_FilePath_normalize_spec__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_148_ = stack[0].m_num;
lean_object* v_x_149_ = stack[1].m_obj;
uint8_t v_res_156_;
v_res_156_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v_a_148_, v_x_149_);
stack->m_num = v_res_156_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00System_FilePath_normalize_spec__0___boxed(lean_object* v_a_157_, lean_object* v_x_158_){
_start:
{
uint32_t v_a_boxed_159_; uint8_t v_res_160_; lean_object* v_r_161_; 
v_a_boxed_159_ = lean_unbox_uint32(v_a_157_);
lean_dec(v_a_157_);
v_res_160_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v_a_boxed_159_, v_x_158_);
lean_dec(v_x_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00System_FilePath_normalize_spec__1(lean_object* v_s_162_, lean_object* v_p_163_){
_start:
{
uint32_t v___y_165_; lean_object* v___x_170_; uint8_t v_decide_171_; 
v___x_170_ = lean_string_utf8_byte_size(v_s_162_);
v_decide_171_ = lean_nat_dec_eq(v_p_163_, v___x_170_);
if (v_decide_171_ == 0)
{
lean_object* v___x_172_; uint32_t v___x_173_; uint8_t v___x_174_; 
v___x_172_ = l_System_FilePath_pathSeparators;
v___x_173_ = lean_string_utf8_get_fast(v_s_162_, v_p_163_);
v___x_174_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_173_, v___x_172_);
if (v___x_174_ == 0)
{
v___y_165_ = v___x_173_;
goto v___jp_164_;
}
else
{
uint32_t v___x_175_; 
v___x_175_ = l_System_FilePath_pathSeparator;
v___y_165_ = v___x_175_;
goto v___jp_164_;
}
}
else
{
lean_dec(v_p_163_);
return v_s_162_;
}
v___jp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_inc(v_p_163_);
v___x_166_ = lean_string_utf8_set(v_s_162_, v_p_163_, v___y_165_);
v___x_167_ = l_Char_utf8Size(v___y_165_);
v___x_168_ = lean_nat_add(v_p_163_, v___x_167_);
lean_dec(v___x_167_);
lean_dec(v_p_163_);
v_s_162_ = v___x_166_;
v_p_163_ = v___x_168_;
goto _start;
}
}
}
static lean_object* _init_l_System_FilePath_normalize___closed__0(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = l_System_FilePath_pathSeparators;
v___x_177_ = l_List_lengthTR___redArg(v___x_176_);
return v___x_177_;
}
}
static uint8_t _init_l_System_FilePath_normalize___closed__1(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_obj_once(&l_System_FilePath_normalize___closed__0, &l_System_FilePath_normalize___closed__0_once, _init_l_System_FilePath_normalize___closed__0);
v___x_180_ = lean_nat_dec_eq(v___x_179_, v___x_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object* v_p_181_){
_start:
{
lean_object* v_p_182_; uint8_t v___x_183_; 
v_p_182_ = l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(v_p_181_);
v___x_183_ = lean_uint8_once(&l_System_FilePath_normalize___closed__1, &l_System_FilePath_normalize___closed__1_once, _init_l_System_FilePath_normalize___closed__1);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v_p_185_; 
v___x_184_ = lean_unsigned_to_nat(0u);
v_p_185_ = l_String_mapAux___at___00System_FilePath_normalize_spec__1(v_p_182_, v___x_184_);
return v_p_185_;
}
else
{
return v_p_182_;
}
}
}
uint8_t l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1(lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_186_) == 0)
{
if (lean_obj_tag(v_x_187_) == 0)
{
uint8_t v___x_188_; 
v___x_188_ = 1;
return v___x_188_;
}
else
{
uint8_t v___x_189_; 
v___x_189_ = 0;
return v___x_189_;
}
}
else
{
if (lean_obj_tag(v_x_187_) == 0)
{
uint8_t v___x_190_; 
v___x_190_ = 0;
return v___x_190_;
}
else
{
lean_object* v_val_191_; lean_object* v_val_192_; uint32_t v___x_193_; uint32_t v___x_194_; uint8_t v___x_195_; 
v_val_191_ = lean_ctor_get(v_x_186_, 0);
v_val_192_ = lean_ctor_get(v_x_187_, 0);
v___x_193_ = lean_unbox_uint32(v_val_191_);
v___x_194_ = lean_unbox_uint32(v_val_192_);
v___x_195_ = lean_uint32_dec_eq(v___x_193_, v___x_194_);
return v___x_195_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_186_ = stack[0].m_obj;
lean_object* v_x_187_ = stack[1].m_obj;
uint8_t v_res_196_;
v_res_196_ = l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1(v_x_186_, v_x_187_);
stack->m_num = v_res_196_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1___boxed(lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1(v_x_197_, v_x_198_);
lean_dec(v_x_198_);
lean_dec(v_x_197_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(lean_object* v___x_201_, lean_object* v___x_202_, lean_object* v_a_203_, lean_object* v_b_204_){
_start:
{
lean_object* v_str_205_; lean_object* v_startInclusive_206_; lean_object* v_endExclusive_207_; lean_object* v___x_208_; uint8_t v_decide_209_; 
v_str_205_ = lean_ctor_get(v___x_202_, 0);
v_startInclusive_206_ = lean_ctor_get(v___x_202_, 1);
v_endExclusive_207_ = lean_ctor_get(v___x_202_, 2);
v___x_208_ = lean_nat_sub(v_endExclusive_207_, v_startInclusive_206_);
v_decide_209_ = lean_nat_dec_eq(v_a_203_, v___x_208_);
lean_dec(v___x_208_);
if (v_decide_209_ == 0)
{
lean_object* v_zero_210_; uint8_t v_isZero_211_; 
v_zero_210_ = lean_unsigned_to_nat(0u);
v_isZero_211_ = lean_nat_dec_eq(v_b_204_, v_zero_210_);
if (v_isZero_211_ == 1)
{
uint32_t v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v_b_204_);
v___x_212_ = lean_string_utf8_get_fast(v___x_201_, v_a_203_);
lean_dec(v_a_203_);
v___x_213_ = lean_box_uint32(v___x_212_);
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_one_218_; lean_object* v_n_219_; 
v___x_215_ = lean_nat_add(v_startInclusive_206_, v_a_203_);
lean_dec(v_a_203_);
v___x_216_ = lean_string_utf8_next_fast(v_str_205_, v___x_215_);
lean_dec(v___x_215_);
v___x_217_ = lean_nat_sub(v___x_216_, v_startInclusive_206_);
v_one_218_ = lean_unsigned_to_nat(1u);
v_n_219_ = lean_nat_sub(v_b_204_, v_one_218_);
lean_dec(v_b_204_);
v_a_203_ = v___x_217_;
v_b_204_ = v_n_219_;
goto _start;
}
}
else
{
lean_object* v___x_221_; 
lean_dec(v_b_204_);
lean_dec(v_a_203_);
v___x_221_ = lean_box(0);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg___boxed(lean_object* v___x_222_, lean_object* v___x_223_, lean_object* v_a_224_, lean_object* v_b_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_222_, v___x_223_, v_a_224_, v_b_225_);
lean_dec_ref(v___x_223_);
lean_dec_ref(v___x_222_);
return v_res_226_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_227_; lean_object* v___x_228_; 
v___x_227_ = 58;
v___x_228_ = lean_box_uint32(v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
}
uint8_t l_System_FilePath_isAbsolute(lean_object* v_p_231_){
_start:
{
lean_object* v___x_232_; uint32_t v___y_234_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_232_ = l_System_FilePath_pathSeparators;
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_string_utf8_byte_size(v_p_231_);
lean_inc_ref(v_p_231_);
v___x_246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_246_, 0, v_p_231_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
lean_ctor_set(v___x_246_, 2, v___x_245_);
v___x_247_ = l_String_Slice_Pos_get_x3f(v___x_246_, v___x_244_);
lean_dec_ref_known(v___x_246_, 3);
if (lean_obj_tag(v___x_247_) == 0)
{
uint32_t v___x_248_; 
v___x_248_ = 65;
v___y_234_ = v___x_248_;
goto v___jp_233_;
}
else
{
lean_object* v_val_249_; uint32_t v___x_250_; 
v_val_249_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_val_249_);
lean_dec_ref_known(v___x_247_, 1);
v___x_250_ = lean_unbox_uint32(v_val_249_);
lean_dec(v_val_249_);
v___y_234_ = v___x_250_;
goto v___jp_233_;
}
v___jp_233_:
{
uint8_t v___x_235_; 
v___x_235_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_234_, v___x_232_);
if (v___x_235_ == 0)
{
uint8_t v___x_236_; 
v___x_236_ = l_System_Platform_isWindows;
if (v___x_236_ == 0)
{
lean_dec_ref(v_p_231_);
return v___x_236_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_string_utf8_byte_size(v_p_231_);
lean_inc_ref(v_p_231_);
v___x_239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_239_, 0, v_p_231_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
lean_ctor_set(v___x_239_, 2, v___x_238_);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v_p_231_, v___x_239_, v___x_237_, v___x_240_);
lean_dec_ref_known(v___x_239_, 3);
lean_dec_ref(v_p_231_);
v___x_242_ = lean_obj_once(&l_System_FilePath_isAbsolute___closed__0, &l_System_FilePath_isAbsolute___closed__0_once, _init_l_System_FilePath_isAbsolute___closed__0);
v___x_243_ = l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1(v___x_241_, v___x_242_);
lean_dec(v___x_241_);
return v___x_243_;
}
}
else
{
lean_dec_ref(v_p_231_);
return v___x_235_;
}
}
}
}
LEAN_EXPORT void l_System_FilePath_isAbsolute_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_231_ = stack[0].m_obj;
uint8_t v_res_251_;
v_res_251_ = l_System_FilePath_isAbsolute(v_p_231_);
stack->m_num = v_res_251_;
}
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object* v_p_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_System_FilePath_isAbsolute(v_p_252_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(lean_object* v___x_255_, lean_object* v___x_256_, lean_object* v_n_257_, lean_object* v_it_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_256_, v___x_255_, v_it_258_, v_n_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object* v___x_260_, lean_object* v___x_261_, lean_object* v_n_262_, lean_object* v_it_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(v___x_260_, v___x_261_, v_n_262_, v_it_263_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_260_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(lean_object* v___x_265_, lean_object* v___x_266_, lean_object* v_inst_267_, lean_object* v_R_268_, lean_object* v_a_269_, lean_object* v_b_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_265_, v___x_266_, v_a_269_, v_b_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___boxed(lean_object* v___x_272_, lean_object* v___x_273_, lean_object* v_inst_274_, lean_object* v_R_275_, lean_object* v_a_276_, lean_object* v_b_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(v___x_272_, v___x_273_, v_inst_274_, v_R_275_, v_a_276_, v_b_277_);
lean_dec_ref(v___x_273_);
lean_dec_ref(v___x_272_);
return v_res_278_;
}
}
uint8_t l_System_FilePath_isRelative(lean_object* v_p_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = l_System_FilePath_isAbsolute(v_p_279_);
if (v___x_280_ == 0)
{
uint8_t v___x_281_; 
v___x_281_ = 1;
return v___x_281_;
}
else
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
}
}
LEAN_EXPORT void l_System_FilePath_isRelative_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_279_ = stack[0].m_obj;
uint8_t v_res_283_;
v_res_283_ = l_System_FilePath_isRelative(v_p_279_);
stack->m_num = v_res_283_;
}
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object* v_p_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_System_FilePath_isRelative(v_p_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
static lean_object* _init_l_System_FilePath_join___closed__0(void){
_start:
{
uint32_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = l_System_FilePath_pathSeparator;
v___x_288_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_289_ = lean_string_push(v___x_288_, v___x_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object* v_p_290_, lean_object* v_sub_291_){
_start:
{
uint8_t v___x_292_; 
lean_inc_ref(v_sub_291_);
v___x_292_ = l_System_FilePath_isAbsolute(v_sub_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_294_ = lean_string_append(v_p_290_, v___x_293_);
v___x_295_ = lean_string_append(v___x_294_, v_sub_291_);
lean_dec_ref(v_sub_291_);
return v___x_295_;
}
else
{
lean_dec_ref(v_p_290_);
return v_sub_291_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(lean_object* v_s_299_, lean_object* v_a_300_, lean_object* v_b_301_){
_start:
{
lean_object* v___x_302_; uint8_t v_decide_303_; 
v___x_302_ = lean_unsigned_to_nat(0u);
v_decide_303_ = lean_nat_dec_eq(v_a_300_, v___x_302_);
if (v_decide_303_ == 0)
{
lean_object* v_str_304_; lean_object* v_startInclusive_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint32_t v___x_314_; uint8_t v___x_315_; 
v_str_304_ = lean_ctor_get(v_s_299_, 0);
v_startInclusive_305_ = lean_ctor_get(v_s_299_, 1);
v___x_306_ = l_System_FilePath_pathSeparators;
v___x_307_ = lean_nat_add(v_startInclusive_305_, v_a_300_);
lean_inc(v___x_307_);
lean_inc(v_startInclusive_305_);
lean_inc_ref(v_str_304_);
v___x_308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_308_, 0, v_str_304_);
lean_ctor_set(v___x_308_, 1, v_startInclusive_305_);
lean_ctor_set(v___x_308_, 2, v___x_307_);
v___x_309_ = lean_nat_sub(v___x_307_, v_startInclusive_305_);
lean_dec(v___x_307_);
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = lean_nat_sub(v___x_309_, v___x_310_);
lean_dec(v___x_309_);
v___x_312_ = l_String_Slice_posLE(v___x_308_, v___x_311_);
lean_dec_ref_known(v___x_308_, 3);
v___x_313_ = lean_nat_add(v_startInclusive_305_, v___x_312_);
v___x_314_ = lean_string_utf8_get_fast(v_str_304_, v___x_313_);
lean_dec(v___x_313_);
v___x_315_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_314_, v___x_306_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v___x_312_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_nat_sub(v_a_300_, v___x_310_);
lean_dec(v_a_300_);
v___x_318_ = l_String_Slice_posLE(v_s_299_, v___x_317_);
v_a_300_ = v___x_318_;
v_b_301_ = v___x_316_;
goto _start;
}
else
{
lean_object* v___x_320_; 
lean_dec(v_a_300_);
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_312_);
return v___x_320_;
}
}
else
{
lean_dec(v_a_300_);
lean_inc(v_b_301_);
return v_b_301_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg___boxed(lean_object* v_s_321_, lean_object* v_a_322_, lean_object* v_b_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_321_, v_a_322_, v_b_323_);
lean_dec(v_b_323_);
lean_dec_ref(v_s_321_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(lean_object* v_s_325_){
_start:
{
lean_object* v_startInclusive_326_; lean_object* v_endExclusive_327_; lean_object* v_searcher_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_startInclusive_326_ = lean_ctor_get(v_s_325_, 1);
v_endExclusive_327_ = lean_ctor_get(v_s_325_, 2);
v_searcher_328_ = lean_nat_sub(v_endExclusive_327_, v_startInclusive_326_);
v___x_329_ = lean_box(0);
v___x_330_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_325_, v_searcher_328_, v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___boxed(lean_object* v_s_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v_s_331_);
lean_dec_ref(v_s_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object* v_p_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_string_utf8_byte_size(v_p_333_);
v___x_336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_336_, 0, v_p_333_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
lean_ctor_set(v___x_336_, 2, v___x_335_);
v___x_337_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v___x_336_);
lean_dec_ref_known(v___x_336_, 3);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v___x_338_; 
v___x_338_ = lean_box(0);
return v___x_338_;
}
else
{
lean_object* v_val_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
v_val_339_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_337_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_val_339_);
lean_dec(v___x_337_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_val_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(lean_object* v_s_347_, lean_object* v_inst_348_, lean_object* v_R_349_, lean_object* v_a_350_, lean_object* v_b_351_, lean_object* v_c_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_347_, v_a_350_, v_b_351_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___boxed(lean_object* v_s_354_, lean_object* v_inst_355_, lean_object* v_R_356_, lean_object* v_a_357_, lean_object* v_b_358_, lean_object* v_c_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(v_s_354_, v_inst_355_, v_R_356_, v_a_357_, v_b_358_, v_c_359_);
lean_dec(v_b_358_);
lean_dec_ref(v_s_354_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(lean_object* v_p_361_){
_start:
{
lean_object* v___x_362_; uint32_t v___y_364_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_362_ = l_System_FilePath_pathSeparators;
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = lean_string_utf8_byte_size(v_p_361_);
lean_inc_ref(v_p_361_);
v___x_378_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_378_, 0, v_p_361_);
lean_ctor_set(v___x_378_, 1, v___x_376_);
lean_ctor_set(v___x_378_, 2, v___x_377_);
v___x_379_ = l_String_Slice_Pos_get_x3f(v___x_378_, v___x_376_);
lean_dec_ref_known(v___x_378_, 3);
if (lean_obj_tag(v___x_379_) == 0)
{
uint32_t v___x_380_; 
v___x_380_ = 65;
v___y_364_ = v___x_380_;
goto v___jp_363_;
}
else
{
lean_object* v_val_381_; uint32_t v___x_382_; 
v_val_381_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_val_381_);
lean_dec_ref_known(v___x_379_, 1);
v___x_382_ = lean_unbox_uint32(v_val_381_);
lean_dec(v_val_381_);
v___y_364_ = v___x_382_;
goto v___jp_363_;
}
v___jp_363_:
{
uint8_t v___x_365_; 
v___x_365_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_364_, v___x_362_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_unsigned_to_nat(3u);
v___x_368_ = lean_string_utf8_byte_size(v_p_361_);
v___x_369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_369_, 0, v_p_361_);
lean_ctor_set(v___x_369_, 1, v___x_366_);
lean_ctor_set(v___x_369_, 2, v___x_368_);
v___x_370_ = l_String_Slice_Pos_nextn(v___x_369_, v___x_366_, v___x_367_);
lean_dec_ref_known(v___x_369_, 3);
return v___x_370_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = lean_unsigned_to_nat(1u);
v___x_373_ = lean_string_utf8_byte_size(v_p_361_);
v___x_374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_374_, 0, v_p_361_);
lean_ctor_set(v___x_374_, 1, v___x_371_);
lean_ctor_set(v___x_374_, 2, v___x_373_);
v___x_375_ = l_String_Slice_Pos_nextn(v___x_374_, v___x_371_, v___x_372_);
lean_dec_ref_known(v___x_374_, 3);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object* v_p_383_){
_start:
{
lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___x_394_; lean_object* v___y_396_; 
lean_inc_ref(v_p_383_);
v___x_394_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_383_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v___x_416_; 
v___x_416_ = lean_box(0);
v___y_396_ = v___x_416_;
goto v___jp_395_;
}
else
{
lean_object* v_val_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_val_417_ = lean_ctor_get(v___x_394_, 0);
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_string_utf8_extract_fast(v_p_383_, v___x_418_, v_val_417_);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
v___y_396_ = v___x_420_;
goto v___jp_395_;
}
v___jp_384_:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
lean_inc(v___y_386_);
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v___y_386_);
v___x_390_ = l_Option_instDecidableEq___redArg(v___y_387_, v___y_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_dec(v___y_386_);
lean_dec_ref(v_p_383_);
return v___y_385_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec(v___y_385_);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_string_utf8_extract_fast(v_p_383_, v___x_391_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v_p_383_);
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
v___jp_395_:
{
uint8_t v___x_397_; 
lean_inc_ref(v_p_383_);
v___x_397_ = l_System_FilePath_isAbsolute(v_p_383_);
if (v___x_397_ == 0)
{
lean_dec(v___x_394_);
lean_dec_ref(v_p_383_);
return v___y_396_;
}
else
{
lean_object* v_afterRootDirectory_398_; lean_object* v___x_399_; uint8_t v_decide_400_; 
lean_inc_ref(v_p_383_);
v_afterRootDirectory_398_ = l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(v_p_383_);
v___x_399_ = lean_string_utf8_byte_size(v_p_383_);
v_decide_400_ = lean_nat_dec_eq(v_afterRootDirectory_398_, v___x_399_);
if (v_decide_400_ == 0)
{
lean_object* v___x_401_; 
lean_inc_ref(v_p_383_);
v___x_401_ = lean_alloc_closure((void*)(l_String_instDecidableEqPos___boxed), 3, 1);
lean_closure_set(v___x_401_, 0, v_p_383_);
if (lean_obj_tag(v___x_394_) == 0)
{
v___y_385_ = v___y_396_;
v___y_386_ = v_afterRootDirectory_398_;
v___y_387_ = v___x_401_;
v___y_388_ = v___x_394_;
goto v___jp_384_;
}
else
{
lean_object* v_val_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_val_402_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_val_402_);
lean_dec_ref_known(v___x_394_, 1);
v___x_403_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_p_383_);
v___x_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_404_, 0, v_p_383_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
lean_ctor_set(v___x_404_, 2, v___x_399_);
v___x_405_ = l_String_Slice_Pos_next_x3f(v___x_404_, v_val_402_);
lean_dec(v_val_402_);
lean_dec_ref_known(v___x_404_, 3);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v___x_406_; 
v___x_406_ = lean_box(0);
v___y_385_ = v___y_396_;
v___y_386_ = v_afterRootDirectory_398_;
v___y_387_ = v___x_401_;
v___y_388_ = v___x_406_;
goto v___jp_384_;
}
else
{
lean_object* v_val_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_val_407_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_405_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_val_407_);
lean_dec(v___x_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_val_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
v___y_385_ = v___y_396_;
v___y_386_ = v_afterRootDirectory_398_;
v___y_387_ = v___x_401_;
v___y_388_ = v___x_412_;
goto v___jp_384_;
}
}
}
}
}
else
{
lean_object* v___x_415_; 
lean_dec(v_afterRootDirectory_398_);
lean_dec(v___y_396_);
lean_dec(v___x_394_);
lean_dec_ref(v_p_383_);
v___x_415_ = lean_box(0);
return v___x_415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object* v_p_423_){
_start:
{
lean_object* v___y_425_; lean_object* v___x_437_; 
lean_inc_ref(v_p_423_);
v___x_437_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_423_);
if (lean_obj_tag(v___x_437_) == 0)
{
v___y_425_ = v_p_423_;
goto v___jp_424_;
}
else
{
lean_object* v_val_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_val_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_string_utf8_byte_size(v_p_423_);
lean_inc_ref(v_p_423_);
v___x_441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_441_, 0, v_p_423_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
lean_ctor_set(v___x_441_, 2, v___x_440_);
v___x_442_ = l_String_Slice_Pos_next_x21(v___x_441_, v_val_438_);
lean_dec(v_val_438_);
lean_dec_ref_known(v___x_441_, 3);
v___x_443_ = lean_string_utf8_extract_fast(v_p_423_, v___x_442_, v___x_440_);
lean_dec(v___x_442_);
lean_dec_ref(v_p_423_);
v___y_425_ = v___x_443_;
goto v___jp_424_;
}
v___jp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_426_ = lean_string_utf8_byte_size(v___y_425_);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_nat_dec_eq(v___x_426_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_430_ = lean_string_dec_eq(v___y_425_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
v___x_432_ = lean_string_dec_eq(v___y_425_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v___y_425_);
return v___x_433_;
}
else
{
lean_object* v___x_434_; 
lean_dec_ref(v___y_425_);
v___x_434_ = lean_box(0);
return v___x_434_;
}
}
else
{
lean_object* v___x_435_; 
lean_dec_ref(v___y_425_);
v___x_435_ = lean_box(0);
return v___x_435_;
}
}
else
{
lean_object* v___x_436_; 
lean_dec_ref(v___y_425_);
v___x_436_ = lean_box(0);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(lean_object* v_s_444_, lean_object* v_a_445_, lean_object* v_b_446_){
_start:
{
lean_object* v___x_447_; uint8_t v_decide_448_; 
v___x_447_ = lean_unsigned_to_nat(0u);
v_decide_448_ = lean_nat_dec_eq(v_a_445_, v___x_447_);
if (v_decide_448_ == 0)
{
lean_object* v_str_449_; lean_object* v_startInclusive_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint32_t v___x_458_; uint32_t v___x_459_; uint8_t v___x_460_; 
v_str_449_ = lean_ctor_get(v_s_444_, 0);
v_startInclusive_450_ = lean_ctor_get(v_s_444_, 1);
v___x_451_ = lean_nat_add(v_startInclusive_450_, v_a_445_);
lean_inc(v___x_451_);
lean_inc(v_startInclusive_450_);
lean_inc_ref(v_str_449_);
v___x_452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_452_, 0, v_str_449_);
lean_ctor_set(v___x_452_, 1, v_startInclusive_450_);
lean_ctor_set(v___x_452_, 2, v___x_451_);
v___x_453_ = lean_nat_sub(v___x_451_, v_startInclusive_450_);
lean_dec(v___x_451_);
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_sub(v___x_453_, v___x_454_);
lean_dec(v___x_453_);
v___x_456_ = l_String_Slice_posLE(v___x_452_, v___x_455_);
lean_dec_ref_known(v___x_452_, 3);
v___x_457_ = lean_nat_add(v_startInclusive_450_, v___x_456_);
v___x_458_ = lean_string_utf8_get_fast(v_str_449_, v___x_457_);
lean_dec(v___x_457_);
v___x_459_ = 46;
v___x_460_ = lean_uint32_dec_eq(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec(v___x_456_);
v___x_461_ = lean_box(0);
v___x_462_ = lean_nat_sub(v_a_445_, v___x_454_);
lean_dec(v_a_445_);
v___x_463_ = l_String_Slice_posLE(v_s_444_, v___x_462_);
v_a_445_ = v___x_463_;
v_b_446_ = v___x_461_;
goto _start;
}
else
{
lean_object* v___x_465_; 
lean_dec(v_a_445_);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_456_);
return v___x_465_;
}
}
else
{
lean_dec(v_a_445_);
lean_inc(v_b_446_);
return v_b_446_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg___boxed(lean_object* v_s_466_, lean_object* v_a_467_, lean_object* v_b_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_466_, v_a_467_, v_b_468_);
lean_dec(v_b_468_);
lean_dec_ref(v_s_466_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(lean_object* v_s_470_){
_start:
{
lean_object* v_startInclusive_471_; lean_object* v_endExclusive_472_; lean_object* v_searcher_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_startInclusive_471_ = lean_ctor_get(v_s_470_, 1);
v_endExclusive_472_ = lean_ctor_get(v_s_470_, 2);
v_searcher_473_ = lean_nat_sub(v_endExclusive_472_, v_startInclusive_471_);
v___x_474_ = lean_box(0);
v___x_475_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_470_, v_searcher_473_, v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0___boxed(lean_object* v_s_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v_s_476_);
lean_dec_ref(v_s_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object* v_p_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_System_FilePath_fileName(v_p_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
return v___x_479_;
}
else
{
lean_object* v_val_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_val_480_ = lean_ctor_get(v___x_479_, 0);
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = lean_string_utf8_byte_size(v_val_480_);
lean_inc(v_val_480_);
v___x_483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_483_, 0, v_val_480_);
lean_ctor_set(v___x_483_, 1, v___x_481_);
lean_ctor_set(v___x_483_, 2, v___x_482_);
v___x_484_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_483_);
lean_dec_ref_known(v___x_483_, 3);
if (lean_obj_tag(v___x_484_) == 0)
{
return v___x_479_;
}
else
{
lean_object* v_val_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_494_; 
v_val_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_494_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_494_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_val_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_494_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
uint8_t v___x_489_; 
v___x_489_ = lean_nat_dec_eq(v_val_485_, v___x_481_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_492_; 
lean_inc(v_val_480_);
lean_dec_ref_known(v___x_479_, 1);
v___x_490_ = lean_string_utf8_extract(v_val_480_, v___x_481_, v_val_485_);
lean_dec(v_val_485_);
lean_dec(v_val_480_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_490_);
v___x_492_ = v___x_487_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
else
{
lean_del_object(v___x_487_);
lean_dec(v_val_485_);
return v___x_479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(lean_object* v_s_495_, lean_object* v_inst_496_, lean_object* v_R_497_, lean_object* v_a_498_, lean_object* v_b_499_, lean_object* v_c_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_495_, v_a_498_, v_b_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___boxed(lean_object* v_s_502_, lean_object* v_inst_503_, lean_object* v_R_504_, lean_object* v_a_505_, lean_object* v_b_506_, lean_object* v_c_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(v_s_502_, v_inst_503_, v_R_504_, v_a_505_, v_b_506_, v_c_507_);
lean_dec(v_b_506_);
lean_dec_ref(v_s_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object* v_p_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_System_FilePath_fileName(v_p_509_);
if (lean_obj_tag(v___x_510_) == 0)
{
return v___x_510_;
}
else
{
lean_object* v_val_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_val_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc_n(v_val_511_, 2);
lean_dec_ref_known(v___x_510_, 1);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_string_utf8_byte_size(v_val_511_);
v___x_514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_514_, 0, v_val_511_);
lean_ctor_set(v___x_514_, 1, v___x_512_);
lean_ctor_set(v___x_514_, 2, v___x_513_);
v___x_515_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_514_);
lean_dec_ref_known(v___x_514_, 3);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v___x_516_; 
lean_dec(v_val_511_);
v___x_516_ = lean_box(0);
return v___x_516_;
}
else
{
lean_object* v_val_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_529_; 
v_val_517_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_529_ == 0)
{
v___x_519_ = v___x_515_;
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_val_517_);
lean_dec(v___x_515_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
uint8_t v___x_521_; 
v___x_521_ = lean_nat_dec_eq(v_val_517_, v___x_512_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_val_517_, v___x_522_);
lean_dec(v_val_517_);
v___x_524_ = lean_string_utf8_extract(v_val_511_, v___x_523_, v___x_513_);
lean_dec(v___x_523_);
lean_dec(v_val_511_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_524_);
v___x_526_ = v___x_519_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
else
{
lean_object* v___x_528_; 
lean_del_object(v___x_519_);
lean_dec(v_val_517_);
lean_dec(v_val_511_);
v___x_528_ = lean_box(0);
return v___x_528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object* v_p_530_, lean_object* v_fname_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_System_FilePath_parent(v_p_530_);
if (lean_obj_tag(v___x_532_) == 0)
{
return v_fname_531_;
}
else
{
lean_object* v_val_533_; lean_object* v___x_534_; 
v_val_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_val_533_);
lean_dec_ref_known(v___x_532_, 1);
v___x_534_ = l_System_FilePath_join(v_val_533_, v_fname_531_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object* v_p_535_, lean_object* v_ext_536_){
_start:
{
lean_object* v___x_537_; 
lean_inc_ref(v_p_535_);
v___x_537_ = l_System_FilePath_fileName(v_p_535_);
if (lean_obj_tag(v___x_537_) == 0)
{
return v_p_535_;
}
else
{
lean_object* v_val_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_val_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_val_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = lean_string_utf8_byte_size(v_ext_536_);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_nat_dec_eq(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_542_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_543_ = lean_string_append(v_val_538_, v___x_542_);
v___x_544_ = lean_string_append(v___x_543_, v_ext_536_);
v___x_545_ = l_System_FilePath_withFileName(v_p_535_, v___x_544_);
return v___x_545_;
}
else
{
lean_object* v___x_546_; 
v___x_546_ = l_System_FilePath_withFileName(v_p_535_, v_val_538_);
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object* v_p_547_, lean_object* v_ext_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_System_FilePath_addExtension(v_p_547_, v_ext_548_);
lean_dec_ref(v_ext_548_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object* v_p_550_, lean_object* v_ext_551_){
_start:
{
lean_object* v___x_552_; 
lean_inc_ref(v_p_550_);
v___x_552_ = l_System_FilePath_fileStem(v_p_550_);
if (lean_obj_tag(v___x_552_) == 0)
{
return v_p_550_;
}
else
{
lean_object* v_val_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_val_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_val_553_);
lean_dec_ref_known(v___x_552_, 1);
v___x_554_ = lean_string_utf8_byte_size(v_ext_551_);
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = lean_nat_dec_eq(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_557_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_558_ = lean_string_append(v_val_553_, v___x_557_);
v___x_559_ = lean_string_append(v___x_558_, v_ext_551_);
v___x_560_ = l_System_FilePath_withFileName(v_p_550_, v___x_559_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = l_System_FilePath_withFileName(v_p_550_, v_val_553_);
return v___x_561_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object* v_p_562_, lean_object* v_ext_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_System_FilePath_withExtension(v_p_562_, v_ext_563_);
lean_dec_ref(v_ext_563_);
return v_res_564_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_566_ = lean_string_utf8_byte_size(v___x_565_);
return v___x_566_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0);
v___x_569_ = lean_nat_dec_eq(v___x_568_, v___x_567_);
return v___x_569_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_570_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0);
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_571_);
lean_ctor_set(v___x_573_, 2, v___x_570_);
return v___x_573_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2);
v___x_575_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3);
v___x_578_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2);
v___x_579_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v___x_577_);
lean_ctor_set(v___x_579_, 2, v___x_576_);
lean_ctor_set(v___x_579_, 3, v___x_576_);
return v___x_579_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v___x_580_);
return v___x_582_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg(){
_start:
{
uint8_t v___x_589_; 
v___x_589_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5);
return v___x_590_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__7));
return v___x_591_;
}
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_592_;
v_res_592_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg();
stack->m_obj
 = v_res_592_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___boxed(lean_object* v___dummy_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg();
return v_res_594_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0(void){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg();
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(lean_object* v_s_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(lean_object* v_s_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v_s_598_);
lean_dec_ref(v_s_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object* v___x_600_, lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v_a_603_, lean_object* v_b_604_){
_start:
{
lean_object* v_it_606_; lean_object* v_startInclusive_607_; lean_object* v_endExclusive_608_; 
if (lean_obj_tag(v_a_603_) == 0)
{
lean_object* v_currPos_613_; lean_object* v_searcher_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_720_; 
v_currPos_613_ = lean_ctor_get(v_a_603_, 0);
v_searcher_614_ = lean_ctor_get(v_a_603_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_a_603_);
if (v_isSharedCheck_720_ == 0)
{
v___x_616_ = v_a_603_;
v_isShared_617_ = v_isSharedCheck_720_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_searcher_614_);
lean_inc(v_currPos_613_);
lean_dec(v_a_603_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_720_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v_it_619_; lean_object* v_it_625_; lean_object* v_startPos_626_; lean_object* v_endPos_627_; 
switch(lean_obj_tag(v_searcher_614_))
{
case 0:
{
lean_object* v_pos_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_652_; 
lean_del_object(v___x_616_);
v_pos_640_ = lean_ctor_get(v_searcher_614_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v_searcher_614_);
if (v_isSharedCheck_652_ == 0)
{
v___x_642_ = v_searcher_614_;
v_isShared_643_ = v_isSharedCheck_652_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_pos_640_);
lean_dec(v_searcher_614_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_652_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_startInclusive_644_; lean_object* v_endExclusive_645_; lean_object* v___x_646_; uint8_t v_decide_647_; 
v_startInclusive_644_ = lean_ctor_get(v___x_601_, 1);
v_endExclusive_645_ = lean_ctor_get(v___x_601_, 2);
v___x_646_ = lean_nat_sub(v_endExclusive_645_, v_startInclusive_644_);
v_decide_647_ = lean_nat_dec_eq(v_pos_640_, v___x_646_);
lean_dec(v___x_646_);
if (v_decide_647_ == 0)
{
lean_object* v___x_649_; 
lean_inc(v_pos_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 1);
v___x_649_ = v___x_642_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_pos_640_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_inc(v_pos_640_);
v_it_625_ = v___x_649_;
v_startPos_626_ = v_pos_640_;
v_endPos_627_ = v_pos_640_;
goto v___jp_624_;
}
}
else
{
lean_object* v___x_651_; 
lean_del_object(v___x_642_);
v___x_651_ = lean_box(3);
lean_inc(v_pos_640_);
v_it_625_ = v___x_651_;
v_startPos_626_ = v_pos_640_;
v_endPos_627_ = v_pos_640_;
goto v___jp_624_;
}
}
}
case 1:
{
lean_object* v_pos_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_661_; 
v_pos_653_ = lean_ctor_get(v_searcher_614_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v_searcher_614_);
if (v_isSharedCheck_661_ == 0)
{
v___x_655_ = v_searcher_614_;
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_pos_653_);
lean_dec(v_searcher_614_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = lean_string_utf8_next_fast(v___x_600_, v_pos_653_);
lean_dec(v_pos_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set_tag(v___x_655_, 0);
lean_ctor_set(v___x_655_, 0, v___x_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
v_it_619_ = v___x_659_;
goto v___jp_618_;
}
}
}
case 2:
{
lean_object* v_needle_662_; lean_object* v_table_663_; lean_object* v_stackPos_664_; lean_object* v_needlePos_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_719_; 
v_needle_662_ = lean_ctor_get(v_searcher_614_, 0);
v_table_663_ = lean_ctor_get(v_searcher_614_, 1);
v_stackPos_664_ = lean_ctor_get(v_searcher_614_, 2);
v_needlePos_665_ = lean_ctor_get(v_searcher_614_, 3);
v_isSharedCheck_719_ = !lean_is_exclusive(v_searcher_614_);
if (v_isSharedCheck_719_ == 0)
{
v___x_667_ = v_searcher_614_;
v_isShared_668_ = v_isSharedCheck_719_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_needlePos_665_);
lean_inc(v_stackPos_664_);
lean_inc(v_table_663_);
lean_inc(v_needle_662_);
lean_dec(v_searcher_614_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_719_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_str_669_; lean_object* v_startInclusive_670_; lean_object* v_endExclusive_671_; lean_object* v_basePos_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_str_669_ = lean_ctor_get(v_needle_662_, 0);
v_startInclusive_670_ = lean_ctor_get(v_needle_662_, 1);
v_endExclusive_671_ = lean_ctor_get(v_needle_662_, 2);
v_basePos_672_ = lean_nat_sub(v_stackPos_664_, v_needlePos_665_);
v___x_673_ = lean_nat_sub(v_endExclusive_671_, v_startInclusive_670_);
v___x_674_ = lean_nat_add(v_basePos_672_, v___x_673_);
v___x_675_ = lean_nat_dec_le(v___x_674_, v___x_602_);
lean_dec(v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
lean_dec(v___x_673_);
lean_del_object(v___x_667_);
lean_dec(v_needlePos_665_);
lean_dec(v_stackPos_664_);
lean_dec_ref(v_table_663_);
lean_dec_ref(v_needle_662_);
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_add(v_basePos_672_, v___x_676_);
lean_dec(v_basePos_672_);
v___x_678_ = lean_nat_dec_le(v___x_677_, v___x_602_);
lean_dec(v___x_677_);
if (v___x_678_ == 0)
{
lean_del_object(v___x_616_);
goto v___jp_638_;
}
else
{
lean_object* v___x_679_; 
v___x_679_ = lean_box(3);
v_it_619_ = v___x_679_;
goto v___jp_618_;
}
}
else
{
uint8_t v_stackByte_680_; lean_object* v___x_681_; uint8_t v_patByte_682_; uint8_t v___x_683_; 
lean_dec(v_basePos_672_);
lean_inc(v_stackPos_664_);
v_stackByte_680_ = lean_string_get_byte_fast(v___x_600_, v_stackPos_664_);
v___x_681_ = lean_nat_add(v_startInclusive_670_, v_needlePos_665_);
v_patByte_682_ = lean_string_get_byte_fast(v_str_669_, v___x_681_);
v___x_683_ = lean_uint8_dec_eq(v_stackByte_680_, v_patByte_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; uint8_t v_decide_685_; 
lean_dec(v___x_673_);
v___x_684_ = lean_unsigned_to_nat(0u);
v_decide_685_ = lean_nat_dec_eq(v_needlePos_665_, v___x_684_);
if (v_decide_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_newNeedlePos_688_; uint8_t v___x_689_; 
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_nat_sub(v_needlePos_665_, v___x_686_);
lean_dec(v_needlePos_665_);
v_newNeedlePos_688_ = lean_array_fget_borrowed(v_table_663_, v___x_687_);
lean_dec(v___x_687_);
v___x_689_ = lean_nat_dec_eq(v_newNeedlePos_688_, v___x_684_);
if (v___x_689_ == 0)
{
lean_object* v___x_691_; 
lean_inc(v_newNeedlePos_688_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 3, v_newNeedlePos_688_);
v___x_691_ = v___x_667_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_needle_662_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_table_663_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_stackPos_664_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_newNeedlePos_688_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v_it_619_ = v___x_691_;
goto v___jp_618_;
}
}
else
{
lean_object* v_nextStackPos_693_; lean_object* v___x_695_; 
v_nextStackPos_693_ = l_String_Slice_posGE___redArg(v___x_601_, v_stackPos_664_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 3, v___x_684_);
lean_ctor_set(v___x_667_, 2, v_nextStackPos_693_);
v___x_695_ = v___x_667_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_needle_662_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_table_663_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_nextStackPos_693_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v___x_684_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
v_it_619_ = v___x_695_;
goto v___jp_618_;
}
}
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v_nextStackPos_699_; lean_object* v___x_701_; 
lean_dec(v_needlePos_665_);
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = lean_nat_add(v_stackPos_664_, v___x_697_);
lean_dec(v_stackPos_664_);
v_nextStackPos_699_ = l_String_Slice_posGE___redArg(v___x_601_, v___x_698_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 3, v___x_684_);
lean_ctor_set(v___x_667_, 2, v_nextStackPos_699_);
v___x_701_ = v___x_667_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_needle_662_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_table_663_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_nextStackPos_699_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v___x_684_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
v_it_619_ = v___x_701_;
goto v___jp_618_;
}
}
}
else
{
lean_object* v___x_703_; lean_object* v_nextStackPos_704_; lean_object* v_nextNeedlePos_705_; uint8_t v_decide_706_; 
lean_del_object(v___x_616_);
v___x_703_ = lean_unsigned_to_nat(1u);
v_nextStackPos_704_ = lean_nat_add(v_stackPos_664_, v___x_703_);
lean_dec(v_stackPos_664_);
v_nextNeedlePos_705_ = lean_nat_add(v_needlePos_665_, v___x_703_);
lean_dec(v_needlePos_665_);
v_decide_706_ = lean_nat_dec_eq(v_nextNeedlePos_705_, v___x_673_);
lean_dec(v___x_673_);
if (v_decide_706_ == 0)
{
lean_object* v___x_708_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 3, v_nextNeedlePos_705_);
lean_ctor_set(v___x_667_, 2, v_nextStackPos_704_);
v___x_708_ = v___x_667_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_needle_662_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_table_663_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_nextStackPos_704_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v_nextNeedlePos_705_);
v___x_708_ = v_reuseFailAlloc_711_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; 
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v_currPos_613_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v_a_603_ = v___x_709_;
goto _start;
}
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_712_ = lean_nat_sub(v_nextStackPos_704_, v_nextNeedlePos_705_);
lean_dec(v_nextNeedlePos_705_);
v___x_713_ = l_String_Slice_pos_x21(v___x_601_, v___x_712_);
lean_dec(v___x_712_);
v___x_714_ = l_String_Slice_pos_x21(v___x_601_, v_nextStackPos_704_);
v___x_715_ = lean_unsigned_to_nat(0u);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 3, v___x_715_);
lean_ctor_set(v___x_667_, 2, v_nextStackPos_704_);
v___x_717_ = v___x_667_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_needle_662_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_table_663_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_nextStackPos_704_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
v_it_625_ = v___x_717_;
v_startPos_626_ = v___x_713_;
v_endPos_627_ = v___x_714_;
goto v___jp_624_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_616_);
goto v___jp_638_;
}
}
v___jp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v_it_619_);
v___x_621_ = v___x_616_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_currPos_613_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_it_619_);
v___x_621_ = v_reuseFailAlloc_623_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
v_a_603_ = v___x_621_;
goto _start;
}
}
v___jp_624_:
{
lean_object* v_slice_628_; lean_object* v_startInclusive_629_; lean_object* v_endExclusive_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
v_slice_628_ = l_String_Slice_subslice_x21(v___x_601_, v_currPos_613_, v_startPos_626_);
v_startInclusive_629_ = lean_ctor_get(v_slice_628_, 0);
v_endExclusive_630_ = lean_ctor_get(v_slice_628_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v_slice_628_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v_slice_628_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_endExclusive_630_);
lean_inc(v_startInclusive_629_);
lean_dec(v_slice_628_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_nextIt_635_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 1, v_it_625_);
lean_ctor_set(v___x_632_, 0, v_endPos_627_);
v_nextIt_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_endPos_627_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_it_625_);
v_nextIt_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
v_it_606_ = v_nextIt_635_;
v_startInclusive_607_ = v_startInclusive_629_;
v_endExclusive_608_ = v_endExclusive_630_;
goto v___jp_605_;
}
}
}
v___jp_638_:
{
lean_object* v___x_639_; 
v___x_639_ = lean_box(1);
lean_inc(v___x_602_);
v_it_606_ = v___x_639_;
v_startInclusive_607_ = v_currPos_613_;
v_endExclusive_608_ = v___x_602_;
goto v___jp_605_;
}
}
}
else
{
lean_dec(v___x_602_);
lean_dec_ref(v___x_600_);
return v_b_604_;
}
v___jp_605_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
lean_inc_ref(v___x_600_);
v___x_609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_609_, 0, v___x_600_);
lean_ctor_set(v___x_609_, 1, v_startInclusive_607_);
lean_ctor_set(v___x_609_, 2, v_endExclusive_608_);
v___x_610_ = l_String_Slice_toString(v___x_609_);
lean_dec_ref_known(v___x_609_, 3);
v___x_611_ = lean_array_push(v_b_604_, v___x_610_);
v_a_603_ = v_it_606_;
v_b_604_ = v___x_611_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object* v___x_721_, lean_object* v___x_722_, lean_object* v___x_723_, lean_object* v_a_724_, lean_object* v_b_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_721_, v___x_722_, v___x_723_, v_a_724_, v_b_725_);
lean_dec_ref(v___x_722_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object* v_p_729_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_730_ = l_System_FilePath_normalize(v_p_729_);
v___x_731_ = lean_unsigned_to_nat(0u);
v___x_732_ = lean_string_utf8_byte_size(v___x_730_);
lean_inc_ref(v___x_730_);
v___x_733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_733_, 0, v___x_730_);
lean_ctor_set(v___x_733_, 1, v___x_731_);
lean_ctor_set(v___x_733_, 2, v___x_732_);
v___x_734_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
v___x_735_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_736_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_730_, v___x_733_, v___x_732_, v___x_734_, v___x_735_);
lean_dec_ref_known(v___x_733_, 3);
v___x_737_ = lean_array_to_list(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object* v___x_738_, lean_object* v___x_739_, lean_object* v___x_740_, lean_object* v_inst_741_, lean_object* v_R_742_, lean_object* v_a_743_, lean_object* v_b_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_738_, v___x_739_, v___x_740_, v_a_743_, v_b_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object* v___x_746_, lean_object* v___x_747_, lean_object* v___x_748_, lean_object* v_inst_749_, lean_object* v_R_750_, lean_object* v_a_751_, lean_object* v_b_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(v___x_746_, v___x_747_, v___x_748_, v_inst_749_, v_R_750_, v_a_751_, v_b_752_);
lean_dec_ref(v___x_747_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object* v_parts_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_756_ = l_String_intercalate(v___x_755_, v_parts_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object* v_toString_757_){
_start:
{
lean_inc_ref(v_toString_757_);
return v_toString_757_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object* v_toString_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_System_instCoeStringFilePath___lam__0(v_toString_758_);
lean_dec_ref(v_toString_758_);
return v_res_759_;
}
}
static uint32_t _init_l_System_SearchPath_separator(void){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = l_System_Platform_isWindows;
if (v___x_762_ == 0)
{
uint32_t v___x_763_; 
v___x_763_ = 58;
return v___x_763_;
}
else
{
uint32_t v___x_764_; 
v___x_764_ = 59;
return v___x_764_;
}
}
}
lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___closed__0));
return v___x_768_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_769_;
v_res_769_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg();
stack->m_obj
 = v_res_769_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___boxed(lean_object* v___dummy_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg();
return v_res_771_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0(void){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg();
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(lean_object* v_s_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___boxed(lean_object* v_s_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v_s_775_);
lean_dec_ref(v_s_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(lean_object* v_s_777_, lean_object* v___x_778_, lean_object* v___x_779_, lean_object* v_a_780_, lean_object* v_b_781_){
_start:
{
lean_object* v_it_783_; lean_object* v_startInclusive_784_; lean_object* v_endExclusive_785_; 
if (lean_obj_tag(v_a_780_) == 0)
{
lean_object* v_currPos_789_; lean_object* v_searcher_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_813_; 
v_currPos_789_ = lean_ctor_get(v_a_780_, 0);
v_searcher_790_ = lean_ctor_get(v_a_780_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_a_780_);
if (v_isSharedCheck_813_ == 0)
{
v___x_792_ = v_a_780_;
v_isShared_793_ = v_isSharedCheck_813_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_searcher_790_);
lean_inc(v_currPos_789_);
lean_dec(v_a_780_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_813_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
uint8_t v_decide_794_; 
v_decide_794_ = lean_nat_dec_eq(v_searcher_790_, v___x_779_);
if (v_decide_794_ == 0)
{
uint32_t v___x_795_; uint32_t v___x_796_; uint8_t v___x_797_; 
v___x_795_ = l_System_SearchPath_separator;
v___x_796_ = lean_string_utf8_get_fast(v_s_777_, v_searcher_790_);
v___x_797_ = lean_uint32_dec_eq(v___x_796_, v___x_795_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_string_utf8_next_fast(v_s_777_, v_searcher_790_);
lean_dec(v_searcher_790_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v___x_798_);
v___x_800_ = v___x_792_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_currPos_789_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_802_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
v_a_780_ = v___x_800_;
goto _start;
}
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v_slice_806_; lean_object* v_nextIt_808_; 
v___x_803_ = lean_string_utf8_next_fast(v_s_777_, v_searcher_790_);
v___x_804_ = lean_nat_sub(v___x_803_, v_searcher_790_);
v___x_805_ = lean_nat_add(v_searcher_790_, v___x_804_);
lean_dec(v___x_804_);
v_slice_806_ = l_String_Slice_subslice_x21(v___x_778_, v_currPos_789_, v_searcher_790_);
lean_inc(v___x_805_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v___x_805_);
lean_ctor_set(v___x_792_, 0, v___x_805_);
v_nextIt_808_ = v___x_792_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_805_);
v_nextIt_808_ = v_reuseFailAlloc_811_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v_startInclusive_809_; lean_object* v_endExclusive_810_; 
v_startInclusive_809_ = lean_ctor_get(v_slice_806_, 0);
lean_inc(v_startInclusive_809_);
v_endExclusive_810_ = lean_ctor_get(v_slice_806_, 1);
lean_inc(v_endExclusive_810_);
lean_dec_ref(v_slice_806_);
v_it_783_ = v_nextIt_808_;
v_startInclusive_784_ = v_startInclusive_809_;
v_endExclusive_785_ = v_endExclusive_810_;
goto v___jp_782_;
}
}
}
else
{
lean_object* v___x_812_; 
lean_del_object(v___x_792_);
lean_dec(v_searcher_790_);
v___x_812_ = lean_box(1);
lean_inc(v___x_779_);
v_it_783_ = v___x_812_;
v_startInclusive_784_ = v_currPos_789_;
v_endExclusive_785_ = v___x_779_;
goto v___jp_782_;
}
}
}
else
{
lean_dec(v___x_779_);
return v_b_781_;
}
v___jp_782_:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_string_utf8_extract_fast(v_s_777_, v_startInclusive_784_, v_endExclusive_785_);
lean_dec(v_endExclusive_785_);
lean_dec(v_startInclusive_784_);
v___x_787_ = lean_array_push(v_b_781_, v___x_786_);
v_a_780_ = v_it_783_;
v_b_781_ = v___x_787_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg___boxed(lean_object* v_s_814_, lean_object* v___x_815_, lean_object* v___x_816_, lean_object* v_a_817_, lean_object* v_b_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_814_, v___x_815_, v___x_816_, v_a_817_, v_b_818_);
lean_dec_ref(v___x_815_);
lean_dec_ref(v_s_814_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object* v_s_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_string_utf8_byte_size(v_s_820_);
lean_inc_ref(v_s_820_);
v___x_823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_823_, 0, v_s_820_);
lean_ctor_set(v___x_823_, 1, v___x_821_);
lean_ctor_set(v___x_823_, 2, v___x_822_);
v___x_824_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0);
v___x_825_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_826_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_820_, v___x_823_, v___x_822_, v___x_824_, v___x_825_);
lean_dec_ref_known(v___x_823_, 3);
lean_dec_ref(v_s_820_);
v___x_827_ = lean_array_to_list(v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(lean_object* v_s_828_, lean_object* v___x_829_, lean_object* v___x_830_, lean_object* v_inst_831_, lean_object* v_R_832_, lean_object* v_a_833_, lean_object* v_b_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_828_, v___x_829_, v___x_830_, v_a_833_, v_b_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___boxed(lean_object* v_s_836_, lean_object* v___x_837_, lean_object* v___x_838_, lean_object* v_inst_839_, lean_object* v_R_840_, lean_object* v_a_841_, lean_object* v_b_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(v_s_836_, v___x_837_, v___x_838_, v_inst_839_, v_R_840_, v_a_841_, v_b_842_);
lean_dec_ref(v___x_837_);
lean_dec_ref(v_s_836_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
if (lean_obj_tag(v_a_844_) == 0)
{
lean_object* v___x_846_; 
v___x_846_ = l_List_reverse___redArg(v_a_845_);
return v___x_846_;
}
else
{
lean_object* v_head_847_; lean_object* v_tail_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_856_; 
v_head_847_ = lean_ctor_get(v_a_844_, 0);
v_tail_848_ = lean_ctor_get(v_a_844_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v_a_844_);
if (v_isSharedCheck_856_ == 0)
{
v___x_850_ = v_a_844_;
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_tail_848_);
lean_inc(v_head_847_);
lean_dec(v_a_844_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v_a_845_);
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_head_847_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_a_845_);
v___x_853_ = v_reuseFailAlloc_855_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
v_a_844_ = v_tail_848_;
v_a_845_ = v___x_853_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_System_SearchPath_toString___closed__0(void){
_start:
{
uint32_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_857_ = l_System_SearchPath_separator;
v___x_858_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_859_ = lean_string_push(v___x_858_, v___x_857_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object* v_path_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_861_ = lean_obj_once(&l_System_SearchPath_toString___closed__0, &l_System_SearchPath_toString___closed__0_once, _init_l_System_SearchPath_toString___closed__0);
v___x_862_ = lean_box(0);
v___x_863_ = l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(v_path_860_, v___x_862_);
v___x_864_ = l_String_intercalate(v___x_861_, v___x_863_);
return v___x_864_;
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
