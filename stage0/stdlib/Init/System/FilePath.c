// Lean compiler output
// Module: Init.System.FilePath
// Imports: import Init.Data.String.Modify import Init.Data.String.Search import Init.Data.String.Iterate public import Init.Data.ToString.Basic import Init.Data.Iterators.Consumers.Collect import Init.System.Platform import Init.Data.String.Length import Init.Data.Iterators.Combinators.Take import Init.Data.Iterators.Consumers.Access
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
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
lean_object* v___y_161_; lean_object* v___y_162_; uint32_t v___y_166_; lean_object* v___x_178_; uint8_t v_decide_179_; 
v___x_178_ = lean_string_utf8_byte_size(v_s_158_);
v_decide_179_ = lean_nat_dec_eq(v_p_159_, v___x_178_);
if (v_decide_179_ == 0)
{
lean_object* v___x_180_; uint32_t v___x_181_; uint8_t v___x_182_; 
v___x_180_ = l_System_FilePath_pathSeparators;
v___x_181_ = lean_string_utf8_get_fast(v_s_158_, v_p_159_);
v___x_182_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_181_, v___x_180_);
if (v___x_182_ == 0)
{
v___y_166_ = v___x_181_;
goto v___jp_165_;
}
else
{
uint32_t v___x_183_; 
v___x_183_ = l_System_FilePath_pathSeparator;
v___y_166_ = v___x_183_;
goto v___jp_165_;
}
}
else
{
lean_dec(v_p_159_);
return v_s_158_;
}
v___jp_160_:
{
lean_object* v___x_163_; 
v___x_163_ = lean_nat_add(v_p_159_, v___y_162_);
lean_dec(v_p_159_);
v_s_158_ = v___y_161_;
v_p_159_ = v___x_163_;
goto _start;
}
v___jp_165_:
{
lean_object* v___x_167_; uint32_t v___x_168_; uint8_t v___x_169_; 
lean_inc(v_p_159_);
v___x_167_ = lean_string_utf8_set(v_s_158_, v_p_159_, v___y_166_);
v___x_168_ = 127;
v___x_169_ = lean_uint32_dec_le(v___y_166_, v___x_168_);
if (v___x_169_ == 0)
{
uint32_t v___x_170_; uint8_t v___x_171_; 
v___x_170_ = 2047;
v___x_171_ = lean_uint32_dec_le(v___y_166_, v___x_170_);
if (v___x_171_ == 0)
{
uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_172_ = 65535;
v___x_173_ = lean_uint32_dec_le(v___y_166_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_unsigned_to_nat(4u);
v___y_161_ = v___x_167_;
v___y_162_ = v___x_174_;
goto v___jp_160_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = lean_unsigned_to_nat(3u);
v___y_161_ = v___x_167_;
v___y_162_ = v___x_175_;
goto v___jp_160_;
}
}
else
{
lean_object* v___x_176_; 
v___x_176_ = lean_unsigned_to_nat(2u);
v___y_161_ = v___x_167_;
v___y_162_ = v___x_176_;
goto v___jp_160_;
}
}
else
{
lean_object* v___x_177_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v___y_161_ = v___x_167_;
v___y_162_ = v___x_177_;
goto v___jp_160_;
}
}
}
}
static lean_object* _init_l_System_FilePath_normalize___closed__0(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = l_System_FilePath_pathSeparators;
v___x_185_ = l_List_lengthTR___redArg(v___x_184_);
return v___x_185_;
}
}
static uint8_t _init_l_System_FilePath_normalize___closed__1(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_obj_once(&l_System_FilePath_normalize___closed__0, &l_System_FilePath_normalize___closed__0_once, _init_l_System_FilePath_normalize___closed__0);
v___x_188_ = lean_nat_dec_eq(v___x_187_, v___x_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object* v_p_189_){
_start:
{
lean_object* v_p_190_; uint8_t v___x_191_; 
v_p_190_ = l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(v_p_189_);
v___x_191_ = lean_uint8_once(&l_System_FilePath_normalize___closed__1, &l_System_FilePath_normalize___closed__1_once, _init_l_System_FilePath_normalize___closed__1);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v_p_193_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v_p_193_ = l_String_mapAux___at___00System_FilePath_normalize_spec__1(v_p_190_, v___x_192_);
return v_p_193_;
}
else
{
return v_p_190_;
}
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1(lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
if (lean_obj_tag(v_x_194_) == 0)
{
if (lean_obj_tag(v_x_195_) == 0)
{
uint8_t v___x_196_; 
v___x_196_ = 1;
return v___x_196_;
}
else
{
uint8_t v___x_197_; 
v___x_197_ = 0;
return v___x_197_;
}
}
else
{
if (lean_obj_tag(v_x_195_) == 0)
{
uint8_t v___x_198_; 
v___x_198_ = 0;
return v___x_198_;
}
else
{
lean_object* v_val_199_; lean_object* v_val_200_; uint32_t v___x_201_; uint32_t v___x_202_; uint8_t v___x_203_; 
v_val_199_ = lean_ctor_get(v_x_194_, 0);
v_val_200_ = lean_ctor_get(v_x_195_, 0);
v___x_201_ = lean_unbox_uint32(v_val_199_);
v___x_202_ = lean_unbox_uint32(v_val_200_);
v___x_203_ = lean_uint32_dec_eq(v___x_201_, v___x_202_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1___boxed(lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1(v_x_204_, v_x_205_);
lean_dec(v_x_205_);
lean_dec(v_x_204_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(lean_object* v___x_208_, lean_object* v___x_209_, lean_object* v_a_210_, lean_object* v_b_211_){
_start:
{
lean_object* v_str_212_; lean_object* v_startInclusive_213_; lean_object* v_endExclusive_214_; lean_object* v___x_215_; uint8_t v_decide_216_; 
v_str_212_ = lean_ctor_get(v___x_209_, 0);
v_startInclusive_213_ = lean_ctor_get(v___x_209_, 1);
v_endExclusive_214_ = lean_ctor_get(v___x_209_, 2);
v___x_215_ = lean_nat_sub(v_endExclusive_214_, v_startInclusive_213_);
v_decide_216_ = lean_nat_dec_eq(v_a_210_, v___x_215_);
lean_dec(v___x_215_);
if (v_decide_216_ == 0)
{
lean_object* v_zero_217_; uint8_t v_isZero_218_; 
v_zero_217_ = lean_unsigned_to_nat(0u);
v_isZero_218_ = lean_nat_dec_eq(v_b_211_, v_zero_217_);
if (v_isZero_218_ == 1)
{
uint32_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v_b_211_);
v___x_219_ = lean_string_utf8_get_fast(v___x_208_, v_a_210_);
lean_dec(v_a_210_);
v___x_220_ = lean_box_uint32(v___x_219_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v_one_225_; lean_object* v_n_226_; 
v___x_222_ = lean_nat_add(v_startInclusive_213_, v_a_210_);
lean_dec(v_a_210_);
v___x_223_ = lean_string_utf8_next_fast(v_str_212_, v___x_222_);
lean_dec(v___x_222_);
v___x_224_ = lean_nat_sub(v___x_223_, v_startInclusive_213_);
v_one_225_ = lean_unsigned_to_nat(1u);
v_n_226_ = lean_nat_sub(v_b_211_, v_one_225_);
lean_dec(v_b_211_);
v_a_210_ = v___x_224_;
v_b_211_ = v_n_226_;
goto _start;
}
}
else
{
lean_object* v___x_228_; 
lean_dec(v_b_211_);
lean_dec(v_a_210_);
v___x_228_ = lean_box(0);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg___boxed(lean_object* v___x_229_, lean_object* v___x_230_, lean_object* v_a_231_, lean_object* v_b_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_229_, v___x_230_, v_a_231_, v_b_232_);
lean_dec_ref(v___x_230_);
lean_dec_ref(v___x_229_);
return v_res_233_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_234_; lean_object* v___x_235_; 
v___x_234_ = 58;
v___x_235_ = lean_box_uint32(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_System_FilePath_isAbsolute___closed__0(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object* v_p_238_){
_start:
{
lean_object* v___x_239_; uint32_t v___y_241_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_239_ = l_System_FilePath_pathSeparators;
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_string_utf8_byte_size(v_p_238_);
lean_inc_ref(v_p_238_);
v___x_253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_253_, 0, v_p_238_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
lean_ctor_set(v___x_253_, 2, v___x_252_);
v___x_254_ = l_String_Slice_Pos_get_x3f(v___x_253_, v___x_251_);
lean_dec_ref_known(v___x_253_, 3);
if (lean_obj_tag(v___x_254_) == 0)
{
uint32_t v___x_255_; 
v___x_255_ = 65;
v___y_241_ = v___x_255_;
goto v___jp_240_;
}
else
{
lean_object* v_val_256_; uint32_t v___x_257_; 
v_val_256_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_val_256_);
lean_dec_ref_known(v___x_254_, 1);
v___x_257_ = lean_unbox_uint32(v_val_256_);
lean_dec(v_val_256_);
v___y_241_ = v___x_257_;
goto v___jp_240_;
}
v___jp_240_:
{
uint8_t v___x_242_; 
v___x_242_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_241_, v___x_239_);
if (v___x_242_ == 0)
{
uint8_t v___x_243_; 
v___x_243_ = l_System_Platform_isWindows;
if (v___x_243_ == 0)
{
lean_dec_ref(v_p_238_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_string_utf8_byte_size(v_p_238_);
lean_inc_ref(v_p_238_);
v___x_246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_246_, 0, v_p_238_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
lean_ctor_set(v___x_246_, 2, v___x_245_);
v___x_247_ = lean_unsigned_to_nat(1u);
v___x_248_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v_p_238_, v___x_246_, v___x_244_, v___x_247_);
lean_dec_ref_known(v___x_246_, 3);
lean_dec_ref(v_p_238_);
v___x_249_ = lean_obj_once(&l_System_FilePath_isAbsolute___closed__0, &l_System_FilePath_isAbsolute___closed__0_once, _init_l_System_FilePath_isAbsolute___closed__0);
v___x_250_ = l_instBEqOption_beq___at___00System_FilePath_isAbsolute_spec__1(v___x_248_, v___x_249_);
lean_dec(v___x_248_);
return v___x_250_;
}
}
else
{
lean_dec_ref(v_p_238_);
return v___x_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object* v_p_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_System_FilePath_isAbsolute(v_p_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(lean_object* v___x_261_, lean_object* v___x_262_, lean_object* v_n_263_, lean_object* v_it_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_262_, v___x_261_, v_it_264_, v_n_263_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0___boxed(lean_object* v___x_266_, lean_object* v___x_267_, lean_object* v_n_268_, lean_object* v_it_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(v___x_266_, v___x_267_, v_n_268_, v_it_269_);
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_266_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(lean_object* v___x_271_, lean_object* v___x_272_, lean_object* v_inst_273_, lean_object* v_R_274_, lean_object* v_a_275_, lean_object* v_b_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_271_, v___x_272_, v_a_275_, v_b_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___boxed(lean_object* v___x_278_, lean_object* v___x_279_, lean_object* v_inst_280_, lean_object* v_R_281_, lean_object* v_a_282_, lean_object* v_b_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(v___x_278_, v___x_279_, v_inst_280_, v_R_281_, v_a_282_, v_b_283_);
lean_dec_ref(v___x_279_);
lean_dec_ref(v___x_278_);
return v_res_284_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object* v_p_285_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = l_System_FilePath_isAbsolute(v_p_285_);
if (v___x_286_ == 0)
{
uint8_t v___x_287_; 
v___x_287_ = 1;
return v___x_287_;
}
else
{
uint8_t v___x_288_; 
v___x_288_ = 0;
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object* v_p_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_System_FilePath_isRelative(v_p_289_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
static lean_object* _init_l_System_FilePath_join___closed__0(void){
_start:
{
uint32_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = l_System_FilePath_pathSeparator;
v___x_293_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_294_ = lean_string_push(v___x_293_, v___x_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object* v_p_295_, lean_object* v_sub_296_){
_start:
{
uint8_t v___x_297_; 
lean_inc_ref(v_sub_296_);
v___x_297_ = l_System_FilePath_isAbsolute(v_sub_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_299_ = lean_string_append(v_p_295_, v___x_298_);
v___x_300_ = lean_string_append(v___x_299_, v_sub_296_);
lean_dec_ref(v_sub_296_);
return v___x_300_;
}
else
{
lean_dec_ref(v_p_295_);
return v_sub_296_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(lean_object* v_s_304_, lean_object* v_a_305_, lean_object* v_b_306_){
_start:
{
lean_object* v___x_307_; uint8_t v_decide_308_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v_decide_308_ = lean_nat_dec_eq(v_a_305_, v___x_307_);
if (v_decide_308_ == 0)
{
lean_object* v_str_309_; lean_object* v_startInclusive_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint32_t v___x_319_; uint8_t v___x_320_; 
v_str_309_ = lean_ctor_get(v_s_304_, 0);
v_startInclusive_310_ = lean_ctor_get(v_s_304_, 1);
v___x_311_ = l_System_FilePath_pathSeparators;
v___x_312_ = lean_nat_add(v_startInclusive_310_, v_a_305_);
lean_inc(v___x_312_);
lean_inc(v_startInclusive_310_);
lean_inc_ref(v_str_309_);
v___x_313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_313_, 0, v_str_309_);
lean_ctor_set(v___x_313_, 1, v_startInclusive_310_);
lean_ctor_set(v___x_313_, 2, v___x_312_);
v___x_314_ = lean_nat_sub(v___x_312_, v_startInclusive_310_);
lean_dec(v___x_312_);
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_sub(v___x_314_, v___x_315_);
lean_dec(v___x_314_);
v___x_317_ = l_String_Slice_posLE(v___x_313_, v___x_316_);
lean_dec_ref_known(v___x_313_, 3);
v___x_318_ = lean_nat_add(v_startInclusive_310_, v___x_317_);
v___x_319_ = lean_string_utf8_get_fast(v_str_309_, v___x_318_);
lean_dec(v___x_318_);
v___x_320_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___x_319_, v___x_311_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec(v___x_317_);
v___x_321_ = lean_box(0);
v___x_322_ = lean_nat_sub(v_a_305_, v___x_315_);
lean_dec(v_a_305_);
v___x_323_ = l_String_Slice_posLE(v_s_304_, v___x_322_);
v_a_305_ = v___x_323_;
v_b_306_ = v___x_321_;
goto _start;
}
else
{
lean_object* v___x_325_; 
lean_dec(v_a_305_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_317_);
return v___x_325_;
}
}
else
{
lean_dec(v_a_305_);
lean_inc(v_b_306_);
return v_b_306_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg___boxed(lean_object* v_s_326_, lean_object* v_a_327_, lean_object* v_b_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_326_, v_a_327_, v_b_328_);
lean_dec(v_b_328_);
lean_dec_ref(v_s_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(lean_object* v_s_330_){
_start:
{
lean_object* v_startInclusive_331_; lean_object* v_endExclusive_332_; lean_object* v_searcher_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_startInclusive_331_ = lean_ctor_get(v_s_330_, 1);
v_endExclusive_332_ = lean_ctor_get(v_s_330_, 2);
v_searcher_333_ = lean_nat_sub(v_endExclusive_332_, v_startInclusive_331_);
v___x_334_ = lean_box(0);
v___x_335_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_330_, v_searcher_333_, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___boxed(lean_object* v_s_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v_s_336_);
lean_dec_ref(v_s_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object* v_p_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_string_utf8_byte_size(v_p_338_);
v___x_341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_341_, 0, v_p_338_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
lean_ctor_set(v___x_341_, 2, v___x_340_);
v___x_342_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v___x_341_);
lean_dec_ref_known(v___x_341_, 3);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v___x_343_; 
v___x_343_ = lean_box(0);
return v___x_343_;
}
else
{
lean_object* v_val_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
v_val_344_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_342_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_val_344_);
lean_dec(v___x_342_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_val_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(lean_object* v_s_352_, lean_object* v_inst_353_, lean_object* v_R_354_, lean_object* v_a_355_, lean_object* v_b_356_, lean_object* v_c_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_352_, v_a_355_, v_b_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___boxed(lean_object* v_s_359_, lean_object* v_inst_360_, lean_object* v_R_361_, lean_object* v_a_362_, lean_object* v_b_363_, lean_object* v_c_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(v_s_359_, v_inst_360_, v_R_361_, v_a_362_, v_b_363_, v_c_364_);
lean_dec(v_b_363_);
lean_dec_ref(v_s_359_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(lean_object* v_p_366_){
_start:
{
lean_object* v___x_367_; uint32_t v___y_369_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_367_ = l_System_FilePath_pathSeparators;
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = lean_string_utf8_byte_size(v_p_366_);
lean_inc_ref(v_p_366_);
v___x_383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_383_, 0, v_p_366_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
lean_ctor_set(v___x_383_, 2, v___x_382_);
v___x_384_ = l_String_Slice_Pos_get_x3f(v___x_383_, v___x_381_);
lean_dec_ref_known(v___x_383_, 3);
if (lean_obj_tag(v___x_384_) == 0)
{
uint32_t v___x_385_; 
v___x_385_ = 65;
v___y_369_ = v___x_385_;
goto v___jp_368_;
}
else
{
lean_object* v_val_386_; uint32_t v___x_387_; 
v_val_386_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_val_386_);
lean_dec_ref_known(v___x_384_, 1);
v___x_387_ = lean_unbox_uint32(v_val_386_);
lean_dec(v_val_386_);
v___y_369_ = v___x_387_;
goto v___jp_368_;
}
v___jp_368_:
{
uint8_t v___x_370_; 
v___x_370_ = l_List_elem___at___00System_FilePath_normalize_spec__0(v___y_369_, v___x_367_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = lean_unsigned_to_nat(3u);
v___x_373_ = lean_string_utf8_byte_size(v_p_366_);
v___x_374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_374_, 0, v_p_366_);
lean_ctor_set(v___x_374_, 1, v___x_371_);
lean_ctor_set(v___x_374_, 2, v___x_373_);
v___x_375_ = l_String_Slice_Pos_nextn(v___x_374_, v___x_371_, v___x_372_);
lean_dec_ref_known(v___x_374_, 3);
return v___x_375_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_string_utf8_byte_size(v_p_366_);
v___x_379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_379_, 0, v_p_366_);
lean_ctor_set(v___x_379_, 1, v___x_376_);
lean_ctor_set(v___x_379_, 2, v___x_378_);
v___x_380_ = l_String_Slice_Pos_nextn(v___x_379_, v___x_376_, v___x_377_);
lean_dec_ref_known(v___x_379_, 3);
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object* v_p_388_){
_start:
{
lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___x_399_; lean_object* v___y_401_; 
lean_inc_ref(v_p_388_);
v___x_399_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_388_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v___x_421_; 
v___x_421_ = lean_box(0);
v___y_401_ = v___x_421_;
goto v___jp_400_;
}
else
{
lean_object* v_val_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v_val_422_ = lean_ctor_get(v___x_399_, 0);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_string_utf8_extract_fast(v_p_388_, v___x_423_, v_val_422_);
v___x_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
v___y_401_ = v___x_425_;
goto v___jp_400_;
}
v___jp_389_:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
lean_inc(v___y_391_);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v___y_391_);
v___x_395_ = l_Option_instDecidableEq___redArg(v___y_390_, v___y_393_, v___x_394_);
if (v___x_395_ == 0)
{
lean_dec(v___y_391_);
lean_dec_ref(v_p_388_);
return v___y_392_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v___y_392_);
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = lean_string_utf8_extract_fast(v_p_388_, v___x_396_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v_p_388_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
v___jp_400_:
{
uint8_t v___x_402_; 
lean_inc_ref(v_p_388_);
v___x_402_ = l_System_FilePath_isAbsolute(v_p_388_);
if (v___x_402_ == 0)
{
lean_dec(v___x_399_);
lean_dec_ref(v_p_388_);
return v___y_401_;
}
else
{
lean_object* v_afterRootDirectory_403_; lean_object* v___x_404_; uint8_t v_decide_405_; 
lean_inc_ref(v_p_388_);
v_afterRootDirectory_403_ = l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(v_p_388_);
v___x_404_ = lean_string_utf8_byte_size(v_p_388_);
v_decide_405_ = lean_nat_dec_eq(v_afterRootDirectory_403_, v___x_404_);
if (v_decide_405_ == 0)
{
lean_object* v___x_406_; 
lean_inc_ref(v_p_388_);
v___x_406_ = lean_alloc_closure((void*)(l_String_instDecidableEqPos___boxed), 3, 1);
lean_closure_set(v___x_406_, 0, v_p_388_);
if (lean_obj_tag(v___x_399_) == 0)
{
v___y_390_ = v___x_406_;
v___y_391_ = v_afterRootDirectory_403_;
v___y_392_ = v___y_401_;
v___y_393_ = v___x_399_;
goto v___jp_389_;
}
else
{
lean_object* v_val_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v_val_407_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_val_407_);
lean_dec_ref_known(v___x_399_, 1);
v___x_408_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_p_388_);
v___x_409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_409_, 0, v_p_388_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
lean_ctor_set(v___x_409_, 2, v___x_404_);
v___x_410_ = l_String_Slice_Pos_next_x3f(v___x_409_, v_val_407_);
lean_dec(v_val_407_);
lean_dec_ref_known(v___x_409_, 3);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(0);
v___y_390_ = v___x_406_;
v___y_391_ = v_afterRootDirectory_403_;
v___y_392_ = v___y_401_;
v___y_393_ = v___x_411_;
goto v___jp_389_;
}
else
{
lean_object* v_val_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_val_412_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_410_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_val_412_);
lean_dec(v___x_410_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_val_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
v___y_390_ = v___x_406_;
v___y_391_ = v_afterRootDirectory_403_;
v___y_392_ = v___y_401_;
v___y_393_ = v___x_417_;
goto v___jp_389_;
}
}
}
}
}
else
{
lean_object* v___x_420_; 
lean_dec(v_afterRootDirectory_403_);
lean_dec(v___y_401_);
lean_dec(v___x_399_);
lean_dec_ref(v_p_388_);
v___x_420_ = lean_box(0);
return v___x_420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object* v_p_428_){
_start:
{
lean_object* v___y_430_; lean_object* v___x_442_; 
lean_inc_ref(v_p_428_);
v___x_442_ = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_428_);
if (lean_obj_tag(v___x_442_) == 0)
{
v___y_430_ = v_p_428_;
goto v___jp_429_;
}
else
{
lean_object* v_val_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_val_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_val_443_);
lean_dec_ref_known(v___x_442_, 1);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_string_utf8_byte_size(v_p_428_);
lean_inc_ref(v_p_428_);
v___x_446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_446_, 0, v_p_428_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
lean_ctor_set(v___x_446_, 2, v___x_445_);
v___x_447_ = l_String_Slice_Pos_next_x21(v___x_446_, v_val_443_);
lean_dec(v_val_443_);
lean_dec_ref_known(v___x_446_, 3);
v___x_448_ = lean_string_utf8_extract_fast(v_p_428_, v___x_447_, v___x_445_);
lean_dec(v___x_447_);
lean_dec_ref(v_p_428_);
v___y_430_ = v___x_448_;
goto v___jp_429_;
}
v___jp_429_:
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_431_ = lean_string_utf8_byte_size(v___y_430_);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_nat_dec_eq(v___x_431_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_435_ = lean_string_dec_eq(v___y_430_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = ((lean_object*)(l_System_FilePath_fileName___closed__1));
v___x_437_ = lean_string_dec_eq(v___y_430_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
v___x_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_438_, 0, v___y_430_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; 
lean_dec_ref(v___y_430_);
v___x_439_ = lean_box(0);
return v___x_439_;
}
}
else
{
lean_object* v___x_440_; 
lean_dec_ref(v___y_430_);
v___x_440_ = lean_box(0);
return v___x_440_;
}
}
else
{
lean_object* v___x_441_; 
lean_dec_ref(v___y_430_);
v___x_441_ = lean_box(0);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(lean_object* v_s_449_, lean_object* v_a_450_, lean_object* v_b_451_){
_start:
{
lean_object* v___x_452_; uint8_t v_decide_453_; 
v___x_452_ = lean_unsigned_to_nat(0u);
v_decide_453_ = lean_nat_dec_eq(v_a_450_, v___x_452_);
if (v_decide_453_ == 0)
{
lean_object* v_str_454_; lean_object* v_startInclusive_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint32_t v___x_463_; uint32_t v___x_464_; uint8_t v___x_465_; 
v_str_454_ = lean_ctor_get(v_s_449_, 0);
v_startInclusive_455_ = lean_ctor_get(v_s_449_, 1);
v___x_456_ = lean_nat_add(v_startInclusive_455_, v_a_450_);
lean_inc(v___x_456_);
lean_inc(v_startInclusive_455_);
lean_inc_ref(v_str_454_);
v___x_457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_457_, 0, v_str_454_);
lean_ctor_set(v___x_457_, 1, v_startInclusive_455_);
lean_ctor_set(v___x_457_, 2, v___x_456_);
v___x_458_ = lean_nat_sub(v___x_456_, v_startInclusive_455_);
lean_dec(v___x_456_);
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_sub(v___x_458_, v___x_459_);
lean_dec(v___x_458_);
v___x_461_ = l_String_Slice_posLE(v___x_457_, v___x_460_);
lean_dec_ref_known(v___x_457_, 3);
v___x_462_ = lean_nat_add(v_startInclusive_455_, v___x_461_);
v___x_463_ = lean_string_utf8_get_fast(v_str_454_, v___x_462_);
lean_dec(v___x_462_);
v___x_464_ = 46;
v___x_465_ = lean_uint32_dec_eq(v___x_463_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v___x_461_);
v___x_466_ = lean_box(0);
v___x_467_ = lean_nat_sub(v_a_450_, v___x_459_);
lean_dec(v_a_450_);
v___x_468_ = l_String_Slice_posLE(v_s_449_, v___x_467_);
v_a_450_ = v___x_468_;
v_b_451_ = v___x_466_;
goto _start;
}
else
{
lean_object* v___x_470_; 
lean_dec(v_a_450_);
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_461_);
return v___x_470_;
}
}
else
{
lean_dec(v_a_450_);
lean_inc(v_b_451_);
return v_b_451_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg___boxed(lean_object* v_s_471_, lean_object* v_a_472_, lean_object* v_b_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_471_, v_a_472_, v_b_473_);
lean_dec(v_b_473_);
lean_dec_ref(v_s_471_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(lean_object* v_s_475_){
_start:
{
lean_object* v_startInclusive_476_; lean_object* v_endExclusive_477_; lean_object* v_searcher_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_startInclusive_476_ = lean_ctor_get(v_s_475_, 1);
v_endExclusive_477_ = lean_ctor_get(v_s_475_, 2);
v_searcher_478_ = lean_nat_sub(v_endExclusive_477_, v_startInclusive_476_);
v___x_479_ = lean_box(0);
v___x_480_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_475_, v_searcher_478_, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0___boxed(lean_object* v_s_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v_s_481_);
lean_dec_ref(v_s_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object* v_p_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_System_FilePath_fileName(v_p_483_);
if (lean_obj_tag(v___x_484_) == 0)
{
return v___x_484_;
}
else
{
lean_object* v_val_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_val_485_ = lean_ctor_get(v___x_484_, 0);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_string_utf8_byte_size(v_val_485_);
lean_inc(v_val_485_);
v___x_488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_488_, 0, v_val_485_);
lean_ctor_set(v___x_488_, 1, v___x_486_);
lean_ctor_set(v___x_488_, 2, v___x_487_);
v___x_489_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_488_);
lean_dec_ref_known(v___x_488_, 3);
if (lean_obj_tag(v___x_489_) == 0)
{
return v___x_484_;
}
else
{
lean_object* v_val_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_499_; 
v_val_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_499_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_499_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_val_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_499_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
uint8_t v___x_494_; 
v___x_494_ = lean_nat_dec_eq(v_val_490_, v___x_486_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_497_; 
lean_inc(v_val_485_);
lean_dec_ref_known(v___x_484_, 1);
v___x_495_ = lean_string_utf8_extract(v_val_485_, v___x_486_, v_val_490_);
lean_dec(v_val_490_);
lean_dec(v_val_485_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_495_);
v___x_497_ = v___x_492_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
else
{
lean_del_object(v___x_492_);
lean_dec(v_val_490_);
return v___x_484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(lean_object* v_s_500_, lean_object* v_inst_501_, lean_object* v_R_502_, lean_object* v_a_503_, lean_object* v_b_504_, lean_object* v_c_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_500_, v_a_503_, v_b_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___boxed(lean_object* v_s_507_, lean_object* v_inst_508_, lean_object* v_R_509_, lean_object* v_a_510_, lean_object* v_b_511_, lean_object* v_c_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(v_s_507_, v_inst_508_, v_R_509_, v_a_510_, v_b_511_, v_c_512_);
lean_dec(v_b_511_);
lean_dec_ref(v_s_507_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object* v_p_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_System_FilePath_fileName(v_p_514_);
if (lean_obj_tag(v___x_515_) == 0)
{
return v___x_515_;
}
else
{
lean_object* v_val_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_val_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc_n(v_val_516_, 2);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = lean_string_utf8_byte_size(v_val_516_);
v___x_519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_519_, 0, v_val_516_);
lean_ctor_set(v___x_519_, 1, v___x_517_);
lean_ctor_set(v___x_519_, 2, v___x_518_);
v___x_520_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_519_);
lean_dec_ref_known(v___x_519_, 3);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v___x_521_; 
lean_dec(v_val_516_);
v___x_521_ = lean_box(0);
return v___x_521_;
}
else
{
lean_object* v_val_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_534_; 
v_val_522_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_534_ == 0)
{
v___x_524_ = v___x_520_;
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_val_522_);
lean_dec(v___x_520_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
uint8_t v___x_526_; 
v___x_526_ = lean_nat_dec_eq(v_val_522_, v___x_517_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = lean_nat_add(v_val_522_, v___x_527_);
lean_dec(v_val_522_);
v___x_529_ = lean_string_utf8_extract(v_val_516_, v___x_528_, v___x_518_);
lean_dec(v___x_528_);
lean_dec(v_val_516_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_529_);
v___x_531_ = v___x_524_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
else
{
lean_object* v___x_533_; 
lean_del_object(v___x_524_);
lean_dec(v_val_522_);
lean_dec(v_val_516_);
v___x_533_ = lean_box(0);
return v___x_533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object* v_p_535_, lean_object* v_fname_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_System_FilePath_parent(v_p_535_);
if (lean_obj_tag(v___x_537_) == 0)
{
return v_fname_536_;
}
else
{
lean_object* v_val_538_; lean_object* v___x_539_; 
v_val_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_val_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = l_System_FilePath_join(v_val_538_, v_fname_536_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object* v_p_540_, lean_object* v_ext_541_){
_start:
{
lean_object* v___x_542_; 
lean_inc_ref(v_p_540_);
v___x_542_ = l_System_FilePath_fileName(v_p_540_);
if (lean_obj_tag(v___x_542_) == 0)
{
return v_p_540_;
}
else
{
lean_object* v_val_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v_val_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v___x_542_, 1);
v___x_544_ = lean_string_utf8_byte_size(v_ext_541_);
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_nat_dec_eq(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_547_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_548_ = lean_string_append(v_val_543_, v___x_547_);
v___x_549_ = lean_string_append(v___x_548_, v_ext_541_);
v___x_550_ = l_System_FilePath_withFileName(v_p_540_, v___x_549_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; 
v___x_551_ = l_System_FilePath_withFileName(v_p_540_, v_val_543_);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object* v_p_552_, lean_object* v_ext_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_System_FilePath_addExtension(v_p_552_, v_ext_553_);
lean_dec_ref(v_ext_553_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object* v_p_555_, lean_object* v_ext_556_){
_start:
{
lean_object* v___x_557_; 
lean_inc_ref(v_p_555_);
v___x_557_ = l_System_FilePath_fileStem(v_p_555_);
if (lean_obj_tag(v___x_557_) == 0)
{
return v_p_555_;
}
else
{
lean_object* v_val_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_val_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_val_558_);
lean_dec_ref_known(v___x_557_, 1);
v___x_559_ = lean_string_utf8_byte_size(v_ext_556_);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_nat_dec_eq(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_562_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_563_ = lean_string_append(v_val_558_, v___x_562_);
v___x_564_ = lean_string_append(v___x_563_, v_ext_556_);
v___x_565_ = l_System_FilePath_withFileName(v_p_555_, v___x_564_);
return v___x_565_;
}
else
{
lean_object* v___x_566_; 
v___x_566_ = l_System_FilePath_withFileName(v_p_555_, v_val_558_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object* v_p_567_, lean_object* v_ext_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_System_FilePath_withExtension(v_p_567_, v_ext_568_);
lean_dec_ref(v_ext_568_);
return v_res_569_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_571_ = lean_string_utf8_byte_size(v___x_570_);
return v___x_571_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0);
v___x_574_ = lean_nat_dec_eq(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_575_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_576_);
lean_ctor_set(v___x_578_, 2, v___x_575_);
return v___x_578_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2);
v___x_580_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3);
v___x_583_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2);
v___x_584_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v___x_582_);
lean_ctor_set(v___x_584_, 2, v___x_581_);
lean_ctor_set(v___x_584_, 3, v___x_581_);
return v___x_584_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg(){
_start:
{
uint8_t v___x_594_; 
v___x_594_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
v___x_595_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5);
return v___x_595_;
}
else
{
lean_object* v___x_596_; 
v___x_596_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__7));
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___boxed(lean_object* v___dummy_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg();
return v_res_598_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0(void){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg();
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(lean_object* v_s_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(lean_object* v_s_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v_s_602_);
lean_dec_ref(v_s_602_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object* v___x_604_, lean_object* v___x_605_, lean_object* v___x_606_, lean_object* v_a_607_, lean_object* v_b_608_){
_start:
{
lean_object* v_it_610_; lean_object* v_startInclusive_611_; lean_object* v_endExclusive_612_; 
if (lean_obj_tag(v_a_607_) == 0)
{
lean_object* v_currPos_617_; lean_object* v_searcher_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_724_; 
v_currPos_617_ = lean_ctor_get(v_a_607_, 0);
v_searcher_618_ = lean_ctor_get(v_a_607_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_a_607_);
if (v_isSharedCheck_724_ == 0)
{
v___x_620_ = v_a_607_;
v_isShared_621_ = v_isSharedCheck_724_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_searcher_618_);
lean_inc(v_currPos_617_);
lean_dec(v_a_607_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_724_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_it_623_; lean_object* v_it_629_; lean_object* v_startPos_630_; lean_object* v_endPos_631_; 
switch(lean_obj_tag(v_searcher_618_))
{
case 0:
{
lean_object* v_pos_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_656_; 
lean_del_object(v___x_620_);
v_pos_644_ = lean_ctor_get(v_searcher_618_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v_searcher_618_);
if (v_isSharedCheck_656_ == 0)
{
v___x_646_ = v_searcher_618_;
v_isShared_647_ = v_isSharedCheck_656_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_pos_644_);
lean_dec(v_searcher_618_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_656_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v_startInclusive_648_; lean_object* v_endExclusive_649_; lean_object* v___x_650_; uint8_t v_decide_651_; 
v_startInclusive_648_ = lean_ctor_get(v___x_605_, 1);
v_endExclusive_649_ = lean_ctor_get(v___x_605_, 2);
v___x_650_ = lean_nat_sub(v_endExclusive_649_, v_startInclusive_648_);
v_decide_651_ = lean_nat_dec_eq(v_pos_644_, v___x_650_);
lean_dec(v___x_650_);
if (v_decide_651_ == 0)
{
lean_object* v___x_653_; 
lean_inc(v_pos_644_);
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 1);
v___x_653_ = v___x_646_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_pos_644_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_inc(v_pos_644_);
v_it_629_ = v___x_653_;
v_startPos_630_ = v_pos_644_;
v_endPos_631_ = v_pos_644_;
goto v___jp_628_;
}
}
else
{
lean_object* v___x_655_; 
lean_del_object(v___x_646_);
v___x_655_ = lean_box(3);
lean_inc(v_pos_644_);
v_it_629_ = v___x_655_;
v_startPos_630_ = v_pos_644_;
v_endPos_631_ = v_pos_644_;
goto v___jp_628_;
}
}
}
case 1:
{
lean_object* v_pos_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_665_; 
v_pos_657_ = lean_ctor_get(v_searcher_618_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_searcher_618_);
if (v_isSharedCheck_665_ == 0)
{
v___x_659_ = v_searcher_618_;
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_pos_657_);
lean_dec(v_searcher_618_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = lean_string_utf8_next_fast(v___x_604_, v_pos_657_);
lean_dec(v_pos_657_);
if (v_isShared_660_ == 0)
{
lean_ctor_set_tag(v___x_659_, 0);
lean_ctor_set(v___x_659_, 0, v___x_661_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
v_it_623_ = v___x_663_;
goto v___jp_622_;
}
}
}
case 2:
{
lean_object* v_needle_666_; lean_object* v_table_667_; lean_object* v_stackPos_668_; lean_object* v_needlePos_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_723_; 
v_needle_666_ = lean_ctor_get(v_searcher_618_, 0);
v_table_667_ = lean_ctor_get(v_searcher_618_, 1);
v_stackPos_668_ = lean_ctor_get(v_searcher_618_, 2);
v_needlePos_669_ = lean_ctor_get(v_searcher_618_, 3);
v_isSharedCheck_723_ = !lean_is_exclusive(v_searcher_618_);
if (v_isSharedCheck_723_ == 0)
{
v___x_671_ = v_searcher_618_;
v_isShared_672_ = v_isSharedCheck_723_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_needlePos_669_);
lean_inc(v_stackPos_668_);
lean_inc(v_table_667_);
lean_inc(v_needle_666_);
lean_dec(v_searcher_618_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_723_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_str_673_; lean_object* v_startInclusive_674_; lean_object* v_endExclusive_675_; lean_object* v_basePos_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_str_673_ = lean_ctor_get(v_needle_666_, 0);
v_startInclusive_674_ = lean_ctor_get(v_needle_666_, 1);
v_endExclusive_675_ = lean_ctor_get(v_needle_666_, 2);
v_basePos_676_ = lean_nat_sub(v_stackPos_668_, v_needlePos_669_);
v___x_677_ = lean_nat_sub(v_endExclusive_675_, v_startInclusive_674_);
v___x_678_ = lean_nat_add(v_basePos_676_, v___x_677_);
v___x_679_ = lean_nat_dec_le(v___x_678_, v___x_606_);
lean_dec(v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
lean_dec(v___x_677_);
lean_del_object(v___x_671_);
lean_dec(v_needlePos_669_);
lean_dec(v_stackPos_668_);
lean_dec_ref(v_table_667_);
lean_dec_ref(v_needle_666_);
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_add(v_basePos_676_, v___x_680_);
lean_dec(v_basePos_676_);
v___x_682_ = lean_nat_dec_le(v___x_681_, v___x_606_);
lean_dec(v___x_681_);
if (v___x_682_ == 0)
{
lean_del_object(v___x_620_);
goto v___jp_642_;
}
else
{
lean_object* v___x_683_; 
v___x_683_ = lean_box(3);
v_it_623_ = v___x_683_;
goto v___jp_622_;
}
}
else
{
uint8_t v_stackByte_684_; lean_object* v___x_685_; uint8_t v_patByte_686_; uint8_t v___x_687_; 
lean_dec(v_basePos_676_);
lean_inc(v_stackPos_668_);
v_stackByte_684_ = lean_string_get_byte_fast(v___x_604_, v_stackPos_668_);
v___x_685_ = lean_nat_add(v_startInclusive_674_, v_needlePos_669_);
v_patByte_686_ = lean_string_get_byte_fast(v_str_673_, v___x_685_);
v___x_687_ = lean_uint8_dec_eq(v_stackByte_684_, v_patByte_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; uint8_t v_decide_689_; 
lean_dec(v___x_677_);
v___x_688_ = lean_unsigned_to_nat(0u);
v_decide_689_ = lean_nat_dec_eq(v_needlePos_669_, v___x_688_);
if (v_decide_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_newNeedlePos_692_; uint8_t v___x_693_; 
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_sub(v_needlePos_669_, v___x_690_);
lean_dec(v_needlePos_669_);
v_newNeedlePos_692_ = lean_array_fget_borrowed(v_table_667_, v___x_691_);
lean_dec(v___x_691_);
v___x_693_ = lean_nat_dec_eq(v_newNeedlePos_692_, v___x_688_);
if (v___x_693_ == 0)
{
lean_object* v___x_695_; 
lean_inc(v_newNeedlePos_692_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 3, v_newNeedlePos_692_);
v___x_695_ = v___x_671_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_needle_666_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_table_667_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_stackPos_668_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v_newNeedlePos_692_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
v_it_623_ = v___x_695_;
goto v___jp_622_;
}
}
else
{
lean_object* v_nextStackPos_697_; lean_object* v___x_699_; 
v_nextStackPos_697_ = l_String_Slice_posGE___redArg(v___x_605_, v_stackPos_668_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 3, v___x_688_);
lean_ctor_set(v___x_671_, 2, v_nextStackPos_697_);
v___x_699_ = v___x_671_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_needle_666_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_table_667_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_nextStackPos_697_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v___x_688_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v_it_623_ = v___x_699_;
goto v___jp_622_;
}
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_nextStackPos_703_; lean_object* v___x_705_; 
lean_dec(v_needlePos_669_);
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = lean_nat_add(v_stackPos_668_, v___x_701_);
lean_dec(v_stackPos_668_);
v_nextStackPos_703_ = l_String_Slice_posGE___redArg(v___x_605_, v___x_702_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 3, v___x_688_);
lean_ctor_set(v___x_671_, 2, v_nextStackPos_703_);
v___x_705_ = v___x_671_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_needle_666_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_table_667_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_nextStackPos_703_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v___x_688_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
v_it_623_ = v___x_705_;
goto v___jp_622_;
}
}
}
else
{
lean_object* v___x_707_; lean_object* v_nextStackPos_708_; lean_object* v_nextNeedlePos_709_; uint8_t v_decide_710_; 
lean_del_object(v___x_620_);
v___x_707_ = lean_unsigned_to_nat(1u);
v_nextStackPos_708_ = lean_nat_add(v_stackPos_668_, v___x_707_);
lean_dec(v_stackPos_668_);
v_nextNeedlePos_709_ = lean_nat_add(v_needlePos_669_, v___x_707_);
lean_dec(v_needlePos_669_);
v_decide_710_ = lean_nat_dec_eq(v_nextNeedlePos_709_, v___x_677_);
lean_dec(v___x_677_);
if (v_decide_710_ == 0)
{
lean_object* v___x_712_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 3, v_nextNeedlePos_709_);
lean_ctor_set(v___x_671_, 2, v_nextStackPos_708_);
v___x_712_ = v___x_671_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_needle_666_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_table_667_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_nextStackPos_708_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_nextNeedlePos_709_);
v___x_712_ = v_reuseFailAlloc_715_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; 
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_currPos_617_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v_a_607_ = v___x_713_;
goto _start;
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_716_ = lean_nat_sub(v_nextStackPos_708_, v_nextNeedlePos_709_);
lean_dec(v_nextNeedlePos_709_);
v___x_717_ = l_String_Slice_pos_x21(v___x_605_, v___x_716_);
lean_dec(v___x_716_);
v___x_718_ = l_String_Slice_pos_x21(v___x_605_, v_nextStackPos_708_);
v___x_719_ = lean_unsigned_to_nat(0u);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 3, v___x_719_);
lean_ctor_set(v___x_671_, 2, v_nextStackPos_708_);
v___x_721_ = v___x_671_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_needle_666_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_table_667_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_nextStackPos_708_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
v_it_629_ = v___x_721_;
v_startPos_630_ = v___x_717_;
v_endPos_631_ = v___x_718_;
goto v___jp_628_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_620_);
goto v___jp_642_;
}
}
v___jp_622_:
{
lean_object* v___x_625_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 1, v_it_623_);
v___x_625_ = v___x_620_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_currPos_617_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_it_623_);
v___x_625_ = v_reuseFailAlloc_627_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
v_a_607_ = v___x_625_;
goto _start;
}
}
v___jp_628_:
{
lean_object* v_slice_632_; lean_object* v_startInclusive_633_; lean_object* v_endExclusive_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
v_slice_632_ = l_String_Slice_subslice_x21(v___x_605_, v_currPos_617_, v_startPos_630_);
v_startInclusive_633_ = lean_ctor_get(v_slice_632_, 0);
v_endExclusive_634_ = lean_ctor_get(v_slice_632_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v_slice_632_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v_slice_632_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_endExclusive_634_);
lean_inc(v_startInclusive_633_);
lean_dec(v_slice_632_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_nextIt_639_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v_it_629_);
lean_ctor_set(v___x_636_, 0, v_endPos_631_);
v_nextIt_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_endPos_631_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_it_629_);
v_nextIt_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
v_it_610_ = v_nextIt_639_;
v_startInclusive_611_ = v_startInclusive_633_;
v_endExclusive_612_ = v_endExclusive_634_;
goto v___jp_609_;
}
}
}
v___jp_642_:
{
lean_object* v___x_643_; 
v___x_643_ = lean_box(1);
lean_inc(v___x_606_);
v_it_610_ = v___x_643_;
v_startInclusive_611_ = v_currPos_617_;
v_endExclusive_612_ = v___x_606_;
goto v___jp_609_;
}
}
}
else
{
lean_dec(v___x_606_);
lean_dec_ref(v___x_604_);
return v_b_608_;
}
v___jp_609_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_inc_ref(v___x_604_);
v___x_613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_613_, 0, v___x_604_);
lean_ctor_set(v___x_613_, 1, v_startInclusive_611_);
lean_ctor_set(v___x_613_, 2, v_endExclusive_612_);
v___x_614_ = l_String_Slice_toString(v___x_613_);
lean_dec_ref_known(v___x_613_, 3);
v___x_615_ = lean_array_push(v_b_608_, v___x_614_);
v_a_607_ = v_it_610_;
v_b_608_ = v___x_615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object* v___x_725_, lean_object* v___x_726_, lean_object* v___x_727_, lean_object* v_a_728_, lean_object* v_b_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_725_, v___x_726_, v___x_727_, v_a_728_, v_b_729_);
lean_dec_ref(v___x_726_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object* v_p_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_734_ = l_System_FilePath_normalize(v_p_733_);
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = lean_string_utf8_byte_size(v___x_734_);
lean_inc_ref(v___x_734_);
v___x_737_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_737_, 0, v___x_734_);
lean_ctor_set(v___x_737_, 1, v___x_735_);
lean_ctor_set(v___x_737_, 2, v___x_736_);
v___x_738_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
v___x_739_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_740_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_734_, v___x_737_, v___x_736_, v___x_738_, v___x_739_);
lean_dec_ref_known(v___x_737_, 3);
v___x_741_ = lean_array_to_list(v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object* v___x_742_, lean_object* v___x_743_, lean_object* v___x_744_, lean_object* v_inst_745_, lean_object* v_R_746_, lean_object* v_a_747_, lean_object* v_b_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_742_, v___x_743_, v___x_744_, v_a_747_, v_b_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object* v___x_750_, lean_object* v___x_751_, lean_object* v___x_752_, lean_object* v_inst_753_, lean_object* v_R_754_, lean_object* v_a_755_, lean_object* v_b_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(v___x_750_, v___x_751_, v___x_752_, v_inst_753_, v_R_754_, v_a_755_, v_b_756_);
lean_dec_ref(v___x_751_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object* v_parts_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_760_ = l_String_intercalate(v___x_759_, v_parts_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object* v_toString_761_){
_start:
{
lean_inc_ref(v_toString_761_);
return v_toString_761_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object* v_toString_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_System_instCoeStringFilePath___lam__0(v_toString_762_);
lean_dec_ref(v_toString_762_);
return v_res_763_;
}
}
static uint32_t _init_l_System_SearchPath_separator(void){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = l_System_Platform_isWindows;
if (v___x_766_ == 0)
{
uint32_t v___x_767_; 
v___x_767_ = 58;
return v___x_767_;
}
else
{
uint32_t v___x_768_; 
v___x_768_ = 59;
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___closed__0));
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___boxed(lean_object* v___dummy_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg();
return v_res_774_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0(void){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg();
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(lean_object* v_s_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___boxed(lean_object* v_s_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v_s_778_);
lean_dec_ref(v_s_778_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(lean_object* v_s_780_, lean_object* v___x_781_, lean_object* v___x_782_, lean_object* v_a_783_, lean_object* v_b_784_){
_start:
{
lean_object* v_it_786_; lean_object* v_startInclusive_787_; lean_object* v_endExclusive_788_; 
if (lean_obj_tag(v_a_783_) == 0)
{
lean_object* v_currPos_792_; lean_object* v_searcher_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_816_; 
v_currPos_792_ = lean_ctor_get(v_a_783_, 0);
v_searcher_793_ = lean_ctor_get(v_a_783_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v_a_783_);
if (v_isSharedCheck_816_ == 0)
{
v___x_795_ = v_a_783_;
v_isShared_796_ = v_isSharedCheck_816_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_searcher_793_);
lean_inc(v_currPos_792_);
lean_dec(v_a_783_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_816_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
uint8_t v_decide_797_; 
v_decide_797_ = lean_nat_dec_eq(v_searcher_793_, v___x_782_);
if (v_decide_797_ == 0)
{
uint32_t v___x_798_; uint32_t v___x_799_; uint8_t v___x_800_; 
v___x_798_ = l_System_SearchPath_separator;
v___x_799_ = lean_string_utf8_get_fast(v_s_780_, v_searcher_793_);
v___x_800_ = lean_uint32_dec_eq(v___x_799_, v___x_798_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = lean_string_utf8_next_fast(v_s_780_, v_searcher_793_);
lean_dec(v_searcher_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___x_801_);
v___x_803_ = v___x_795_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_currPos_792_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_801_);
v___x_803_ = v_reuseFailAlloc_805_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
v_a_783_ = v___x_803_;
goto _start;
}
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_slice_809_; lean_object* v_nextIt_811_; 
v___x_806_ = lean_string_utf8_next_fast(v_s_780_, v_searcher_793_);
v___x_807_ = lean_nat_sub(v___x_806_, v_searcher_793_);
v___x_808_ = lean_nat_add(v_searcher_793_, v___x_807_);
lean_dec(v___x_807_);
v_slice_809_ = l_String_Slice_subslice_x21(v___x_781_, v_currPos_792_, v_searcher_793_);
lean_inc(v___x_808_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___x_808_);
lean_ctor_set(v___x_795_, 0, v___x_808_);
v_nextIt_811_ = v___x_795_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_808_);
v_nextIt_811_ = v_reuseFailAlloc_814_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v_startInclusive_812_; lean_object* v_endExclusive_813_; 
v_startInclusive_812_ = lean_ctor_get(v_slice_809_, 0);
lean_inc(v_startInclusive_812_);
v_endExclusive_813_ = lean_ctor_get(v_slice_809_, 1);
lean_inc(v_endExclusive_813_);
lean_dec_ref(v_slice_809_);
v_it_786_ = v_nextIt_811_;
v_startInclusive_787_ = v_startInclusive_812_;
v_endExclusive_788_ = v_endExclusive_813_;
goto v___jp_785_;
}
}
}
else
{
lean_object* v___x_815_; 
lean_del_object(v___x_795_);
lean_dec(v_searcher_793_);
v___x_815_ = lean_box(1);
lean_inc(v___x_782_);
v_it_786_ = v___x_815_;
v_startInclusive_787_ = v_currPos_792_;
v_endExclusive_788_ = v___x_782_;
goto v___jp_785_;
}
}
}
else
{
lean_dec(v___x_782_);
return v_b_784_;
}
v___jp_785_:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_string_utf8_extract_fast(v_s_780_, v_startInclusive_787_, v_endExclusive_788_);
lean_dec(v_endExclusive_788_);
lean_dec(v_startInclusive_787_);
v___x_790_ = lean_array_push(v_b_784_, v___x_789_);
v_a_783_ = v_it_786_;
v_b_784_ = v___x_790_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg___boxed(lean_object* v_s_817_, lean_object* v___x_818_, lean_object* v___x_819_, lean_object* v_a_820_, lean_object* v_b_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_817_, v___x_818_, v___x_819_, v_a_820_, v_b_821_);
lean_dec_ref(v___x_818_);
lean_dec_ref(v_s_817_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object* v_s_823_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_string_utf8_byte_size(v_s_823_);
lean_inc_ref(v_s_823_);
v___x_826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_826_, 0, v_s_823_);
lean_ctor_set(v___x_826_, 1, v___x_824_);
lean_ctor_set(v___x_826_, 2, v___x_825_);
v___x_827_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0);
v___x_828_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_829_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_823_, v___x_826_, v___x_825_, v___x_827_, v___x_828_);
lean_dec_ref_known(v___x_826_, 3);
lean_dec_ref(v_s_823_);
v___x_830_ = lean_array_to_list(v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(lean_object* v_s_831_, lean_object* v___x_832_, lean_object* v___x_833_, lean_object* v_inst_834_, lean_object* v_R_835_, lean_object* v_a_836_, lean_object* v_b_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_831_, v___x_832_, v___x_833_, v_a_836_, v_b_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___boxed(lean_object* v_s_839_, lean_object* v___x_840_, lean_object* v___x_841_, lean_object* v_inst_842_, lean_object* v_R_843_, lean_object* v_a_844_, lean_object* v_b_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(v_s_839_, v___x_840_, v___x_841_, v_inst_842_, v_R_843_, v_a_844_, v_b_845_);
lean_dec_ref(v___x_840_);
lean_dec_ref(v_s_839_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
if (lean_obj_tag(v_a_847_) == 0)
{
lean_object* v___x_849_; 
v___x_849_ = l_List_reverse___redArg(v_a_848_);
return v___x_849_;
}
else
{
lean_object* v_head_850_; lean_object* v_tail_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
v_head_850_ = lean_ctor_get(v_a_847_, 0);
v_tail_851_ = lean_ctor_get(v_a_847_, 1);
v_isSharedCheck_859_ = !lean_is_exclusive(v_a_847_);
if (v_isSharedCheck_859_ == 0)
{
v___x_853_ = v_a_847_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_tail_851_);
lean_inc(v_head_850_);
lean_dec(v_a_847_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v_a_848_);
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_head_850_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_a_848_);
v___x_856_ = v_reuseFailAlloc_858_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
v_a_847_ = v_tail_851_;
v_a_848_ = v___x_856_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_System_SearchPath_toString___closed__0(void){
_start:
{
uint32_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = l_System_SearchPath_separator;
v___x_861_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_862_ = lean_string_push(v___x_861_, v___x_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object* v_path_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_864_ = lean_obj_once(&l_System_SearchPath_toString___closed__0, &l_System_SearchPath_toString___closed__0_once, _init_l_System_SearchPath_toString___closed__0);
v___x_865_ = lean_box(0);
v___x_866_ = l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(v_path_863_, v___x_865_);
v___x_867_ = l_String_intercalate(v___x_864_, v___x_866_);
return v___x_867_;
}
}
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
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
res = runtime_initialize_Init_Data_String_Iterate(builtin);
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
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
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
res = initialize_Init_Data_String_Iterate(builtin);
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
