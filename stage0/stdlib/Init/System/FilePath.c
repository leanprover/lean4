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
static lean_once_cell_t l_System_FilePath_extension___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_System_FilePath_extension___closed__0;
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
lean_dec(v_tail_108_);
lean_dec_ref_known(v___x_107_, 2);
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
lean_inc(v_val_411_);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_string_utf8_extract_fast(v_p_377_, v___x_412_, v_val_411_);
lean_dec(v_val_411_);
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
v___y_390_ = v___x_414_;
goto v___jp_389_;
}
v___jp_378_:
{
lean_object* v___x_383_; uint8_t v___x_384_; 
lean_inc(v___y_379_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___y_379_);
v___x_384_ = l_Option_instDecidableEq___redArg(v___y_380_, v___y_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_dec(v___y_379_);
lean_dec_ref(v_p_377_);
return v___y_381_;
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec(v___y_381_);
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_string_utf8_extract_fast(v_p_377_, v___x_385_, v___y_379_);
lean_dec(v___y_379_);
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
v___y_379_ = v_afterRootDirectory_392_;
v___y_380_ = v___x_395_;
v___y_381_ = v___y_390_;
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
v___y_379_ = v_afterRootDirectory_392_;
v___y_380_ = v___x_395_;
v___y_381_ = v___y_390_;
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
v___y_379_ = v_afterRootDirectory_392_;
v___y_380_ = v___x_395_;
v___y_381_ = v___y_390_;
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
lean_inc_n(v_val_474_, 2);
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_string_utf8_byte_size(v_val_474_);
v___x_477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_477_, 0, v_val_474_);
lean_ctor_set(v___x_477_, 1, v___x_475_);
lean_ctor_set(v___x_477_, 2, v___x_476_);
v___x_478_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_477_);
lean_dec_ref_known(v___x_477_, 3);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_dec(v_val_474_);
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
lean_dec(v_val_474_);
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
static lean_object* _init_l_System_FilePath_extension___closed__0(void){
_start:
{
uint32_t v___x_503_; lean_object* v___x_504_; 
v___x_503_ = 46;
v___x_504_ = l_Char_utf8Size(v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object* v_p_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_System_FilePath_fileName(v_p_505_);
if (lean_obj_tag(v___x_506_) == 0)
{
return v___x_506_;
}
else
{
lean_object* v_val_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_val_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc_n(v_val_507_, 2);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = lean_string_utf8_byte_size(v_val_507_);
v___x_510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_510_, 0, v_val_507_);
lean_ctor_set(v___x_510_, 1, v___x_508_);
lean_ctor_set(v___x_510_, 2, v___x_509_);
v___x_511_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v___x_510_);
lean_dec_ref_known(v___x_510_, 3);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v___x_512_; 
lean_dec(v_val_507_);
v___x_512_ = lean_box(0);
return v___x_512_;
}
else
{
lean_object* v_val_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_525_; 
v_val_513_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_525_ == 0)
{
v___x_515_ = v___x_511_;
v_isShared_516_ = v_isSharedCheck_525_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_val_513_);
lean_dec(v___x_511_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_525_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
uint8_t v___x_517_; 
v___x_517_ = lean_nat_dec_eq(v_val_513_, v___x_508_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_518_ = lean_obj_once(&l_System_FilePath_extension___closed__0, &l_System_FilePath_extension___closed__0_once, _init_l_System_FilePath_extension___closed__0);
v___x_519_ = lean_nat_add(v_val_513_, v___x_518_);
lean_dec(v_val_513_);
v___x_520_ = lean_string_utf8_extract(v_val_507_, v___x_519_, v___x_509_);
lean_dec(v___x_519_);
lean_dec(v_val_507_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_520_);
v___x_522_ = v___x_515_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
else
{
lean_object* v___x_524_; 
lean_del_object(v___x_515_);
lean_dec(v_val_513_);
lean_dec(v_val_507_);
v___x_524_ = lean_box(0);
return v___x_524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object* v_p_526_, lean_object* v_fname_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_System_FilePath_parent(v_p_526_);
if (lean_obj_tag(v___x_528_) == 0)
{
return v_fname_527_;
}
else
{
lean_object* v_val_529_; lean_object* v___x_530_; 
v_val_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_val_529_);
lean_dec_ref_known(v___x_528_, 1);
v___x_530_ = l_System_FilePath_join(v_val_529_, v_fname_527_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object* v_p_531_, lean_object* v_ext_532_){
_start:
{
lean_object* v___x_533_; 
lean_inc_ref(v_p_531_);
v___x_533_ = l_System_FilePath_fileName(v_p_531_);
if (lean_obj_tag(v___x_533_) == 0)
{
return v_p_531_;
}
else
{
lean_object* v_val_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v_val_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_val_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = lean_string_utf8_byte_size(v_ext_532_);
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_nat_dec_eq(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_538_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_539_ = lean_string_append(v_val_534_, v___x_538_);
v___x_540_ = lean_string_append(v___x_539_, v_ext_532_);
v___x_541_ = l_System_FilePath_withFileName(v_p_531_, v___x_540_);
return v___x_541_;
}
else
{
lean_object* v___x_542_; 
v___x_542_ = l_System_FilePath_withFileName(v_p_531_, v_val_534_);
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object* v_p_543_, lean_object* v_ext_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_System_FilePath_addExtension(v_p_543_, v_ext_544_);
lean_dec_ref(v_ext_544_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object* v_p_546_, lean_object* v_ext_547_){
_start:
{
lean_object* v___x_548_; 
lean_inc_ref(v_p_546_);
v___x_548_ = l_System_FilePath_fileStem(v_p_546_);
if (lean_obj_tag(v___x_548_) == 0)
{
return v_p_546_;
}
else
{
lean_object* v_val_549_; lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v_val_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_val_549_);
lean_dec_ref_known(v___x_548_, 1);
v___x_550_ = lean_string_utf8_byte_size(v_ext_547_);
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = lean_nat_dec_eq(v___x_550_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_553_ = ((lean_object*)(l_System_FilePath_fileName___closed__0));
v___x_554_ = lean_string_append(v_val_549_, v___x_553_);
v___x_555_ = lean_string_append(v___x_554_, v_ext_547_);
v___x_556_ = l_System_FilePath_withFileName(v_p_546_, v___x_555_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = l_System_FilePath_withFileName(v_p_546_, v_val_549_);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object* v_p_558_, lean_object* v_ext_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_System_FilePath_withExtension(v_p_558_, v_ext_559_);
lean_dec_ref(v_ext_559_);
return v_res_560_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_562_ = lean_string_utf8_byte_size(v___x_561_);
return v___x_562_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0);
v___x_565_ = lean_nat_dec_eq(v___x_564_, v___x_563_);
return v___x_565_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_566_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__0);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_567_);
lean_ctor_set(v___x_569_, 2, v___x_566_);
return v___x_569_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2);
v___x_571_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__3);
v___x_574_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__2);
v___x_575_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_573_);
lean_ctor_set(v___x_575_, 2, v___x_572_);
lean_ctor_set(v___x_575_, 3, v___x_572_);
return v___x_575_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__4);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg(){
_start:
{
uint8_t v___x_585_; 
v___x_585_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__1);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__5);
return v___x_586_;
}
else
{
lean_object* v___x_587_; 
v___x_587_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___closed__7));
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg___boxed(lean_object* v___dummy_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg();
return v_res_589_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0(void){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___redArg();
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(lean_object* v_s_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(lean_object* v_s_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v_s_593_);
lean_dec_ref(v_s_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(lean_object* v___x_595_, lean_object* v___x_596_, lean_object* v___x_597_, lean_object* v_a_598_, lean_object* v_b_599_){
_start:
{
lean_object* v_it_601_; lean_object* v_startInclusive_602_; lean_object* v_endExclusive_603_; 
if (lean_obj_tag(v_a_598_) == 0)
{
lean_object* v_currPos_608_; lean_object* v_searcher_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_715_; 
v_currPos_608_ = lean_ctor_get(v_a_598_, 0);
v_searcher_609_ = lean_ctor_get(v_a_598_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v_a_598_);
if (v_isSharedCheck_715_ == 0)
{
v___x_611_ = v_a_598_;
v_isShared_612_ = v_isSharedCheck_715_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_searcher_609_);
lean_inc(v_currPos_608_);
lean_dec(v_a_598_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_715_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_it_614_; lean_object* v_it_620_; lean_object* v_startPos_621_; lean_object* v_endPos_622_; 
switch(lean_obj_tag(v_searcher_609_))
{
case 0:
{
lean_object* v_pos_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_647_; 
lean_del_object(v___x_611_);
v_pos_635_ = lean_ctor_get(v_searcher_609_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_searcher_609_);
if (v_isSharedCheck_647_ == 0)
{
v___x_637_ = v_searcher_609_;
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_pos_635_);
lean_dec(v_searcher_609_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v_startInclusive_639_; lean_object* v_endExclusive_640_; lean_object* v___x_641_; uint8_t v_decide_642_; 
v_startInclusive_639_ = lean_ctor_get(v___x_596_, 1);
v_endExclusive_640_ = lean_ctor_get(v___x_596_, 2);
v___x_641_ = lean_nat_sub(v_endExclusive_640_, v_startInclusive_639_);
v_decide_642_ = lean_nat_dec_eq(v_pos_635_, v___x_641_);
lean_dec(v___x_641_);
if (v_decide_642_ == 0)
{
lean_object* v___x_644_; 
lean_inc(v_pos_635_);
if (v_isShared_638_ == 0)
{
lean_ctor_set_tag(v___x_637_, 1);
v___x_644_ = v___x_637_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_pos_635_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_inc(v_pos_635_);
v_it_620_ = v___x_644_;
v_startPos_621_ = v_pos_635_;
v_endPos_622_ = v_pos_635_;
goto v___jp_619_;
}
}
else
{
lean_object* v___x_646_; 
lean_del_object(v___x_637_);
v___x_646_ = lean_box(3);
lean_inc(v_pos_635_);
v_it_620_ = v___x_646_;
v_startPos_621_ = v_pos_635_;
v_endPos_622_ = v_pos_635_;
goto v___jp_619_;
}
}
}
case 1:
{
lean_object* v_pos_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_656_; 
v_pos_648_ = lean_ctor_get(v_searcher_609_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v_searcher_609_);
if (v_isSharedCheck_656_ == 0)
{
v___x_650_ = v_searcher_609_;
v_isShared_651_ = v_isSharedCheck_656_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_pos_648_);
lean_dec(v_searcher_609_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_656_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_652_ = lean_string_utf8_next_fast(v___x_595_, v_pos_648_);
lean_dec(v_pos_648_);
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 0);
lean_ctor_set(v___x_650_, 0, v___x_652_);
v___x_654_ = v___x_650_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
v_it_614_ = v___x_654_;
goto v___jp_613_;
}
}
}
case 2:
{
lean_object* v_needle_657_; lean_object* v_table_658_; lean_object* v_stackPos_659_; lean_object* v_needlePos_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_714_; 
v_needle_657_ = lean_ctor_get(v_searcher_609_, 0);
v_table_658_ = lean_ctor_get(v_searcher_609_, 1);
v_stackPos_659_ = lean_ctor_get(v_searcher_609_, 2);
v_needlePos_660_ = lean_ctor_get(v_searcher_609_, 3);
v_isSharedCheck_714_ = !lean_is_exclusive(v_searcher_609_);
if (v_isSharedCheck_714_ == 0)
{
v___x_662_ = v_searcher_609_;
v_isShared_663_ = v_isSharedCheck_714_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_needlePos_660_);
lean_inc(v_stackPos_659_);
lean_inc(v_table_658_);
lean_inc(v_needle_657_);
lean_dec(v_searcher_609_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_714_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_str_664_; lean_object* v_startInclusive_665_; lean_object* v_endExclusive_666_; lean_object* v_basePos_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_str_664_ = lean_ctor_get(v_needle_657_, 0);
v_startInclusive_665_ = lean_ctor_get(v_needle_657_, 1);
v_endExclusive_666_ = lean_ctor_get(v_needle_657_, 2);
v_basePos_667_ = lean_nat_sub(v_stackPos_659_, v_needlePos_660_);
v___x_668_ = lean_nat_sub(v_endExclusive_666_, v_startInclusive_665_);
v___x_669_ = lean_nat_add(v_basePos_667_, v___x_668_);
v___x_670_ = lean_nat_dec_le(v___x_669_, v___x_597_);
lean_dec(v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
lean_dec(v___x_668_);
lean_del_object(v___x_662_);
lean_dec(v_needlePos_660_);
lean_dec(v_stackPos_659_);
lean_dec_ref(v_table_658_);
lean_dec_ref(v_needle_657_);
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = lean_nat_add(v_basePos_667_, v___x_671_);
lean_dec(v_basePos_667_);
v___x_673_ = lean_nat_dec_le(v___x_672_, v___x_597_);
lean_dec(v___x_672_);
if (v___x_673_ == 0)
{
lean_del_object(v___x_611_);
goto v___jp_633_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = lean_box(3);
v_it_614_ = v___x_674_;
goto v___jp_613_;
}
}
else
{
uint8_t v_stackByte_675_; lean_object* v___x_676_; uint8_t v_patByte_677_; uint8_t v___x_678_; 
lean_dec(v_basePos_667_);
lean_inc(v_stackPos_659_);
v_stackByte_675_ = lean_string_get_byte_fast(v___x_595_, v_stackPos_659_);
v___x_676_ = lean_nat_add(v_startInclusive_665_, v_needlePos_660_);
v_patByte_677_ = lean_string_get_byte_fast(v_str_664_, v___x_676_);
v___x_678_ = lean_uint8_dec_eq(v_stackByte_675_, v_patByte_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; uint8_t v_decide_680_; 
lean_dec(v___x_668_);
v___x_679_ = lean_unsigned_to_nat(0u);
v_decide_680_ = lean_nat_dec_eq(v_needlePos_660_, v___x_679_);
if (v_decide_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v_newNeedlePos_683_; uint8_t v___x_684_; 
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_sub(v_needlePos_660_, v___x_681_);
lean_dec(v_needlePos_660_);
v_newNeedlePos_683_ = lean_array_fget_borrowed(v_table_658_, v___x_682_);
lean_dec(v___x_682_);
v___x_684_ = lean_nat_dec_eq(v_newNeedlePos_683_, v___x_679_);
if (v___x_684_ == 0)
{
lean_object* v___x_686_; 
lean_inc(v_newNeedlePos_683_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 3, v_newNeedlePos_683_);
v___x_686_ = v___x_662_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_needle_657_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_table_658_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_stackPos_659_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v_newNeedlePos_683_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
v_it_614_ = v___x_686_;
goto v___jp_613_;
}
}
else
{
lean_object* v_nextStackPos_688_; lean_object* v___x_690_; 
v_nextStackPos_688_ = l_String_Slice_posGE___redArg(v___x_596_, v_stackPos_659_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 3, v___x_679_);
lean_ctor_set(v___x_662_, 2, v_nextStackPos_688_);
v___x_690_ = v___x_662_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_needle_657_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_table_658_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_nextStackPos_688_);
lean_ctor_set(v_reuseFailAlloc_691_, 3, v___x_679_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v_it_614_ = v___x_690_;
goto v___jp_613_;
}
}
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_nextStackPos_694_; lean_object* v___x_696_; 
lean_dec(v_needlePos_660_);
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_nat_add(v_stackPos_659_, v___x_692_);
lean_dec(v_stackPos_659_);
v_nextStackPos_694_ = l_String_Slice_posGE___redArg(v___x_596_, v___x_693_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 3, v___x_679_);
lean_ctor_set(v___x_662_, 2, v_nextStackPos_694_);
v___x_696_ = v___x_662_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_needle_657_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_table_658_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_nextStackPos_694_);
lean_ctor_set(v_reuseFailAlloc_697_, 3, v___x_679_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
v_it_614_ = v___x_696_;
goto v___jp_613_;
}
}
}
else
{
lean_object* v___x_698_; lean_object* v_nextStackPos_699_; lean_object* v_nextNeedlePos_700_; uint8_t v_decide_701_; 
lean_del_object(v___x_611_);
v___x_698_ = lean_unsigned_to_nat(1u);
v_nextStackPos_699_ = lean_nat_add(v_stackPos_659_, v___x_698_);
lean_dec(v_stackPos_659_);
v_nextNeedlePos_700_ = lean_nat_add(v_needlePos_660_, v___x_698_);
lean_dec(v_needlePos_660_);
v_decide_701_ = lean_nat_dec_eq(v_nextNeedlePos_700_, v___x_668_);
lean_dec(v___x_668_);
if (v_decide_701_ == 0)
{
lean_object* v___x_703_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 3, v_nextNeedlePos_700_);
lean_ctor_set(v___x_662_, 2, v_nextStackPos_699_);
v___x_703_ = v___x_662_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_needle_657_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_table_658_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_nextStackPos_699_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v_nextNeedlePos_700_);
v___x_703_ = v_reuseFailAlloc_706_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v_currPos_608_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v_a_598_ = v___x_704_;
goto _start;
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_707_ = lean_nat_sub(v_nextStackPos_699_, v_nextNeedlePos_700_);
lean_dec(v_nextNeedlePos_700_);
v___x_708_ = l_String_Slice_pos_x21(v___x_596_, v___x_707_);
lean_dec(v___x_707_);
v___x_709_ = l_String_Slice_pos_x21(v___x_596_, v_nextStackPos_699_);
v___x_710_ = lean_unsigned_to_nat(0u);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 3, v___x_710_);
lean_ctor_set(v___x_662_, 2, v_nextStackPos_699_);
v___x_712_ = v___x_662_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_needle_657_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_table_658_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_nextStackPos_699_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
v_it_620_ = v___x_712_;
v_startPos_621_ = v___x_708_;
v_endPos_622_ = v___x_709_;
goto v___jp_619_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_611_);
goto v___jp_633_;
}
}
v___jp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 1, v_it_614_);
v___x_616_ = v___x_611_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_currPos_608_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_it_614_);
v___x_616_ = v_reuseFailAlloc_618_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
v_a_598_ = v___x_616_;
goto _start;
}
}
v___jp_619_:
{
lean_object* v_slice_623_; lean_object* v_startInclusive_624_; lean_object* v_endExclusive_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
v_slice_623_ = l_String_Slice_subslice_x21(v___x_596_, v_currPos_608_, v_startPos_621_);
v_startInclusive_624_ = lean_ctor_get(v_slice_623_, 0);
v_endExclusive_625_ = lean_ctor_get(v_slice_623_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_slice_623_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v_slice_623_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_endExclusive_625_);
lean_inc(v_startInclusive_624_);
lean_dec(v_slice_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v_nextIt_630_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_it_620_);
lean_ctor_set(v___x_627_, 0, v_endPos_622_);
v_nextIt_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_endPos_622_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_it_620_);
v_nextIt_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
v_it_601_ = v_nextIt_630_;
v_startInclusive_602_ = v_startInclusive_624_;
v_endExclusive_603_ = v_endExclusive_625_;
goto v___jp_600_;
}
}
}
v___jp_633_:
{
lean_object* v___x_634_; 
v___x_634_ = lean_box(1);
lean_inc(v___x_597_);
v_it_601_ = v___x_634_;
v_startInclusive_602_ = v_currPos_608_;
v_endExclusive_603_ = v___x_597_;
goto v___jp_600_;
}
}
}
else
{
lean_dec(v___x_597_);
lean_dec_ref(v___x_595_);
return v_b_599_;
}
v___jp_600_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
lean_inc_ref(v___x_595_);
v___x_604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_604_, 0, v___x_595_);
lean_ctor_set(v___x_604_, 1, v_startInclusive_602_);
lean_ctor_set(v___x_604_, 2, v_endExclusive_603_);
v___x_605_ = l_String_Slice_toString(v___x_604_);
lean_dec_ref_known(v___x_604_, 3);
v___x_606_ = lean_array_push(v_b_599_, v___x_605_);
v_a_598_ = v_it_601_;
v_b_599_ = v___x_606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(lean_object* v___x_716_, lean_object* v___x_717_, lean_object* v___x_718_, lean_object* v_a_719_, lean_object* v_b_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_716_, v___x_717_, v___x_718_, v_a_719_, v_b_720_);
lean_dec_ref(v___x_717_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object* v_p_724_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_725_ = l_System_FilePath_normalize(v_p_724_);
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_string_utf8_byte_size(v___x_725_);
lean_inc_ref(v___x_725_);
v___x_728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_728_, 0, v___x_725_);
lean_ctor_set(v___x_728_, 1, v___x_726_);
lean_ctor_set(v___x_728_, 2, v___x_727_);
v___x_729_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
v___x_730_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_731_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_725_, v___x_728_, v___x_727_, v___x_729_, v___x_730_);
lean_dec_ref_known(v___x_728_, 3);
v___x_732_ = lean_array_to_list(v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(lean_object* v___x_733_, lean_object* v___x_734_, lean_object* v___x_735_, lean_object* v_inst_736_, lean_object* v_R_737_, lean_object* v_a_738_, lean_object* v_b_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_733_, v___x_734_, v___x_735_, v_a_738_, v_b_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(lean_object* v___x_741_, lean_object* v___x_742_, lean_object* v___x_743_, lean_object* v_inst_744_, lean_object* v_R_745_, lean_object* v_a_746_, lean_object* v_b_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(v___x_741_, v___x_742_, v___x_743_, v_inst_744_, v_R_745_, v_a_746_, v_b_747_);
lean_dec_ref(v___x_742_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object* v_parts_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_obj_once(&l_System_FilePath_join___closed__0, &l_System_FilePath_join___closed__0_once, _init_l_System_FilePath_join___closed__0);
v___x_751_ = l_String_intercalate(v___x_750_, v_parts_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object* v_toString_752_){
_start:
{
lean_inc_ref(v_toString_752_);
return v_toString_752_;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object* v_toString_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_System_instCoeStringFilePath___lam__0(v_toString_753_);
lean_dec_ref(v_toString_753_);
return v_res_754_;
}
}
static uint32_t _init_l_System_SearchPath_separator(void){
_start:
{
uint8_t v___x_757_; 
v___x_757_ = l_System_Platform_isWindows;
if (v___x_757_ == 0)
{
uint32_t v___x_758_; 
v___x_758_ = 58;
return v___x_758_;
}
else
{
uint32_t v___x_759_; 
v___x_759_ = 59;
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___closed__0));
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg___boxed(lean_object* v___dummy_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg();
return v_res_765_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0(void){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___redArg();
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(lean_object* v_s_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___boxed(lean_object* v_s_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v_s_769_);
lean_dec_ref(v_s_769_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(lean_object* v_s_771_, lean_object* v___x_772_, lean_object* v___x_773_, lean_object* v_a_774_, lean_object* v_b_775_){
_start:
{
lean_object* v_it_777_; lean_object* v_startInclusive_778_; lean_object* v_endExclusive_779_; 
if (lean_obj_tag(v_a_774_) == 0)
{
lean_object* v_currPos_783_; lean_object* v_searcher_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_807_; 
v_currPos_783_ = lean_ctor_get(v_a_774_, 0);
v_searcher_784_ = lean_ctor_get(v_a_774_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_a_774_);
if (v_isSharedCheck_807_ == 0)
{
v___x_786_ = v_a_774_;
v_isShared_787_ = v_isSharedCheck_807_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_searcher_784_);
lean_inc(v_currPos_783_);
lean_dec(v_a_774_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_807_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
uint8_t v_decide_788_; 
v_decide_788_ = lean_nat_dec_eq(v_searcher_784_, v___x_773_);
if (v_decide_788_ == 0)
{
uint32_t v___x_789_; uint32_t v___x_790_; uint8_t v___x_791_; 
v___x_789_ = l_System_SearchPath_separator;
v___x_790_ = lean_string_utf8_get_fast(v_s_771_, v_searcher_784_);
v___x_791_ = lean_uint32_dec_eq(v___x_790_, v___x_789_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_string_utf8_next_fast(v_s_771_, v_searcher_784_);
lean_dec(v_searcher_784_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v___x_792_);
v___x_794_ = v___x_786_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_currPos_783_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_792_);
v___x_794_ = v_reuseFailAlloc_796_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
v_a_774_ = v___x_794_;
goto _start;
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_slice_800_; lean_object* v_nextIt_802_; 
v___x_797_ = lean_string_utf8_next_fast(v_s_771_, v_searcher_784_);
v___x_798_ = lean_nat_sub(v___x_797_, v_searcher_784_);
v___x_799_ = lean_nat_add(v_searcher_784_, v___x_798_);
lean_dec(v___x_798_);
v_slice_800_ = l_String_Slice_subslice_x21(v___x_772_, v_currPos_783_, v_searcher_784_);
lean_inc(v___x_799_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v___x_799_);
lean_ctor_set(v___x_786_, 0, v___x_799_);
v_nextIt_802_ = v___x_786_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_799_);
v_nextIt_802_ = v_reuseFailAlloc_805_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v_startInclusive_803_; lean_object* v_endExclusive_804_; 
v_startInclusive_803_ = lean_ctor_get(v_slice_800_, 0);
lean_inc(v_startInclusive_803_);
v_endExclusive_804_ = lean_ctor_get(v_slice_800_, 1);
lean_inc(v_endExclusive_804_);
lean_dec_ref(v_slice_800_);
v_it_777_ = v_nextIt_802_;
v_startInclusive_778_ = v_startInclusive_803_;
v_endExclusive_779_ = v_endExclusive_804_;
goto v___jp_776_;
}
}
}
else
{
lean_object* v___x_806_; 
lean_del_object(v___x_786_);
lean_dec(v_searcher_784_);
v___x_806_ = lean_box(1);
lean_inc(v___x_773_);
v_it_777_ = v___x_806_;
v_startInclusive_778_ = v_currPos_783_;
v_endExclusive_779_ = v___x_773_;
goto v___jp_776_;
}
}
}
else
{
lean_dec(v___x_773_);
return v_b_775_;
}
v___jp_776_:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_string_utf8_extract_fast(v_s_771_, v_startInclusive_778_, v_endExclusive_779_);
lean_dec(v_endExclusive_779_);
lean_dec(v_startInclusive_778_);
v___x_781_ = lean_array_push(v_b_775_, v___x_780_);
v_a_774_ = v_it_777_;
v_b_775_ = v___x_781_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg___boxed(lean_object* v_s_808_, lean_object* v___x_809_, lean_object* v___x_810_, lean_object* v_a_811_, lean_object* v_b_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_808_, v___x_809_, v___x_810_, v_a_811_, v_b_812_);
lean_dec_ref(v___x_809_);
lean_dec_ref(v_s_808_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object* v_s_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_string_utf8_byte_size(v_s_814_);
lean_inc_ref(v_s_814_);
v___x_817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_817_, 0, v_s_814_);
lean_ctor_set(v___x_817_, 1, v___x_815_);
lean_ctor_set(v___x_817_, 2, v___x_816_);
v___x_818_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0);
v___x_819_ = ((lean_object*)(l_System_FilePath_components___closed__0));
v___x_820_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_814_, v___x_817_, v___x_816_, v___x_818_, v___x_819_);
lean_dec_ref_known(v___x_817_, 3);
lean_dec_ref(v_s_814_);
v___x_821_ = lean_array_to_list(v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(lean_object* v_s_822_, lean_object* v___x_823_, lean_object* v___x_824_, lean_object* v_inst_825_, lean_object* v_R_826_, lean_object* v_a_827_, lean_object* v_b_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_822_, v___x_823_, v___x_824_, v_a_827_, v_b_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___boxed(lean_object* v_s_830_, lean_object* v___x_831_, lean_object* v___x_832_, lean_object* v_inst_833_, lean_object* v_R_834_, lean_object* v_a_835_, lean_object* v_b_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(v_s_830_, v___x_831_, v___x_832_, v_inst_833_, v_R_834_, v_a_835_, v_b_836_);
lean_dec_ref(v___x_831_);
lean_dec_ref(v_s_830_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
if (lean_obj_tag(v_a_838_) == 0)
{
lean_object* v___x_840_; 
v___x_840_ = l_List_reverse___redArg(v_a_839_);
return v___x_840_;
}
else
{
lean_object* v_head_841_; lean_object* v_tail_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_head_841_ = lean_ctor_get(v_a_838_, 0);
v_tail_842_ = lean_ctor_get(v_a_838_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_a_838_);
if (v_isSharedCheck_850_ == 0)
{
v___x_844_ = v_a_838_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_tail_842_);
lean_inc(v_head_841_);
lean_dec(v_a_838_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_a_839_);
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_head_841_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_a_839_);
v___x_847_ = v_reuseFailAlloc_849_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
v_a_838_ = v_tail_842_;
v_a_839_ = v___x_847_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_System_SearchPath_toString___closed__0(void){
_start:
{
uint32_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = l_System_SearchPath_separator;
v___x_852_ = ((lean_object*)(l_System_instInhabitedFilePath_default___closed__0));
v___x_853_ = lean_string_push(v___x_852_, v___x_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object* v_path_854_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_855_ = lean_obj_once(&l_System_SearchPath_toString___closed__0, &l_System_SearchPath_toString___closed__0_once, _init_l_System_SearchPath_toString___closed__0);
v___x_856_ = lean_box(0);
v___x_857_ = l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(v_path_854_, v___x_856_);
v___x_858_ = l_String_intercalate(v___x_855_, v___x_857_);
return v___x_858_;
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
